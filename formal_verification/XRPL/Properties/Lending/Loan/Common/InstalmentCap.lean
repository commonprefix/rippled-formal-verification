import XRPL.Properties.Lending.Loan.Common.InterestDue

/-! # A scheduled instalment takes at most the rounded periodic payment

The deltas of an instalment that isn't the last are capped by PeriodicPayment rounded up at LoanScale: the
shortage step takes any excess off, interest first, then the management fee, then the principal. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private Number.min_val Number.max_val Number.clamp_val Number.floorZero
  from XRPL.Properties.Lending.Loan.Common.InterestDue

/-- A branch on `c` that passes: the branch taken, with whether `c` held. -/
private lemma ite_bind_ok_cond {α β : Type} (c : Prop) [Decidable c] (x : Except Error α) (d : α)
    (K : α → Except Error β) (b : β) (h : (if c then x >>= K else pure d >>= K) = .ok b) :
    ∃ a, ((¬ c ∧ a = d) ∨ (c ∧ x = .ok a)) ∧ K a = .ok b := by
  split at h
  · obtain ⟨a, ha, h⟩ := bind_ok_peel _ _ _ h
    exact ⟨a, Or.inr ⟨‹c›, ha⟩, h⟩
  · exact ⟨d, Or.inl ⟨‹¬ c›, rfl⟩, h⟩

/-- A normalized number's sign is negative exactly when its value is. -/
private lemma Number.signum_neg_iff' {n : Number} (hn : n.isNormalized) : n.signum < 0 ↔ n.toRat < 0 := by
  rw [← not_le, ← not_le, Number.signum_nonneg_iff_toRat hn]

/-- Taking part of a positive excess off an amount of at least zero, exactly. Both stay at least zero, and
`value − excess` is kept. -/
private lemma reduceCapped_exact {s : Int} (value excess v' e' : Number) (hv : Number.OnGrid s value)
    (he : Number.OnGrid s excess) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hvb : value.toRat < 2 ^ 63 * 10 ^ s) (heb : excess.toRat < 2 ^ 63 * 10 ^ s) (hv0 : 0 ≤ value.toRat)
    (he0 : 0 ≤ excess.toRat) (h : reduceCapped value excess = .ok (v', e')) :
    Number.OnGrid s v' ∧ Number.OnGrid s e' ∧ 0 ≤ v'.toRat ∧ 0 ≤ e'.toRat ∧
      v'.toRat = value.toRat - min value.toRat excess.toRat ∧
      e'.toRat = excess.toRat - min value.toRat excess.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold reduceCapped at h
  simp only [bind, Except.bind] at h
  split at h
  · walk_ok
    have h1 := Except.ok.inj ‹pure _ = Except.ok (v', e')›
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hm := Number.OnGrid.min hv he
    have hmv := Number.min_val value excess hv.1 he.1
    have hm0 : 0 ≤ min value.toRat excess.toRat := le_min hv0 he0
    have v1 := Number.OnGrid.sub_toRat hv hm hs (by
      rw [hmv, abs_lt]; constructor <;> linarith [min_le_left value.toRat excess.toRat]) ‹_›
    have v2 := Number.OnGrid.sub_toRat he hm hs (by
      rw [hmv, abs_lt]; constructor <;> linarith [min_le_right value.toRat excess.toRat]) ‹_›
    rw [hmv] at v1 v2
    refine ⟨Number.OnGrid.sub hv hm hs ‹_›, Number.OnGrid.sub he hm hs ‹_›, ?_, ?_, v1, v2⟩
    · rw [v1]; linarith [min_le_left value.toRat excess.toRat]
    · rw [v2]; linarith [min_le_right value.toRat excess.toRat]
  · rename_i hgt
    have h1 := Except.ok.inj h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have he' : excess.toRat ≤ 0 := by
      by_contra hc
      push Not at hc
      exact hgt ((operator_gt_iff _ _ he.1 Number.zero_isNormalized).mpr (by rw [Number.toRat_zero]; exact hc))
    have hz : excess.toRat = 0 := le_antisymm he' he0
    refine ⟨hv, he, hv0, he0, ?_, ?_⟩
    · rw [hz, min_eq_right hv0]; ring
    · rw [hz, min_eq_right hv0]; ring

/-- Deltas that are each at least zero and on the grid, together below `2^63` units. -/
private structure LoanStateDeltas.Small (s : Int) (d : LoanStateDeltas) : Prop where
  principal_grid : Number.OnGrid s d.principal
  interest_grid : Number.OnGrid s d.interest
  managementFee_grid : Number.OnGrid s d.managementFee
  principal_nonneg : 0 ≤ d.principal.toRat
  interest_nonneg : 0 ≤ d.interest.toRat
  managementFee_nonneg : 0 ≤ d.managementFee.toRat
  sum_lt : d.principal.toRat + d.interest.toRat + d.managementFee.toRat < 2 ^ 63 * 10 ^ s

/-- Taking an excess off deltas of at least zero keeps them at least zero, and takes off exactly the excess
when the deltas cover it. -/
private lemma LoanStateDeltas.Small.reduce {s : Int} {d d' : LoanStateDeltas} {excess : Number}
    (hd : d.Small s) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (he : Number.OnGrid s excess)
    (he0 : 0 ≤ excess.toRat) (heb : excess.toRat < 2 ^ 63 * 10 ^ s) (hr : d.reduceByExcess excess = .ok d') :
    d'.Small s ∧ (excess.toRat ≤ d.principal.toRat + d.interest.toRat + d.managementFee.toRat →
      d'.principal.toRat + d'.interest.toRat + d'.managementFee.toRat =
        d.principal.toRat + d.interest.toRat + d.managementFee.toRat - excess.toRat) := by
  obtain ⟨gp, gi, gm, hp0, hi0, hm0, hsum⟩ := hd
  have hpow : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold LoanStateDeltas.reduceByExcess at hr
  simp only [bind, Except.bind] at hr
  walk_ok
  rename_i _ a ha _ b hb' _ c hc hd'
  obtain rfl := (Except.ok.inj hd').symm
  obtain ⟨ga1, ga2, ha1, ha2, va1, va2⟩ := reduceCapped_exact _ _ a.1 a.2 gi he hs (by linarith) (by linarith)
    hi0 he0 ha
  obtain ⟨gb1, gb2, hb1, hb2, vb1, vb2⟩ := reduceCapped_exact _ _ b.1 b.2 gm ga2 hs (by linarith)
    (by rw [va2]; linarith [le_min hi0 he0]) hm0 ha2 hb'
  obtain ⟨gc1, -, hc1, -, vc1, -⟩ := reduceCapped_exact _ _ c.1 c.2 gp gb2 hs (by linarith)
    (by rw [vb2]; linarith [le_min hm0 ha2, le_min hi0 he0, min_le_right d.interest.toRat excess.toRat]) hp0 hb2 hc
  refine ⟨⟨gc1, ga1, gb1, hc1, ha1, hb1, ?_⟩, fun hcov => ?_⟩
  · show c.1.toRat + a.1.toRat + b.1.toRat < _
    rw [vc1, va1, vb1]
    linarith [le_min hp0 hb2, le_min hi0 he0, le_min hm0 ha2]
  · show c.1.toRat + a.1.toRat + b.1.toRat = _
    have hfinal : min d.principal.toRat b.2.toRat + min d.interest.toRat excess.toRat +
        min d.managementFee.toRat a.2.toRat = excess.toRat := by
      rcases le_total excess.toRat d.interest.toRat with h1 | h1
      · have ea2 : a.2.toRat = 0 := by rw [va2, min_eq_right h1]; ring
        have eb2 : b.2.toRat = 0 := by rw [vb2, ea2, min_eq_right hm0]; ring
        rw [min_eq_right h1, ea2, eb2, min_eq_right hm0, min_eq_right hp0]; ring
      · have ea2 : a.2.toRat = excess.toRat - d.interest.toRat := by rw [va2, min_eq_left h1]
        rcases le_total a.2.toRat d.managementFee.toRat with h2 | h2
        · have eb2 : b.2.toRat = 0 := by rw [vb2, min_eq_right h2]; ring
          rw [min_eq_left h1, min_eq_right h2, eb2, min_eq_right hp0, ea2]; ring
        · have eb2 : b.2.toRat = excess.toRat - d.interest.toRat - d.managementFee.toRat := by
            rw [vb2, min_eq_left h2, ea2]
          have h3 : b.2.toRat ≤ d.principal.toRat := by rw [eb2]; linarith
          rw [min_eq_left h1, min_eq_left h2, min_eq_right h3, eb2]; ring
    rw [vc1, va1, vb1]
    linarith

/-- A scheduled instalment that isn't the last takes at most PeriodicPayment rounded up off the loan. `pp'` is
PeriodicPayment rounded up at LoanScale. -/
lemma Loan.scheduledComponents_value_le (l : Loan) (pc : PaymentComponents) (pp' : Number) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hpp : STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp')
    (h : Loan.scheduledComponents l = .ok pc) (hnf : pc.isFinal = false) :
    pc.totalValueDelta.toRat ≤ pp'.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp'', hpp'', h⟩ := bind_ok_peel _ _ _ h
  rw [hpp] at hpp''
  obtain rfl := Except.ok.inj hpp''
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    simp at hnf
  rename_i hnf'
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨cs, hcs, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, hpr1, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hpr1
  obtain ⟨ts, hts, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tpo, htpo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨ti, hti, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tm, htm, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨dp, hdp, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨di, hdi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨dm, hdm, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨room, hroom, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨ppi, hppi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨rff, hrff, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨t1, ht1, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨ov, hov, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d2, hd2, h⟩ := ite_bind_ok_cond _ _ _ _ _ h
  obtain ⟨t2, ht2, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sh, hsh, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d3, hd3, h⟩ := ite_bind_ok_cond _ _ _ _ _ h
  obtain ⟨t3, ht3, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  -- the current state is the loan's amounts, with interestDue `T - P - M ≥ 0`
  obtain ⟨t, p, m, -, -, -, htv, hpv, hmv, hiv, -, h1, h2, h3⟩ := Loan.state_units l cs hcs
  have hiD : cs.interestDue.toRat = l.totalValueOutstanding.toRat - l.principalOutstanding.toRat -
      l.managementFeeOutstanding.toRat := by
    rw [hiv.val, ← h1, ← h2, ← h3, htv.val, hpv.val, hmv.val]; push_cast; ring
  have gI : Number.OnGrid l.loanScale cs.interestDue := ⟨hiv.norm, _, hiv.val⟩
  have gcT : Number.OnGrid l.loanScale cs.valueOutstanding := by rw [h1]; exact gT
  have gcP : Number.OnGrid l.loanScale cs.principalOutstanding := by rw [h2]; exact gP
  have gcM : Number.OnGrid l.loanScale cs.managementFeeDue := by rw [h3]; exact gM
  have vcT : cs.valueOutstanding.toRat = l.totalValueOutstanding.toRat := by rw [h1]
  have vcP : cs.principalOutstanding.toRat = l.principalOutstanding.toRat := by rw [h2]
  have vcM : cs.managementFeeDue.toRat = l.managementFeeOutstanding.toRat := by rw [h3]
  set T := l.totalValueOutstanding.toRat with hTdef
  set P := l.principalOutstanding.toRat with hPdef
  set M := l.managementFeeOutstanding.toRat with hMdef
  have hi' : 0 ≤ T - P - M := hi
  have hpos : (0 : ℚ) < 2 ^ 63 * 10 ^ l.loanScale := by positivity
  -- the periodic payment rounded up is below the total value
  have gpp := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hpp
  have hpp0 : 0 ≤ pp'.toRat := by
    have : 0 < l.periodicPayment.toRat := l.exact.periodicPayment_pos
    exact STAmount.roundToNumericType_some_nonneg _ _ _ _ _ l.wf.periodicPayment_norm this.le
      (Or.inr (Or.inl rfl)) hr hpp
  have hppT : pp'.toRat < T := by
    have : l.totalValueOutstanding.operator_le pp' = false := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnf'
      simpa using hnf'.2
    rw [← not_le, ← operator_le_iff _ _ gT.1 gpp.1, this]
    simp
  have gtpo := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint htpo
  have gti := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hti
  have gtm := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint htm
  obtain ⟨gp0, vp0⟩ := Number.floorZero (Number.OnGrid.sub gcP gtpo hs hdp)
  obtain ⟨gi0, vi0⟩ := Number.floorZero (Number.OnGrid.sub gI gti hs hdi)
  obtain ⟨gm0, vm0⟩ := Number.floorZero (Number.OnGrid.sub gcM gtm hs hdm)
  set P0 := ({ principal := dp, interest := di, managementFee := dm } : LoanStateDeltas).nonNegative.principal
  set I0 := ({ principal := dp, interest := di, managementFee := dm } : LoanStateDeltas).nonNegative.interest
  set M0 := ({ principal := dp, interest := di, managementFee := dm } : LoanStateDeltas).nonNegative.managementFee
  have gP0 : Number.OnGrid l.loanScale P0 := gp0
  have gI0 : Number.OnGrid l.loanScale I0 := gi0
  have gM0 : Number.OnGrid l.loanScale M0 := gm0
  have vP0 : 0 ≤ P0.toRat := by rw [show P0.toRat = max 0 dp.toRat from vp0]; exact le_max_left _ _
  have vI0 : 0 ≤ I0.toRat := by rw [show I0.toRat = max 0 di.toRat from vi0]; exact le_max_left _ _
  have vM0 : 0 ≤ M0.toRat := by rw [show M0.toRat = max 0 dm.toRat from vm0]; exact le_max_left _ _
  have gP1 := Number.OnGrid.min gP0 gcP
  have vP1 := Number.min_val _ _ gP0.1 gcP.1
  rw [vcP] at vP1
  have gRoom := Number.OnGrid.sub gpp gP1 hs hroom
  have gR := Number.OnGrid.max (Number.OnGrid.zero l.loanScale) gRoom
  have vR := Number.max_val _ _ Number.zero_isNormalized gRoom.1
  rw [Number.toRat_zero] at vR
  have gIm := Number.OnGrid.min gI0 gR
  have vIm := Number.min_val _ _ gI0.1 gR.1
  have gI1 := Number.OnGrid.min gIm gI
  have vI1 := Number.min_val _ _ gIm.1 gI.1
  rw [hiD, vIm, vR] at vI1
  set P1 := Number.min P0 cs.principalOutstanding with hP1def
  set I1 := Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue with hI1def
  have hP1 : 0 ≤ P1.toRat ∧ P1.toRat ≤ P := by rw [vP1]; exact ⟨le_min vP0 hP0, min_le_right _ _⟩
  have vroom := Number.OnGrid.sub_toRat gpp gP1 hs (by rw [abs_lt]; constructor <;> linarith) hroom
  have hI1 : 0 ≤ I1.toRat ∧ I1.toRat ≤ T - P - M ∧ I1.toRat ≤ max 0 (pp'.toRat - P1.toRat) := by
    rw [vI1, ← vroom]
    exact ⟨le_min (le_min vI0 (le_max_left _ _)) hi', min_le_right _ _,
      le_trans (min_le_left _ _) (min_le_right _ _)⟩
  have vppi := Number.OnGrid.add_toRat gP1 gI1 hs (by rw [abs_lt]; constructor <;> linarith) hppi
  have gppi := Number.OnGrid.add gP1 gI1 hs hppi
  have vrff := Number.OnGrid.sub_toRat gpp gppi hs (by rw [abs_lt, vppi]; constructor <;> linarith) hrff
  have grff := Number.OnGrid.sub gpp gppi hs hrff
  have gMm := Number.OnGrid.min gM0 grff
  have vMm := Number.min_val _ _ gM0.1 grff.1
  have gM1 := Number.OnGrid.min gMm gcM
  have vM1 := Number.min_val _ _ gMm.1 gcM.1
  rw [vcM, vMm, vrff, vppi] at vM1
  set M1 := Number.min (Number.min M0 rff) cs.managementFeeDue with hM1def
  have vt1 : t1.toRat = P1.toRat + I1.toRat + M1.toRat := by
    unfold LoanStateDeltas.total at ht1
    obtain ⟨u, hu, ht1⟩ := bind_ok_peel _ _ _ ht1
    have vu := Number.OnGrid.add_toRat gP1 gI1 hs (by rw [abs_lt]; constructor <;> linarith) hu
    have gu := Number.OnGrid.add gP1 gI1 hs hu
    have hM1le : M1.toRat ≤ M := by rw [vM1]; exact min_le_right _ _
    have hM1b : |M1.toRat| ≤ T := by
      rw [vM1, abs_le]
      constructor
      · refine le_min (le_min (by linarith) (by linarith)) (by linarith)
      · exact le_trans (min_le_right _ _) (by linarith)
    rw [Number.OnGrid.add_toRat gu gM1 hs (by
      rw [vu, abs_lt]; constructor <;> linarith [(abs_le.mp hM1b).1, (abs_le.mp hM1b).2, hM1le]) ht1, vu]
  have gt1 : Number.OnGrid l.loanScale t1 := by
    unfold LoanStateDeltas.total at ht1
    obtain ⟨u, hu, ht1⟩ := bind_ok_peel _ _ _ ht1
    exact Number.OnGrid.add (Number.OnGrid.add gP1 gI1 hs hu) gM1 hs ht1
  -- the final total is at most `pp'`, then the clamp keeps it there
  have ht3 : Number.OnGrid l.loanScale t3 ∧ t3.toRat ≤ pp'.toRat := by
    by_cases hneg : M1.toRat < 0
    · -- a fee room below zero: principal took all the room, the total is exactly `pp'`
      have hrff0 : rff.toRat < 0 := by
        by_contra hc
        push Not at hc
        rw [vM1] at hneg
        have : 0 ≤ min (min M0.toRat (pp'.toRat - (P1.toRat + I1.toRat))) M :=
          le_min (le_min vM0 (by rw [vrff, vppi] at hc; linarith)) hM0
        linarith
      have hM1v : M1.toRat = pp'.toRat - (P1.toRat + I1.toRat) := by
        rw [vM1, min_eq_left (le_trans (min_le_right _ _) (by rw [vrff, vppi] at hrff0; linarith)),
          min_eq_right (by rw [vrff, vppi] at hrff0; linarith)]
      have hvt1 : t1.toRat = pp'.toRat := by rw [vt1, hM1v]; ring
      -- no overpayment to take off, and no shortage after
      have hov0 : ov.operator_gt Number.zero = false := by
        have vov := Number.OnGrid.sub_toRat gt1 gcT hs (by rw [hvt1, vcT, abs_lt]; constructor <;> linarith) hov
        rw [Bool.eq_false_iff]
        intro hgt
        rw [operator_gt_iff _ _ (Number.OnGrid.sub gt1 gcT hs hov).1 Number.zero_isNormalized, Number.toRat_zero,
          vov, hvt1, vcT] at hgt
        linarith
      have hd2e : d2 = { principal := P1, interest := I1, managementFee := M1 } := by
        rcases hd2 with ⟨-, rfl⟩ | ⟨hc, -⟩
        · rfl
        · rw [hov0] at hc; exact absurd hc (by decide)
      subst hd2e
      rw [ht1] at ht2
      obtain rfl := Except.ok.inj ht2
      have vsh := Number.OnGrid.sub_toRat gpp gt1 hs (by rw [hvt1, abs_lt]; constructor <;> linarith) hsh
      have hsh0 : ¬ sh.signum < 0 := by
        rw [Number.signum_neg_iff' (Number.OnGrid.sub gpp gt1 hs hsh).1, vsh, hvt1]
        simp
      have hd3e : d3 = { principal := P1, interest := I1, managementFee := M1 } := by
        rcases hd3 with ⟨-, rfl⟩ | ⟨hc, -⟩
        · rfl
        · exact absurd hc hsh0
      subst hd3e
      rw [ht1] at ht3
      obtain rfl := Except.ok.inj ht3
      exact ⟨gt1, by rw [hvt1]⟩
    · -- every delta at least zero: any reduction keeps them so, and the shortage step lands on `pp'`
      push Not at hneg
      have hsm1 : LoanStateDeltas.Small l.loanScale { principal := P1, interest := I1, managementFee := M1 } :=
        ⟨gP1, gI1, gM1, hP1.1, hI1.1, hneg, by
          show P1.toRat + I1.toRat + M1.toRat < _
          have : M1.toRat ≤ M := by rw [vM1]; exact min_le_right _ _
          linarith⟩
      have hsm2 : LoanStateDeltas.Small l.loanScale d2 ∧
          d2.principal.toRat + d2.interest.toRat + d2.managementFee.toRat ≤ P1.toRat + I1.toRat + M1.toRat := by
        rcases hd2 with ⟨-, rfl⟩ | ⟨hc, hred⟩
        · exact ⟨hsm1, le_refl _⟩
        · have gov := Number.OnGrid.sub gt1 gcT hs hov
          have vov := Number.OnGrid.sub_toRat gt1 gcT hs (by
            rw [vt1, vcT, abs_lt]; constructor <;> linarith [hsm1.sum_lt]) hov
          have hov0 : 0 < ov.toRat := by
            have := (operator_gt_iff _ _ gov.1 Number.zero_isNormalized).mp hc
            rwa [Number.toRat_zero] at this
          have hovb : ov.toRat < 2 ^ 63 * 10 ^ l.loanScale := by rw [vov, vt1, vcT]; linarith [hsm1.sum_lt]
          have hovle : ov.toRat ≤ P1.toRat + I1.toRat + M1.toRat := by rw [vov, vt1, vcT]; linarith
          obtain ⟨hsm, hsum⟩ := hsm1.reduce hs gov hov0.le hovb hred
          refine ⟨hsm, ?_⟩
          rw [hsum hovle]
          linarith
      obtain ⟨hsm2, hle2⟩ := hsm2
      have vt2 : t2.toRat = d2.principal.toRat + d2.interest.toRat + d2.managementFee.toRat := by
        unfold LoanStateDeltas.total at ht2
        obtain ⟨u, hu, ht2⟩ := bind_ok_peel _ _ _ ht2
        have vu := Number.OnGrid.add_toRat hsm2.principal_grid hsm2.interest_grid hs (by
          rw [abs_lt]; constructor <;> linarith [hsm2.principal_nonneg, hsm2.interest_nonneg,
            hsm2.managementFee_nonneg, hsm2.sum_lt]) hu
        have gu := Number.OnGrid.add hsm2.principal_grid hsm2.interest_grid hs hu
        rw [Number.OnGrid.add_toRat gu hsm2.managementFee_grid hs (by
          rw [vu, abs_lt]; constructor <;> linarith [hsm2.principal_nonneg, hsm2.interest_nonneg,
            hsm2.managementFee_nonneg, hsm2.sum_lt]) ht2, vu]
      have gt2 : Number.OnGrid l.loanScale t2 := by
        unfold LoanStateDeltas.total at ht2
        obtain ⟨u, hu, ht2⟩ := bind_ok_peel _ _ _ ht2
        exact Number.OnGrid.add (Number.OnGrid.add hsm2.principal_grid hsm2.interest_grid hs hu)
          hsm2.managementFee_grid hs ht2
      have hsm2s := hsm2.sum_lt
      have hsm2p := hsm2.principal_nonneg
      have hsm2i := hsm2.interest_nonneg
      have hsm2m := hsm2.managementFee_nonneg
      have vsh := Number.OnGrid.sub_toRat gpp gt2 hs (by rw [vt2, abs_lt]; constructor <;> linarith) hsh
      have gsh := Number.OnGrid.sub gpp gt2 hs hsh
      rcases hd3 with ⟨hc, rfl⟩ | ⟨hc, hred⟩
      · -- no shortage: the total is already at most `pp'`
        rw [ht2] at ht3
        obtain rfl := Except.ok.inj ht3
        refine ⟨gt2, ?_⟩
        by_contra hgt
        push Not at hgt
        exact hc ((Number.signum_neg_iff' gsh.1).mpr (by rw [vsh]; linarith))
      · -- the shortage step takes the excess `t2 - pp'` off
        have hneg' : sh.toRat < 0 := (Number.signum_neg_iff' gsh.1).mp hc
        have gex := gsh.neg
        have vex : sh.operator_neg.toRat = t2.toRat - pp'.toRat := by rw [Number.toRat_neg, vsh]; ring
        obtain ⟨hsm3, hsum3⟩ := hsm2.reduce hs gex (by rw [vex]; linarith) (by rw [vex, vt2]; linarith) hred
        have vt3 : t3.toRat = d3.principal.toRat + d3.interest.toRat + d3.managementFee.toRat := by
          unfold LoanStateDeltas.total at ht3
          obtain ⟨u, hu, ht3⟩ := bind_ok_peel _ _ _ ht3
          have vu := Number.OnGrid.add_toRat hsm3.principal_grid hsm3.interest_grid hs (by
            rw [abs_lt]; constructor <;> linarith [hsm3.principal_nonneg, hsm3.interest_nonneg,
              hsm3.managementFee_nonneg, hsm3.sum_lt]) hu
          have gu := Number.OnGrid.add hsm3.principal_grid hsm3.interest_grid hs hu
          rw [Number.OnGrid.add_toRat gu hsm3.managementFee_grid hs (by
            rw [vu, abs_lt]; constructor <;> linarith [hsm3.principal_nonneg, hsm3.interest_nonneg,
              hsm3.managementFee_nonneg, hsm3.sum_lt]) ht3, vu]
        have gt3 : Number.OnGrid l.loanScale t3 := by
          unfold LoanStateDeltas.total at ht3
          obtain ⟨u, hu, ht3⟩ := bind_ok_peel _ _ _ ht3
          exact Number.OnGrid.add (Number.OnGrid.add hsm3.principal_grid hsm3.interest_grid hs hu)
            hsm3.managementFee_grid hs ht3
        refine ⟨gt3, ?_⟩
        rw [vt3, hsum3 (by rw [vex, ← vt2]; linarith), vex, ← vt2]
        linarith
  obtain ⟨gt3, ht3'⟩ := ht3
  show (t3.clamp Number.zero cs.valueOutstanding).toRat ≤ pp'.toRat
  rw [Number.clamp_val t3 Number.zero cs.valueOutstanding gt3.1 Number.zero_isNormalized gcT.1
    (by rw [Number.toRat_zero, vcT]; exact hT0), Number.toRat_zero]
  exact max_le hpp0 (le_trans (min_le_left _ _) ht3')

end XRPL.Model.Lending
