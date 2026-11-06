import XRPL.Properties.Lending.Loan.Common.Outstanding
import XRPL.Properties.Lending.Loan.Common.Grid
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
import XRPL.Properties.Lending.Loan.Common.SetInterest

/-! # interestDue never goes below zero

Every amount an instalment computes sits on the LoanScale grid, and every sum it needs is exact. A
scheduled instalment takes at most interestDue off the interest, so the paid loan keeps it at least zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.unimpairIfImpaired Loan.settlePayment
  Loan.overpaymentComponents from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- An integral loan's interestDue is never negative, as for every lawful loan. -/
lemma Loan.interestDue_nonneg_of_integral (l : Loan) (_h : l.broker.numericType.isIntegral = true) :
    0 ≤ l.toExact.interestDue :=
  l.exact.interest_nonneg

/-- A paid-off loan owes nothing, so its interestDue is zero. -/
lemma Loan.interestDue_paid (l : Loan) (h : l.paymentRemaining = 0) : l.toExact.interestDue = 0 := by
  obtain ⟨h1, h2, h3⟩ := l.exact.paid_zeroed h
  unfold RawLoan.Exact.interestDue
  rw [h1, h2, h3]
  ring

private lemma Number.min_val (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.min x y).toRat = min x.toRat y.toRat := by
  unfold Number.min
  by_cases h : y.operator_lt x = true
  · rw [if_pos h]; exact (min_eq_right ((operator_lt_iff _ _ hy hx).mp h).le).symm
  · rw [if_neg h]; exact (min_eq_left ((operator_lt_eq_false_iff _ _ hy hx).mp (by simpa using h))).symm

private lemma Number.max_val (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.max x y).toRat = max x.toRat y.toRat := by
  unfold Number.max
  by_cases h : x.operator_lt y = true
  · rw [if_pos h]; exact (max_eq_right ((operator_lt_iff _ _ hx hy).mp h).le).symm
  · rw [if_neg h]; exact (max_eq_left ((operator_lt_eq_false_iff _ _ hx hy).mp (by simpa using h))).symm

/-- A clamp into `[lo, hi]` has the clamped value. -/
private lemma Number.clamp_val (x lo hi : Number) (hx : x.isNormalized) (hlo : lo.isNormalized)
    (hhi : hi.isNormalized) (hle : lo.toRat ≤ hi.toRat) :
    (Number.clamp x lo hi).toRat = max lo.toRat (min x.toRat hi.toRat) := by
  unfold Number.clamp
  by_cases h1 : x.operator_lt lo = true
  · rw [if_pos h1]
    have := (operator_lt_iff _ _ hx hlo).mp h1
    rw [max_eq_left ((min_le_left _ _).trans this.le)]
  · rw [if_neg h1]
    have h1' := (operator_lt_eq_false_iff _ _ hx hlo).mp (by simpa using h1)
    by_cases h2 : hi.operator_lt x = true
    · rw [if_pos h2]
      rw [min_eq_right ((operator_lt_iff _ _ hhi hx).mp h2).le, max_eq_right hle]
    · rw [if_neg h2]
      have h2' := (operator_lt_eq_false_iff _ _ hhi hx).mp (by simpa using h2)
      rw [min_eq_left h2', max_eq_right h1']

/-- An amount floored at zero is on the grid and has the floored value. -/
private lemma Number.floorZero {s : Int} {x : Number} (hx : Number.OnGrid s x) :
    Number.OnGrid s (if x.signum < 0 then Number.zero else x) ∧
      (if x.signum < 0 then Number.zero else x).toRat = max 0 x.toRat := by
  by_cases h : x.signum < 0
  · rw [if_pos h, Number.toRat_zero]
    have : x.toRat < 0 := by
      by_contra hc
      push Not at hc
      exact absurd ((Number.signum_nonneg_iff_toRat hx.1).mpr hc) (by omega)
    exact ⟨Number.OnGrid.zero s, (max_eq_left this.le).symm⟩
  · rw [if_neg h]
    have : 0 ≤ x.toRat := (Number.signum_nonneg_iff_toRat hx.1).mp (by omega)
    exact ⟨hx, (max_eq_right this).symm⟩

/-- The deltas of an instalment against a loan owing `P` of principal, `I` of interest and `M` of fee: the
principal and interest deltas between zero and what is owed, the fee delta at most `M` and at least `-(P+I+M)`. -/
structure LoanStateDeltas.InRange (s : Int) (P I M : ℚ) (d : LoanStateDeltas) : Prop where
  scale : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1
  bound : P + I + M < 2 ^ 63 * 10 ^ s
  owed_nonneg : 0 ≤ P ∧ 0 ≤ I ∧ 0 ≤ M
  principal_grid : Number.OnGrid s d.principal
  interest_grid : Number.OnGrid s d.interest
  managementFee_grid : Number.OnGrid s d.managementFee
  principal_range : 0 ≤ d.principal.toRat ∧ d.principal.toRat ≤ P
  interest_range : 0 ≤ d.interest.toRat ∧ d.interest.toRat ≤ I
  managementFee_range : -(P + I + M) ≤ d.managementFee.toRat ∧ d.managementFee.toRat ≤ M

/-- Taking part of an excess off a delta between `-B` and `B`: a nonnegative delta stays between zero and itself,
a negative one between itself and zero. -/
private lemma reduceCapped_range {s : Int} (value excess v' e' : Number) (B : ℚ) (hv : Number.OnGrid s value)
    (he : Number.OnGrid s excess) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hB : B < 2 ^ 63 * 10 ^ s) (hlo : -B ≤ value.toRat) (hhi : value.toRat ≤ B)
    (h : reduceCapped value excess = .ok (v', e')) :
    Number.OnGrid s v' ∧ Number.OnGrid s e' ∧ (0 ≤ value.toRat → 0 ≤ v'.toRat ∧ v'.toRat ≤ value.toRat) ∧
      (value.toRat < 0 → value.toRat ≤ v'.toRat ∧ v'.toRat ≤ 0) := by
  unfold reduceCapped at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i hgt
    have hpos : 0 < excess.toRat := by
      have := (operator_gt_iff excess Number.zero he.1 Number.zero_isNormalized).mp hgt
      rwa [Number.toRat_zero] at this
    walk_ok
    have h1 := Except.ok.inj ‹pure _ = Except.ok (v', e')›
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hm : Number.OnGrid s (Number.min value excess) := Number.OnGrid.min hv he
    have hmv := Number.min_val value excess hv.1 he.1
    have hval : (value.toRat < 0 → min value.toRat excess.toRat = value.toRat) ∧
        (0 ≤ value.toRat → 0 ≤ value.toRat - min value.toRat excess.toRat ∧
          value.toRat - min value.toRat excess.toRat ≤ value.toRat) := by
      refine ⟨fun hn => min_eq_left (by linarith), fun hn => ⟨by linarith [min_le_left value.toRat excess.toRat],
        by linarith [le_min hn hpos.le, min_le_left value.toRat excess.toRat]⟩⟩
    have hsub := Number.OnGrid.sub_toRat hv hm hs (by
      rw [hmv, abs_lt]
      constructor
      · by_cases hn : value.toRat < 0
        · rw [hval.1 hn]; have : (0 : ℚ) < 2 ^ 63 * 10 ^ s := by positivity
          linarith
        · push Not at hn; linarith [(hval.2 hn).1, show (0 : ℚ) < 2 ^ 63 * 10 ^ s by positivity]
      · by_cases hn : value.toRat < 0
        · rw [hval.1 hn]; have : (0 : ℚ) < 2 ^ 63 * 10 ^ s := by positivity
          linarith
        · push Not at hn; linarith [(hval.2 hn).2]) ‹_›
    refine ⟨Number.OnGrid.sub hv hm hs ‹_›, Number.OnGrid.sub he hm hs ‹_›, fun hn => ?_, fun hn => ?_⟩
    · rw [hsub, hmv]; exact hval.2 hn
    · rw [hsub, hmv, hval.1 hn]; constructor <;> linarith
  · have h1 := Except.ok.inj h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨hv, he, fun hn => ⟨hn, le_refl _⟩, fun hn => ⟨le_refl _, hn.le⟩⟩

/-- Taking an excess off deltas in range keeps them in range. -/
private lemma LoanStateDeltas.InRange.reduce {s : Int} {P I M : ℚ} {d d' : LoanStateDeltas} {excess : Number}
    (hd : d.InRange s P I M) (he : Number.OnGrid s excess) (hr : d.reduceByExcess excess = .ok d') :
    d'.InRange s P I M := by
  obtain ⟨hs, hb, ⟨hP, hI, hM⟩, gp, gi, gm, ⟨p0, p1⟩, ⟨i0, i1⟩, ⟨m0, m1⟩⟩ := hd
  unfold LoanStateDeltas.reduceByExcess at hr
  simp only [bind, Except.bind] at hr
  walk_ok
  rename_i _ a ha _ b hb' _ c hc hd'
  obtain rfl := (Except.ok.inj hd').symm
  have hB : P + I + M < 2 ^ 63 * 10 ^ s := hb
  have r1 := reduceCapped_range _ _ a.1 a.2 (P + I + M) gi he hs hB (by linarith) (by linarith) ha
  have r2 := reduceCapped_range _ _ b.1 b.2 (P + I + M) gm r1.2.1 hs hB m0 (by linarith) hb'
  have r3 := reduceCapped_range _ _ c.1 c.2 (P + I + M) gp r2.2.1 hs hB (by linarith) (by linarith) hc
  refine ⟨hs, hb, ⟨hP, hI, hM⟩, r3.1, r1.1, r2.1, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := r3.2.2.1 p0; exact ⟨h1, h2.trans p1⟩
  · obtain ⟨h1, h2⟩ := r1.2.2.1 i0; exact ⟨h1, h2.trans i1⟩
  · by_cases hn : d.managementFee.toRat < 0
    · obtain ⟨h1, h2⟩ := r2.2.2.2 hn; exact ⟨by linarith, by linarith⟩
    · push Not at hn
      obtain ⟨h1, h2⟩ := r2.2.2.1 hn; exact ⟨by linarith, by linarith⟩

/-- The total of deltas in range is exact. -/
private lemma LoanStateDeltas.InRange.total {s : Int} {P I M : ℚ} {d : LoanStateDeltas} {t : Number}
    (hd : d.InRange s P I M) (ht : d.total = .ok t) :
    Number.OnGrid s t ∧ t.toRat = d.principal.toRat + d.interest.toRat + d.managementFee.toRat := by
  obtain ⟨hs, hb, ⟨hP, hI, hM⟩, gp, gi, gm, ⟨p0, p1⟩, ⟨i0, i1⟩, ⟨m0, m1⟩⟩ := hd
  unfold LoanStateDeltas.total at ht
  simp only [bind, Except.bind] at ht
  split at ht
  · cases ht
  · rename_i u hu
    have hu' := Number.add_exact_of_grid gp gi (by linarith) (by linarith) hs hu
    have gu := Number.OnGrid.add gp gi hs hu
    have ht' := Number.add_exact_of_grid gu gm (by rw [hu']; linarith) (by rw [hu']; linarith) hs ht
    exact ⟨Number.OnGrid.add gu gm hs ht, by rw [ht', hu']⟩

/-- The outstanding amounts of a lawful loan are on the LoanScale grid and not negative, and TotalValueOutstanding
is below `2^63` units. -/
lemma Loan.outstanding_grid (l : Loan) :
    Number.OnGrid l.loanScale l.totalValueOutstanding ∧ Number.OnGrid l.loanScale l.principalOutstanding ∧
      Number.OnGrid l.loanScale l.managementFeeOutstanding ∧
      l.totalValueOutstanding.toRat < 2 ^ 63 * 10 ^ l.loanScale ∧ 0 ≤ l.principalOutstanding.toRat ∧
      0 ≤ l.managementFeeOutstanding.toRat ∧ 0 ≤ l.totalValueOutstanding.toRat := by
  have he := Loan.exact l
  have heg := Loan.grid l
  have hB := NumericType.mantissaBound_le l.toExact.numericType
  have hp : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨t, ht, htv⟩ := heg.totalValueOutstanding_atExponent
  obtain ⟨p, -, hpv⟩ := heg.principalOutstanding_atExponent
  obtain ⟨m, -, hmv⟩ := heg.managementFeeOutstanding_atExponent
  simp only [RawLoan.toExact] at htv hpv hmv
  refine ⟨⟨l.wf.totalValueOutstanding_norm, t, by rw [htv]; push_cast; rfl⟩,
    ⟨l.wf.principalOutstanding_norm, p, by rw [hpv]; push_cast; rfl⟩,
    ⟨l.wf.managementFeeOutstanding_norm, m, by rw [hmv]; push_cast; rfl⟩, ?_, by rw [hpv]; positivity,
    by rw [hmv]; positivity, by rw [htv]; positivity⟩
  rw [htv]
  have : (t : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le ht hB
  exact mul_lt_mul_of_pos_right this hp

/-- The tracked deltas of an instalment that isn't the last: on the LoanScale grid, each between zero and
what the loan owes, and together taking at most interestDue off the interest. -/
structure PaymentComponents.Tracked (l : Loan) (pc : PaymentComponents) : Prop where
  totalValue_grid : Number.OnGrid l.loanScale pc.totalValueDelta
  principal_grid : Number.OnGrid l.loanScale pc.principalDelta
  managementFee_grid : Number.OnGrid l.loanScale pc.managementFeeDelta
  totalValue_range : 0 ≤ pc.totalValueDelta.toRat ∧ pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat
  principal_range : 0 ≤ pc.principalDelta.toRat ∧ pc.principalDelta.toRat ≤ l.principalOutstanding.toRat
  managementFee_range :
    0 ≤ pc.managementFeeDelta.toRat ∧ pc.managementFeeDelta.toRat ≤ l.managementFeeOutstanding.toRat
  interest_le : pc.totalValueDelta.toRat - pc.principalDelta.toRat - pc.managementFeeDelta.toRat ≤
    l.toExact.interestDue
  managementFee_le_value : pc.managementFeeDelta.toRat ≤ pc.totalValueDelta.toRat

private lemma ite_bind_ok {α β : Type} (c : Prop) [Decidable c] (x : Except Error α) (d : α)
    (K : α → Except Error β) (b : β) (h : (if c then x >>= K else pure d >>= K) = .ok b) :
    ∃ a, (a = d ∨ (c ∧ x = .ok a)) ∧ K a = .ok b := by
  split at h
  · obtain ⟨a, ha, h⟩ := bind_ok_peel _ _ _ h
    exact ⟨a, Or.inr ⟨‹c›, ha⟩, h⟩
  · exact ⟨d, Or.inl rfl, h⟩

/-- A scheduled instalment takes at most interestDue off the interest. The last one clears the loan. -/
lemma Loan.scheduledComponents_tracked (l : Loan) (pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (h : Loan.scheduledComponents l = .ok pc) : pc.isFinal = true ∨ (pc.isFinal = false ∧ pc.Tracked l) := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', hpp', h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · left
    obtain rfl := (Except.ok.inj h).symm
    rfl
  rename_i hnf
  right
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
  obtain ⟨d2, hd2, h⟩ := ite_bind_ok _ _ _ _ _ h
  obtain ⟨t2, ht2, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sh, hsh, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d3, hd3, h⟩ := ite_bind_ok _ _ _ _ _ h
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
  have gpp := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hpp'
  have hpp0 : 0 ≤ pp'.toRat := by
    have : 0 < l.periodicPayment.toRat := l.exact.periodicPayment_pos
    exact STAmount.roundToNumericType_some_nonneg _ _ _ _ _ l.wf.periodicPayment_norm this.le
      (Or.inr (Or.inl rfl)) hr hpp'
  have hppT : pp'.toRat < T := by
    have : l.totalValueOutstanding.operator_le pp' = false := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnf
      simpa using hnf.2
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
  have hP1 : 0 ≤ (Number.min P0 cs.principalOutstanding).toRat ∧ (Number.min P0 cs.principalOutstanding).toRat ≤ P := by
    rw [vP1]; exact ⟨le_min vP0 hP0, min_le_right _ _⟩
  have hI1 : 0 ≤ (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat ∧
      (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat ≤ T - P - M := by
    rw [vI1]; exact ⟨le_min (le_min vI0 (le_max_left _ _)) hi', min_le_right _ _⟩
  have vppi := Number.add_exact_of_grid gP1 gI1 (by linarith) (by linarith) hs hppi
  have gppi := Number.OnGrid.add gP1 gI1 hs hppi
  have vrff := Number.OnGrid.sub_toRat gpp gppi hs (by rw [abs_lt, vppi]; constructor <;> linarith) hrff
  have grff := Number.OnGrid.sub gpp gppi hs hrff
  have gMm := Number.OnGrid.min gM0 grff
  have vMm := Number.min_val _ _ gM0.1 grff.1
  have gM1 := Number.OnGrid.min gMm gcM
  have vM1 := Number.min_val _ _ gMm.1 gcM.1
  rw [vcM, vMm, vrff, vppi] at vM1
  have hM1 : -(P + (T - P - M) + M) ≤
      (Number.min (Number.min M0 rff) cs.managementFeeDue).toRat ∧
      (Number.min (Number.min M0 rff) cs.managementFeeDue).toRat ≤ M := by
    rw [vM1]
    refine ⟨le_min (le_min (by linarith) (by linarith)) (by linarith), min_le_right _ _⟩
  have hJ1 : LoanStateDeltas.InRange l.loanScale P (T - P - M) M
      { principal := Number.min P0 cs.principalOutstanding,
        interest := Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue,
        managementFee := Number.min (Number.min M0 rff) cs.managementFeeDue } :=
    ⟨hs, by linarith, ⟨hP0, hi', hM0⟩, gP1, gI1, gM1, hP1, hI1, hM1⟩
  obtain ⟨gt1, -⟩ := hJ1.total ht1
  have gov := Number.OnGrid.sub gt1 gcT hs hov
  have hJ2 : d2.InRange l.loanScale P (T - P - M) M := by
    rcases hd2 with rfl | ⟨-, hred⟩
    · exact hJ1
    · exact hJ1.reduce gov hred
  obtain ⟨gt2, -⟩ := hJ2.total ht2
  have gsh := Number.OnGrid.sub gpp gt2 hs hsh
  have hJ3 : d3.InRange l.loanScale P (T - P - M) M := by
    rcases hd3 with rfl | ⟨-, hred⟩
    · exact hJ2
    · exact hJ2.reduce gsh.neg hred
  obtain ⟨gt3, vt3⟩ := hJ3.total ht3
  obtain ⟨-, -, -, gp3, -, gm3, ⟨p0, p1⟩, ⟨i0, i1⟩, ⟨m0, m1⟩⟩ := hJ3
  have vT := Number.clamp_val t3 Number.zero cs.valueOutstanding gt3.1 Number.zero_isNormalized gcT.1
    (by rw [Number.toRat_zero, vcT]; exact hT0)
  have vP := Number.clamp_val d3.principal Number.zero cs.principalOutstanding gp3.1 Number.zero_isNormalized gcP.1
    (by rw [Number.toRat_zero, vcP]; exact hP0)
  have vM := Number.clamp_val d3.managementFee Number.zero cs.managementFeeDue gm3.1 Number.zero_isNormalized gcM.1
    (by rw [Number.toRat_zero, vcM]; exact hM0)
  rw [Number.toRat_zero, vcT, vt3] at vT
  rw [Number.toRat_zero, vcP] at vP
  rw [Number.toRat_zero, vcM] at vM
  rw [min_eq_left (by linarith), max_eq_right p0] at vP
  rw [min_eq_left m1] at vM
  rw [min_eq_left (by linarith [le_max_left 0 d3.managementFee.toRat])] at vT
  refine ⟨rfl, ⟨Number.OnGrid.clamp gt3 (Number.OnGrid.zero _) gcT, Number.OnGrid.clamp gp3 (Number.OnGrid.zero _) gcP,
    Number.OnGrid.clamp gm3 (Number.OnGrid.zero _) gcM, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show 0 ≤ (t3.clamp _ _).toRat ∧ (t3.clamp _ _).toRat ≤ T
    rw [vT]; exact ⟨le_max_left _ _, max_le hT0 (by linarith)⟩
  · show 0 ≤ (d3.principal.clamp _ _).toRat ∧ (d3.principal.clamp _ _).toRat ≤ P
    rw [vP]; exact ⟨p0, p1⟩
  · show 0 ≤ (d3.managementFee.clamp _ _).toRat ∧ (d3.managementFee.clamp _ _).toRat ≤ M
    rw [vM]; exact ⟨le_max_left _ _, max_le hM0 m1⟩
  · show (t3.clamp _ _).toRat - (d3.principal.clamp _ _).toRat - (d3.managementFee.clamp _ _).toRat ≤ T - P - M
    rw [vT, vP, vM]
    rcases le_total 0 d3.managementFee.toRat with hm | hm
    · rw [max_eq_right hm, max_eq_right (by linarith)]; linarith
    · rw [max_eq_left hm]
      rcases le_total 0 (d3.principal.toRat + d3.interest.toRat + d3.managementFee.toRat) with ht | ht
      · rw [max_eq_right ht]; linarith
      · rw [max_eq_left ht]; linarith
  · show (d3.managementFee.clamp _ _).toRat ≤ (t3.clamp _ _).toRat
    rw [vT, vM]
    exact max_le_max (le_refl _) (by linarith)

/-- One instalment keeps interestDue at least zero. The last one pays the loan off, any other takes its
tracked deltas off the loan exactly. -/
private lemma Loan.doPayment_interestDue (l l' : Loan) (pc : PaymentComponents) (hi : 0 ≤ l.toExact.interestDue)
    (hpc : pc.isFinal = true ∨ (pc.isFinal = false ∧ pc.Tracked l)) (h : Loan.doPayment l pc = .ok l') :
    0 ≤ l'.toExact.interestDue := by
  rcases hpc with hf | ⟨hf, ht⟩
  · have hpaid : l'.paymentRemaining = 0 := by
      simp only [Loan.doPayment, hf, ↓reduceIte] at h
      unfold_ter at h
      walk_ok
      exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1
    rw [Loan.interestDue_paid l' hpaid]
  · obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, hle, -⟩ := ht
    obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
    have hs := Loan.loanScale_bounds l
    simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    rename_i _ tv htv _ pv hpv _ mv hmv _ _ hlaw
    have h1 := (RawLoan.to_lawful_ok hlaw).1
    have hi0 : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
      hi
    have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
    have e2 := (congrArg RawLoan.principalOutstanding h1 :)
    have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
    simp only at e1 e2 e3
    have vtv := Number.OnGrid.sub_toRat gT gtv hs (by rw [abs_lt]; constructor <;> linarith) htv
    have vpv := Number.OnGrid.sub_toRat gP gpd hs (by rw [abs_lt]; constructor <;> linarith) hpv
    have vmv := Number.OnGrid.sub_toRat gM gmd hs (by rw [abs_lt]; constructor <;> linarith) hmv
    have hi' : pc.totalValueDelta.toRat - pc.principalDelta.toRat - pc.managementFeeDelta.toRat ≤
      l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat := hle
    show 0 ≤ l'.totalValueOutstanding.toRat - l'.principalOutstanding.toRat - l'.managementFeeOutstanding.toRat
    rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, e1,
      show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, e2,
      show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, e3, vtv, vpv, vmv]
    linarith

/-- The instalment loop keeps interestDue at least zero. -/
private lemma UnsettledPayment.payInstalments_interestDue {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number) (p' : UnsettledPayment α) (hlo : -81 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue)
    (h : UnsettledPayment.payInstalments payment n amount = .ok p') : 0 ≤ p'.loan.toExact.interestDue := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact hi
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact hi
    · exact hi
    all_goals
      have hs := Loan.scheduledComponents_tracked payment.loan _ hlo hint hi
        ‹Loan.scheduledComponents payment.loan = _›
      have hd := Loan.doPayment_interestDue payment.loan _ _ hi hs ‹Loan.doPayment _ _ = _›
      have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
    · exact hd
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      have key := fun a b c => ih _ a b c h3
      simp only at key
      rw [hst.loanScale, hst.broker] at key
      exact key hlo hint hd

/-- The loan without the impaired flag owes the same, at the same scale and on the same broker. -/
private lemma Loan.unimpaired_same (loan : Loan) :
    -81 ≤ loan.loanScale → (loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) →
      0 ≤ loan.toExact.interestDue → -81 ≤ loan.unimpaired.loanScale ∧
        (loan.unimpaired.broker.numericType.isIntegral = true → loan.unimpaired.loanScale ≤ 0) ∧
        0 ≤ loan.unimpaired.toExact.interestDue := by
  intro h1 h2 h3
  have e1 : loan.unimpaired.totalValueOutstanding = loan.totalValueOutstanding := rfl
  have e2 : loan.unimpaired.principalOutstanding = loan.principalOutstanding := rfl
  have e3 : loan.unimpaired.managementFeeOutstanding = loan.managementFeeOutstanding := rfl
  have e4 : loan.unimpaired.loanScale = loan.loanScale := rfl
  have e5 : loan.unimpaired.broker = loan.broker := rfl
  refine ⟨by rw [e4]; exact h1, by rw [e4, e5]; exact h2, ?_⟩
  show 0 ≤ loan.unimpaired.totalValueOutstanding.toRat - loan.unimpaired.principalOutstanding.toRat -
    loan.unimpaired.managementFeeOutstanding.toRat
  rw [e1, e2, e3]
  exact h3

/-- A regular, late or full payment's instalments keep interestDue at least zero. -/
lemma Loan.payInstalments_interestDue (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32) (p : UnsettledPayment Vault) (hpt : pt ≠ .overpayment) (hlo : -81 ≤ loan.loanScale)
    (hint : loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) (hi : 0 ≤ loan.toExact.interestDue)
    (hp : (loan.payInstalments v pt amount now).run = .ok (.ok p)) : 0 ≤ p.loan.toExact.interestDue := by
  obtain ⟨hlo', hint', hi'⟩ := Loan.unimpaired_same loan hlo hint hi
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    refine UnsettledPayment.payInstalments_interestDue _ _ _ _ ?_ ?_ ?_ hloop
    · exact hlo'
    · exact hint'
    · exact hi'
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    refine Loan.doPayment_interestDue loan.unimpaired p.loan pc hi' ?_ hdo
    rcases Loan.scheduledComponents_tracked loan pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
    · exact Or.inl (by rw [e4]; exact hf)
    · refine Or.inr ⟨by rw [e4]; exact hf, ?_⟩
      obtain ⟨g1, g2, g3, r1, r2, r3, hle, hmv⟩ := ht
      exact ⟨by rw [e1]; exact g1, by rw [e2]; exact g2, by rw [e3]; exact g3, by rw [e1]; exact r1,
        by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e1, e2, e3]; exact hle, by rw [e1, e3]; exact hmv⟩
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    exact Loan.doPayment_interestDue loan.unimpaired p.loan _ hi' (Or.inl rfl) hdo
  · exact absurd rfl hpt

/-- The settlement puts the paid loan on the updated broker, so it keeps the paid loan's amounts. -/
lemma Loan.settle_interestDue (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (hs : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.loan'.toExact.interestDue = p.loan.toExact.interestDue := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  show r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat -
    r.loan'.managementFeeOutstanding.toRat = _
  rw [show r.loan'.totalValueOutstanding = r.loan'.toRawLoan.totalValueOutstanding from rfl,
    show r.loan'.principalOutstanding = r.loan'.toRawLoan.principalOutstanding from rfl,
    show r.loan'.managementFeeOutstanding = r.loan'.toRawLoan.managementFeeOutstanding from rfl, h1]
  rfl

/-- A payment keeps the numeric type of the loan's broker. -/
lemma Loan.pay_numericType (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.broker.numericType = loan.broker.numericType := by
  have hb := Loan.pay_broker_fields loan v pt amount now r h
  exact (congrArg RawLoanBroker.numericType hb :)

/-- A regular, late or full payment keeps interestDue at least zero. -/
private lemma Loan.pay_interestDue_nonneg (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (hpt : pt ≠ .overpayment) (hlo : -81 ≤ loan.loanScale)
    (hi : 0 ≤ loan.toExact.interestDue) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    0 ≤ r.loan'.toExact.interestDue := by
  by_cases hnt : loan.broker.numericType.isIntegral = true
  · apply Loan.interestDue_nonneg_of_integral
    rw [Loan.pay_numericType loan v pt amount now r h]
    exact hnt
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  rw [Loan.settle_interestDue p r hs]
  exact Loan.payInstalments_interestDue loan v pt amount now p hpt hlo (fun h => absurd h hnt) hi hp

/-- A loan's interestDue, read from its raw state. -/
lemma Loan.interestDue_of_raw (l : Loan) (r : RawLoan) (h : l.toRawLoan = r) :
    l.toExact.interestDue = r.totalValueOutstanding.toRat - r.principalOutstanding.toRat -
      r.managementFeeOutstanding.toRat := by
  subst h; rfl

/-- The overpayment tail keeps interestDue at least zero. -/
private lemma UnsettledPayment.applyOverpayment_interestDue (payment p' : UnsettledPayment Vault) (amount : Number)
    (hlo : -81 ≤ payment.loan.loanScale) (hfrac : payment.loan.broker.numericType = .fractional)
    (hi : 0 ≤ payment.loan.toExact.interestDue)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') : 0 ≤ p'.loan.toExact.interestDue := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hi
    | skip
  have hopc := ‹Loan.overpaymentComponents _ _ = _›
  have hovn := STAmount.roundToNumericType_isNormalized _ _ _ _ _
    ‹STAmount.roundToNumericType _ _ rounding_mode.downward _ = _›
  have hre := Loan.tryOverpayment_interestDue_nonneg _ _ _ hlo hfrac hi
    (Loan.overpaymentComponents_principalDelta_normalized _ _ _ hovn hopc) ‹Loan.tryOverpayment _ _ = _›
  have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  dsimp only
  rw [Loan.interestDue_of_raw _ _ h1]
  exact hre

/-- An overpayment keeps interestDue at least zero. -/
private lemma Loan.overpayment_interestDue_nonneg (loan : Loan) (v : Vault)
    (amount : Number) (now : UInt32) (r : LoanWithAmounts Vault) (hlo : -81 ≤ loan.loanScale)
    (hi : 0 ≤ loan.toExact.interestDue)
    (h : (loan.pay v .overpayment amount now).run = .ok (.ok r)) : 0 ≤ r.loan'.toExact.interestDue := by
  by_cases hnt : loan.broker.numericType.isIntegral = true
  · apply Loan.interestDue_nonneg_of_integral
    rw [Loan.pay_numericType loan v _ amount now r h]
    exact hnt
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v _ amount now r h
  rw [Loan.settle_interestDue p r hs]
  obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
  have hi0 := Loan.payInstalments_interestDue loan v .regular amount now p0 (by decide) hlo
    (fun h => absurd h hnt) hi h0
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
  refine UnsettledPayment.applyOverpayment_interestDue p0 p amount ?_ ?_ hi0 h1
  · rw [hst.loanScale]; exact hlo
  · rw [hst.broker]
    cases hn : loan.broker.numericType with
    | integral _ _ _ _ => rw [hn] at hnt; exact absurd rfl hnt
    | fractional => exact hn

/-- An accept keeps the loan's amounts, so it keeps interestDue. -/
lemma Loan.accept_interestDue (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.toExact.interestDue = loan.toExact.interestDue := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hr := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
  exact Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hr :)
    (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.managementFeeOutstanding hr :)

/-- Each step keeps interestDue at least zero. -/
lemma Loan.ReachableFrom.interestDue_nonneg {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) (h0 : 0 ≤ start.toExact.interestDue)
    (hlo : -81 ≤ start.loanScale) : 0 ≤ loan.toExact.interestDue := by
  induction hr with
  | refl => exact h0
  | refresh loan loan' _ _ _ _ h ih =>
    have hr := (RawLoan.to_lawful_ok h).1
    rw [Loan.toExact_interestDue_congr (l := loan) (l' := loan') (congrArg RawLoan.totalValueOutstanding hr :)
      (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.managementFeeOutstanding hr :)]
    exact ih
  | accept loan _ _ v r _ _ _ h ih =>
    rw [Loan.accept_interestDue loan v r h]
    exact ih
  | regularPayment loan _ t' v amount r hprev _ _ h ih =>
    have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hprev).2.2.2.2.2.2.1
    exact Loan.pay_interestDue_nonneg loan v .regular amount t' r (by decide) (hls ▸ hlo) ih h
  | latePayment loan _ t' v amount r hprev _ _ h ih =>
    have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hprev).2.2.2.2.2.2.1
    exact Loan.pay_interestDue_nonneg loan v .late amount t' r (by decide) (hls ▸ hlo) ih h
  | fullPayment loan _ t' v amount r hprev _ _ h ih =>
    have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hprev).2.2.2.2.2.2.1
    exact Loan.pay_interestDue_nonneg loan v .full amount t' r (by decide) (hls ▸ hlo) ih h
  | overpayment loan _ t' v amount r hprev _ _ h ih =>
    have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hprev
    exact Loan.overpayment_interestDue_nonneg loan v amount t' r (hft.2.2.2.2.2.2.1 ▸ hlo) ih h
  | impair loan _ t' v r _ _ _ h ih =>
    simp only [Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    rw [Loan.changeImpairment_interestDue loan v true r ‹_›]
    exact ih
  | unimpair loan _ _ v r _ _ _ h ih =>
    rw [Loan.changeImpairment_interestDue loan v false r h]
    exact ih
  | default loan _ _ v r _ _ _ h ih =>
    obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
    rw [Loan.interestDue_paid r.loan' (congrArg RawLoan.paymentRemaining hloan :)]

/-- A new loan's LoanScale is at least the vault's base scale, so at least `-10`. -/
lemma Loan.Created.loanScale_ge {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    -10 ≤ start.loanScale := by
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, _, _, _, _, _, _, hchecks, -, -, -, hl, -⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hbase := Vault.baseExponent_scale_range v
  have hls := (computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2).1
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  rw [hLS]
  omega

/-- Every reachable loan has interestDue at least zero. -/
lemma Loan.Reachable.interestDue_nonneg {loan : Loan} {t : UInt32} (h : loan.Reachable t) :
    0 ≤ loan.toExact.interestDue := by
  obtain ⟨start, t₀, hc, hr⟩ := h
  exact hr.interestDue_nonneg hc.interestDue_nonneg (by have := hc.loanScale_ge; omega)

/-- Every reachable loan owes at least its principal and fee: TotalValueOutstanding ≥ PrincipalOutstanding +
ManagementFeeOutstanding. -/
lemma Loan.Reachable.interest_nonneg_proof (loan : Loan) (t : UInt32) (h : loan.Reachable t) :
    loan.toExact.principalOutstanding + loan.toExact.managementFeeOutstanding ≤
      loan.toExact.totalValueOutstanding := by
  have := Loan.Reachable.interestDue_nonneg h
  unfold RawLoan.Exact.interestDue at this
  linarith

end XRPL.Model.Lending
