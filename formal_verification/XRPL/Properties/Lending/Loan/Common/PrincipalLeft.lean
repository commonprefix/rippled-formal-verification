import XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal
import XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
import XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Loan.Common.AcceptProofs
import XRPL.Properties.Lending.Loan.Common.ReachableProofs

/-! # Principal left after LoanSet and each instalment

LoanSet lends a positive principal at a PeriodicPayment of at least `10^-40`. An instalment that isn't the last takes
less than PrincipalOutstanding, as the theoretical principal of the payments after it rounds up to a positive target. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped_range ite_bind_ok Number.min_val Number.max_val Number.clamp_val Number.floorZero
  LoanStateDeltas.InRange.reduce LoanStateDeltas.InRange.total from XRPL.Properties.Lending.Loan.Common.InterestDue
open private LoanState.buildTheoretical_principal_eq Loan.doPayment_periodicPayment
  from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private LoanState.buildTheoretical_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private Loan.doPayment_principal from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private STAmount.isNormalized_of_isRounded_false Loan.create_principal_pos Loan.canCreate_principal_exact
  from XRPL.Properties.Lending.Loan.Common.SetInterest

local notation "ε" => Number.nearestError

/-- A lawful loan's periodic rate is normalized, at least zero, at most `200`, and zero or at least `10^-12`. -/
lemma Loan.periodicRate_bounds (l : Loan) (rate : Number) (h : l.periodicRate = .ok rate) :
    rate.isNormalized ∧ 0 ≤ rate.toRat ∧ (rate.toRat ≠ 0 → 1 / 10 ^ 12 ≤ rate.toRat) ∧ rate.toRat ≤ 200 := by
  have hint : 60 ≤ l.schedule.paymentInterval.toNat := by
    have := (UInt32.le_iff_toNat_le).mp l.valid.paymentInterval_min
    have h60 : minPaymentInterval.toNat = 60 := rfl
    omega
  exact ⟨loanPeriodicRate_isNormalized _ _ rate h, loanPeriodicRate_nonneg _ _ rate h,
    loanPeriodicRate_ge _ _ rate hint h, loanPeriodicRate_le _ _ rate l.valid.interestRate_cap h⟩

/-- The theoretical principal of one payment or more is at least `10^-43`, for a lawful loan with a
PeriodicPayment of at least `10^-40`. -/
lemma Loan.theoretical_principal_ge (l : Loan) (k : UInt32) (rate : Number) (ts : LoanState) (hk : k ≠ 0)
    (hpp : 1 / 10 ^ 40 ≤ l.periodicPayment.toRat) (hrate : l.periodicRate = .ok rate)
    (h : LoanState.buildTheoretical l.periodicPayment rate k l.broker.managementFeeRate = .ok ts) :
    1 / 10 ^ 43 ≤ ts.principalOutstanding.toRat := by
  obtain ⟨hN, h0, hlow, hhigh⟩ := Loan.periodicRate_bounds l rate hrate
  exact loanPrincipalFromPeriodicPayment_ge _ _ k _ l.wf.periodicPayment_norm hpp hN h0 hlow hhigh hk
    (LoanState.buildTheoretical_principal_eq _ _ _ _ _ hk h)

/-- Taking an excess off deltas in range never raises the principal delta. -/
private lemma LoanStateDeltas.InRange.reduce_principal_le {s : Int} {P I M : ℚ} {d d' : LoanStateDeltas}
    {excess : Number} (hd : d.InRange s P I M) (he : Number.OnGrid s excess)
    (hr : d.reduceByExcess excess = .ok d') : d'.principal.toRat ≤ d.principal.toRat := by
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
  exact (r3.2.2.1 p0).2

/-- A scheduled instalment that isn't the last takes less than PrincipalOutstanding when the theoretical
principal of the payments after it is at least `10^-81`. That principal rounds up to a positive target. -/
lemma Loan.scheduledComponents_principal_lt (l : Loan) (pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hPpos : 0 < l.principalOutstanding.toRat)
    (htheory : ∀ rate ts, l.periodicRate = .ok rate →
      LoanState.buildTheoretical l.periodicPayment rate (l.paymentRemaining - 1) l.broker.managementFeeRate =
        .ok ts → (10 : ℚ) ^ (-81 : ℤ) ≤ ts.principalOutstanding.toRat)
    (h : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) :
    pc.principalDelta.toRat < l.principalOutstanding.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', hpp', h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    simp at hf
  rename_i hnf
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
  -- the target principal rounded up is positive
  have hts0 := htheory rate ts hrate hts
  have htsN := (LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm
    (Loan.periodicRate_bounds l rate hrate).1 hts).2.1
  have htpo0 : 0 < tpo.toRat := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hts0)
    (STAmount.roundToNumericType_upward_ge_of_large _ _ _ _ htsN hts0 hr htpo)
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
  -- the floored principal delta is below PrincipalOutstanding, since the target is positive
  have hP0lt : P0.toRat < P := by
    rw [show P0.toRat = max 0 dp.toRat from vp0]
    rcases le_or_gt tpo.toRat P with hle | hlt
    · have vdp := Number.OnGrid.sub_toRat gcP gtpo hs (by rw [vcP, abs_lt]; constructor <;> linarith) hdp
      rw [vdp, vcP]
      exact max_lt hPpos (by linarith)
    · have hR := operator_sub_rounded_to_nearest _ _ _ gcP.1 gtpo.1 hdp
      have hdp0 := Number.roundsToRepresentable_nonpos _ _ hR (by rw [vcP]; linarith)
      rw [max_eq_left hdp0]; exact hPpos
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
  have hP1 : 0 ≤ (Number.min P0 cs.principalOutstanding).toRat ∧
      (Number.min P0 cs.principalOutstanding).toRat ≤ P := by
    rw [vP1]; exact ⟨le_min vP0 hP0, min_le_right _ _⟩
  have hI1 : 0 ≤ (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat ∧
      (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat ≤ T - P - M := by
    rw [vI1]; exact ⟨le_min (le_min vI0 (le_max_left _ _)) hi', min_le_right _ _⟩
  have vppi := Number.OnGrid.add_toRat gP1 gI1 hs (by rw [abs_lt]; constructor <;> linarith) hppi
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
  -- the deltas stay in range through both reductions, and the principal delta only drops
  have hJ1 : LoanStateDeltas.InRange l.loanScale P (T - P - M) M
      { principal := Number.min P0 cs.principalOutstanding,
        interest := Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue,
        managementFee := Number.min (Number.min M0 rff) cs.managementFeeDue } :=
    ⟨hs, by linarith, ⟨hP0, hi', hM0⟩, gP1, gI1, gM1, hP1, hI1, hM1⟩
  obtain ⟨gt1, -⟩ := LoanStateDeltas.InRange.total hJ1 ht1
  have gov := Number.OnGrid.sub gt1 gcT hs hov
  have hJ2 : d2.InRange l.loanScale P (T - P - M) M := by
    rcases hd2 with rfl | ⟨-, hred⟩
    · exact hJ1
    · exact LoanStateDeltas.InRange.reduce hJ1 gov hred
  have hd2p : d2.principal.toRat ≤ (Number.min P0 cs.principalOutstanding).toRat := by
    rcases hd2 with rfl | ⟨-, hred⟩
    · exact le_refl _
    · have := LoanStateDeltas.InRange.reduce_principal_le hJ1 gov hred
      exact this
  obtain ⟨gt2, -⟩ := LoanStateDeltas.InRange.total hJ2 ht2
  have gsh := Number.OnGrid.sub gpp gt2 hs hsh
  have hJ3 : d3.InRange l.loanScale P (T - P - M) M := by
    rcases hd3 with rfl | ⟨-, hred⟩
    · exact hJ2
    · exact LoanStateDeltas.InRange.reduce hJ2 gsh.neg hred
  have hd3p : d3.principal.toRat ≤ d2.principal.toRat := by
    rcases hd3 with rfl | ⟨-, hred⟩
    · exact le_refl _
    · have := LoanStateDeltas.InRange.reduce_principal_le hJ2 gsh.neg hred
      exact this
  obtain ⟨-, -, -, gp3, -, -, ⟨p0, p1⟩, -, -⟩ := hJ3
  -- the clamp keeps the principal delta
  have vP := Number.clamp_val d3.principal Number.zero cs.principalOutstanding gp3.1 Number.zero_isNormalized gcP.1
    (by rw [Number.toRat_zero, vcP]; exact hP0)
  rw [Number.toRat_zero, vcP] at vP
  rw [min_eq_left (by linarith), max_eq_right p0] at vP
  have hgoal : (Number.clamp d3.principal Number.zero cs.principalOutstanding).toRat < P := by
    rw [vP]
    rw [vP1] at hd2p
    linarith [min_le_left P0.toRat P]
  exact hgoal

/-- An instalment that isn't the last, taking whole LoanScale units below PrincipalOutstanding, leaves principal. -/
private lemma Loan.doPayment_principal_pos (l l' : Loan) (pc : PaymentComponents) (hf : pc.isFinal = false)
    (hg : Number.OnGrid l.loanScale pc.principalDelta) (h0 : 0 ≤ pc.principalDelta.toRat)
    (hlt : pc.principalDelta.toRat < l.principalOutstanding.toRat) (h : Loan.doPayment l pc = .ok l') :
    0 < l'.principalOutstanding.toRat := by
  obtain ⟨-, hstep, -⟩ := Loan.doPayment_principal l l' pc h
  obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid l
  have hv := Number.OnGrid.sub_exact hPg hg h0 hlt.le hPlt (Loan.loanScale_bounds l) (hstep hf)
  rw [hv]; linarith

/-- While payments are left, PrincipalOutstanding is not zero and PeriodicPayment is at least `10^-40`. -/
def Loan.PrincipalLeft (l : Loan) : Prop :=
  l.paymentRemaining ≠ 0 → l.principalOutstanding ≠ Number.zero ∧ 1 / 10 ^ 40 ≤ l.periodicPayment.toRat

/-- A loan with the same count, PrincipalOutstanding and PeriodicPayment keeps the principal left. -/
lemma Loan.PrincipalLeft.of_same {l l' : Loan} (h : l.PrincipalLeft)
    (h1 : l'.paymentRemaining = l.paymentRemaining) (h2 : l'.principalOutstanding = l.principalOutstanding)
    (h3 : l'.periodicPayment = l.periodicPayment) : l'.PrincipalLeft := by
  intro hr
  rw [h1] at hr
  rw [h2, h3]
  exact h hr

/-- A loan rebuilt with the same count, PrincipalOutstanding and PeriodicPayment keeps the principal left. -/
lemma Loan.PrincipalLeft.of_raw {l l' : Loan} {raw : RawLoan} (h : l.PrincipalLeft) (hl : raw.to_lawful = .ok l')
    (h1 : raw.paymentRemaining = l.paymentRemaining) (h2 : raw.principalOutstanding = l.principalOutstanding)
    (h3 : raw.periodicPayment = l.periodicPayment) : l'.PrincipalLeft := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact h.of_same (by rw [← h1, ← hr]) (by rw [← h2, ← hr]) (by rw [← h3, ← hr])

/-- A loan with no payments left has the principal left. -/
lemma Loan.PrincipalLeft.of_paid {l : Loan} (h : l.paymentRemaining = 0) : l.PrincipalLeft :=
  fun h' => absurd h h'

/-- A loan with the principal left and payments left has a positive PrincipalOutstanding. -/
lemma Loan.PrincipalLeft.pos {l : Loan} (h : l.PrincipalLeft) (hr : l.paymentRemaining ≠ 0) :
    0 < l.principalOutstanding.toRat := by
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hne : l.principalOutstanding.toRat ≠ 0 := fun h0 =>
    (h hr).1 ((Number.toRat_eq_zero_iff_eq_zero l.wf.principalOutstanding_norm).mp h0)
  exact lt_of_le_of_ne hP0 (Ne.symm hne)

/-- One scheduled instalment keeps the principal left. The last one leaves no payments, any other leaves
principal and keeps PeriodicPayment. -/
lemma Loan.doPayment_principalLeft (l l' : Loan) (pc pc' : PaymentComponents) (hs : l.PayShape)
    (hl : l.PrincipalLeft) (hr0 : l.paymentRemaining ≠ 0) (hpc : Loan.scheduledComponents l = .ok pc)
    (e2 : pc'.principalDelta = pc.principalDelta) (e4 : pc'.isFinal = pc.isFinal)
    (h : Loan.doPayment l pc' = .ok l') : l'.PrincipalLeft := by
  cases hf : pc.isFinal
  · have hpp := (hl hr0).2
    have hPpos := hl.pos hr0
    have hr1 := Loan.scheduledComponents_not_last l pc hpc hf
    have hk : l.paymentRemaining - 1 ≠ 0 := by
      intro h
      apply hr1
      have h0 : l.paymentRemaining.toNat ≠ 0 := fun h' => hr0 (UInt32.toNat_inj.mp (by simpa using h'))
      have h1 := congrArg UInt32.toNat h
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at h1
      exact UInt32.toNat_inj.mp (by simp at h1 ⊢; omega)
    have hlt := Loan.scheduledComponents_principal_lt l pc hs.1 hs.2 hs.3 hPpos
      (fun rate ts hrate hts => le_trans (by norm_num) (Loan.theoretical_principal_ge l _ rate ts hk hpp hrate hts))
      hpc hf
    rcases Loan.scheduledComponents_tracked l pc hs.1 hs.2 hs.3 hpc with hf' | ⟨-, ht⟩
    · rw [hf] at hf'; cases hf'
    have hpos := Loan.doPayment_principal_pos l l' pc' (by rw [e4]; exact hf)
      (by rw [e2]; exact ht.principal_grid) (by rw [e2]; exact ht.principal_range.1) (by rw [e2]; exact hlt) h
    have hpp' := Loan.doPayment_periodicPayment l l' pc' h
    intro _
    refine ⟨fun h0 => ?_, by rw [hpp']; exact hpp⟩
    rw [h0, Number.toRat_zero] at hpos
    exact lt_irrefl _ hpos
  · exact Loan.PrincipalLeft.of_paid (Loan.doPayment_final l l' pc' (by rw [e4]; exact hf) h)

/-- A loan a LoanSet creates has principal left and a PeriodicPayment of at least `10^-40`. PrincipalRequested
is at least one LoanScale unit, so at least `10^-10`. -/
lemma Loan.Created.principalLeft {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) : start.PrincipalLeft := by
  have hls := h.loanScale_ge
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, allowsOverpayment, r, hcan, hok, rfl⟩ := h
  have hst := Loan.canCreate_principal_exact broker v principal fees _ t₀ twoStep hcan
  have hp := STAmount.isNormalized_of_isRounded_false _ _ hst
  have hpos := Loan.create_principal_pos broker v principal rates fees _ allowsOverpayment twoStep r hp hok
  have hPO := Loan.create_principalOutstanding broker v principal rates fees _ allowsOverpayment twoStep r hp
    hpos.le hst hok
  -- PrincipalRequested is at least one LoanScale unit
  have hP10 : 1 / 10 ^ 10 ≤ principal.toRat := by
    obtain ⟨⟨-, k, hk⟩, -⟩ := Loan.principal_onGrid r.loan'
    rw [hPO] at hk
    have hD : (0 : ℚ) < 10 ^ r.loan'.loanScale := zpow_pos (by norm_num) _
    have hk1 : (1 : ℚ) ≤ k := by
      have hk0 : (0 : ℚ) < k := by
        by_contra hc
        push Not at hc
        rw [hk] at hpos
        nlinarith
      have : 0 < k := Int.cast_pos.mp hk0
      exact_mod_cast this
    calc (1 : ℚ) / 10 ^ 10 = 10 ^ (-10 : ℤ) := by norm_num
      _ ≤ 10 ^ r.loan'.loanScale := zpow_le_zpow_right₀ (by norm_num) hls
      _ ≤ k * 10 ^ r.loan'.loanScale := le_mul_of_one_le_left hD.le hk1
      _ = principal.toRat := hk.symm
  obtain ⟨props, _, _, _, hchecks, hl, -⟩ :=
    Loan.create_loan_eq broker v principal rates fees _ allowsOverpayment twoStep r hok
  obtain ⟨rate, _, _, _, hrate, hpp, -⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hR : r.loan'.periodicRate = .ok rate := by
    have hRt : r.loan'.rates = rates := by show r.loan'.toRawLoan.rates = _; rw [hl]; rfl
    have hSc : r.loan'.schedule = LoanSchedule.build pi pt gp sd t₀ twoStep := by
      show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
    unfold Loan.periodicRate
    rw [hRt, hSc]
    exact hrate
  obtain ⟨hN, h0, hlow, -⟩ := Loan.periodicRate_bounds r.loan' rate hR
  have hpp0 : 0 < r.loan'.periodicPayment.toRat := r.loan'.exact.periodicPayment_pos
  rw [hPP] at hpp0
  intro _
  refine ⟨?_, ?_⟩
  · rw [hPO]
    intro h0
    rw [h0, Number.toRat_zero] at hpos
    exact lt_irrefl _ hpos
  · rw [hPP]
    have hge := loanPeriodicPayment_ge principal rate _ _ _ (by norm_num) hp hP10 hN h0 hlow (ne_of_gt hpp0) hpp
    have he' := Number.nearestError_le
    calc (1 : ℚ) / 10 ^ 40 ≤ 1 / 10 ^ 10 * (1 - 1 / 10 ^ 18) ^ 4 / (3 * 2 ^ 32) := by norm_num
      _ ≤ 1 / 10 ^ 10 * (1 - ε) ^ 4 / (3 * 2 ^ 32) := by gcongr
      _ ≤ _ := hge

/-- A reachable loan has the shape the instalment loop needs: LoanScale at least `-81`, `0` or below for an integral
asset, and interestDue at least zero. -/
lemma Loan.ReachableFrom.payShape {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hc : Loan.Created start t₀) (hr : Loan.ReachableFrom start t₀ loan t) : loan.PayShape := by
  obtain ⟨hlo, -, hint⟩ := Loan.Reachable.loanScale_facts ⟨start, t₀, hc, hr⟩
  exact ⟨by omega, hint, hr.interestDue_nonneg hc.interestDue_nonneg (by have := hc.loanScale_ge; omega)⟩

end XRPL.Model.Lending
