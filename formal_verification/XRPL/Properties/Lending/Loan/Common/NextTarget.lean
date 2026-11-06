import XRPL.Properties.Lending.Loan.Common.TheoreticalMonotone
import XRPL.Properties.Lending.Loan.Common.OverpaymentPrincipal
import XRPL.Properties.Lending.Loan.Common.ScheduleComputes

/-! # A loan keeps principal while payments are left, when the payment factor falls

When the payment factor falls by at least four roundings per payment, the theoretical principal after the next
payment stays at most PrincipalOutstanding. So no payment clears the principal while payments are left. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.lateComponents_scheduled LoanState.build_fields Number.max_isNormalized'
  from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private ite_bind_ok Number.min_val Number.max_val Number.clamp_val Number.floorZero LoanStateDeltas.InRange.reduce
  LoanStateDeltas.InRange.total from XRPL.Properties.Lending.Loan.Common.InterestDue
open private LoanStateDeltas.InRange.reduce_principal_le from XRPL.Properties.Lending.Loan.Common.PrincipalLeft
open private Loan.PayShape.doPayment_with_fee from XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
open private LoanState.buildTheoretical_principal_eq Loan.doPayment_periodicPayment
  computeLoanPropertiesFromPeriodicRate_pp Loan.overpaymentComponents_principal_grid
  from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private LoanState.buildTheoretical_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private Loan.doPayment_principal from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private STAmount.isNormalized_of_isRounded_false Loan.create_principal_pos Loan.canCreate_principal_exact
  from XRPL.Properties.Lending.Loan.Common.SetInterest
open private Loan.scheduledComponents_theory Loan.manageDefault_terms
  from XRPL.Properties.Lending.Loan.Common.ScheduleComputes
open private Loan.tryOverpayment_periodic_ge Number.OnGrid.unit_le
  from XRPL.Properties.Lending.Loan.Common.OverpaymentPrincipal

/-- The loan's payment factor falls by at least four roundings for every count of payments from two up to
PaymentTotal. -/
def Loan.FactorGaps (l : Loan) : Prop :=
  ∀ rate, l.periodicRate = .ok rate → ∀ k : UInt32, 2 ≤ k.toNat → k ≤ l.schedule.paymentTotal → FactorGap rate k

/-- The theoretical principal of `k` payments of the loan's PeriodicPayment is at most PrincipalOutstanding. -/
def Loan.TheoryBelow (l : Loan) (k : UInt32) : Prop :=
  ∀ rate tpo, l.periodicRate = .ok rate → loanPrincipalFromPeriodicPayment l.periodicPayment rate k = .ok tpo →
    tpo.toRat ≤ l.principalOutstanding.toRat

/-- The theoretical principal of the payments left computes and is at most PrincipalOutstanding. -/
def Loan.TheoryLeft (l : Loan) : Prop :=
  ∀ rate, l.periodicRate = .ok rate → ∃ tpo, loanPrincipalFromPeriodicPayment l.periodicPayment rate
    l.paymentRemaining = .ok tpo ∧ tpo.toRat ≤ l.principalOutstanding.toRat

/-- What the induction keeps: the principal left, the falling payment factor, at most PaymentTotal payments left,
and while payments are left the theoretical principal after the next payment at most PrincipalOutstanding. -/
structure Loan.NextShape (l : Loan) : Prop where
  left : l.PrincipalLeft
  gaps : l.FactorGaps
  count : l.paymentRemaining ≤ l.schedule.paymentTotal
  next : l.paymentRemaining ≠ 0 → l.TheoryBelow (l.paymentRemaining - 1)

/-- A loan with the same count, PrincipalOutstanding, PeriodicPayment, rates and schedule keeps the shape. -/
lemma Loan.NextShape.of_same {l l' : Loan} (h : l.NextShape) (h1 : l'.paymentRemaining = l.paymentRemaining)
    (h2 : l'.principalOutstanding = l.principalOutstanding) (h3 : l'.periodicPayment = l.periodicPayment)
    (h4 : l'.rates = l.rates) (h5 : l'.schedule = l.schedule) : l'.NextShape := by
  have hR : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [h4, h5]
  refine ⟨h.left.of_same h1 h2 h3, fun rate hrate k hk2 hk => h.gaps rate (hR ▸ hrate) k hk2 (h5 ▸ hk),
    by rw [h1, h5]; exact h.count, fun hn rate tpo hrate htpo => ?_⟩
  rw [h1] at hn htpo
  rw [h3] at htpo
  rw [h2]
  exact h.next hn rate tpo (hR ▸ hrate) htpo

/-- A loan rebuilt with the same count, PrincipalOutstanding, PeriodicPayment, rates and schedule keeps the shape. -/
lemma Loan.NextShape.of_raw {l l' : Loan} {raw : RawLoan} (h : l.NextShape) (hl : raw.to_lawful = .ok l')
    (h1 : raw.paymentRemaining = l.paymentRemaining) (h2 : raw.principalOutstanding = l.principalOutstanding)
    (h3 : raw.periodicPayment = l.periodicPayment) (h4 : raw.rates = l.rates) (h5 : raw.schedule = l.schedule) :
    l'.NextShape := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact h.of_same (by rw [← h1, ← hr]) (by rw [← h2, ← hr]) (by rw [← h3, ← hr]) (by rw [← h4, ← hr])
    (by rw [← h5, ← hr])

/-- A loan with no payments left and the same rates and schedule keeps the shape. -/
lemma Loan.NextShape.of_paid {l l' : Loan} (h : l.NextShape) (h0 : l'.paymentRemaining = 0)
    (h4 : l'.rates = l.rates) (h5 : l'.schedule = l.schedule) : l'.NextShape := by
  have hR : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [h4, h5]
  exact ⟨Loan.PrincipalLeft.of_paid h0, fun rate hrate k hk2 hk => h.gaps rate (hR ▸ hrate) k hk2 (h5 ▸ hk),
    by rw [h0, UInt32.le_iff_toNat_le]; simp, fun hn => absurd h0 hn⟩

/-- The loan without the impaired flag keeps the shape. -/
lemma Loan.NextShape.unimpaired {l : Loan} (h : l.NextShape) : l.unimpaired.NextShape :=
  ⟨h.left, h.gaps, h.count, h.next⟩

/-- The theoretical principal of the payments left at most PrincipalOutstanding keeps the one after the next
payment below it too, when the payment factor falls. -/
lemma Loan.TheoryLeft.next {l : Loan} (h : l.TheoryLeft) (hg : l.FactorGaps)
    (hle : l.paymentRemaining ≤ l.schedule.paymentTotal) (hl : l.PrincipalLeft) :
    l.paymentRemaining ≠ 0 → l.TheoryBelow (l.paymentRemaining - 1) := by
  intro hn rate t' hrate h'
  obtain ⟨t, ht, htle⟩ := h rate hrate
  obtain ⟨hN, h0, hlow, hhigh⟩ := Loan.periodicRate_bounds l rate hrate
  have := loanPrincipalFromPeriodicPayment_pred_le _ _ _ t t' l.wf.periodicPayment_norm (hl hn).2 hN h0 hlow hhigh
    hn (fun h2 => hg rate hrate _ h2 hle) ht h'
  linarith

/-- A scheduled instalment that isn't the last takes at most PrincipalOutstanding less the theoretical principal
after it, or nothing. Its target is that principal rounded up, and the principal delta is floored at zero. -/
lemma Loan.scheduledComponents_principal_le (l : Loan) (pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (htheory : ∀ rate ts, l.periodicRate = .ok rate →
      LoanState.buildTheoretical l.periodicPayment rate (l.paymentRemaining - 1) l.broker.managementFeeRate =
        .ok ts → (10 : ℚ) ^ (-81 : ℤ) ≤ ts.principalOutstanding.toRat)
    (h : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) (rate0 theo : Number)
    (hrate0 : l.periodicRate = .ok rate0)
    (htheo : loanPrincipalFromPeriodicPayment l.periodicPayment rate0 (l.paymentRemaining - 1) = .ok theo) :
    pc.principalDelta.toRat ≤ max 0 (l.principalOutstanding.toRat - theo.toRat) := by
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
  -- the target is the theoretical principal rounded up
  rw [hrate0] at hrate
  obtain rfl := Except.ok.inj hrate
  have hk : l.paymentRemaining - 1 ≠ 0 := by
    intro h0
    apply hnf
    have : l.paymentRemaining = 1 := by
      have := congrArg (· + 1) h0
      simpa using this
    simp [this]
  have htheo' := LoanState.buildTheoretical_principal_eq _ _ _ _ _ hk hts
  rw [htheo, Except.ok.injEq] at htheo'
  subst htheo'
  have hts0 := htheory rate0 ts hrate0 hts
  have htsN := (LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm
    (Loan.periodicRate_bounds l rate0 hrate0).1 hts).2.1
  have htpoge := STAmount.roundToNumericType_upward_ge_of_large _ _ _ _ htsN hts0 hr htpo
  have htpo0 : 0 < tpo.toRat := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hts0) htpoge
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
  have hP0le : P0.toRat ≤ max 0 (P - ts.principalOutstanding.toRat) := by
    rw [show P0.toRat = max 0 dp.toRat from vp0]
    rcases le_or_gt tpo.toRat P with hle | hlt
    · have vdp := Number.OnGrid.sub_toRat gcP gtpo hs (by rw [vcP, abs_lt]; constructor <;> linarith) hdp
      rw [vdp, vcP]
      exact max_le_max (le_refl 0) (by linarith)
    · have hR := operator_sub_rounded_to_nearest _ _ _ gcP.1 gtpo.1 hdp
      have hdp0 := Number.roundsToRepresentable_nonpos _ _ hR (by rw [vcP]; linarith)
      rw [max_eq_left hdp0]; exact le_max_left _ _
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
  have vP := Number.clamp_val d3.principal Number.zero cs.principalOutstanding gp3.1 Number.zero_isNormalized gcP.1
    (by rw [Number.toRat_zero, vcP]; exact hP0)
  rw [Number.toRat_zero, vcP] at vP
  rw [min_eq_left (by linarith), max_eq_right p0] at vP
  have hgoal : (Number.clamp d3.principal Number.zero cs.principalOutstanding).toRat ≤
      max 0 (P - ts.principalOutstanding.toRat) := by
    rw [vP]
    rw [vP1] at hd2p
    linarith [min_le_left P0.toRat P]
  exact hgoal

/-- One scheduled instalment keeps the shape, and leaves the theoretical principal of the payments left at most
PrincipalOutstanding. The last one leaves no payments, any other at least the theoretical principal after it. -/
lemma Loan.doPayment_nextShape (l l' : Loan) (pc pc' : PaymentComponents) (hs : l.PayShape) (hn : l.NextShape)
    (hr0 : l.paymentRemaining ≠ 0) (hpc : Loan.scheduledComponents l = .ok pc)
    (e2 : pc'.principalDelta = pc.principalDelta) (e4 : pc'.isFinal = pc.isFinal)
    (h : Loan.doPayment l pc' = .ok l') : l'.NextShape ∧ l'.TheoryLeft := by
  have hst := Loan.doPayment_sameTerms l l' pc' h
  have hR : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [hst.rates, hst.schedule]
  have hpp' := Loan.doPayment_periodicPayment l l' pc' h
  have hleft := Loan.doPayment_principalLeft l l' pc pc' hs hn.left hr0 hpc e2 e4 h
  have hcount : l'.paymentRemaining ≤ l'.schedule.paymentTotal := by
    rw [hst.schedule]
    have hle := UInt32.le_iff_toNat_le.mp hn.count
    rw [UInt32.le_iff_toNat_le]
    cases hf : pc.isFinal
    · rw [(Loan.doPayment_notFinal l l' pc' (by rw [e4]; exact hf) h).1,
        UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          have : l.paymentRemaining.toNat ≠ 0 := fun h' => hr0 (UInt32.toNat_inj.mp (by simpa using h'))
          simp; omega)]
      omega
    · rw [Loan.doPayment_final l l' pc' (by rw [e4]; exact hf) h]
      simp
  have hgaps : l'.FactorGaps := fun rate hrate k hk2 hk =>
    hn.gaps rate (hR ▸ hrate) k hk2 (hst.schedule ▸ hk)
  have htheory : l'.TheoryLeft := by
    intro rate hrate
    rw [hR] at hrate
    cases hf : pc.isFinal
    · have hf' : pc'.isFinal = false := by rw [e4]; exact hf
      have hpr' := (Loan.doPayment_notFinal l l' pc' hf' h).1
      obtain ⟨theo, htheo⟩ := Loan.scheduledComponents_theory hpc hf rate hrate
      have hpp := (hn.left hr0).2
      have hr1 := Loan.scheduledComponents_not_last l pc hpc hf
      have hk : l.paymentRemaining - 1 ≠ 0 := by
        intro h0
        apply hr1
        have := congrArg (· + 1) h0
        simpa using this
      have hδ := Loan.scheduledComponents_principal_le l pc hs.1 hs.2 hs.3
        (fun rate ts hrate hts => le_trans (by norm_num) (Loan.theoretical_principal_ge l _ rate ts hk hpp hrate hts))
        hpc hf rate theo hrate htheo
      have hbelow := hn.next hr0 rate theo hrate htheo
      rcases Loan.scheduledComponents_tracked l pc hs.1 hs.2 hs.3 hpc with hf'' | ⟨-, ht⟩
      · rw [hf] at hf''; cases hf''
      obtain ⟨-, hstep, -⟩ := Loan.doPayment_principal l l' pc' h
      obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid l
      have hv := Number.OnGrid.sub_exact hPg (by rw [e2]; exact ht.principal_grid)
        (by rw [e2]; exact ht.principal_range.1) (by rw [e2]; exact ht.principal_range.2) hPlt
        (Loan.loanScale_bounds l) (hstep hf')
      refine ⟨theo, by rw [hpp', hpr']; exact htheo, ?_⟩
      rw [hv, e2]
      rcases le_total 0 (l.principalOutstanding.toRat - theo.toRat) with h0 | h0
      · rw [max_eq_right h0] at hδ; linarith
      · rw [max_eq_left h0] at hδ; linarith
    · have hf' : pc'.isFinal = true := by rw [e4]; exact hf
      have hpr' := Loan.doPayment_final l l' pc' hf' h
      obtain ⟨hfin, -, -⟩ := Loan.doPayment_principal l l' pc' h
      refine ⟨Number.zero, by rw [hpr']; rfl, ?_⟩
      rw [hfin hf', Number.toRat_zero]
  exact ⟨⟨hleft, hgaps, hcount, htheory.next hgaps hcount hleft⟩, htheory⟩

/-- The instalment loop keeps the shape, and once it pays an instalment the theoretical principal of the payments
left is at most PrincipalOutstanding. -/
lemma UnsettledPayment.payInstalments_nextShape {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      payment.loan.PayShape → payment.loan.NextShape → p'.loan.NextShape ∧ (p' = payment ∨ p'.loan.TheoryLeft) := by
  intro n
  induction n with
  | zero =>
    intro payment p' h _ hn
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨hn, Or.inl rfl⟩
  | succ n ih =>
    intro payment p' h hs hn
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact ⟨hn, Or.inl rfl⟩
    · exact ⟨hn, Or.inl rfl⟩
    all_goals
      have hpr0 : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hpc := ‹Loan.scheduledComponents payment.loan = _›
      have hdo := ‹Loan.doPayment _ _ = _›
      obtain ⟨hstep, hK⟩ := Loan.doPayment_nextShape _ _ _ _ hs hn hpr0 hpc rfl rfl hdo
    · exact ⟨hstep, Or.inr hK⟩
    · obtain ⟨h1, h2⟩ := ih _ p' ‹UnsettledPayment.payInstalments _ n amount = _›
        (Loan.PayShape.doPayment_with_fee hs _ _ hpc hdo) hstep
      refine ⟨h1, Or.inr ?_⟩
      rcases h2 with rfl | h2
      · exact hK
      · exact h2

/-- A regular, late or full payment keeps the shape. -/
lemma Loan.pay_nextShape (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hpt : pt ≠ .overpayment) (hs : loan.PayShape) (hn : loan.NextShape)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) : r.loan'.NextShape := by
  obtain ⟨p, hp, hsettle⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hsettle
  suffices hp' : p.loan.NextShape from hp'.of_raw hloan rfl rfl rfl rfl rfl
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    exact (UnsettledPayment.payInstalments_nextShape amount _ _ p hloop hs.unimpaired hn.unimpaired).1
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, -, e2, -, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    exact (Loan.doPayment_nextShape loan.unimpaired p.loan pc0 pc hs.unimpaired hn.unimpaired
      (Loan.payInstalments_ok loan v .late amount now p hp).1.remaining
      (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) e2 e4 hdo).1
  · obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .full amount now p hp
    exact hn.unimpaired.of_paid (Loan.fullPayInstalments_paid loan v amount now p hp) hst.rates hst.schedule
  · exact absurd rfl hpt

/-- A re-amortization on a loan whose theoretical principal is at most PrincipalOutstanding leaves principal, and the
theoretical principal of its new PeriodicPayment after the next payment is at most the new PrincipalOutstanding. -/
private lemma Loan.tryOverpayment_next (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80) (hn : l.paymentRemaining ≠ 0)
    (hδg : Number.OnGrid l.loanScale opc.principalDelta) (hδ0 : 0 < opc.principalDelta.toRat)
    (hK : l.TheoryBelow l.paymentRemaining)
    (hgap : ∀ rate, l.periodicRate = .ok rate → 2 ≤ l.paymentRemaining.toNat → FactorGap rate l.paymentRemaining)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    0 < re.state.principalOutstanding.toRat ∧
      ∀ rate t, l.periodicRate = .ok rate →
        loanPrincipalFromPeriodicPayment re.periodicPayment rate (l.paymentRemaining - 1) = .ok t →
        t.toRat ≤ re.state.principalOutstanding.toRat := by
  have hsb := Loan.loanScale_bounds l
  obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid l
  have hP := l.wf.principalOutstanding_norm
  have hδN := hδg.1
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  rename_i _ rate hrate _ st hst _ th hth _ de hde _ rp0 hrp0 _ props hprops _ s1 hs1 _ s2 hs2 _ pin hpin _ gi hgi
    _ pmf hpmf _ s3 hs3 _ po hpo _ int hintr _ tvo htvo _ tvo' htvo' _ mfo hmfo _ s4 hs4 _ dl hdl _ io hio _ g hg
    hgs _ _ _ hsig _ hle _ hneg _ _ fee hfee hw
  obtain ⟨-, hst2, -, -⟩ := Loan.state_fields l st hst
  obtain ⟨-, hb2, -⟩ := LoanState.build_fields _ _ _ _ hs4
  obtain ⟨-, hp2, -⟩ := LoanState.build_fields _ _ _ _ hs3
  rw [hst2] at hpin
  rw [hp2, hst2] at hpo
  obtain ⟨hrN, h0r, -, -⟩ := Loan.periodicRate_bounds l rate hrate
  -- the re-amortized principal is positive, or the new PeriodicPayment would be zero
  have hthN := (LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm hrN hth).2.1
  have hrp0N := operator_sub_isNormalized_to_nearest_sz _ _ _ hthN hδN hrp0
  have hmaxN := Number.max_isNormalized' hrp0N Number.zero_isNormalized
  have hpp := computeLoanPropertiesFromPeriodicRate_pp _ _ _ _ _ _ _ hprops
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hmaxN hrN hpp
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at hsig
  have hpp0 := (Number.signum_pos_iff_toRat hppN).mp hsig.1.1
  have hrp : 0 < rp0.toRat := by
    by_contra hle0
    push Not at hle0
    have hmax : rp0.max Number.zero = Number.zero := by
      have hv := Number.max_val _ _ hrp0N Number.zero_isNormalized
      rw [Number.toRat_zero, max_eq_right hle0] at hv
      exact (Number.toRat_eq_zero_iff_eq_zero hmaxN).mp hv
    rw [hmax] at hpp
    have h0 : loanPeriodicPayment Number.zero rate l.paymentRemaining = .ok Number.zero := by
      simp [loanPeriodicPayment, show Number.zero.operator_eq Number.zero = true from rfl]
    rw [h0, Except.ok.injEq] at hpp
    rw [← hpp, Number.toRat_zero] at hpp0
    exact lt_irrefl _ hpp0
  have hthδ : opc.principalDelta.toRat < th.principalOutstanding.toRat := by
    by_contra hle1
    push Not at hle1
    have := Number.roundsToRepresentable_nonpos _ _
      (operator_sub_rounded_to_nearest _ _ _ hthN hδN hrp0) (by linarith)
    linarith
  -- the theoretical principal is at most PrincipalOutstanding, so the pinned principal is positive and exact
  have hthP := hK rate th.principalOutstanding hrate (LoanState.buildTheoretical_principal_eq _ _ _ _ _ hn hth)
  have hv := Number.OnGrid.sub_exact hPg hδg hδ0.le (by linarith) hPlt hsb hpin
  have gpin := Number.OnGrid.sub hPg hδg hsb hpin
  have hpin0 : 0 < pin.toRat := by rw [hv]; linarith
  -- the committed principal is the pinned principal rounded up, clamped to PrincipalOutstanding
  have hpoge : pin.toRat ≤ po.toRat := by
    unfold roundAndClamp at hpo
    simp only [bind, Except.bind] at hpo
    split at hpo
    · cases hpo
    rename_i R hR
    have hRge := STAmount.roundToNumericType_upward_ge_of_large _ _ _ _ gpin.1
      (le_trans (zpow_le_zpow_right₀ (by norm_num) hs.1) (Number.OnGrid.unit_le gpin hpin0)) hs hR
    have hRN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hR
    have hc := Number.clamp_val R Number.zero l.principalOutstanding hRN Number.zero_isNormalized hP
      (by rw [Number.toRat_zero]; linarith)
    rw [Except.ok.inj hpo, Number.toRat_zero] at hc
    rw [hc]
    exact le_trans (le_min hRge (by rw [hv]; linarith)) (le_max_right _ _)
  have hrpin : rp0.toRat ≤ pin.toRat :=
    (operator_sub_rounded_to_nearest _ _ _ hthN hδN hrp0).le_of_ge (Or.inl rfl) pin gpin.1 (by rw [hv]; linarith)
  have hmaxv : (rp0.max Number.zero).toRat = rp0.toRat := by
    rw [Number.max_val _ _ hrp0N Number.zero_isNormalized, Number.toRat_zero, max_eq_left hrp.le]
  show 0 < s4.principalOutstanding.toRat ∧ ∀ rate' t, l.periodicRate = .ok rate' →
    loanPrincipalFromPeriodicPayment props.periodicPayment rate' (l.paymentRemaining - 1) = .ok t →
    t.toRat ≤ s4.principalOutstanding.toRat
  rw [hb2]
  refine ⟨by linarith, fun rate' t hrate' ht => ?_⟩
  rw [hrate, Except.ok.injEq] at hrate'
  subst hrate'
  have := loanPrincipalFromPeriodicPayment_reamortized_le _ _ _ _ _ hmaxN (by rw [hmaxv]; exact hrp.le) hrN h0r
    (hgap rate hrate) hpp ht
  rw [hmaxv] at this
  linarith

/-- The overpayment tail keeps the shape, after scheduled instalments that left the theoretical principal of the
payments left at most PrincipalOutstanding. -/
private lemma UnsettledPayment.applyOverpayment_nextShape (payment p : UnsettledPayment Vault) (amount : Number)
    (hlo : -10 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hn : payment.loan.NextShape) (hK : payment.loan.TheoryLeft)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p) : p.loan.NextShape := by
  have hhi : payment.loan.loanScale ≤ 80 := by
    have := payment.loan.wf.loanScale_range.2; unfold cMaxOffset at this; exact this
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first | exact hn | skip
  rename_i _ a' ha' hcond _ un hun _ ov hov hovp _ opc hopc hpd _ _ re hre _ am ham _ l' hl'
  have hpr : payment.loan.paymentRemaining ≠ 0 := by
    intro h0
    simp [h0] at hcond
  have hs' : -81 ≤ payment.loan.loanScale ∧ payment.loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hovg := STAmount.roundToNumericType_onGrid _ _ _ _ _ hs' hint hov
  have hδg := Loan.overpaymentComponents_principal_grid _ _ _ hs' hint hovg hopc
  have hδ0 : 0 < opc.principalDelta.toRat := by
    have hgt : opc.principalDelta.operator_gt Number.zero = true := by
      revert hpd; cases opc.principalDelta.operator_gt Number.zero <;> simp
    have := (operator_gt_iff _ _ hδg.1 Number.zero_isNormalized).mp hgt
    rwa [Number.toRat_zero] at this
  have hpp40 := Loan.tryOverpayment_periodic_ge _ _ _ hlo hδg hδ0 hre
  have hK' : payment.loan.TheoryBelow payment.loan.paymentRemaining := fun rate tpo hrate htpo => by
    obtain ⟨t, ht, hle⟩ := hK rate hrate
    rw [ht, Except.ok.injEq] at htpo
    rw [← htpo]
    exact hle
  obtain ⟨hpo0, hnext⟩ := Loan.tryOverpayment_next payment.loan opc re hs' hpr hδg hδ0 hK'
    (fun rate hrate h2 => hn.gaps rate hrate _ h2 hn.count) hre
  have hr := (RawLoan.to_lawful_ok hl').1
  have f1 : l'.principalOutstanding = re.state.principalOutstanding := (congrArg RawLoan.principalOutstanding hr :)
  have f3 : l'.paymentRemaining = payment.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hr :)
  have f5 : l'.periodicPayment = re.periodicPayment := (congrArg RawLoan.periodicPayment hr :)
  have f6 : l'.rates = payment.loan.rates := (congrArg RawLoan.rates hr :)
  have f7 : l'.schedule = payment.loan.schedule := (congrArg RawLoan.schedule hr :)
  have hR : l'.periodicRate = payment.loan.periodicRate := by unfold Loan.periodicRate; rw [f6, f7]
  show l'.NextShape
  refine ⟨fun _ => ⟨fun h0 => ?_, by rw [f5]; exact hpp40⟩, fun rate hrate k hk2 hk =>
    hn.gaps rate (hR ▸ hrate) k hk2 (f7 ▸ hk), by rw [f3, f7]; exact hn.count, fun _ rate t hrate ht => ?_⟩
  · rw [f1] at h0
    rw [h0, Number.toRat_zero] at hpo0
    exact lt_irrefl _ hpo0
  · rw [f3, f5] at ht
    rw [f1]
    exact hnext rate t (hR ▸ hrate) ht

/-- An overpayment keeps the shape, on a loan whose LoanScale is at least `-10`. It never clears the principal
while payments are left. -/
lemma Loan.overpayment_nextShape (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hs : loan.PayShape) (hlo : -10 ≤ loan.loanScale) (hn : loan.NextShape)
    (hok : (loan.overpayment v amount now).run = .ok (.ok r)) : r.loan'.NextShape := by
  obtain ⟨p, hp, hsettle⟩ := Loan.pay_ok loan v .overpayment amount now r hok
  obtain ⟨payment, hpay, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hsettle
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  obtain ⟨si, -, hloop, hc0⟩ := Loan.payScheduled_loop loan v amount now payment hpay
  obtain ⟨hpn, hor⟩ := UnsettledPayment.payInstalments_nextShape amount _ _ _ hloop hs.unimpaired hn.unimpaired
  have hK : payment.loan.TheoryLeft := by
    rcases hor with heq | hK
    · exact absurd (congrArg UnsettledPayment.count heq) hc0
    · exact hK
  have hp' := UnsettledPayment.applyOverpayment_nextShape payment p amount (by rw [hst.loanScale]; exact hlo)
    (by rw [hst.loanScale, hst.broker]; exact hs.2) hpn hK h1
  exact hp'.of_raw hloan rfl rfl rfl rfl rfl

/-- An accept keeps the shape. -/
lemma Loan.accept_nextShape (loan : Loan) (v : Vault) (r : LoanWithPool Vault) (hn : loan.NextShape)
    (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.NextShape := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hraw := ‹RawLoan.to_lawful _ = Except.ok _›
  exact hn.of_raw hraw rfl rfl rfl rfl rfl

/-- Changing the impairment keeps the shape. -/
private lemma Loan.changeImpairment_nextShape (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (hn : loan.NextShape) (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : r.loan'.NextShape := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hraw := ‹RawLoan.to_lawful _ = Except.ok _›
    exact hn.of_raw hraw rfl rfl rfl rfl rfl

/-- A loan a LoanSet creates has the shape, when its payment factor falls. Its PeriodicPayment re-amortizes
PrincipalRequested, so the theoretical principal after its first payment is at most PrincipalRequested. -/
lemma Loan.Created.nextShape {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) (hg : start.FactorGaps) :
    start.NextShape := by
  have hleft := h.principalLeft
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, allowsOverpayment, r, hcan, hok, rfl⟩ := h
  have hst := Loan.canCreate_principal_exact broker v principal fees _ t₀ twoStep hcan
  have hp := STAmount.isNormalized_of_isRounded_false _ _ hst
  have hpos := Loan.create_principal_pos broker v principal rates fees _ allowsOverpayment twoStep r hp hok
  have hPO := Loan.create_principalOutstanding broker v principal rates fees _ allowsOverpayment twoStep r hp
    hpos.le hst hok
  obtain ⟨props, _, _, _, hchecks, hl, -⟩ :=
    Loan.create_loan_eq broker v principal rates fees _ allowsOverpayment twoStep r hok
  obtain ⟨rate, _, _, _, hrate, hpp, -⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hN : r.loan'.paymentRemaining = (LoanSchedule.build pi pt gp sd t₀ twoStep).paymentTotal := by
    show r.loan'.toRawLoan.paymentRemaining = _; rw [hl]; rfl
  have hSc : r.loan'.schedule = LoanSchedule.build pi pt gp sd t₀ twoStep := by
    show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
  have hR : r.loan'.periodicRate = .ok rate := by
    have hRt : r.loan'.rates = rates := by show r.loan'.toRawLoan.rates = _; rw [hl]; rfl
    unfold Loan.periodicRate
    rw [hRt, hSc]
    exact hrate
  obtain ⟨hNr, h0, -, -⟩ := Loan.periodicRate_bounds r.loan' rate hR
  refine ⟨hleft, hg, by rw [hN, hSc]; exact UInt32.le_iff_toNat_le.mpr (le_refl _), fun _ rate' tpo hrate' htpo => ?_⟩
  rw [hR, Except.ok.injEq] at hrate'
  subst hrate'
  rw [hPP, hN] at htpo
  rw [hPO]
  exact loanPrincipalFromPeriodicPayment_reamortized_le principal rate _ _ _ hp hpos.le hNr h0
    (fun h2 => hg rate hR _ h2 (by rw [hSc]; exact UInt32.le_iff_toNat_le.mpr (le_refl _))) hpp htpo

/-- Every loan reachable with a falling payment factor keeps the shape. -/
lemma Loan.ReachableFrom.nextShape {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hc : Loan.Created start t₀) (hg : start.FactorGaps) (hr : Loan.ReachableFrom start t₀ loan t) :
    loan.NextShape := by
  induction hr with
  | refl => exact hc.nextShape hg
  | refresh _ _ _ _ _ _ h ih => exact ih.of_raw h rfl rfl rfl rfl rfl
  | accept _ _ _ _ _ _ _ _ h ih => exact Loan.accept_nextShape _ _ _ ih h
  | regularPayment _ _ _ _ _ _ hr' _ _ h ih =>
    exact Loan.pay_nextShape _ _ .regular _ _ _ (by decide) (hr'.payShape hc) ih h
  | latePayment _ _ _ _ _ _ hr' _ _ h ih =>
    exact Loan.pay_nextShape _ _ .late _ _ _ (by decide) (hr'.payShape hc) ih h
  | fullPayment _ _ _ _ _ _ hr' _ _ h ih =>
    exact Loan.pay_nextShape _ _ .full _ _ _ (by decide) (hr'.payShape hc) ih h
  | overpayment _ _ _ _ _ _ hr' _ _ h ih =>
    exact Loan.overpayment_nextShape _ _ _ _ _ (hr'.payShape hc)
      (Loan.Reachable.loanScale_facts ⟨start, t₀, hc, hr'⟩).1 ih h
  | impair _ _ _ _ _ _ _ _ h ih =>
    simp only [Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_nextShape _ _ true _ ih ‹_›
  | unimpair _ _ _ _ _ _ _ _ h ih => exact Loan.changeImpairment_nextShape _ _ false _ ih h
  | default _ _ _ _ _ _ _ _ h ih =>
    obtain ⟨h1, h2⟩ := Loan.manageDefault_terms _ _ _ h
    exact ih.of_paid (Loan.manageDefault_paid _ _ _ h) h1 h2

/-- A reachable loan whose payment factor falls by at least four roundings per payment has principal left while
payments are left, with or without the overpayment flag. -/
lemma Loan.Reachable.principal_left_of_factorGap {loan : Loan} {t : UInt32} (hr : loan.Reachable t)
    (hgap : ∀ rate, loan.periodicRate = .ok rate → ∀ k : UInt32, 2 ≤ k.toNat → k ≤ loan.schedule.paymentTotal →
      FactorGap rate k)
    (hn : loan.paymentRemaining ≠ 0) : loan.principalOutstanding ≠ Number.zero := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  have hkt := hr'.keepsTerms
  have hR : loan.periodicRate = start.periodicRate := by unfold Loan.periodicRate; rw [hkt.rates, hkt.schedule]
  have hg : start.FactorGaps := fun rate hrate k hk2 hk =>
    hgap rate (hR ▸ hrate) k hk2 (by rw [hkt.schedule]; exact hk)
  exact ((hr'.nextShape hc hg).left hn).1

end XRPL.Model.Lending
