import XRPL.Properties.Lending.Loan.Common.InterestDue
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterestIntegral
import XRPL.Properties.Lending.Loan.Common.PaySteps
import XRPL.Properties.Lending.Loan.Common.ManageDefs
import XRPL.Properties.Lending.Loan.Common.ManageCover
import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional
import XRPL.Properties.Lending.Ledger.Common.RecheckPool
import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Vault.Proofs.Support.Errors

/-! # The loan re-checks inside a payment

A payment re-checks the loan after each instalment, after an overpayment and on the updated broker. Every step between
fails only with a Number or STAmount error, so `notLawful` comes only from these, the broker or the vault re-check. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.overpaymentComponents
  Loan.tryOverpayment Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment
  UnsettledPayment.payInstalments Loan.doPayment Loan.settlePayment validatePostPayment roundAndSplitInterest
  from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private computeLoanPropertiesFromPeriodicRate_periodicPayment_normalized LoanState.buildTheoretical_normalized
  Loan.reamortized_interestDue_nonneg from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps
open private Number.min_val Number.max_val Number.clamp_val Number.floorZero LoanStateDeltas.InRange.total ite_bind_ok
  Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue

private lemma loanLatePaymentInterest_ne_notLawful (po : Number) (rate : TenthBips32) (now due : UInt32) :
    loanLatePaymentInterest po rate now due ≠ .error .notLawful := by
  unfold loanLatePaymentInterest
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [loanPeriodicRate_ne_notLawful, Number.operator_mul_ne_notLawful]

private lemma loanAccruedInterest_ne_notLawful (po rate : Number) (now start prev interval : UInt32) :
    loanAccruedInterest po rate now start prev interval ≠ .error .notLawful := by
  unfold loanAccruedInterest
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_mul_ne_notLawful, Number.operator_div_ne_notLawful]

private lemma computeFullPaymentInterest_ne_notLawful (po rate : Number) (now interval prev start : UInt32)
    (close : TenthBips32) :
    computeFullPaymentInterest po rate now interval prev start close ≠ .error .notLawful := by
  unfold computeFullPaymentInterest
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [loanAccruedInterest_ne_notLawful, tenthBipsOfValue_ne_notLawful,
    Number.operator_add_ne_notLawful]

private lemma LoanState.buildTheoretical_ne_notLawful (pp rate : Number) (pr : UInt32) (m : TenthBips16) :
    LoanState.buildTheoretical pp rate pr m ≠ .error .notLawful := by
  unfold LoanState.buildTheoretical
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_mul_ne_notLawful, loanPrincipalFromPeriodicPayment_ne_notLawful,
    Number.operator_sub_ne_notLawful, tenthBipsOfValue_ne_notLawful]

private lemma LoanState.grossInterestOutstanding_ne_notLawful (st : LoanState) :
    st.grossInterestOutstanding ≠ .error .notLawful :=
  Number.operator_add_ne_notLawful _ _ _

private lemma LoanState.calculateDeltas_ne_notLawful (x y : LoanState) :
    LoanState.calculateDeltas x y ≠ .error .notLawful := by
  unfold LoanState.calculateDeltas
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_sub_ne_notLawful]

private lemma LoanStateDeltas.total_ne_notLawful (d : LoanStateDeltas) : d.total ≠ .error .notLawful := by
  unfold LoanStateDeltas.total
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.operator_add_ne_notLawful]

private lemma LoanState.addDeltas_ne_notLawful (x : LoanState) (d : LoanStateDeltas) :
    x.addDeltas d ≠ .error .notLawful := by
  unfold LoanState.addDeltas
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [LoanStateDeltas.total_ne_notLawful, Number.operator_add_ne_notLawful]

private lemma reduceCapped_ne_notLawful (value excess : Number) :
    reduceCapped value excess ≠ .error .notLawful := by
  unfold reduceCapped
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_sub_ne_notLawful]

private lemma LoanStateDeltas.reduceByExcess_ne_notLawful (d : LoanStateDeltas) (excess : Number) :
    d.reduceByExcess excess ≠ .error .notLawful := by
  unfold LoanStateDeltas.reduceByExcess
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [reduceCapped_ne_notLawful]

private lemma PaymentComponents.totalDue_ne_notLawful (pc : PaymentComponents) :
    pc.totalDue ≠ .error .notLawful := by
  unfold PaymentComponents.totalDue
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.operator_add_ne_notLawful]

private lemma PaymentComponents.paidAmounts_ne_notLawful (pc : PaymentComponents) :
    pc.paidAmounts ≠ .error .notLawful := by
  intro h
  unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Number.operator_add_ne_notLawful, Number.operator_sub_ne_notLawful]

private lemma PaymentAmounts.add_ne_notLawful (a b : PaymentAmounts) : a.add b ≠ .error .notLawful := by
  unfold PaymentAmounts.add
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_add_ne_notLawful]

private lemma roundAndClamp_ne_notLawful (value cap : Number) (mode : rounding_mode) (nt : NumericType) (s : Int) :
    roundAndClamp value cap mode nt s ≠ .error .notLawful := by
  unfold roundAndClamp
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.roundToNumericType_ne_notLawful]

private lemma LoanProperties.amortizationGuards_ne_notLawful (props : LoanProperties) (p : Number) (b : Bool)
    (pr : UInt32) (nt : NumericType) : props.amortizationGuards p b pr nt ≠ .error .notLawful := by
  unfold LoanProperties.amortizationGuards
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_sub_ne_notLawful, STAmount.roundToNumericType_ne_notLawful,
    Number.operator_div_ne_notLawful, Number.to_rep_ne_notLawful]

private lemma Loan.periodicRate_ne_notLawful (l : Loan) : l.periodicRate ≠ .error .notLawful :=
  loanPeriodicRate_ne_notLawful _ _

private lemma Loan.state_ne_notLawful (l : Loan) : l.state ≠ .error .notLawful :=
  LoanState.build_ne_notLawful _ _ _

private lemma roundAndSplitInterest_ne_notLawful (i : Number) (rate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (s : Int) : roundAndSplitInterest i rate mode nt s ≠ .error .notLawful := by
  intro h
  unfold roundAndSplitInterest at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [STAmount.roundToNumericType_ne_notLawful, computeManagementFee_ne_notLawful,
    Number.operator_sub_ne_notLawful]

private lemma Loan.scheduledComponents_ne_notLawful (l : Loan) :
    Loan.scheduledComponents l ≠ .error .notLawful := by
  intro h
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Loan.periodicRate_ne_notLawful, STAmount.roundToNumericType_ne_notLawful,
    Loan.state_ne_notLawful, LoanState.buildTheoretical_ne_notLawful, Number.operator_sub_ne_notLawful,
    Number.operator_add_ne_notLawful, LoanStateDeltas.total_ne_notLawful,
    LoanStateDeltas.reduceByExcess_ne_notLawful]

private lemma Loan.lateComponents_ne_notLawful (l : Loan) (now : UInt32) :
    Loan.lateComponents l now ≠ .error .notLawful := by
  intro h
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Loan.scheduledComponents_ne_notLawful, loanLatePaymentInterest_ne_notLawful,
    roundAndSplitInterest_ne_notLawful, Number.operator_add_ne_notLawful]

private lemma Loan.fullComponents_ne_notLawful (l : Loan) (now : UInt32) :
    Loan.fullComponents l now ≠ .error .notLawful := by
  intro h
  unfold Loan.fullComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Loan.periodicRate_ne_notLawful, loanPrincipalFromPeriodicPayment_ne_notLawful,
    computeFullPaymentInterest_ne_notLawful, roundAndSplitInterest_ne_notLawful, Loan.state_ne_notLawful,
    STAmount.roundToNumericType_ne_notLawful, Number.operator_add_ne_notLawful, Number.operator_sub_ne_notLawful]

private lemma Loan.overpaymentComponents_ne_notLawful (l : Loan) (x : Number) :
    Loan.overpaymentComponents l x ≠ .error .notLawful := by
  intro h
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [tenthBipsOfValue_ne_notLawful, STAmount.roundToNumericType_ne_notLawful,
    roundAndSplitInterest_ne_notLawful, Number.operator_sub_ne_notLawful]

private lemma Loan.tryOverpayment_ne_notLawful (l : Loan) (opc : PaymentComponents) :
    Loan.tryOverpayment l opc ≠ .error .notLawful := by
  intro h
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Loan.periodicRate_ne_notLawful, Loan.state_ne_notLawful,
    LoanState.buildTheoretical_ne_notLawful, LoanState.calculateDeltas_ne_notLawful,
    Number.operator_sub_ne_notLawful, computeLoanPropertiesFromPeriodicRate_ne_notLawful,
    LoanState.addDeltas_ne_notLawful, tenthBipsOfValue_ne_notLawful, LoanState.build_ne_notLawful,
    roundAndClamp_ne_notLawful, LoanState.grossInterestOutstanding_ne_notLawful, Number.operator_add_ne_notLawful,
    LoanProperties.amortizationGuards_ne_notLawful]

/-- A scheduled instalment that isn't the last takes less than TotalValueOutstanding. Its value delta is at
most the periodic payment rounded up, which is below TotalValueOutstanding for an instalment that isn't the last. -/
lemma Loan.scheduledComponents_delta_lt (l : Loan) (pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (h : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) :
    pc.totalValueDelta.toRat < l.totalValueOutstanding.toRat := by
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
  obtain ⟨gt1, vt1⟩ := LoanStateDeltas.InRange.total hJ1 ht1
  have ht1pp : t1.toRat ≤ pp'.toRat := by
    rw [vt1]
    have := min_le_left (min M0.toRat (pp'.toRat - ((Number.min P0 cs.principalOutstanding).toRat +
      (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat))) M
    have h2 := min_le_right M0.toRat (pp'.toRat - ((Number.min P0 cs.principalOutstanding).toRat +
      (Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue).toRat))
    show _ + _ + (Number.min (Number.min M0 rff) cs.managementFeeDue).toRat ≤ _
    rw [vM1]
    linarith
  -- so nothing is over the outstanding value and nothing is short of the payment
  have hd2' : d2 = (⟨Number.min P0 cs.principalOutstanding,
      Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue,
      Number.min (Number.min M0 rff) cs.managementFeeDue⟩ : LoanStateDeltas) := by
    rcases hd2 with rfl | ⟨hgt, -⟩
    · rfl
    · exfalso
      have gov := Number.OnGrid.sub gt1 gcT hs hov
      have hR := operator_sub_rounded_to_nearest _ _ _ gt1.1 gcT.1 hov
      have hov0 := Number.roundsToRepresentable_nonpos _ _ hR (by rw [vcT]; linarith)
      have := (operator_gt_iff _ _ gov.1 Number.zero_isNormalized).mp hgt
      rw [Number.toRat_zero] at this
      linarith
  subst hd2'
  have ht2v : t2.toRat = t1.toRat := by rw [Except.ok.inj (ht1.symm.trans ht2)]
  have hd3' : d3 = (⟨Number.min P0 cs.principalOutstanding,
      Number.min (Number.min I0 (Number.max Number.zero room)) cs.interestDue,
      Number.min (Number.min M0 rff) cs.managementFeeDue⟩ : LoanStateDeltas) := by
    rcases hd3 with rfl | ⟨hneg, -⟩
    · rfl
    · exfalso
      have gt2 : Number.OnGrid l.loanScale t2 := by rw [Except.ok.inj (ht1.symm.trans ht2)] at gt1; exact gt1
      have gsh := Number.OnGrid.sub gpp gt2 hs hsh
      have hR := operator_sub_rounded_to_nearest _ _ _ gpp.1 gt2.1 hsh
      have hsh0 := hR.ge_of_le (Or.inl rfl) Number.zero Number.zero_isNormalized
        (by rw [Number.toRat_zero, ht2v]; linarith)
      rw [Number.toRat_zero] at hsh0
      have := (Number.signum_nonneg_iff_toRat gsh.1).mpr hsh0
      omega
  subst hd3'
  have ht3v : t3.toRat = t1.toRat := by rw [Except.ok.inj (ht1.symm.trans ht3)]
  -- the clamp keeps the value delta at most the payment
  have vT := Number.clamp_val t3 Number.zero cs.valueOutstanding (by
      rw [Except.ok.inj (ht1.symm.trans ht3)] at gt1; exact gt1.1) Number.zero_isNormalized gcT.1
    (by rw [Number.toRat_zero, vcT]; exact hT0)
  rw [Number.toRat_zero, vcT, ht3v] at vT
  show (Number.clamp t3 Number.zero cs.valueOutstanding).toRat < T
  rw [vT]
  exact max_lt (by linarith) (lt_of_le_of_lt (min_le_left _ _) (by linarith))

/-- The last instalment writes a lawful loan: it owes nothing and has no due date. -/
private lemma Loan.doPayment_final_lawful (l : Loan) :
    ∃ l', ({ l.toRawLoan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := l.nextPaymentDueDate, nextPaymentDueDate := 0 } : RawLoan).to_lawful = .ok l' := by
  set rl : RawLoan := { l.toRawLoan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := l.nextPaymentDueDate, nextPaymentDueDate := 0 } with hrl
  have hz : Number.zero.isAtExponent l.loanScale l.broker.numericType = true := by
    unfold Number.isAtExponent; simp
  have hwf : rl.WF :=
    { l.wf with
      principalOutstanding_norm := Number.zero_isNormalized
      totalValueOutstanding_norm := Number.zero_isNormalized
      managementFeeOutstanding_norm := Number.zero_isNormalized
      totalValueOutstanding_atExponent := hz
      principalOutstanding_atExponent := hz
      managementFeeOutstanding_atExponent := hz }
  have he := l.exact
  have hvalid : rl.toExact.Valid :=
    { he with
      paid_zeroed := fun _ => ⟨Number.toRat_zero, Number.toRat_zero, Number.toRat_zero⟩
      unpaid_nonzero := fun h => absurd rfl h
      principalOutstanding_nonneg := by show (0 : ℚ) ≤ Number.zero.toRat; rw [Number.toRat_zero]
      totalValueOutstanding_nonneg := by show (0 : ℚ) ≤ Number.zero.toRat; rw [Number.toRat_zero]
      managementFeeOutstanding_nonneg := by show (0 : ℚ) ≤ Number.zero.toRat; rw [Number.toRat_zero]
      paid_no_due_date := fun _ => rfl
      interest_nonneg := by
        show (0 : ℚ) ≤ Number.zero.toRat - Number.zero.toRat - Number.zero.toRat
        rw [Number.toRat_zero]; simp
      paymentRemaining_le_total := UInt32.zero_le
      dueDate_schedule := fun h => absurd rfl h }
  obtain ⟨l', hl', -⟩ := RawLoan.to_lawful_ok_of hwf ((RawLoan.valid_iff_exact rl hwf).mpr hvalid)
  exact ⟨l', hl'⟩

/-- A whole number of units at most an amount the asset stores at that exponent is stored too. -/
private lemma atExponent_of_le {x y : ℚ} {s : Int} {B : ℕ} (hy : Number.AtExponent y s B) (k : ℤ)
    (hx : x = (k : ℚ) * 10 ^ s) (h0 : 0 ≤ x) (hle : x ≤ y) : Number.AtExponent x s B := by
  obtain ⟨m, hm, hmv⟩ := hy
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ k := le_of_mul_le_mul_right (by rw [zero_mul, ← hx]; exact h0) hp
    exact_mod_cast this
  have hkm : k ≤ m := by
    have : (k : ℚ) ≤ m := le_of_mul_le_mul_right (by rw [← hx, ← hmv]; exact hle) hp
    exact_mod_cast this
  exact ⟨k.toNat, by omega, by rw [hx]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hk0).symm⟩

/-- An instalment that isn't the last writes a lawful loan when its deltas are tracked, it leaves value
outstanding, and at least two payments remain. -/
private lemma Loan.doPayment_tracked_lawful (l : Loan) (pc : PaymentComponents) (ht : pc.Tracked l)
    (hlt : pc.totalValueDelta.toRat < l.totalValueOutstanding.toRat) (hr0 : l.paymentRemaining ≠ 0)
    (hr1 : l.paymentRemaining ≠ 1) (tv pv mv : Number)
    (htv : l.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest = .ok tv)
    (hpv : l.principalOutstanding.operator_sub pc.principalDelta .to_nearest = .ok pv)
    (hmv : l.managementFeeOutstanding.operator_sub pc.managementFeeDelta .to_nearest = .ok mv) :
    ∃ l', ({ l.toRawLoan with
      totalValueOutstanding := tv, principalOutstanding := pv, managementFeeOutstanding := mv,
      paymentRemaining := l.paymentRemaining - 1, previousPaymentDueDate := l.nextPaymentDueDate,
      nextPaymentDueDate := l.nextPaymentDueDate + l.schedule.paymentInterval } : RawLoan).to_lawful = .ok l' := by
  obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, hle, -⟩ := ht
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hs := Loan.loanScale_bounds l
  have hgrid := l.grid
  have hbound : ∀ x : ℚ, Number.AtExponent x l.loanScale l.toExact.numericType.mantissaBound →
      x < 2 ^ 63 * 10 ^ l.loanScale := by
    intro x ⟨m, hm, hx⟩
    have hB := NumericType.mantissaBound_le l.toExact.numericType
    have : (m : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hm hB
    rw [hx]; exact mul_lt_mul_of_pos_right this (zpow_pos (by norm_num) _)
  have hPb : l.principalOutstanding.toRat < 2 ^ 63 * 10 ^ l.loanScale :=
    hbound _ hgrid.principalOutstanding_atExponent
  have hMb : l.managementFeeOutstanding.toRat < 2 ^ 63 * 10 ^ l.loanScale :=
    hbound _ hgrid.managementFeeOutstanding_atExponent
  have vtv := Number.OnGrid.sub_toRat gT gtv hs (by rw [abs_lt]; constructor <;> linarith) htv
  have vpv := Number.OnGrid.sub_toRat gP gpd hs (by rw [abs_lt]; constructor <;> linarith) hpv
  have vmv := Number.OnGrid.sub_toRat gM gmd hs (by rw [abs_lt]; constructor <;> linarith) hmv
  have gtv' := Number.OnGrid.sub gT gtv hs htv
  have gpv' := Number.OnGrid.sub gP gpd hs hpv
  have gmv' := Number.OnGrid.sub gM gmd hs hmv
  set rl : RawLoan := { l.toRawLoan with
      totalValueOutstanding := tv, principalOutstanding := pv, managementFeeOutstanding := mv,
      paymentRemaining := l.paymentRemaining - 1, previousPaymentDueDate := l.nextPaymentDueDate,
      nextPaymentDueDate := l.nextPaymentDueDate + l.schedule.paymentInterval } with hrl
  have htv0 : 0 ≤ tv.toRat := by rw [vtv]; linarith
  have hpv0 : 0 ≤ pv.toRat := by rw [vpv]; linarith
  have hmv0 : 0 ≤ mv.toRat := by rw [vmv]; linarith
  have hwf : rl.WF :=
    { l.wf with
      totalValueOutstanding_norm := gtv'.1
      principalOutstanding_norm := gpv'.1
      managementFeeOutstanding_norm := gmv'.1
      totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gtv'.1 htv0).mpr
        (atExponent_of_le hgrid.totalValueOutstanding_atExponent gtv'.2.choose gtv'.2.choose_spec htv0
          (by show tv.toRat ≤ l.totalValueOutstanding.toRat; linarith))
      principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gpv'.1 hpv0).mpr
        (atExponent_of_le hgrid.principalOutstanding_atExponent gpv'.2.choose gpv'.2.choose_spec hpv0
          (by show pv.toRat ≤ l.principalOutstanding.toRat; linarith))
      managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gmv'.1 hmv0).mpr
        (atExponent_of_le hgrid.managementFeeOutstanding_atExponent gmv'.2.choose gmv'.2.choose_spec hmv0
          (by show mv.toRat ≤ l.managementFeeOutstanding.toRat; linarith)) }
  have hpr : l.paymentRemaining - 1 ≠ 0 := by
    intro h
    apply hr1
    have h0 : l.paymentRemaining.toNat ≠ 0 := fun h' => hr0 (UInt32.toNat_inj.mp (by simpa using h'))
    have h1 := congrArg UInt32.toNat h
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at h1
    exact UInt32.toNat_inj.mp (by simp at h1 ⊢; omega)
  -- one instalment moves the due date one interval on, still by the largest ledger time
  have hP1 : 1 ≤ l.paymentRemaining.toNat := by
    have : l.paymentRemaining.toNat ≠ 0 := fun h0 => hr0 (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  have hP2 : 2 ≤ l.paymentRemaining.toNat := by
    have : l.paymentRemaining.toNat ≠ 1 := fun h1 => hr1 (UInt32.toNat_inj.mp (by simpa using h1))
    omega
  have hsub : (l.paymentRemaining - 1).toNat = l.paymentRemaining.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hP1)]; rfl
  have hle0 := UInt32.le_iff_toNat_le.mp l.valid.paymentRemaining_le_total
  have hnext := l.valid.dueDate_schedule hr0
  have hend := l.valid.schedule_in_time
  have hM : maxTime.toNat = 4294967295 := rfl
  set T := l.schedule.paymentTotal.toNat
  set P := l.paymentRemaining.toNat
  set i := l.schedule.paymentInterval.toNat
  have hbound : (T - P + 2) * i ≤ T * i := Nat.mul_le_mul_right _ (by omega)
  have hsum : (l.nextPaymentDueDate + l.schedule.paymentInterval).toNat = l.nextPaymentDueDate.toNat + i := by
    rw [UInt32.toNat_add]
    apply Nat.mod_eq_of_lt
    have : (T - P + 1) * i + i = (T - P + 2) * i := by ring
    omega
  have he := l.exact
  have hvalid : rl.toExact.Valid :=
    { he with
      paid_zeroed := fun h => absurd h hpr
      unpaid_nonzero := fun _ => Or.inl (by show tv.toRat ≠ 0; rw [vtv]; linarith)
      principalOutstanding_nonneg := hpv0
      totalValueOutstanding_nonneg := htv0
      managementFeeOutstanding_nonneg := hmv0
      paid_no_due_date := fun h => absurd h hpr
      interest_nonneg := by
        show 0 ≤ tv.toRat - pv.toRat - mv.toRat
        have hle' : pc.totalValueDelta.toRat - pc.principalDelta.toRat - pc.managementFeeDelta.toRat ≤
          l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat := hle
        rw [vtv, vpv, vmv]; linarith
      paymentRemaining_le_total := by
        show l.paymentRemaining - 1 ≤ l.schedule.paymentTotal
        have := he.paymentRemaining_le_total
        rw [UInt32.le_iff_toNat_le] at this ⊢
        rw [hsub]; omega
      dueDate_schedule := fun _ => by
        show (l.nextPaymentDueDate + l.schedule.paymentInterval).toNat = l.schedule.startDate.toNat +
          (l.schedule.paymentTotal.toNat - (l.paymentRemaining - 1).toNat + 1) * l.schedule.paymentInterval.toNat
        rw [hsum, hnext, hsub]
        have hk : T - (P - 1) + 1 = (T - P + 1) + 1 := by omega
        rw [hk]; ring }
  obtain ⟨l', hl', -⟩ := RawLoan.to_lawful_ok_of hwf ((RawLoan.valid_iff_exact rl hwf).mpr hvalid)
  exact ⟨l', hl'⟩

/-- An instalment never fails the loan re-check when it is the last, or its deltas are tracked, it leaves
value outstanding and at least two payments remain. -/
lemma Loan.doPayment_ne_notLawful (l : Loan) (pc : PaymentComponents)
    (hpc : pc.isFinal = true ∨ (pc.isFinal = false ∧ pc.Tracked l ∧
      pc.totalValueDelta.toRat < l.totalValueOutstanding.toRat ∧ l.paymentRemaining ≠ 0 ∧
      l.paymentRemaining ≠ 1)) :
    Loan.doPayment l pc ≠ .error .notLawful := by
  intro h
  rcases hpc with hf | ⟨hf, ht, hlt, hr0, hr1⟩
  · simp only [Loan.doPayment, hf, ↓reduceIte] at h
    obtain ⟨l', hl'⟩ := Loan.doPayment_final_lawful l
    unfold_ter at h
    rw [hl'] at h
    cases h
  · simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
      | skip
    rename_i hw
    obtain ⟨l', hl'⟩ := Loan.doPayment_tracked_lawful l pc ht hlt hr0 hr1 _ _ _ ‹_› ‹_› ‹_›
    rw [hl'] at hw
    cases hw

/-- What the instalment loop keeps about its loan: LoanScale in the asset's range and interestDue at least zero. -/
structure Loan.PayShape (l : Loan) : Prop where
  loanScale_ge : -81 ≤ l.loanScale
  loanScale_integral : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0
  interest_nonneg : 0 ≤ l.toExact.interestDue

/-- A scheduled instalment never fails the loan re-check on a loan of that shape. -/
lemma Loan.doPayment_scheduled_ne_notLawful (l : Loan) (hl : l.PayShape) (pc pc' : PaymentComponents)
    (hpc : Loan.scheduledComponents l = .ok pc) (hr0 : l.paymentRemaining ≠ 0)
    (hpc' : pc'.totalValueDelta = pc.totalValueDelta ∧ pc'.principalDelta = pc.principalDelta ∧
      pc'.managementFeeDelta = pc.managementFeeDelta ∧ pc'.isFinal = pc.isFinal) :
    Loan.doPayment l pc' ≠ .error .notLawful := by
  obtain ⟨e1, e2, e3, e4⟩ := hpc'
  apply Loan.doPayment_ne_notLawful
  rcases Loan.scheduledComponents_tracked l pc hl.1 hl.2 hl.3 hpc with hf | ⟨hf, ht⟩
  · exact Or.inl (by rw [e4]; exact hf)
  · refine Or.inr ⟨by rw [e4]; exact hf, ?_, ?_, hr0, Loan.scheduledComponents_not_last l pc hpc hf⟩
    · obtain ⟨g1, g2, g3, r1, r2, r3, hle, hmv⟩ := ht
      exact ⟨by rw [e1]; exact g1, by rw [e2]; exact g2, by rw [e3]; exact g3, by rw [e1]; exact r1,
        by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e1, e2, e3]; exact hle, by rw [e1, e3]; exact hmv⟩
    · rw [e1]; exact Loan.scheduledComponents_delta_lt l pc hl.1 hl.2 hl.3 hpc hf

/-- A scheduled instalment that passes keeps the loan's shape. -/
lemma Loan.PayShape.doPayment {l l' : Loan} (hl : l.PayShape) (pc pc' : PaymentComponents)
    (hpc : Loan.scheduledComponents l = .ok pc)
    (hpc' : pc'.totalValueDelta = pc.totalValueDelta ∧ pc'.principalDelta = pc.principalDelta ∧
      pc'.managementFeeDelta = pc.managementFeeDelta ∧ pc'.isFinal = pc.isFinal)
    (h : Loan.doPayment l pc' = .ok l') : l'.PayShape := by
  obtain ⟨e1, e2, e3, e4⟩ := hpc'
  have hst := Loan.doPayment_sameTerms _ _ _ h
  refine ⟨by rw [hst.loanScale]; exact hl.1, by rw [hst.loanScale, hst.broker]; exact hl.2, ?_⟩
  refine Loan.doPayment_interestDue l l' pc' hl.3 ?_ h
  rcases Loan.scheduledComponents_tracked l pc hl.1 hl.2 hl.3 hpc with hf | ⟨hf, ht⟩
  · exact Or.inl (by rw [e4]; exact hf)
  · refine Or.inr ⟨by rw [e4]; exact hf, ?_⟩
    obtain ⟨g1, g2, g3, r1, r2, r3, hle, hmv⟩ := ht
    exact ⟨by rw [e1]; exact g1, by rw [e2]; exact g2, by rw [e3]; exact g3, by rw [e1]; exact r1,
      by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e1, e2, e3]; exact hle, by rw [e1, e3]; exact hmv⟩

/-- The instalment loop's form of `doPayment_scheduled_ne_notLawful`: the scheduled instalment with a fee. -/
private lemma Loan.doPayment_with_fee_ne_notLawful (l : Loan) (hl : l.PayShape) (pc : PaymentComponents)
    (fee : Number) (hpc : Loan.scheduledComponents l = .ok pc) (hr0 : ¬(l.paymentRemaining == 0) = true) :
    Loan.doPayment l { pc with untrackedManagementFee := fee } ≠ .error .notLawful :=
  Loan.doPayment_scheduled_ne_notLawful l hl pc _ hpc (by simpa using hr0) ⟨rfl, rfl, rfl, rfl⟩

/-- The instalment loop's form of `PayShape.doPayment`. -/
private lemma Loan.PayShape.doPayment_with_fee {l l' : Loan} (hl : l.PayShape) (pc : PaymentComponents)
    (fee : Number) (hpc : Loan.scheduledComponents l = .ok pc)
    (h : Loan.doPayment l { pc with untrackedManagementFee := fee } = .ok l') : l'.PayShape :=
  hl.doPayment pc _ hpc ⟨rfl, rfl, rfl, rfl⟩ h

/-- The instalment loop never fails the loan re-check on a loan of that shape. -/
lemma UnsettledPayment.payInstalments_ne_notLawful {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number) (hl : payment.loan.PayShape) :
    UnsettledPayment.payInstalments payment n amount ≠ .error .notLawful := by
  induction n generalizing payment with
  | zero => rw [UnsettledPayment.payInstalments]; exact nofun
  | succ n ih =>
    intro h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.scheduledComponents_ne_notLawful _ ‹_›
      | exact PaymentComponents.totalDue_ne_notLawful _ ‹_›
      | exact Number.operator_add_ne_notLawful _ _ _ ‹_›
      | exact PaymentComponents.paidAmounts_ne_notLawful _ ‹_›
      | exact PaymentAmounts.add_ne_notLawful _ _ ‹_›
      | skip
    · exact Loan.doPayment_with_fee_ne_notLawful _ hl _ _ ‹_› ‹_› ‹_›
    · refine ih _ ?_ ‹UnsettledPayment.payInstalments _ n amount = Except.error Error.notLawful›
      exact Loan.PayShape.doPayment_with_fee hl _ _ ‹_› ‹_›

/-- The unimpair before a payment never fails a re-check when the asset stores AssetsAvailable exactly. It
moves only LossUnrealized and clears the loan's impaired flag. -/
lemma Loan.unimpairIfImpaired_ne_notLawful (loan : Loan) (v : Vault)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    (Loan.unimpairIfImpaired loan v).run ≠ .error .notLawful := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp]; exact nofun
  · rw [Loan.unimpairIfImpaired_impaired loan v himp]
    have hc : PoolBalanceChange.Normalized { loss := loan.principalOutstanding.operator_neg } :=
      ⟨Number.zero_isNormalized, Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm,
        Number.zero_isNormalized, Number.zero_isNormalized⟩
    have hne := Vault.poolAdjust_ne_notLawful v { loss := loan.principalOutstanding.operator_neg } hc
      (fun raw hadj => by
        obtain ⟨aa', ad', lu', ar', yu', hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
        obtain ⟨aa, haa1, haa2⟩ := hs.cash
        obtain rfl := Number.eq_of_add_zero haa1
        obtain rfl := Number.eq_of_add_zero hs.deployed
        obtain rfl := Number.eq_of_add_zero hs.reserved
        have haa' := STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm haa haa2
        have hex := v.exact
        refine ⟨hex.assetsDeployed_representable, hex.assetsReserved_le, fun h0 => ?_,
          (Vault.round_cash_valid v _ haa2).1, (Vault.round_cash_valid v _ haa2).2⟩
        have hs0 : v.toExact.sharesTotal = 0 := by
          show v.sharesTotal.toRat.num.toNat = 0
          rw [h0, Number.toRat_zero]; rfl
        obtain ⟨e1, e2⟩ := hex.empty_shares hs0
        exact ⟨by rw [haa']; exact e1, e2⟩)
    split
    · rename_i e he; intro h; cases h; exact hne he
    · exact nofun
    · exact nofun

/-- The loan without the impaired flag has the same shape. -/
lemma Loan.PayShape.unimpaired {l : Loan} (hl : l.PayShape) : l.unimpaired.PayShape :=
  ⟨hl.1, hl.2, by
    show 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat
    exact hl.3⟩

/-- A full payment pays the loan off in one instalment. -/
private lemma Loan.fullComponents_final (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.fullComponents l now = .ok pc) : pc.isFinal = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    Loan.fullComponents_ok_inv l now pc h
  rfl

/-- A late instalment never fails the loan re-check on a loan of that shape. -/
private lemma Loan.doPayment_late_ne_notLawful (l : Loan) (hl : l.PayShape) (now : UInt32) (pc : PaymentComponents)
    (hpc : Loan.lateComponents l now = .ok pc) (hr0 : l.paymentRemaining ≠ 0) :
    Loan.doPayment l pc ≠ .error .notLawful := by
  obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled l now pc hpc
  exact Loan.doPayment_scheduled_ne_notLawful l hl pc0 pc hpc0 hr0 ⟨e1, e2, e3, e4⟩

/-- The unimpair that passes hands on the loan without the impaired flag. -/
private lemma Loan.unimpairIfImpaired_loan' (loan : Loan) (v : Vault) (a : LoanWithPool Vault)
    (h : Loan.unimpairIfImpaired loan v = .ok (.ok a)) : a.loan' = loan.unimpaired :=
  Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact h)

/-- The scheduled instalments never fail a re-check when the unimpair does not. -/
private lemma Loan.payScheduled_ne_notLawful (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (hl : loan.PayShape) (hu : (Loan.unimpairIfImpaired loan v).run ≠ .error .notLawful) :
    (Loan.payScheduledInstalments loan v amount now).run ≠ .error .notLawful := by
  intro h
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hu (by simp only [ExceptT.run]; assumption)
    | exact RawLoan.interestDue_ne_notLawful _ ‹_›
    | skip
  rename_i hloop
  refine UnsettledPayment.payInstalments_ne_notLawful _ _ _ ?_ hloop
  dsimp only
  rw [Loan.unimpairIfImpaired_loan' loan v _ ‹Loan.unimpairIfImpaired loan v = _›]
  exact hl.unimpaired

/-- A payment's instalments never fail a re-check on a loan of that shape, when the unimpair and the
overpayment tail do not. -/
lemma Loan.payInstalments_ne_notLawful (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32) (hl : loan.PayShape) (hu : (Loan.unimpairIfImpaired loan v).run ≠ .error .notLawful)
    (hover : pt = .overpayment → ∀ p0, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      UnsettledPayment.applyOverpayment p0 amount ≠ .error .notLawful) :
    (loan.payInstalments v pt amount now).run ≠ .error .notLawful := by
  cases pt
  · exact Loan.payScheduled_ne_notLawful loan v amount now hl hu
  · intro h
    simp only [Loan.payInstalments, Loan.payInstalment] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact hu (by simp only [ExceptT.run]; assumption)
      | exact Loan.lateComponents_ne_notLawful _ _ ‹_›
      | exact PaymentComponents.totalDue_ne_notLawful _ ‹_›
      | exact RawLoan.interestDue_ne_notLawful _ ‹_›
      | exact PaymentComponents.paidAmounts_ne_notLawful _ ‹_›
      | skip
    rename_i hdo
    have hla := Loan.unimpairIfImpaired_loan' loan v _ ‹Loan.unimpairIfImpaired loan v = _›
    refine Loan.doPayment_late_ne_notLawful _ ?_ now _ ‹Loan.lateComponents _ now = _› ?_ hdo
    · rw [hla]; exact hl.unimpaired
    · rw [hla]
      show loan.paymentRemaining ≠ 0
      intro h0
      apply ‹¬(loan.paymentRemaining == 0 || _) = true›
      simp [h0]
  · intro h
    simp only [Loan.payInstalments, Loan.payInstalment] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact hu (by simp only [ExceptT.run]; assumption)
      | exact Loan.fullComponents_ne_notLawful _ _ ‹_›
      | exact PaymentComponents.totalDue_ne_notLawful _ ‹_›
      | exact RawLoan.interestDue_ne_notLawful _ ‹_›
      | exact PaymentComponents.paidAmounts_ne_notLawful _ ‹_›
      | skip
    rename_i hdo
    exact Loan.doPayment_ne_notLawful _ _ (Or.inl (Loan.fullComponents_final _ _ _ ‹Loan.fullComponents _ now = _›))
      hdo
  · intro h
    simp only [Loan.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact Loan.payScheduled_ne_notLawful loan v amount now hl hu (by simp only [ExceptT.run]; assumption)
    · rename_i hov
      exact hover rfl _ (by simp only [ExceptT.run, Loan.payInstalments]; assumption) hov

private lemma validatePostPayment_ne_notLawful (v : Vault) (r : LoanWithAmounts Vault) :
    (validatePostPayment v r).run ≠ .error .notLawful := by
  intro h
  simp only [validatePostPayment] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [Vault.pool_assetsTotal, RawVault.assetsTotal_ne_notLawful]

/-- A loan put on a broker of the same asset is lawful. Its checks read the broker only through the asset. -/
private lemma Loan.withBroker_lawful (loan : Loan) (b : LoanBroker) (hnt : b.numericType = loan.broker.numericType) :
    ∃ loan', ({ loan.toRawLoan with broker := b } : RawLoan).to_lawful = .ok loan' := by
  have hv := loan.valid
  have hvalid : ({ loan.toRawLoan with broker := b } : RawLoan).Valid := { hv with }
  have hw := loan.wf
  have hwf : ({ loan.toRawLoan with broker := b } : RawLoan).WF :=
    { hw with
      totalValueOutstanding_atExponent := by show _ = true; rw [hnt]; exact hw.totalValueOutstanding_atExponent
      principalOutstanding_atExponent := by show _ = true; rw [hnt]; exact hw.principalOutstanding_atExponent
      managementFeeOutstanding_atExponent := by
        show _ = true; rw [hnt]; exact hw.managementFeeOutstanding_atExponent }
  obtain ⟨l', hl', -⟩ := RawLoan.to_lawful_ok_of hwf hvalid
  exact ⟨l', hl'⟩

/-- The broker a settlement writes is lawful when its new DebtTotal and CoverAvailable are computed from a
principal of at most DebtTotal and a cover that stays at least zero, and it counts a loan. -/
private lemma LoanBroker.settle_lawful (b : LoanBroker) (pp dt' ca' : Number) (hpn : pp.isNormalized)
    (hp0 : 0 ≤ pp.toRat) (hple : pp.toRat ≤ b.debtTotal.toRat) (hcount : b.loanCount ≠ 0)
    (hdt : b.debtTotal.operator_sub pp .to_nearest = .ok dt') (hcan : ca'.isNormalized) (hca0 : 0 ≤ ca'.toRat) :
    ∃ b', ({ b.toRawLoanBroker with debtTotal := dt', coverAvailable := ca' } : RawLoanBroker).to_lawful = .ok b' := by
  have hdtn := operator_sub_isNormalized_to_nearest_sz _ _ _ b.wf.debtTotal_norm hpn hdt
  have hdt0 := operator_sub_nonneg _ _ _ b.wf.debtTotal_norm hpn hdt (by linarith)
  have hdtle := Number.operator_sub_le_self b.wf.debtTotal_norm hpn hp0 hdt
  set rb : RawLoanBroker := { b.toRawLoanBroker with debtTotal := dt', coverAvailable := ca' }
  have hwf : rb.WF := ⟨hdtn, b.wf.debtMaximum_norm, hcan⟩
  have he := b.exact
  have hvalid : rb.toExact.Valid :=
    { he with
      debtTotal_nonneg := hdt0
      coverAvailable_nonneg := hca0
      debt_within_cap := fun hm => le_trans hdtle (he.debt_within_cap hm)
      empty_broker := fun h0 => absurd (UInt32.toNat_inj.mp (by simpa [RawLoanBroker.toExact] using h0)) hcount }
  obtain ⟨b', hb', -⟩ := RawLoanBroker.to_lawful_ok_of hwf ((RawLoanBroker.valid_iff_exact rb hwf).mpr hvalid)
  exact ⟨b', hb'⟩

/-- The vault update of a settlement passes its re-check: the vault facts hold for every update, and the credit
floored onto a grid at or above the base keeps the new cash on the base grid. -/
private lemma Loan.settle_pool_ne_notLawful (p : UnsettledPayment Vault) (hpn : p.amounts.principalPaid.isNormalized)
    (hsi : p.scheduledInterest.isNormalized)
    (hpool : ∀ toPool yieldDelta raw, (p.pool.adjustBalances (p.change toPool yieldDelta)).run = .ok (.ok raw) →
      STAmount.Representable p.pool.numericType raw.assetsDeployed.toRat ∧
      raw.assetsReserved.toRat ≤ raw.assetsDeployed.toRat ∧
      (p.pool.sharesTotal = Number.zero → raw.assetsAvailable.toRat = 0 ∧ raw.assetsDeployed.toRat = 0))
    (hnt : p.loan.broker.numericType = p.pool.numericType)
    (hmax : p.pool.numericType.isIntegral = true → p.pool.numericType.maxValue.toNat ≤ maxRep.toNat)
    {tp yd totalPaid si' : Number} {st : STAmount}
    (hfail : AssetPool.adjustBalances p.pool
      { cash := tp, deployed := p.amounts.principalPaid.operator_neg, yield := yd } = .error .notLawful)
    (hsrs : sumRoundAndSubtract (AssetPool.amounts p.pool).assetsAvailable totalPaid (AssetPool.baseExponent p.pool)
      p.loan.broker.numericType .downward = .ok st)
    (htp : st.toNumber .to_nearest = .ok tp) (hdue : p.loan.interestDue = .ok si')
    (hyd : si'.operator_sub p.scheduledInterest .to_nearest = .ok yd) : False := by
  rw [Vault.pool_amounts, Vault.pool_baseExponent] at hsrs
  have hcN :
      PoolBalanceChange.Normalized { cash := tp, deployed := p.amounts.principalPaid.operator_neg, yield := yd } :=
    ⟨Number.operator_neg_isNormalized _ hpn, Number.zero_isNormalized, Number.zero_isNormalized,
      operator_sub_isNormalized_to_nearest_sz _ _ _ (RawLoan.interestDue_isNormalized _ _ hdue) hsi hyd⟩
  refine Vault.poolAdjust_ne_notLawful p.pool _ hcN (fun raw hadj => ?_) hfail
  obtain ⟨h1, h2, h3⟩ := hpool tp yd raw hadj
  have hg := sumRoundAndSubtract_onGrid _ _ _ _ _ _ _ (Vault.assetsAvailable_onGrid p.pool)
    ⟨p.pool.baseExponent_bounds.1, p.pool.baseExponent_bounds.2.1⟩
    (fun hi => p.pool.baseExponent_bounds.2.2 (hnt ▸ hi)) hsrs htp
  obtain ⟨h4, h5⟩ := Vault.adjustBalances_cash_valid p.pool _ raw hmax hg hadj
    (Vault.adjustBalances_ok_facts p.pool _ raw hcN hadj).2.2.2.2.2.2.1
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A settlement never fails a re-check when the principal it pays is at most DebtTotal, the broker counts
the loan, a fee that joins the cover leaves it at least zero, and the vault update passes its re-check. -/
lemma Loan.settle_ne_notLawful (p : UnsettledPayment Vault)
    (hpaid : p.amounts.principalPaid.isNormalized ∧ 0 ≤ p.amounts.principalPaid.toRat ∧
      p.amounts.principalPaid.toRat ≤ p.loan.broker.debtTotal.toRat)
    (hsi : p.scheduledInterest.isNormalized) (hcount : p.loan.broker.loanCount ≠ 0)
    (hcover : ∀ st toBroker, 0 ≤ p.amounts.feePaid.signum →
      p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok false →
      sumRoundAndSubtract p.loan.broker.coverAvailable p.amounts.feePaid p.pool.baseExponent
        p.loan.broker.numericType .downward = .ok st → st.toNumber .to_nearest = .ok toBroker →
      0 ≤ p.loan.broker.coverAvailable.toRat + toBroker.toRat)
    (hpool : ∀ toPool yieldDelta raw, (p.pool.adjustBalances (p.change toPool yieldDelta)).run = .ok (.ok raw) →
      STAmount.Representable p.pool.numericType raw.assetsDeployed.toRat ∧
      raw.assetsReserved.toRat ≤ raw.assetsDeployed.toRat ∧
      (p.pool.sharesTotal = Number.zero → raw.assetsAvailable.toRat = 0 ∧ raw.assetsDeployed.toRat = 0))
    (hnt : p.loan.broker.numericType = p.pool.numericType)
    (hmax : p.pool.numericType.isIntegral = true → p.pool.numericType.maxValue.toNat ≤ maxRep.toNat) :
    (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run ≠ .error .notLawful := by
  intro h
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact RawLoanBroker.hasMinimumCover_ne_notLawful _ _ ‹_›
    | exact RawLoan.interestDue_ne_notLawful _ ‹_›
    | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
    | exact Number.operator_add_ne_notLawful _ _ _ ‹_›
    | exact sumRoundAndSubtract_ne_notLawful _ _ _ _ _ ‹_›
    | exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    | exact validatePostPayment_ne_notLawful _ _ ‹_›
    | skip
  -- the vault update
  all_goals try
    exact Loan.settle_pool_ne_notLawful p hpaid.1 hsi hpool hnt hmax
      ‹AssetPool.adjustBalances p.pool _ = Except.error Error.notLawful› ‹_› ‹_› ‹_› ‹_›
  -- the broker
  all_goals try
    (have hb := ‹RawLoanBroker.to_lawful _ = Except.error Error.notLawful›
     first
       | (obtain ⟨b', hb'⟩ := LoanBroker.settle_lawful _ _ _ _ hpaid.1 hpaid.2.1 hpaid.2.2 hcount
            ‹p.loan.broker.debtTotal.operator_sub _ _ = _› p.loan.broker.wf.coverAvailable_norm
            p.loan.broker.exact.coverAvailable_nonneg
          rw [hb'] at hb; cases hb)
       | (have hmc := ‹p.loan.broker.hasMinimumCover _ = Except.ok _›
          have hcf := ‹(!_) = true›
          simp only [Bool.not_eq_true'] at hcf
          subst hcf
          have hparts := ‹¬(decide (p.amounts.principalPaid.signum < 0) || decide (p.amounts.interestPaid.signum < 0) ||
            decide (p.amounts.feePaid.signum < 0)) = true›
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hparts
          have hcov := hcover _ _ hparts.2 hmc ‹sumRoundAndSubtract _ _ _ _ _ = _› ‹STAmount.toNumber _ _ = _›
          have hadd := ‹p.loan.broker.coverAvailable.operator_add _ _ = _›
          obtain ⟨b', hb'⟩ := LoanBroker.settle_lawful _ _ _ _ hpaid.1 hpaid.2.1 hpaid.2.2 hcount
            ‹p.loan.broker.debtTotal.operator_sub _ _ = _›
            (operator_add_isNormalized_to_nearest_sz _ _ _ p.loan.broker.wf.coverAvailable_norm
              (STAmount.toNumber_isNormalized _ _ _ ‹STAmount.toNumber _ _ = _›) hadd)
            (operator_add_nonneg _ _ _ p.loan.broker.wf.coverAvailable_norm
              (STAmount.toNumber_isNormalized _ _ _ ‹STAmount.toNumber _ _ = _›) hadd hcov)
          rw [hb'] at hb; cases hb))
  -- the loan on the new broker
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.error Error.notLawful›
    have hbr := ‹RawLoanBroker.to_lawful _ = Except.ok _›
    have hnt := (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok hbr).1 :)
    obtain ⟨l', hl'⟩ := Loan.withBroker_lawful p.loan _ hnt
    rw [hl'] at hl
    cases hl

/-- A payment never fails a re-check when its instalments and its settlement don't. -/
lemma Loan.pay_ne_notLawful_of (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (hpay : (loan.payInstalments v pt amount now).run ≠ .error .notLawful)
    (hsettle : ∀ p, (loan.payInstalments v pt amount now).run = .ok (.ok p) →
      (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run ≠ .error .notLawful) :
    (loan.pay v pt amount now).run ≠ .error .notLawful := by
  rw [Loan.pay_run]
  intro h
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Except.bind] at h hpay hsettle
  rcases hp : loan.payInstalments v pt amount now with e | t | p
  · rw [hp] at h hpay; exact hpay (by simpa using h)
  · rw [hp] at h; simp [pure, Except.pure] at h
  · rw [hp] at h; exact hsettle p (by rw [hp]) (by simpa using h)

/-- A clamp into `[0, cap]` of a grid amount is a grid amount between zero and the cap. -/
private lemma clamp_facts {s : Int} {r cap : Number} (gr : Number.OnGrid s r) (gc : Number.OnGrid s cap)
    (hc0 : 0 ≤ cap.toRat) :
    Number.OnGrid s (Number.clamp r Number.zero cap) ∧ 0 ≤ (Number.clamp r Number.zero cap).toRat ∧
      (Number.clamp r Number.zero cap).toRat ≤ cap.toRat := by
  refine ⟨Number.OnGrid.clamp gr (Number.OnGrid.zero s) gc, ?_⟩
  rcases Number.clamp_zero_cases r cap gr.1 gc.1 with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨h1, h2, he⟩
  · rw [he, Number.toRat_zero]; exact ⟨le_refl _, hc0⟩
  · rw [he]; exact ⟨hc0, le_refl _⟩
  · rw [he]; exact ⟨h1, h2⟩

/-- A re-amortization that passes writes a lawful loan when its interest is at least zero. Its amounts sit on
the LoanScale grid within the old ones, and its guards keep the total value and the periodic payment above zero. -/
private lemma Loan.reamortized_lawful (l : Loan) (opc : PaymentComponents)
    {rate v18 pinnedP G pm po interest tvo tvo' mfo io : Number} {st th th2 st15 s11 s5 : LoanState}
    {de : LoanStateDeltas} {props : LoanProperties} {g : TER}
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hr0 : l.paymentRemaining ≠ 0)
    (hpd : opc.principalDelta.isNormalized) (hrate : l.periodicRate = .ok rate) (hst : l.state = .ok st)
    (hth : LoanState.buildTheoretical l.periodicPayment rate l.paymentRemaining l.broker.managementFeeRate = .ok th)
    (_hde : st.calculateDeltas th = .ok de)
    (h18 : th.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok v18)
    (hprops : computeLoanPropertiesFromPeriodicRate (v18.max Number.zero) rate l.paymentRemaining
      l.broker.managementFeeRate l.broker.numericType l.loanScale = .ok props)
    (_hth2 : LoanState.buildTheoretical props.periodicPayment rate l.paymentRemaining
      l.broker.managementFeeRate = .ok th2)
    (_h15 : th2.addDeltas de = .ok st15)
    (_hpin : st.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok pinnedP)
    (_hG : st15.valueOutstanding.operator_sub pinnedP .to_nearest = .ok G)
    (_hpm : tenthBipsOfValue G l.broker.managementFeeRate.toTenthBips32 .to_nearest = .ok pm)
    (_h11 : LoanState.build st15.valueOutstanding pinnedP pm = .ok s11)
    (hpo : roundAndClamp s11.principalOutstanding st.principalOutstanding .upward l.broker.numericType
      l.loanScale = .ok po)
    (_hint : s11.grossInterestOutstanding = .ok interest)
    (_htvo : po.operator_add interest .to_nearest = .ok tvo)
    (htvo' : roundAndClamp tvo st.valueOutstanding .upward l.broker.numericType l.loanScale = .ok tvo')
    (hmfo : roundAndClamp s11.managementFeeDue st.managementFeeDue .to_nearest l.broker.numericType
      l.loanScale = .ok mfo)
    (h5 : LoanState.build tvo' po mfo = .ok s5) (_hio : s5.grossInterestOutstanding = .ok io)
    (_hguard : LoanProperties.amortizationGuards
      { props with totalValueOutstanding := tvo', principalOutstanding := po
                   managementFeeOutstanding := mfo, loanScale := l.loanScale }
      po (io.operator_ne Number.zero) l.paymentRemaining l.broker.numericType = .ok g)
    (_hg : ¬(!g.isTesSuccess) = true)
    (hsig : ¬(decide (props.periodicPayment.signum ≤ 0) || decide (tvo'.signum ≤ 0) ||
      decide (mfo.signum < 0)) = true)
    (hi : 0 ≤ s5.valueOutstanding.toRat - s5.principalOutstanding.toRat - s5.managementFeeDue.toRat) :
    ∃ l', ({ l.toRawLoan with
      totalValueOutstanding := s5.valueOutstanding
      principalOutstanding := s5.principalOutstanding
      managementFeeOutstanding := s5.managementFeeDue
      periodicPayment := props.periodicPayment } : RawLoan).to_lawful = .ok l' := by
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  obtain ⟨gT, gP, gM, -, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hgrid := l.grid
  -- the committed amounts, rounded at LoanScale and clamped to the loan's own
  obtain ⟨hsT, hsP, hsM, -⟩ := LoanState.build_ok hst
  obtain ⟨h5T, h5P, h5M, -⟩ := LoanState.build_ok h5
  obtain ⟨rpo, hrpo, hpoe⟩ := roundAndClamp_ok hpo
  obtain ⟨rtv, hrtv, htve⟩ := roundAndClamp_ok htvo'
  obtain ⟨rmf, hrmf, hmfe⟩ := roundAndClamp_ok hmfo
  rw [hsP] at hpoe
  rw [hsT] at htve
  rw [hsM] at hmfe
  obtain ⟨gpo, hpo0, hpoP⟩ := clamp_facts (STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hrpo) gP hP0
  obtain ⟨gtv, htv0, htvT⟩ := clamp_facts (STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hrtv) gT hT0
  obtain ⟨gmf, hmf0, hmfM⟩ := clamp_facts (STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hrmf) gM hM0
  rw [← hpoe] at gpo hpo0 hpoP
  rw [← htve] at gtv htv0 htvT
  rw [← hmfe] at gmf hmf0 hmfM
  -- the guards keep the total value and the periodic payment above zero
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hsig
  obtain ⟨⟨hpp, htvpos⟩, -⟩ := hsig
  have hrateN := loanPeriodicRate_isNormalized _ _ _ hrate
  have hthN := LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm hrateN hth
  have hmax : (v18.max Number.zero).isNormalized := by
    unfold Number.max; split
    · exact Number.zero_isNormalized
    · exact operator_sub_isNormalized_to_nearest_sz _ _ _ hthN.2.1 hpd h18
  have hppN := computeLoanPropertiesFromPeriodicRate_periodicPayment_normalized hmax hrateN hprops
  have hpp0 : 0 < props.periodicPayment.toRat := (Number.signum_pos_iff_toRat hppN).mp hpp
  have htvp : 0 < tvo'.toRat := (Number.signum_pos_iff_toRat gtv.1).mp htvpos
  rw [h5T, h5P, h5M] at hi ⊢
  set rl : RawLoan := { l.toRawLoan with
      totalValueOutstanding := tvo', principalOutstanding := po, managementFeeOutstanding := mfo
      periodicPayment := props.periodicPayment } with hrl
  have hwf : rl.WF :=
    { l.wf with
      periodicPayment_norm := hppN
      totalValueOutstanding_norm := gtv.1
      principalOutstanding_norm := gpo.1
      managementFeeOutstanding_norm := gmf.1
      totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gtv.1 htv0).mpr
        (atExponent_of_le hgrid.totalValueOutstanding_atExponent gtv.2.choose gtv.2.choose_spec htv0 htvT)
      principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gpo.1 hpo0).mpr
        (atExponent_of_le hgrid.principalOutstanding_atExponent gpo.2.choose gpo.2.choose_spec hpo0 hpoP)
      managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ gmf.1 hmf0).mpr
        (atExponent_of_le hgrid.managementFeeOutstanding_atExponent gmf.2.choose gmf.2.choose_spec hmf0 hmfM) }
  have he := l.exact
  have hvalid : rl.toExact.Valid :=
    { he with
      paid_zeroed := fun h => absurd h hr0
      unpaid_nonzero := fun _ => Or.inl (ne_of_gt htvp)
      principalOutstanding_nonneg := hpo0
      totalValueOutstanding_nonneg := htv0
      managementFeeOutstanding_nonneg := hmf0
      periodicPayment_pos := hpp0
      paid_no_due_date := fun h => absurd h hr0
      interest_nonneg := by
        show 0 ≤ tvo'.toRat - po.toRat - mfo.toRat
        linarith }
  obtain ⟨l', hl', -⟩ := RawLoan.to_lawful_ok_of hwf ((RawLoan.valid_iff_exact rl hwf).mpr hvalid)
  exact ⟨l', hl'⟩

/-- A re-amortization that passes writes a lawful loan when its interest is at least zero. -/
private lemma Loan.tryOverpayment_lawful (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hpd : opc.principalDelta.isNormalized) (hr0 : l.paymentRemaining ≠ 0)
    (h : Loan.tryOverpayment l opc = .ok (some re))
    (hi : 0 ≤ re.state.valueOutstanding.toRat - re.state.principalOutstanding.toRat -
      re.state.managementFeeDue.toRat) :
    ∃ l', ({ l.toRawLoan with
      totalValueOutstanding := re.state.valueOutstanding
      principalOutstanding := re.state.principalOutstanding
      managementFeeOutstanding := re.state.managementFeeDue
      periodicPayment := re.periodicPayment } : RawLoan).to_lawful = .ok l' := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact Loan.reamortized_lawful l opc hlo hint hr0 hpd ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› hi

/-- A re-amortization that passes keeps interestDue at least zero on an IOU loan, and on an XRP or MPT loan that
counts whole units and owes at most `10^16 + 1` of them. -/
private lemma Loan.tryOverpayment_interestDue_nonneg_any (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hl : l.PayShape)
    (hint : l.broker.numericType.isIntegral = true → l.broker.numericType.maxValue.toNat ≤ maxRep.toNat ∧
      l.loanScale = 0 ∧ l.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ l.loanScale)
    (hpd : opc.principalDelta.isNormalized) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    0 ≤ re.state.valueOutstanding.toRat - re.state.principalOutstanding.toRat - re.state.managementFeeDue.toRat := by
  cases hnt : l.broker.numericType.isIntegral
  · exact Loan.tryOverpayment_interestDue_nonneg _ _ _ hl.1
      (NumericType.eq_fractional_of_not_integral (by simpa using hnt)) hl.3 hpd h
  · obtain ⟨hmax, hls0, hT⟩ := hint hnt
    exact Loan.tryOverpayment_interestDue_nonneg_int _ _ _ hnt hmax hls0 hT hl.3 hpd h

/-- The overpayment tail never fails the loan re-check on a loan of that shape. An XRP or MPT loan counts
whole units, its asset fits an STAmount, and it owes at most `10^16 + 1` units. -/
lemma UnsettledPayment.applyOverpayment_ne_notLawful (payment : UnsettledPayment Vault) (amount : Number)
    (hl : payment.loan.PayShape)
    (hint : payment.loan.broker.numericType.isIntegral = true →
      payment.loan.broker.numericType.maxValue.toNat ≤ maxRep.toNat ∧ payment.loan.loanScale = 0 ∧
        payment.loan.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ payment.loan.loanScale) :
    UnsettledPayment.applyOverpayment payment amount ≠ .error .notLawful := by
  intro h
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact STAmount.roundToNumericType_ne_notLawful _ _ _ _ ‹_›
    | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
    | exact Loan.overpaymentComponents_ne_notLawful _ _ ‹_›
    | exact Loan.tryOverpayment_ne_notLawful _ _ ‹_›
    | exact PaymentAmounts.add_ne_notLawful _ _ ‹_›
    | skip
  rename_i hlaw
  have hopc := ‹Loan.overpaymentComponents _ _ = _›
  have hovn := STAmount.roundToNumericType_isNormalized _ _ _ _ _
    ‹STAmount.roundToNumericType _ _ rounding_mode.downward _ = _›
  have hpd := Loan.overpaymentComponents_principalDelta_normalized _ _ _ hovn hopc
  have htry := ‹Loan.tryOverpayment _ _ = Except.ok (some _)›
  have hi := Loan.tryOverpayment_interestDue_nonneg_any _ _ _ hl hint hpd htry
  have hr0 : payment.loan.paymentRemaining ≠ 0 := by
    intro h0
    apply ‹¬(!(_ && _ && _ && _)) = true›
    simp [h0]
  obtain ⟨l', hl'⟩ := Loan.tryOverpayment_lawful _ _ _ hl.1 hl.2 hpd hr0 htry hi
  rw [hl'] at hlaw
  cases hlaw

end XRPL.Model.Lending
