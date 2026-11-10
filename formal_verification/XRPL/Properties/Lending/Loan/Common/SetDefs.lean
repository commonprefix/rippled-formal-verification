import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Protocol.Common.FixedWidth
import XRPL.Properties.Lending.Loan.LoanValid

/-! # LoanSet checks read in plain terms

The schedule check in whole seconds, the vault check as a phase condition, and the precision
check over PrincipalRequested and the fees. -/

namespace XRPL.Model.Lending

attribute [simp] UInt32.addChecked_ne_notLawful UInt32.subChecked_ne_notLawful Nat.toInt64Checked_ne_notLawful

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultSchedule)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet

/-- The schedule has a positive PaymentTotal and PaymentInterval, and its last grace period ends by the largest
ledger time. -/
structure LoanSchedule.Fits (schedule : LoanSchedule) : Prop where
  paymentTotal_pos : 0 < schedule.paymentTotal
  paymentInterval_pos : 0 < schedule.paymentInterval
  ends_in_time : schedule.startDate.toNat + schedule.gracePeriod.toNat +
    schedule.paymentTotal.toNat * schedule.paymentInterval.toNat ≤ maxTime.toNat

/-- A schedule that fits has its first due date within the ledger clock. -/
lemma LoanSchedule.Fits.firstDue_lt {s : LoanSchedule} (h : s.Fits) :
    s.startDate.toNat + s.paymentInterval.toNat < 2 ^ 32 := by
  have hn := h.paymentTotal_pos
  have hl := h.ends_in_time
  rw [UInt32.lt_iff_toNat_lt] at hn
  simp only [UInt32.toNat_zero] at hn
  have : s.paymentInterval.toNat ≤ s.paymentTotal.toNat * s.paymentInterval.toNat := Nat.le_mul_of_pos_left _ hn
  have hM : maxTime.toNat = 4294967295 := rfl
  omega

/-- The vault lends for this schedule at close time `t`: it has no phase, or it is in the investment
phase and the last payment is due at least 60 seconds before RedemptionDate. -/
def LoanSchedule.FitsVault (schedule : LoanSchedule) (v : Vault) (t : UInt32) : Prop :=
  v.phase t = .noPhase ∨
    (v.phase t = .investment ∧ ∀ s ∈ v.schedule,
      schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat +
        loanRedemptionBuffer ≤ s.redemptionDate.toNat)

/-- The schedule check in whole seconds. -/
lemma LoanSchedule.checkTimeAvailability_eq (s : LoanSchedule) :
    s.checkTimeAvailability =
      if s.gracePeriod.toNat > maxTime.toNat - s.startDate.toNat ∨
          s.paymentInterval.toNat > maxTime.toNat - s.startDate.toNat ∨
          s.paymentTotal.toNat > maxTime.toNat - s.startDate.toNat ∨
          (maxTime.toNat - s.startDate.toNat - s.gracePeriod.toNat) / s.paymentInterval.toNat <
            s.paymentTotal.toNat
      then .ok .tecKILLED else .ok .tesSUCCESS := by
  have hS : s.startDate ≤ maxTime := by
    rw [UInt32.le_iff_toNat_le]; have := s.startDate.toNat_lt; simp [maxTime]; omega
  unfold LoanSchedule.checkTimeAvailability
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i he; rw [UInt32.subChecked_of_le hS] at he; cases he
  rename_i ta hta
  obtain ⟨-, hta⟩ := UInt32.subChecked_eq_ok.mp hta
  have hT : ta.toNat = maxTime.toNat - s.startDate.toNat := by rw [← hta]; exact UInt32.toNat_sub_of_le _ _ hS
  by_cases h1 : (decide (s.gracePeriod > ta) || decide (s.paymentInterval > ta) || decide (s.paymentTotal > ta)) = true
  · rw [if_pos h1]
    simp only [Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hT] at h1
    rw [if_pos (by omega)]
  · rw [if_neg h1]
    simp only [Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hT, not_or, not_lt] at h1
    have hle : s.gracePeriod ≤ ta := by rw [UInt32.le_iff_toNat_le, hT]; omega
    split
    · rename_i he; rw [UInt32.subChecked_of_le hle] at he; cases he
    rename_i tl htl
    obtain ⟨-, htl⟩ := UInt32.subChecked_eq_ok.mp htl
    have hT2 : tl.toNat = maxTime.toNat - s.startDate.toNat - s.gracePeriod.toNat := by
      rw [← htl, UInt32.toNat_sub_of_le _ _ hle, hT]
    have h2 : tl / s.paymentInterval < s.paymentTotal ↔
        (maxTime.toNat - s.startDate.toNat - s.gracePeriod.toNat) / s.paymentInterval.toNat <
          s.paymentTotal.toNat := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_div, hT2]
    by_cases h3 : (maxTime.toNat - s.startDate.toNat - s.gracePeriod.toNat) / s.paymentInterval.toNat <
        s.paymentTotal.toNat
    · rw [if_pos (h2.mpr h3), if_pos (by omega)]
    · rw [if_neg (mt h2.mp h3), if_neg (by omega)]

/-- A schedule whose last grace period ends after the largest ledger time is killed. -/
lemma LoanSchedule.checkTimeAvailability_killed (s : LoanSchedule)
    (h : maxTime.toNat <
      s.startDate.toNat + s.gracePeriod.toNat + s.paymentTotal.toNat * s.paymentInterval.toNat) :
    s.checkTimeAvailability = .ok .tecKILLED := by
  rw [LoanSchedule.checkTimeAvailability_eq, if_pos]
  by_cases hg : s.gracePeriod.toNat > maxTime.toNat - s.startDate.toNat
  · exact Or.inl hg
  refine Or.inr (Or.inr (Or.inr ?_))
  have hM : maxTime.toNat = 4294967295 := rfl
  have hs := s.startDate.toNat_lt
  by_cases hi : s.paymentInterval.toNat = 0
  · rw [hi] at h; simp at h; omega
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega

/-- A schedule that fits passes the schedule check. -/
lemma LoanSchedule.checkTimeAvailability_success (s : LoanSchedule) (hfits : s.Fits) :
    s.checkTimeAvailability = .ok .tesSUCCESS := by
  have hn := hfits.paymentTotal_pos
  have hi := hfits.paymentInterval_pos
  have h := hfits.ends_in_time
  rw [LoanSchedule.checkTimeAvailability_eq, if_neg]
  rw [UInt32.lt_iff_toNat_lt] at hn hi
  simp only [UInt32.toNat_zero] at hn hi
  have hni : s.paymentTotal.toNat ≤ s.paymentTotal.toNat * s.paymentInterval.toNat :=
    Nat.le_mul_of_pos_right _ hi
  have hin : s.paymentInterval.toNat ≤ s.paymentTotal.toNat * s.paymentInterval.toNat :=
    Nat.le_mul_of_pos_left _ hn
  simp only [not_or, not_lt, gt_iff_lt]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hM : maxTime.toNat = 4294967295 := rfl
  rw [Nat.le_div_iff_mul_le hi]
  omega

/-- With a positive PaymentTotal and PaymentInterval, the schedule check passes exactly when the schedule fits. -/
lemma LoanSchedule.checkTimeAvailability_success_iff (s : LoanSchedule)
    (hn : 0 < s.paymentTotal) (hi : 0 < s.paymentInterval) :
    s.checkTimeAvailability = .ok .tesSUCCESS ↔ s.Fits := by
  constructor
  · intro h
    refine ⟨hn, hi, ?_⟩
    by_contra hc
    rw [s.checkTimeAvailability_killed (by omega)] at h
    exact absurd h (by decide)
  · exact s.checkTimeAvailability_success

/-- The precision check over checks that cannot fail: tecPRECISION_LOSS when any amount fails. -/
lemma checkPrecisionFields_pure (principal : Number) (fees : LoanFees) (f : Number → Bool) :
    checkPrecisionFields principal fees (fun x => .ok (f x)) =
      .ok (if (principal :: fees.amountFields).all f then .tesSUCCESS else .tecPRECISION_LOSS) := by
  unfold checkPrecisionFields LoanFees.amountFields
  simp only [List.forIn_cons, List.forIn_nil, List.all_cons, List.all_nil]
  by_cases h1 : f principal <;> by_cases h2 : f fees.originationFee <;> by_cases h3 : f fees.serviceFee <;>
    by_cases h4 : f fees.latePaymentFee <;> by_cases h5 : f fees.closePaymentFee <;>
    simp [h1, h2, h3, h4, h5]

/-- The precision check over checks that all succeed: tecPRECISION_LOSS when any amount fails. -/
lemma checkPrecisionFields_ok (principal : Number) (fees : LoanFees) (f : Number → Except Error Bool)
    (g : Number → Bool) (h : ∀ x ∈ principal :: fees.amountFields, f x = .ok (g x)) :
    checkPrecisionFields principal fees f =
      .ok (if (principal :: fees.amountFields).all g then .tesSUCCESS else .tecPRECISION_LOSS) := by
  have hf : checkPrecisionFields principal fees f =
      checkPrecisionFields principal fees (fun x => .ok (g x)) := by
    unfold checkPrecisionFields LoanFees.amountFields
    unfold LoanFees.amountFields at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [List.forIn_cons, List.forIn_nil]
    rw [h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr (Or.inl rfl))),
      h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  rw [hf, checkPrecisionFields_pure]

/-- The terms pass the LoanSet checks up to the amortization guards: the vault holds the principal,
the loan properties compute, and PrincipalRequested and the fees are exact at LoanScale. -/
structure Loan.CreateTerms (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (properties : LoanProperties) : Prop where
  funds : v.assetsAvailable.operator_lt principal = false
  properties_ok : computeLoanProperties principal rates.interestRate schedule.paymentInterval
    schedule.paymentTotal broker.managementFeeRate broker.numericType v.baseExponent = .ok properties
  exact : ∀ x ∈ principal :: fees.amountFields, isRounded x properties.loanScale broker.numericType = .ok true

/-- The terms pass every LoanSet check: the amortization guards, the Open limit, DebtMaximum and
the minimum cover. `loanState` is the new loan's state and `debtTotal'` the broker's new debt. -/
structure Loan.CreateChecks (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number) : Prop extends Loan.CreateTerms broker v principal rates fees schedule properties where
  guards : properties.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType =
    .ok .tesSUCCESS
  state : LoanState.build properties.totalValueOutstanding principal properties.managementFeeOutstanding =
    .ok loanState
  open_zone : v.exceedsOpenLimit loanState.interestDue = .ok false
  debt : broker.debtTotal.operator_add principal .to_nearest = .ok debtTotal'
  limits : broker.checkLimits debtTotal' v.baseExponent = .ok .tesSUCCESS

/-- The balance change a new loan makes to the vault: the principal leaves AssetsAvailable for
AssetsDeployed, a pending loan reserves it, an active loan adds its interest to YieldUnrealized. -/
def Loan.createChange (principal principal' interestDue : Number) (pending : Bool) : PoolBalanceChange :=
  { cash := principal'.operator_neg
    deployed := principal
    yield := if pending then Number.zero else interestDue
    reserved := if pending then principal' else Number.zero }

/-- What a new loan sends the borrower: an active loan the principal less the origination fee, a pending one
nothing until LoanAccept. -/
def Loan.createAmountToBorrower (principal : Number) (fees : LoanFees) (pending : Bool) : Except Error Number :=
  if pending then .ok Number.zero else principal.operator_sub fees.originationFee .to_nearest

end XRPL.Model.Lending
