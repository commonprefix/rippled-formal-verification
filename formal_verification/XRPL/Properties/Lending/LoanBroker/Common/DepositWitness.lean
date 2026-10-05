import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Witnesses for the `LoanBroker.coverDeposit` theorems

Concrete deposit runs showing where the deposit theorems' hypotheses are needed, checked
by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault)

/-- An IOU broker holding `6.6 * 10^12` of cover. -/
def wbOvercredit : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 6600000000000000000, -6⟩, loanCount := 0 }

def wbOvercreditL : LoanBroker := ⟨wbOvercredit, by native_decide, by native_decide⟩

/-- The deposit, `9999999999999999 * 10^15`. -/
def waOvercredit : STAmount := STAmount.unchecked .fractional 9999999999999999 15 false

/-- The deposit succeeds unrounded and credits more than it deposits. -/
def overcredits (lb : LoanBroker) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      decide (amount.toRat < res.loanBroker'.coverAvailable.toRat - lb.coverAvailable.toRat)
  | _ => false

private lemma overcredits_witness : overcredits wbOvercreditL waOvercredit = true := by native_decide

/-- A deposit can raise `coverAvailable` by more than the deposited amount. -/
lemma LoanBroker.coverDeposit_credit_le_amount_witness :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.IOUCanonical ∧ lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      amount.toRat < res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable := by
  have h := overcredits_witness
  unfold overcredits at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨_, _, res, ⟨rfl, by decide, by decide, by decide, by decide⟩, hres, h.1, h.2⟩
  · exact absurd h (by decide)

/-- An IOU broker holding `9.999999999999999` of cover. -/
def wbDecade : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999999000, -18⟩, loanCount := 0 }

def wbDecadeL : LoanBroker := ⟨wbDecade, by native_decide, by native_decide⟩

/-- The deposit, `10^-15`. -/
def waDecade : STAmount := STAmount.unchecked .fractional 1000000000000000 (-30) false

/-- The deposit is credited unrounded, and withdrawing it afterwards is
rejected. -/
def depositNotWithdrawable (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      match res.loanBroker'.canCoverWithdraw pool amount with
      | .ok .tecPRECISION_LOSS => true
      | _ => false
  | _ => false

private lemma depositNotWithdrawable_witness :
    depositNotWithdrawable wbDecadeL wvPoolL waDecade = true := by native_decide

/-- An amount a deposit credits can be rejected as a withdrawal right after,
once `coverAvailable` has crossed a power of ten. -/
lemma LoanBroker.coverDeposit_withdrawable_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS := by
  have h := depositNotWithdrawable_witness
  unfold depositNotWithdrawable at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hamt, h2⟩ := h
    split at h2
    · rename_i hw
      exact ⟨_, _, _, res, hres, hamt, hw⟩
    · exact absurd h2 (by decide)
  · exact absurd h (by decide)

/-- The deposit is credited unrounded, and clawing it back afterwards is
rejected. -/
def depositNotClawable (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      match res.loanBroker'.canCoverClawback pool (some amount) with
      | .ok .tecPRECISION_LOSS => true
      | _ => false
  | _ => false

private lemma depositNotClawable_witness :
    depositNotClawable wbDecadeL wvPoolL waDecade = true := by native_decide

/-- An amount a deposit credits can be rejected as a clawback right after, once
`coverAvailable` has crossed a power of ten. -/
lemma LoanBroker.coverDeposit_clawable_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverClawback pool (some amount) = .ok .tecPRECISION_LOSS := by
  have h := depositNotClawable_witness
  unfold depositNotClawable at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hamt, h2⟩ := h
    split at h2
    · rename_i hw
      exact ⟨_, _, _, res, hres, hamt, hw⟩
    · exact absurd h2 (by decide)
  · exact absurd h (by decide)

/-- An IOU broker holding `9999999999999999` of cover. -/
def wbFullDigits : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999999000, -3⟩, loanCount := 0 }

def wbFullDigitsL : LoanBroker := ⟨wbFullDigits, by native_decide, by native_decide⟩

/-- The deposit, `9999999999999999`. -/
def waFullDigits : STAmount := STAmount.unchecked .fractional 9999999999999999 0 false

/-- The deposit succeeds and leaves a 17-digit `coverAvailable`. -/
def depositRounds (lb : LoanBroker) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) => STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable
  | _ => false

private lemma depositRounds_witness : depositRounds wbFullDigitsL waFullDigits = true := by
  native_decide

/-- A deposit can leave `coverAvailable` off the asset grid. -/
lemma LoanBroker.coverDeposit_associateAsset_witness :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded := by
  have h := depositRounds_witness
  unfold depositRounds at h
  split at h
  · rename_i res hres
    exact ⟨_, _, res, hres, Or.inr (Or.inr h)⟩
  · exact absurd h (by decide)

/-- An IOU broker holding `9.99999999999999` of cover, scale `10^-15`. -/
def wbOrder : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999990000, -18⟩, loanCount := 0 }

def wbOrderL : LoanBroker := ⟨wbOrder, by native_decide, by native_decide⟩

/-- The first deposit, `10^-14`. It lifts the cover to `10`, scale `10^-14`. -/
def waOrderA : STAmount := STAmount.unchecked .fractional 1000000000000000 (-29) false

/-- The second deposit, `1.3 * 10^-14`. At scale `10^-14` it rounds down to `10^-14`. -/
def waOrderB : STAmount := STAmount.unchecked .fractional 1300000000000000 (-29) false

/-- Both orders of the two deposits succeed, and they take different totals. -/
def depositOrderDependent (lb : LoanBroker) (a b : STAmount) : Bool :=
  match lb.coverDeposit a, lb.coverDeposit b with
  | .ok (.ok r1), .ok (.ok s1) =>
    match r1.loanBroker'.coverDeposit b, s1.loanBroker'.coverDeposit a with
    | .ok (.ok r2), .ok (.ok s2) =>
      decide (r1.amount'.toRat + r2.amount'.toRat ≠ s1.amount'.toRat + s2.amount'.toRat)
    | _, _ => false
  | _, _ => false

private lemma depositOrderDependent_witness : depositOrderDependent wbOrderL waOrderA waOrderB = true := by
  native_decide

/-- Two deposits in the two orders can take different totals from the depositor. -/
lemma LoanBroker.coverDeposit_comm_witness :
    ∃ (lb : LoanBroker) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit b = .ok (.ok s1) ∧ s1.loanBroker'.coverDeposit a = .ok (.ok s2) ∧
      r1.amount'.toRat + r2.amount'.toRat ≠ s1.amount'.toRat + s2.amount'.toRat := by
  have h := depositOrderDependent_witness
  unfold depositOrderDependent at h
  split at h
  · rename_i r1 s1 h1 h3
    split at h
    · rename_i r2 s2 h2 h4
      exact ⟨_, _, _, r1, r2, s1, s2, h1, h2, h3, h4, of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
