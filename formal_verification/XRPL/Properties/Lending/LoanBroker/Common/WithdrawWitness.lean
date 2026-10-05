import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Witnesses for the `LoanBroker.coverWithdraw` theorems

Concrete brokers, each run through the model against `wvPool` and checked by
`native_decide`.

* Two withdrawals: from `coverAvailable` `10^6`, scale `10^-9`, withdrawing
  `5.1 * 10^-10` and then `4.9 * 10^-10` passes both checks. The first withdrawal
  drops the cover below `10^6`, so the scale moves to `10^-10`, where the second
  amount is no longer zero. Withdrawing `4.9 * 10^-10` first rounds to zero at
  scale `10^-9` and is rejected.
* A deposit and a withdrawal: on `coverAvailable` `10`, scale `10^-14`, a deposit
  of `10^-15` rounds to zero and is rejected. After a withdrawal of `0.5` the
  cover is `9.5`, scale `10^-15`, and the same deposit is taken whole.
* Off the asset grid: withdrawing `7.6 * 10^-10` from `10^6` passes the checks and
  leaves `999999.99999999924`, 17 significant digits. Depositing the same amount
  back rounds it down at the new scale `10^-10` to `7 * 10^-10`.
* Inexact debit: withdrawing `1234.567890123456` from `10^18` lowers the cover by
  `1235`. The 19-digit subtraction rounds the amount to whole units, the last
  digit of the cover. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault)

/-- `a` then `b` passes both checks, and `b` alone is rejected. -/
def withdrawOrderDependent (lb : LoanBroker) (pool : Vault) (a b : STAmount) : Bool :=
  match lb.canCoverWithdraw pool a, lb.coverWithdraw a, lb.canCoverWithdraw pool b with
  | .ok .tesSUCCESS, .ok (.ok r1), .ok .tecPRECISION_LOSS =>
    match r1.loanBroker'.canCoverWithdraw pool b with
    | .ok .tesSUCCESS => true
    | _ => false
  | _, _, _ => false

private lemma withdrawOrderDependent_witness :
    withdrawOrderDependent wbMillionL wvPoolL waAboveHalfUnit waBelowHalfUnit = true := by
  native_decide

/-- Two withdrawals can pass their checks in one order while the second is
rejected when it goes first. -/
lemma LoanBroker.coverWithdraw_order_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      lb.canCoverWithdraw pool b = .ok .tecPRECISION_LOSS := by
  have h := withdrawOrderDependent_witness
  unfold withdrawOrderDependent at h
  split at h
  · rename_i r1 h1 h2 h3
    split at h
    · rename_i h4
      exact ⟨_, _, _, _, r1, h1, h2, h4, h3⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- An IOU broker holding `10` of cover, scale `10^-14`, with no debt. -/
def wbTen : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, -17⟩, loanCount := 0 }

def wbTenL : LoanBroker := ⟨wbTen, by native_decide, by native_decide⟩

/-- The deposit, `10^-15`. It rounds to zero at scale `10^-14`. -/
def waDepositSmall : STAmount := STAmount.unchecked .fractional 1000000000000000 (-30) false

/-- The withdrawal, `0.5`. It lowers the cover to `9.5`, scale `10^-15`. -/
def waWithdrawHalf : STAmount := STAmount.unchecked .fractional 5000000000000000 (-16) false

/-- The deposit is rejected first, and taken whole after the withdrawal. -/
def depositAfterWithdraw (lb : LoanBroker) (pool : Vault) (d w : STAmount) : Bool :=
  match lb.roundedCoverAmount d, lb.canCoverWithdraw pool w, lb.coverWithdraw w with
  | .ok (.rejected .tecPRECISION_LOSS), .ok .tesSUCCESS, .ok (.ok r1) =>
    match r1.loanBroker'.roundedCoverAmount d with
    | .ok (.rounded r) => r == d
    | _ => false
  | _, _, _ => false

private lemma depositAfterWithdraw_witness :
    depositAfterWithdraw wbTenL wvPoolL waDepositSmall waWithdrawHalf = true := by native_decide

/-- A deposit can be rejected before a withdrawal and taken whole after it. -/
lemma LoanBroker.coverDeposit_after_withdraw_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (d w : STAmount) (r1 : LoanBrokerCoverResult),
      lb.roundedCoverAmount d = .ok (.rejected .tecPRECISION_LOSS) ∧
      lb.canCoverWithdraw pool w = .ok .tesSUCCESS ∧ lb.coverWithdraw w = .ok (.ok r1) ∧
      r1.loanBroker'.roundedCoverAmount d = .ok (.rounded d) := by
  have h := depositAfterWithdraw_witness
  unfold depositAfterWithdraw at h
  split at h
  · rename_i r1 h1 h2 h3
    split at h
    · rename_i r h4
      rw [beq_iff_eq] at h
      subst h
      exact ⟨_, _, _, _, r1, h1, h2, h3, h4⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The withdrawal passes its checks and leaves a 17-digit `coverAvailable`. -/
def withdrawRounds (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverWithdraw pool amount, lb.coverWithdraw amount with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable
  | _, _ => false

private lemma withdrawRounds_witness : withdrawRounds wbMillionL wvPoolL waBelowUnit = true := by
  native_decide

/-- A withdrawal whose checks passed can leave `coverAvailable` off the asset
grid. -/
lemma LoanBroker.coverWithdraw_associateAsset_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded := by
  have h := withdrawRounds_witness
  unfold withdrawRounds at h
  split at h
  · rename_i res h1 h2
    exact ⟨_, _, _, res, h1, h2, Or.inr (Or.inr h)⟩
  · exact absurd h (by decide)

/-- The withdrawal passes its checks, and depositing the same amount back does not
restore the cover. -/
def redepositShort (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverWithdraw pool amount, lb.coverWithdraw amount with
  | .ok .tesSUCCESS, .ok (.ok r1) =>
    match r1.loanBroker'.coverDeposit amount with
    | .ok (.ok r2) => decide (r2.loanBroker'.coverAvailable.toRat ≠ lb.coverAvailable.toRat)
    | _ => false
  | _, _ => false

private lemma redepositShort_witness : redepositShort wbMillionL wvPoolL waBelowUnit = true := by
  native_decide

/-- Depositing back the amount a withdrawal paid out can leave `coverAvailable`
below where it started. -/
lemma LoanBroker.coverWithdraw_coverDeposit_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit amount = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable := by
  have h := redepositShort_witness
  unfold redepositShort at h
  split at h
  · rename_i r1 h1 h2
    split at h
    · rename_i r2 h3
      exact ⟨_, _, _, r1, r2, h1, h2, h3, of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The withdrawal passes its checks, and `coverAvailable` drops by a different
amount than it pays out. -/
def withdrawsInexact (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverWithdraw pool amount, lb.coverWithdraw amount with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    decide (lb.coverAvailable.toRat - res.loanBroker'.coverAvailable.toRat ≠ amount.toRat)
  | _, _ => false

private lemma withdrawsInexact_witness :
    withdrawsInexact wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A withdrawal from a large cover can lower `coverAvailable` by a different
amount than it pays out. -/
lemma LoanBroker.coverWithdraw_debit_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≠ amount.toRat := by
  have h := withdrawsInexact_witness
  unfold withdrawsInexact at h
  split at h
  · rename_i res h1 h2
    exact ⟨_, _, _, res, h1, h2, ⟨rfl, by decide, by decide, by decide, by decide⟩,
      of_decide_eq_true h⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
