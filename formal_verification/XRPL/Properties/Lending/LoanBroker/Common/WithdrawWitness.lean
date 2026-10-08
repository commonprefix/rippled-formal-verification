import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber

/-! # Witnesses for the `LoanBroker.coverWithdraw` theorems

Concrete withdrawal runs showing where the withdrawal theorems' hypotheses are needed,
checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault)

/-- An IOU broker holding `10` of cover, scale `10^-14`, with no debt. -/
def wbTen : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, -17⟩, loanCount := 0 }

def wbTenL : LoanBroker := ⟨wbTen, by native_decide, by native_decide⟩

/-- An IOU broker holding `9.5` of cover, scale `10^-15`: `wbTen` after withdrawing `0.5`. -/
def wbNineHalf : RawLoanBroker := { wbTen with coverAvailable := ⟨false, 9500000000000000000, -18⟩ }

def wbNineHalfL : LoanBroker := ⟨wbNineHalf, by native_decide, by native_decide⟩

/-- The deposit, `10^-15`. It rounds to zero at scale `10^-14` and not at scale `10^-15`. -/
def waDepositSmall : STAmount := STAmount.unchecked .fractional 1000000000000000 (-30) false

/-- The same deposit is rejected on a cover of `10` and taken whole on a cover of `9.5`. -/
lemma LoanBroker.roundedCoverAmount_precision_loss_witness :
    ∃ (lb lb' : LoanBroker) (amount : STAmount), lb'.numericType = lb.numericType ∧
      lb'.toExact.coverAvailable < lb.toExact.coverAvailable ∧
      lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) ∧
      lb'.roundedCoverAmount amount = .ok (.rounded amount) :=
  ⟨wbTenL, wbNineHalfL, waDepositSmall, by native_decide⟩

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

/-- The withdrawal passes its checks, pays out the requested amount, and `coverAvailable` drops by
more than it pays out. -/
def overdebits (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverWithdraw pool amount, lb.coverWithdraw amount with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    res.amount' == amount &&
      decide (amount.toRat < lb.coverAvailable.toRat - res.loanBroker'.coverAvailable.toRat)
  | _, _ => false

private lemma overdebits_witness : overdebits wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A withdrawal from a large cover can lower `coverAvailable` by more than it pays out. -/
lemma LoanBroker.coverWithdraw_debit_le_amount_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧ res.amount' = amount ∧
      amount.toRat < lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable := by
  have h := overdebits_witness
  unfold overdebits at h
  split at h
  · rename_i res h1 h2
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨_, _, _, res, h1, h2, ⟨rfl, by decide, by decide, by decide, by decide⟩, h.1, h.2⟩
  · exact absurd h (by decide)

/-- The withdrawal passes its checks, a deposit would round its amount to the cover scale, and
`coverAvailable` moves by a different on-ledger amount than it pays out. -/
def withdrawAppliedDeltaDiffers (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverWithdraw pool amount, lb.coverWithdraw amount with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    match lb.roundedCoverAmount res.amount',
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest with
    | .ok (.rounded amount''), .ok deltaCover =>
      match STAmount.ofNumber lb.numericType deltaCover .to_nearest with
      | .ok deltaAmount =>
        !amount''.operator_eq res.amount' && !deltaAmount.operator_eq res.amount'
      | _ => false
    | _, _ => false
  | _, _ => false

private lemma withdrawAppliedDeltaDiffers_witness :
    withdrawAppliedDeltaDiffers wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A withdrawal takes its amount unrounded, so `coverAvailable` can move by a different on-ledger
amount than it pays out. -/
lemma LoanBroker.coverWithdraw_applied_delta_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount amount'' : STAmount) (res : LoanBrokerCoverResult)
      (deltaCover : Number) (deltaAmount : STAmount),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧
      lb.roundedCoverAmount res.amount' = .ok (.rounded amount'') ∧
      amount''.operator_eq res.amount' = false ∧
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq res.amount' = false := by
  have h := withdrawAppliedDeltaDiffers_witness
  unfold withdrawAppliedDeltaDiffers at h
  split at h
  · rename_i res hcan hok
    split at h
    · rename_i amount'' deltaCover hround hsub
      split at h
      · rename_i deltaAmount hda
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact ⟨_, _, _, amount'', res, deltaCover, deltaAmount, hcan, hok,
          ⟨rfl, by decide, by decide, by decide, by decide⟩, hround, h.1, hsub, hda, h.2⟩
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Every withdrawal passes its checks, and withdrawing `a` twice ends at a different cover than
withdrawing `c = a + a` at once. -/
def withdrawSplitDiffers (lb : LoanBroker) (pool : Vault) (a c : STAmount) : Bool :=
  match lb.canCoverWithdraw pool a, lb.coverWithdraw a with
  | .ok .tesSUCCESS, .ok (.ok r1) =>
    match r1.loanBroker'.canCoverWithdraw pool a, r1.loanBroker'.coverWithdraw a with
    | .ok .tesSUCCESS, .ok (.ok r2) =>
      match lb.canCoverWithdraw pool c, lb.coverWithdraw c with
      | .ok .tesSUCCESS, .ok (.ok s) =>
        decide (c.toRat = a.toRat + a.toRat) &&
          decide (r2.loanBroker'.coverAvailable.toRat ≠ s.loanBroker'.coverAvailable.toRat)
      | _, _ => false
    | _, _ => false
  | _, _ => false

private lemma withdrawSplitDiffers_witness :
    withdrawSplitDiffers wbLargeCoverL wvPoolL waSplitPart waSplitWhole = true := by
  native_decide

/-- Two withdrawals can end at a different `coverAvailable` than one withdrawal of their sum. -/
lemma LoanBroker.coverWithdraw_split_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      r1.loanBroker'.coverWithdraw b = .ok (.ok r2) ∧
      lb.canCoverWithdraw pool c = .ok .tesSUCCESS ∧ lb.coverWithdraw c = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧ c.toRat = a.toRat + b.toRat ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable := by
  have h := withdrawSplitDiffers_witness
  unfold withdrawSplitDiffers at h
  split at h
  · rename_i r1 hc1 h1
    split at h
    · rename_i r2 hc2 h2
      split at h
      · rename_i s hc3 h3
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        have hpart : waSplitPart.ExactCanonical :=
          Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩
        exact ⟨_, _, _, _, _, r1, r2, s, hc1, h1, hc2, h2, hc3, h3, hpart, hpart,
          Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, h.1, h.2⟩
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Both orders of the two withdrawals pass every check, and they end at different covers. -/
def withdrawOrderDiffers (lb : LoanBroker) (pool : Vault) (a b : STAmount) : Bool :=
  match lb.canCoverWithdraw pool a, lb.coverWithdraw a with
  | .ok .tesSUCCESS, .ok (.ok r1) =>
    match r1.loanBroker'.canCoverWithdraw pool b, r1.loanBroker'.coverWithdraw b with
    | .ok .tesSUCCESS, .ok (.ok r2) =>
      match lb.canCoverWithdraw pool b, lb.coverWithdraw b with
      | .ok .tesSUCCESS, .ok (.ok s1) =>
        match s1.loanBroker'.canCoverWithdraw pool a, s1.loanBroker'.coverWithdraw a with
        | .ok .tesSUCCESS, .ok (.ok s2) =>
          decide (r2.loanBroker'.coverAvailable.toRat ≠ s2.loanBroker'.coverAvailable.toRat)
        | _, _ => false
      | _, _ => false
    | _, _ => false
  | _, _ => false

private lemma withdrawOrderDiffers_witness :
    withdrawOrderDiffers wbLargeCoverL wvPoolL waSplitPart waOrderPart = true := by
  native_decide

/-- Two withdrawals can pass every check in both orders and end at a different `coverAvailable`. -/
lemma LoanBroker.coverWithdraw_comm_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      r1.loanBroker'.coverWithdraw b = .ok (.ok r2) ∧
      lb.canCoverWithdraw pool b = .ok .tesSUCCESS ∧ lb.coverWithdraw b = .ok (.ok s1) ∧
      s1.loanBroker'.canCoverWithdraw pool a = .ok .tesSUCCESS ∧
      s1.loanBroker'.coverWithdraw a = .ok (.ok s2) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable := by
  have h := withdrawOrderDiffers_witness
  unfold withdrawOrderDiffers at h
  split at h
  · rename_i r1 hc1 h1
    split at h
    · rename_i r2 hc2 h2
      split at h
      · rename_i s1 hc3 h3
        split at h
        · rename_i s2 hc4 h4
          exact ⟨_, _, _, _, r1, r2, s1, s2, hc1, h1, hc2, h2, hc3, h3, hc4, h4,
            Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
            Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, of_decide_eq_true h⟩
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
