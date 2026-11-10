import XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness

/-! # A loan that can be defaulted only in the redemption phase

The closed-ended vault of `NegativeInterestWitness.lean`, RedemptionDate 77761000, checked by `native_decide`. A
loan of 1000 has one payment due 60 seconds before RedemptionDate and a GracePeriod as long as its PaymentInterval.
One second into the redemption phase the payment is missed, but the default is still rejected with tecTOO_SOON. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (VaultSchedule)

open private niGenesis niGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness

/-- No interest and no other rate. -/
private def rdRates : LoanRates :=
  { interestRate := 0, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of 10^12, a broker, at time 1001 a loan of 1000 with one payment due at 77760940 and a GracePeriod of
77759939 seconds, then a close one second after RedemptionDate. -/
private def rdTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -15⟩ rdRates cwFees (some 77759939) (some 1) (some 77759939) 0 false
     false,
   .close 77761001]

/-- After `rdTxs`: the vault is in the redemption phase past RedemptionDate, loan 0 has a payment left and
NextPaymentDueDate + GracePeriod is not yet passed, and its default is rejected with tecTOO_SOON. -/
private def rdCheck : Bool :=
  match niGenesis.run rdTxs with
  | .ok l =>
    match l.loan? 0, l.vault.schedule with
    | some e, some s =>
      decide (l.vault.phase l.now = .redemption) && decide (e.loan.paymentRemaining ≠ 0) &&
        decide (s.redemptionDate.toNat < l.now.toNat) &&
        decide (l.now.toNat ≤ e.loan.nextPaymentDueDate.toNat + e.loan.schedule.gracePeriod.toNat) &&
        match (l.apply (.loanManage 0 .default)).run with
        | .ok (.error .tecTOO_SOON) => true
        | _ => false
    | _, _ => false
  | .error _ => false

private lemma rdCheck_true : rdCheck = true := by native_decide

/-- A reachable ledger in the redemption phase, past RedemptionDate, with a loan whose payment is missed but whose
default is rejected with tecTOO_SOON. -/
lemma LendingLedger.redemption_default_witness :
    ∃ (l : LendingLedger) (j : Nat) (e : LoanEntry) (s : VaultSchedule), l.Reachable ∧
      l.vault.phase l.now = .redemption ∧ l.loan? j = some e ∧ e.loan.paymentRemaining ≠ 0 ∧
      l.vault.schedule = some s ∧ s.redemptionDate.toNat < l.now.toNat ∧
      l.now.toNat ≤ e.loan.nextPaymentDueDate.toNat + e.loan.schedule.gracePeriod.toNat ∧
      (l.apply (.loanManage j .default)).run = .ok (.error .tecTOO_SOON) := by
  have h := rdCheck_true
  unfold rdCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e s he hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hred, hrem⟩, hpast⟩, hdue⟩, hdef⟩ := h
  split at hdef
  case h_2 => cases hdef
  rename_i hrej
  exact ⟨l, 0, e, s, LendingLedger.Reachable.of_run niGenesis_genesis hl, hred, he, hrem, hs, hpast, hdue, hrej⟩

end XRPL.Model.Lending
