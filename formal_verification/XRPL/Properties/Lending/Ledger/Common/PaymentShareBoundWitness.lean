import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # A payment that loses just under one unit of the new scale per share

On the coarsened vault of `CoarsenedVault.lean`, an instalment of 1.9 without interest is credited on the coarser
grid as 1, so the share value falls by 0.9 of a unit of the scale of AssetsAvailable' over SharesTotal. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The coarsened run with a fourth loan D of 3.8 in two instalments of 1.9, created before the vault coarsens. -/
private def sbTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 ⟨false, 3800000000000000000, -18⟩ (cwRates 0) cwFees (some 35424000) (some 2) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- The late instalment of 1.9 of loan D, as an amount. -/
private def sbAmount : Number := ⟨false, 1900000000000000000, -18⟩

/-- Loan D's late instalment of 1.9 is credited as 1: the share value falls by 0.9 of a unit at the new scale. -/
private def sbCheck : Bool :=
  match cwGenesis.run sbTxs with
  | .ok l =>
    match l.loan? 3 with
    | some en =>
      match l.broker? en.brokerIndex with
      | some b =>
        match en.loan.withBroker b with
        | .ok loan =>
          match (loan.payInstalments l.vault .late sbAmount l.now).run with
          | .ok (.ok payment) =>
            match (l.apply (.loanPay 3 .late sbAmount)).run with
            | .ok (.ok l') =>
              match numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType with
              | .ok e =>
                decide (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
                    10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
                  l.vault.assetsAvailable.toRat +
                    (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
                    2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ∧
                  l.vault.toRawVault.shareValue - l'.vault.toRawVault.shareValue =
                    (9 / 10 : ℚ) * 10 ^ e / l.vault.toExact.sharesTotal)
              | .error _ => false
            | _ => false
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma sbCheck_true : sbCheck = true := by native_decide

/-- **A payment on a reachable ledger loses 0.9 of a unit of the new scale per share.** -/
lemma LendingLedger.payment_share_value_lower_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      l.vault.toRawVault.shareValue - l'.vault.toRawVault.shareValue =
        (9 / 10 : ℚ) * 10 ^ e / l.vault.toExact.sharesTotal := by
  have h := sbCheck_true
  unfold sbCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i en hen
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i payment hpay
  split at h
  case h_2 => cases h
  rename_i l' hl'
  split at h
  case h_2 => cases h
  rename_i e he
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true h
  exact ⟨l, l', 3, .late, sbAmount, loan, payment, e, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl',
    ⟨en, b, hen, hb, hw⟩, hpay, h1, h2, he, h3⟩

end XRPL.Model.Lending
