import XRPL.Properties.Lending.Ledger.Common.PaymentShareBoundWitness

/-! # A payment that crosses a power of ten loses ten units of the new scale per share

Loan A pays 95 instalments 132 years late into a Scale 0 vault, which leaves AssetsAvailable at
`99999999999999800000`. Loan B's principal of `199996` takes the sum within 4 of `10^20` and is credited as `10^5`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 0, subscription until 1000, redemption about 28 years later. -/
private def scSchedule : VaultSchedule := ⟨1000, 1000 + 900000000⟩

/-- The new vault VaultCreate makes for `scSchedule`. -/
private def scRawVault : RawVault := { cwRawVault with scale := 0, schedule := some scSchedule }

private def scVault : Vault := ⟨scRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def scGenesis : LendingLedger := { vault := scVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma scGenesis_genesis : scGenesis.Genesis where
  created := ⟨some 0, none, scSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨scVault.wf, scVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- Loan B's principal, `199996`. -/
private def scProbe : Number := ⟨false, 1999960000000000000, -13⟩

/-- A deposit, loan A of `8·10^15` at 100% LateInterestRate in 10000 instalments a minute apart, loan B of `199996`
in one instalment, then 95 late payments of loan A at 4169027330. -/
private def scTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8999820989386497 0) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 8000000000000000000, -3⟩ (cwRates 100000) cwFees (some 60) (some 10000) (some 60) 0 false false,
   .loanSet 0 scProbe (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .close 4169027330] ++ List.replicate 95 (.loanPay 0 .late ⟨false, 2000000000000000000, 0⟩)

/-- Loan B's late payment of `199996` is credited as `10^5`: the share value falls by `9.9996` units of the scale of
AssetsAvailable' over SharesTotal. -/
private def scCheck : Bool :=
  match scGenesis.run scTxs with
  | .ok l =>
    match l.loan? 1 with
    | some en =>
      match l.broker? en.brokerIndex with
      | some b =>
        match en.loan.withBroker b with
        | .ok loan =>
          match (loan.payInstalments l.vault .late scProbe l.now).run with
          | .ok (.ok payment) =>
            match (l.apply (.loanPay 1 .late scProbe)).run with
            | .ok (.ok l') =>
              match numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType with
              | .ok e =>
                decide (2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ≤ l.vault.assetsAvailable.toRat +
                    (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ∧
                  l.vault.toRawVault.shareValue - l'.vault.toRawVault.shareValue =
                    (24999 / 2500 : ℚ) * 10 ^ e / l.vault.toExact.sharesTotal)
              | .error _ => false
            | _ => false
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma scCheck_true : scCheck = true := by native_decide

/-- **A payment on a reachable ledger can lose `9.9996` units of the new scale per share.** AssetsAvailable plus the
payment passes `2^63` base units and lands just below `10^20`, so the floor drops to a coarser grid. -/
lemma LendingLedger.payment_share_value_crossing_reachable :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ≤
        l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      l.vault.toRawVault.shareValue - l'.vault.toRawVault.shareValue =
        (24999 / 2500 : ℚ) * 10 ^ e / l.vault.toExact.sharesTotal := by
  have h := scCheck_true
  unfold scCheck at h
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
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  exact ⟨l, l', 1, .late, scProbe, loan, payment, e, LendingLedger.Reachable.of_run scGenesis_genesis hl, hl',
    ⟨en, b, hen, hb, hw⟩, hpay, h1, he, h2⟩

/-- **A payment on a reachable ledger loses 0.9 of a unit of the new scale per share** while AssetsAvailable plus
the payment stays below `2^63` base units. -/
lemma LendingLedger.payment_share_value_lower_bound_fit_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      l.vault.toRawVault.shareValue - l'.vault.toRawVault.shareValue =
        (9 / 10 : ℚ) * 10 ^ e / l.vault.toExact.sharesTotal := by
  obtain ⟨l, l', i, pt, amount, loan, payment, e, h1, h2, h3, h4, -, h6, h7, h8⟩ :=
    LendingLedger.payment_share_value_lower_bound_witness
  exact ⟨l, l', i, pt, amount, loan, payment, e, h1, h2, h3, h4, h6, h7, h8⟩

end XRPL.Model.Lending
