import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayDue
import XRPL.Properties.Lending.Ledger.Common.LoanTxResults

/-! # Witnesses for a late LoanPay above the XRP range

Runs from a new closed-ended XRP vault, checked by `native_decide`. The largest XRP amount is `10^17` drops.

A vault of `5·10^15` drops lends all of it in one loan with one payment and a LateInterestRate of 100%. The loan is
paid 25 years after its due date, so the late interest is `1.25·10^17` drops. LoanPay rounds the late interest to an
XRP amount before it compares the amount due with the payment, and the model ends in an error where C++ throws
(FV_M4_53). Every other condition of `LendingLedger.loanPay_no_exception_proof` holds on this ledger.

A second run shows the credit condition is needed (FV_M4_59). A vault of `9·10^15` drops lends it in loans A of
`10^14`, B of `4.4·10^15` and C of `4.5·10^15` drops, each paid 646,488,000 seconds late. The payment of A passes.
The payment of B leaves an AssetsAvailable of `9.675·10^16` drops, an XRP amount, and a total with AssetsDeployed
of `1.0125·10^17` drops, which is not one. The vault update stores the total as an amount and ends in an error. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended XRP vault, subscription until 1000, redemption about 30 years later. -/
private def npSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `npSchedule`. -/
private def npRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := .native, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some npSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def npVault : Vault := ⟨npRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def npGenesis : LendingLedger := { vault := npVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma npGenesis_genesis : npGenesis.Genesis where
  created := ⟨none, none, npSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨npVault.wf, npVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private def npFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero,
    closePaymentFee := Number.zero }

/-- No interest, a LateInterestRate of 100%. -/
private def npRates : LoanRates :=
  { interestRate := 0, lateInterestRate := 100000, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- `5·10^15` drops as a `Number`. -/
private def npPrincipal : Number := ⟨false, 5000000000000000000, -3⟩

/-- A deposit of `5·10^15` drops, a broker with no fee and no cover requirement, a loan of all of it with one
payment after 120 seconds, then a ledger close 25 years after the due date. -/
private def npSetup : List LendingTx :=
  [.vaultDeposit 0 (STAmount.unchecked .native 5000000000000000 0 false) false, .close 1001,
    .loanBrokerCreate ⟨none, none, none, none⟩,
    .loanSet 0 npPrincipal npRates npFees (some 120) (some 1) (some 60) 0 false false,
    .close (1001 + 120 + 788400000)]

/-- True when a run ended in the model's out-of-range error. -/
private def npOutOfRange {α : Type} (r : Except Error α) : Bool :=
  match r with
  | .error .outOfRange => true
  | _ => false

private lemma npOutOfRange_spec {α : Type} {r : Except Error α} (h : npOutOfRange r = true) :
    r = .error .outOfRange := by
  unfold npOutOfRange at h
  split at h
  · rfl
  · cases h

/-- The loan is stored and late with one payment left and no cover, the payment passes preflight, the late interest
is above `10^17` drops, and both the instalment and the late LoanPay end in the out-of-range error. -/
private def npLateCheck : Bool :=
  match npGenesis.run npSetup with
  | .ok l =>
    match l.loan? 0 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          decide (l.vault.numericType = NumericType.native) &&
            decide ((LendingTx.loanPay 0 .late npPrincipal).preflight l = .tesSUCCESS) &&
            decide (loan.nextPaymentDueDate < l.now) && decide (loan.paymentRemaining = 1) &&
            decide (loan.broker.coverAvailable.toRat < 10 ^ 96) &&
            decide ((10 : ℚ) ^ 17 < loan.lateInterestExact l.now) &&
            npOutOfRange (loan.payInstalments l.vault .late npPrincipal l.now).run &&
            npOutOfRange (l.apply (.loanPay 0 .late npPrincipal)).run
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma npLateCheck_true : npLateCheck = true := by native_decide

/-- Late LoanPay on a reachable XRP ledger whose late interest is above the largest XRP amount -> an error, not
`tecINSUFFICIENT_PAYMENT`. The loan has one payment left, and the credit and the fee conditions hold. -/
lemma LendingLedger.loanPay_late_out_of_range_witness :
    ∃ (l : LendingLedger) (i : Nat) (amount : Number) (loan : Loan),
      l.Reachable ∧ l.LoanAt i loan ∧ l.vault.numericType = NumericType.native ∧
      (LendingTx.loanPay i .late amount).preflight l = .tesSUCCESS ∧ loan.nextPaymentDueDate < l.now ∧
      loan.paymentRemaining = 1 ∧ loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ l.CreditFits i .late amount ∧
      l.FeeFits i .late amount ∧ (10 : ℚ) ^ 17 < loan.lateInterestExact l.now ∧
      (l.apply (.loanPay i .late amount)).run = .error .outOfRange := by
  have h := npLateCheck_true
  unfold npLateCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hnt, hpre⟩, hlate⟩, hone⟩, hcover⟩, hint⟩, hinst⟩, herr⟩ := h
  have hat : l.LoanAt 0 loan := ⟨e, b, he, hb, hw⟩
  -- the instalment fails, so the conditions on a paid instalment hold with nothing to check
  have hnone : ∀ (loan' : Loan) (p : UnsettledPayment Vault), l.LoanAt 0 loan' →
      (loan'.payInstalments l.vault .late npPrincipal l.now).run = .ok (.ok p) → False := by
    intro loan' p hat' hp
    obtain rfl := LendingLedger.LoanAt.eq hat' hat
    rw [npOutOfRange_spec hinst] at hp
    cases hp
  exact ⟨l, 0, npPrincipal, loan, LendingLedger.Reachable.of_run npGenesis_genesis hl, hat, hnt, hpre, hlate, hone,
    hcover, fun loan' p hat' hp => (hnone loan' p hat' hp).elim, fun loan' p hat' hp => (hnone loan' p hat' hp).elim,
    hint, npOutOfRange_spec herr⟩

/-- `10^17` drops as a `Number`, the largest XRP amount and above every amount due here. -/
private def npLatePayment : Number := ⟨false, 1000000000000000000, -1⟩

/-- A loan of `principal` with one payment after 120 seconds. -/
private def npLoan (principal : Number) : LendingTx :=
  .loanSet 0 principal npRates npFees (some 120) (some 1) (some 60) 0 false false

/-- A deposit of `9·10^15` drops lent in loans A of `10^14`, B of `4.4·10^15` and C of `4.5·10^15` drops. Loan A
is paid 646,488,000 seconds after the due date. -/
private def npTotalSetup : List LendingTx :=
  [.vaultDeposit 0 (STAmount.unchecked .native 9000000000000000 0 false) false, .close 1001,
    .loanBrokerCreate ⟨none, none, none, none⟩, npLoan ⟨false, 1000000000000000000, -4⟩,
    npLoan ⟨false, 4400000000000000000, -3⟩, npLoan ⟨false, 4500000000000000000, -3⟩,
    .close (1001 + 120 + 646488000), .loanPay 0 .late npLatePayment]

/-- Loan B is late with one payment left, its late interest and fee fit and the new AssetsAvailable is an XRP
amount. The new total is above `10^17` drops and the LoanPay ends in the out-of-range error. -/
private def npTotalCheck : Bool :=
  match npGenesis.run npTotalSetup with
  | .ok l =>
    match l.loan? 1 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match (loan.payInstalments l.vault .late npLatePayment l.now).run with
          | .ok (.ok q) =>
            decide (l.vault.numericType = NumericType.native) &&
              decide ((LendingTx.loanPay 1 .late npLatePayment).preflight l = .tesSUCCESS) &&
              decide (loan.nextPaymentDueDate < l.now) && decide (loan.paymentRemaining = 1) &&
              decide (loan.broker.coverAvailable.toRat < 10 ^ 96) &&
              decide (loan.lateInterestExact l.now + 2 ≤ 10 ^ 17) &&
              decide (q.amounts.feePaid.toRat + 1 ≤ 10 ^ 17) &&
              decide (l.vault.assetsAvailable.toRat + q.amounts.principalPaid.toRat +
                q.amounts.interestPaid.toRat + 1 ≤ 10 ^ 17) &&
              decide ((10 : ℚ) ^ 17 < l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat +
                q.amounts.interestPaid.toRat) &&
              npOutOfRange (l.apply (.loanPay 1 .late npLatePayment)).run
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma npTotalCheck_true : npTotalCheck = true := by native_decide

/-- Late LoanPay on a reachable XRP ledger that takes AssetsAvailable + AssetsDeployed above the largest XRP amount
-> an error (FV_M4_59). The late interest, the fee and the new AssetsAvailable fit, so only the total fails. -/
lemma LendingLedger.loanPay_total_out_of_range_witness :
    ∃ (l : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (q : UnsettledPayment Vault),
      l.Reachable ∧ l.LoanAt i loan ∧ l.vault.numericType = NumericType.native ∧
      (LendingTx.loanPay i .late amount).preflight l = .tesSUCCESS ∧ loan.nextPaymentDueDate < l.now ∧
      loan.paymentRemaining = 1 ∧ loan.broker.coverAvailable.toRat < 10 ^ 96 ∧
      loan.lateInterestExact l.now + 2 ≤ 10 ^ 17 ∧ l.FeeFits i .late amount ∧
      (loan.payInstalments l.vault .late amount l.now).run = .ok (.ok q) ∧
      l.vault.assetsAvailable.toRat + q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤ 10 ^ 17 ∧
      (10 : ℚ) ^ 17 < l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + q.amounts.interestPaid.toRat ∧
      (l.apply (.loanPay i .late amount)).run = .error .outOfRange := by
  have h := npTotalCheck_true
  unfold npTotalCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hnt, hpre⟩, hlate⟩, hone⟩, hcover⟩, hint⟩, hfeeq⟩, hcash⟩, htotal⟩, herr⟩ := h
  have hat : l.LoanAt 1 loan := ⟨e, b, he, hb, hw⟩
  have hfee : l.FeeFits 1 .late npLatePayment := by
    intro loan' p hat' hp
    obtain rfl := LendingLedger.LoanAt.eq hat' hat
    rw [hq] at hp
    obtain rfl : q = p := by injection hp with hp; injection hp
    refine Or.inr ⟨Or.inl hnt, ?_⟩
    rw [hnt]
    have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
    rw [this]
    exact hfeeq
  exact ⟨l, 1, npLatePayment, loan, q, LendingLedger.Reachable.of_run npGenesis_genesis hl, hat, hnt, hpre, hlate,
    hone, hcover, hint, hfee, hq, hcash, htotal, npOutOfRange_spec herr⟩

end XRPL.Model.Lending
