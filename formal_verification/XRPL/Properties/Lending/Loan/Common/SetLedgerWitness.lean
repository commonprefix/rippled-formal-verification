import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # Witnesses for LoanSet on a reachable ledger

Runs from a new IOU vault at Scale 6, checked by `native_decide`. A deposit, a broker and a LoanSet with the
numbers of the `Loan.create` witnesses. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 6, subscription until 1000, redemption about 30 years later. -/
private def slSchedule : VaultSchedule := ⟨1000, 1000 + 946700000⟩

/-- The new vault VaultCreate makes for `slSchedule`. -/
private def slRawVault : RawVault := { cwRawVault with scale := 6, schedule := some slSchedule }

private def slVault : Vault := ⟨slRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def slGenesis : LendingLedger := { vault := slVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma slGenesis_genesis : slGenesis.Genesis where
  created := ⟨some 6, none, slSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨slVault.wf, slVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- A deposit of `deposit`, then at close time `1001` a broker with the given management fee and no cover. -/
private def slSetup (deposit : STAmount) (managementFeeRate : Option TenthBips16) : List LendingTx :=
  [.vaultDeposit 0 deposit false, .close 1001, .loanBrokerCreate ⟨none, managementFeeRate, none, none⟩]

/-- A LoanSet of `principal` on broker `0` without fees, `n` payments `interval` seconds apart. -/
private def slLoanSet (principal : Number) (rates : LoanRates) (interval n : UInt32) : LendingTx :=
  .loanSet 0 principal rates lwFees (some interval) (some n) (some 60) 0 false false

/-- The loan at `i` read with its broker's ledger copy, as every loan transaction reads it. -/
private def LendingLedger.slLoanAt? (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan => some loan
      | .error _ => none
    | none => none
  | none => none

private lemma LendingLedger.slLoanAt?_spec {l : LendingLedger} {i : Nat} {loan : Loan}
    (h : l.slLoanAt? i = some loan) : l.LoanAt i loan := by
  unfold LendingLedger.slLoanAt? at h
  split at h
  · rename_i e he
    split at h
    · rename_i b hb
      split at h
      · rename_i loan' hw
        obtain rfl := Option.some.inj h
        exact ⟨e, b, he, hb, hw⟩
      · cases h
    · cases h
  · cases h

/-- The ledger after `setup`, the ledger after `tx` on it and the new loan, or `none` when a step fails. -/
private def slCreate (setup : List LendingTx) (tx : LendingTx) : Option (LendingLedger × LendingLedger × Loan) :=
  match slGenesis.run setup with
  | .ok l =>
    match (l.apply tx).run with
    | .ok (.ok l') =>
      match l'.slLoanAt? l.loans.length with
      | some loan' => some (l, l', loan')
      | none => none
    | _ => none
  | .error _ => none

private lemma slCreate_spec {setup : List LendingTx} {tx : LendingTx} {l l' : LendingLedger} {loan' : Loan}
    (h : slCreate setup tx = some (l, l', loan')) :
    slGenesis.run setup = .ok l ∧ (l.apply tx).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' := by
  unfold slCreate at h
  split at h
  · rename_i l₀ hl₀
    split at h
    · rename_i l₁ hl₁
      split at h
      · rename_i loan₁ hloan
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hl₀, hl₁, LendingLedger.slLoanAt?_spec hloan⟩
      · cases h
    · cases h
  · cases h

/-- A deposit of `3·10^9` and a broker without a management fee. -/
private def slPlain : List LendingTx := slSetup (cwAmount 3000000000000000 (-6)) none

/-- `10^6`, ten payments 60 seconds apart at InterestRate 13 and at 14. The second payment is lower. -/
private def slRateCheck : Bool :=
  match slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -12⟩ (lwRates 13) 60 10),
      slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -12⟩ (lwRates 14) 60 10) with
  | some (_, _, loan₁), some (_, _, loan₂) =>
    decide (loan₂.toExact.periodicPayment < loan₁.toExact.periodicPayment)
  | _, _ => false

private lemma slRateCheck_true : slRateCheck = true := by native_decide

/-- On a reachable ledger a higher InterestRate can lower PeriodicPayment. -/
lemma LendingLedger.create_periodicPayment_rate_monotone_witness :
    ∃ (l l₁ l₂ : LendingLedger) (j : Nat) (principal : Number) (rates₁ rates₂ : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan₁ loan₂ : Loan),
      l.Reachable ∧ rates₂ = { rates₁ with interestRate := rates₂.interestRate } ∧
      rates₁.interestRate < rates₂.interestRate ∧
      (l.apply (.loanSet j principal rates₁ fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₁) ∧
      (l.apply (.loanSet j principal rates₂ fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₂) ∧
      l₁.LoanAt l.loans.length loan₁ ∧ l₂.LoanAt l.loans.length loan₂ ∧
      loan₂.toExact.periodicPayment < loan₁.toExact.periodicPayment := by
  have h := slRateCheck_true
  unfold slRateCheck at h
  split at h
  case h_2 => cases h
  rename_i l l₁ loan₁ l₀ l₂ loan₂ h₁ h₂
  obtain ⟨hs₁, ha₁, hat₁⟩ := slCreate_spec h₁
  obtain ⟨hs₂, ha₂, hat₂⟩ := slCreate_spec h₂
  obtain rfl : l = l₀ := Except.ok.inj (hs₁.symm.trans hs₂)
  exact ⟨l, l₁, l₂, _, _, lwRates 13, lwRates 14, _, _, _, _, _, _, _, loan₁, loan₂,
    LendingLedger.Reachable.of_run slGenesis_genesis hs₁, rfl, by decide, ha₁, ha₂, hat₁, hat₂,
    of_decide_eq_true h⟩

/-- `10^8` at InterestRate 100% in 15396294 and in 15396296 payments 60 seconds apart. The second payment is higher
by one unit in its 19th digit. -/
private def slCountCheck : Bool :=
  match slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -10⟩ (lwRates 100000) 60 15396294),
      slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -10⟩ (lwRates 100000) 60 15396296) with
  | some (_, _, loan₁), some (_, _, loan₂) =>
    decide (loan₁.toExact.periodicPayment < loan₂.toExact.periodicPayment)
  | _, _ => false

private lemma slCountCheck_true : slCountCheck = true := by native_decide

/-- On a reachable ledger two more payments can raise PeriodicPayment. -/
lemma LendingLedger.create_periodicPayment_count_antitone_witness :
    ∃ (l l₁ l₂ : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal₁ paymentTotal₂ gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan₁ loan₂ : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₁ gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₁) ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₂ gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₂) ∧
      l₁.LoanAt l.loans.length loan₁ ∧ l₂.LoanAt l.loans.length loan₂ ∧
      paymentTotal₁.getD defaultPaymentTotal < paymentTotal₂.getD defaultPaymentTotal ∧
      loan₁.toExact.periodicPayment < loan₂.toExact.periodicPayment := by
  have h := slCountCheck_true
  unfold slCountCheck at h
  split at h
  case h_2 => cases h
  rename_i l l₁ loan₁ l₀ l₂ loan₂ h₁ h₂
  obtain ⟨hs₁, ha₁, hat₁⟩ := slCreate_spec h₁
  obtain ⟨hs₂, ha₂, hat₂⟩ := slCreate_spec h₂
  obtain rfl : l = l₀ := Except.ok.inj (hs₁.symm.trans hs₂)
  exact ⟨l, l₁, l₂, _, _, _, _, _, some 15396294, some 15396296, _, _, _, _, loan₁, loan₂,
    LendingLedger.Reachable.of_run slGenesis_genesis hs₁, ha₁, ha₂, hat₁, hat₂, by decide, of_decide_eq_true h⟩

/-- `615000000.00667` at 100% in one payment after fifteen years, with a 9.999% fee, on a deposit of
`620000000`. The fee share `922407750.0100039995` rounds up to `922407750.010004`. -/
private def slFeeTieCheck : Bool :=
  match slCreate (slSetup (cwAmount 6200000000000000 (-7)) (some 9999))
      (slLoanSet ⟨false, 6150000000066700000, -10⟩ (lwRates 100000) 473040000 1) with
  | some (_, _, loan') =>
    decide (0 < loan'.toExact.managementFeeOutstanding - (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding))
  | none => false

private lemma slFeeTieCheck_true : slFeeTieCheck = true := by native_decide

/-- On a reachable ledger ManagementFeeOutstanding can be above ManagementFeeRate × the interest. -/
lemma LendingLedger.create_managementFee_upper_bound_witness :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧
      0 < loan'.toExact.managementFeeOutstanding - (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
        (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) := by
  have h := slFeeTieCheck_true
  unfold slFeeTieCheck at h
  split at h
  case h_2 => cases h
  rename_i l l' loan' hc
  obtain ⟨hs, ha, hat'⟩ := slCreate_spec hc
  exact ⟨l, l', _, _, _, _, _, _, _, _, _, _, loan', LendingLedger.Reachable.of_run slGenesis_genesis hs, ha, hat',
    of_decide_eq_true h⟩

/-- `0.10001` at 10% in one payment after a year, with a 9.999% fee. The interest is 10001 units and its fee
share 999.99999 units. -/
private def slFeeGapCheck : Bool :=
  match slCreate (slSetup (cwAmount 3000000000000000 (-6)) (some 9999))
      (slLoanSet ⟨false, 1000100000000000000, -19⟩ (lwRates 10000) 31536000 1) with
  | some (_, _, loan') =>
    decide ((loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) -
      loan'.toExact.managementFeeOutstanding = 99999 / 100000 * 10 ^ loan'.toExact.loanScale)
  | none => false

private lemma slFeeGapCheck_true : slFeeGapCheck = true := by native_decide

/-- On a reachable ledger ManagementFeeRate × the interest − ManagementFeeOutstanding can be `0.99999` ULP. -/
lemma LendingLedger.create_managementFee_lower_bound_witness :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧
      (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
        (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) -
        loan'.toExact.managementFeeOutstanding = 99999 / 100000 * 10 ^ loan'.toExact.loanScale := by
  have h := slFeeGapCheck_true
  unfold slFeeGapCheck at h
  split at h
  case h_2 => cases h
  rename_i l l' loan' hc
  obtain ⟨hs, ha, hat'⟩ := slCreate_spec hc
  exact ⟨l, l', _, _, _, _, _, _, _, _, _, _, loan', LendingLedger.Reachable.of_run slGenesis_genesis hs, ha, hat',
    of_decide_eq_true h⟩

/-- One base unit at InterestRate 1 in one payment after 60 seconds. The payment is just above the unit, so the
total value rounds up by almost a full unit. -/
private def slValueGapCheck : Bool :=
  match slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -24⟩ (lwRates 1) 60 1) with
  | some (_, _, loan') =>
    decide ((1 - 1 / 10 ^ 10 : ℚ) * 10 ^ loan'.toExact.loanScale <
      loan'.toExact.totalValueOutstanding - loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat)
  | none => false

private lemma slValueGapCheck_true : slValueGapCheck = true := by native_decide

/-- On a reachable ledger TotalValueOutstanding − PeriodicPayment × PaymentTotal can be above `1 − 10^-10` ULP. -/
lemma LendingLedger.create_value_upper_bound_witness :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧ rates.interestRate ≠ 0 ∧
      (1 - 1 / 10 ^ 10 : ℚ) * 10 ^ loan'.toExact.loanScale <
        loan'.toExact.totalValueOutstanding - loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat := by
  have h := slValueGapCheck_true
  unfold slValueGapCheck at h
  split at h
  case h_2 => cases h
  rename_i l l' loan' hc
  obtain ⟨hs, ha, hat'⟩ := slCreate_spec hc
  exact ⟨l, l', _, _, lwRates 1, _, _, _, _, _, _, _, loan', LendingLedger.Reachable.of_run slGenesis_genesis hs, ha,
    hat', by decide, of_decide_eq_true h⟩

/-- `10` at 10% in one payment after a year. The payment `11` is already on the LoanScale grid. -/
private def slValueEqualCheck : Bool :=
  match slCreate slPlain (slLoanSet ⟨false, 1000000000000000000, -17⟩ (lwRates 10000) 31536000 1) with
  | some (_, _, loan') =>
    decide (loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat -
      loan'.toExact.totalValueOutstanding = 0)
  | none => false

private lemma slValueEqualCheck_true : slValueEqualCheck = true := by native_decide

/-- On a reachable ledger PeriodicPayment × PaymentTotal can equal TotalValueOutstanding. -/
lemma LendingLedger.create_value_lower_bound_witness :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧ rates.interestRate ≠ 0 ∧
      loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat - loan'.toExact.totalValueOutstanding = 0 := by
  have h := slValueEqualCheck_true
  unfold slValueEqualCheck at h
  split at h
  case h_2 => cases h
  rename_i l l' loan' hc
  obtain ⟨hs, ha, hat'⟩ := slCreate_spec hc
  exact ⟨l, l', _, _, lwRates 10000, _, _, _, _, _, _, _, loan', LendingLedger.Reachable.of_run slGenesis_genesis hs,
    ha, hat', by decide, of_decide_eq_true h⟩

end XRPL.Model.Lending
