import XRPL.Properties.Lending.Ledger.Common.ReachableProofs

/-! # Witnesses for a LoanSet that ends in an exception

LoanSets whose total value is above the largest XRP or MPT amount end in an error (FV_M4_51, FV_M4_61). -/

set_option linter.style.native false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended vault schedule, subscription until 1000, redemption about 30 years later. -/
private def nsSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `nsSchedule` and an XRP or MPT asset. -/
private def nsRawVault (nt : NumericType) : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := nt, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some nsSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def nsXrpVault : Vault := ⟨nsRawVault .native, by native_decide, by native_decide⟩

private def nsMptVault : Vault := ⟨nsRawVault .int64, by native_decide, by native_decide⟩

/-- The XRP ledger right after VaultCreate. -/
private def nsXrpGenesis : LendingLedger :=
  { vault := nsXrpVault, shares := [], brokers := [], loans := [], now := 0 }

/-- The MPT ledger right after VaultCreate. -/
private def nsMptGenesis : LendingLedger :=
  { vault := nsMptVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma nsXrpGenesis_genesis : nsXrpGenesis.Genesis where
  created := ⟨none, none, nsSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dite_eq_left ⟨nsXrpVault.wf, nsXrpVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private lemma nsMptGenesis_genesis : nsMptGenesis.Genesis where
  created := ⟨none, none, nsSchedule, none, false, .int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dite_eq_left ⟨nsMptVault.wf, nsMptVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private def nsFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero,
    closePaymentFee := Number.zero }

/-- Rates with the given InterestRate and LateInterestRate, in tenth bips. -/
private def nsRates (interestRate lateInterestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := lateInterestRate, closeInterestRate := 0,
    overpaymentInterestRate := 0, overpaymentFee := 0 }

/-- A deposit of `deposit` units of the asset `nt`, then at close time `1001` a broker with no fee and no cover
requirement. -/
private def nsSetup (nt : NumericType) (deposit : UInt64) : List LendingTx :=
  [.vaultDeposit 0 (STAmount.unchecked nt deposit 0 false) false, .close 1001,
    .loanBrokerCreate ⟨none, none, none, none⟩]

/-- A one-step LoanSet on broker `0` with a grace period of 60 seconds. -/
private def nsLoanSet (principal : Number) (interestRate lateInterestRate : TenthBips32)
    (paymentInterval paymentTotal : UInt32) : LendingTx :=
  .loanSet 0 principal (nsRates interestRate lateInterestRate) nsFees (some paymentInterval) (some paymentTotal)
    (some 60) 0 false false

/-- True when LoanCount of broker `0` does not wrap. -/
private def nsCountOk (l : LendingLedger) : Bool :=
  match l.broker? 0 with
  | some b => b.loanCount + 1 != 0
  | none => true

private lemma nsCountOk_spec {l : LendingLedger} (h : nsCountOk l = true) :
    ∀ b, l.broker? 0 = some b → b.loanCount + 1 ≠ 0 := by
  intro b hb
  unfold nsCountOk at h
  rw [hb] at h
  simpa using h

/-- The periodic payment the model computes for the terms, when it computes one. -/
private def nsPayment (principal : Number) (interestRate : TenthBips32) (paymentInterval paymentTotal : UInt32) :
    Option (Number × Number) :=
  match loanPeriodicRate interestRate paymentInterval with
  | .ok rate =>
    match loanPeriodicPayment principal rate paymentTotal with
    | .ok periodicPayment => some (rate, periodicPayment)
    | .error _ => none
  | .error _ => none

private lemma nsPayment_spec {principal : Number} {interestRate : TenthBips32} {paymentInterval paymentTotal : UInt32}
    {rate periodicPayment : Number}
    (h : nsPayment principal interestRate paymentInterval paymentTotal = some (rate, periodicPayment)) :
    loanPeriodicRate interestRate paymentInterval = .ok rate ∧
      loanPeriodicPayment principal rate paymentTotal = .ok periodicPayment := by
  unfold nsPayment at h
  split at h
  · rename_i r hr
    split at h
    · rename_i pp hpp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hr, hpp⟩
    · cases h
  · cases h

/-- True when a run ended in the given model error. -/
private def nsEndsIn (e : Error) (r : Except Error (Except TER LendingLedger)) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

private lemma nsEndsIn_spec {e : Error} {r : Except Error (Except TER LendingLedger)} (h : nsEndsIn e r = true) :
    r = .error e := by
  unfold nsEndsIn at h
  split at h
  · rw [beq_iff_eq.mp h]
  · cases h

private def nsXrpPrincipal : Number := ⟨false, 3300000000000000000, -3⟩

/-- LoanCount does not wrap, the vault total is within `10^17` drops, PeriodicPayment × PaymentTotal is above
`10^17` drops and the LoanSet ends in the out-of-range error. -/
private def nsXrpValueCheck : Bool :=
  match nsXrpGenesis.run (nsSetup .native 3300000000000000) with
  | .ok l =>
    match nsPayment nsXrpPrincipal 100000 943000000 1 with
    | some (_, periodicPayment) =>
      nsCountOk l && decide (l.vault.numericType = NumericType.native) &&
        decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat) &&
        decide ((l.vault.numericType.maxValue.toNat : ℚ) < periodicPayment.toRat * (1 : UInt32).toNat) &&
        nsEndsIn .outOfRange (l.apply (nsLoanSet nsXrpPrincipal 100000 0 943000000 1)).run
    | none => false
  | .error _ => false

private lemma nsXrpValueCheck_true : nsXrpValueCheck = true := by native_decide

/-- LoanSet on a reachable XRP ledger whose PeriodicPayment × PaymentTotal is above the largest XRP amount, with
the vault total within it -> an error, not a result code (FV_M4_51). -/
lemma LendingLedger.loanSet_value_exception_witness :
    ∃ (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (rate periodicPayment : Number),
      l.Reachable ∧ (∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) ∧
      l.vault.numericType = NumericType.native ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat ∧
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate ∧
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment ∧
      (l.vault.numericType.maxValue.toNat : ℚ) <
        periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ∧
      (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .error .outOfRange := by
  have h := nsXrpValueCheck_true
  unfold nsXrpValueCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i rate periodicPayment hpay
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hcount, hnt⟩, htotal⟩, hvalue⟩, herr⟩ := h
  obtain ⟨hrate, hpp⟩ := nsPayment_spec hpay
  exact ⟨l, 0, nsXrpPrincipal, nsRates 100000 0, nsFees, some 943000000, some 1, some 60, 0, false, false, rate,
    periodicPayment, LendingLedger.Reachable.of_run nsXrpGenesis_genesis hl, nsCountOk_spec hcount, hnt, htotal,
    hrate, hpp, hvalue, nsEndsIn_spec herr⟩

/-- A loan of `9·10^15` units in 20 payments one minute apart, no interest, LateInterestRate 100%. -/
private def nsMptLateLoan : LendingTx := nsLoanSet ⟨false, 9000000000000000000, -3⟩ 0 100000 60 20

/-- The loan is made, then each of its 20 payments is made 15 years late. -/
private def nsMptSetup : List LendingTx :=
  nsSetup .int64 9000000000000000 ++ [nsMptLateLoan, .close (1001 + 60 + 473040000)] ++
    List.replicate 20 (.loanPay 0 .late ⟨false, 9000000000000000000, 0⟩)

private def nsMptPrincipal : Number := ⟨false, 1400000000000000000, 0⟩

/-- LoanCount does not wrap, the vault total is within `2^63 - 1` units, PeriodicPayment × PaymentTotal is above
`2^63 - 1` units and the LoanSet ends in the overflow error. -/
private def nsMptValueCheck : Bool :=
  match nsMptGenesis.run nsMptSetup with
  | .ok l =>
    match nsPayment nsMptPrincipal 100000 470000000 1 with
    | some (_, periodicPayment) =>
      nsCountOk l && decide (l.vault.numericType = NumericType.int64) &&
        decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat) &&
        decide ((l.vault.numericType.maxValue.toNat : ℚ) < periodicPayment.toRat * (1 : UInt32).toNat) &&
        nsEndsIn .overflow (l.apply (nsLoanSet nsMptPrincipal 100000 0 470000000 1)).run
    | none => false
  | .error _ => false

private lemma nsMptValueCheck_true : nsMptValueCheck = true := by native_decide

/-- LoanSet on a reachable MPT ledger whose PeriodicPayment × PaymentTotal is above the largest MPT amount, with
the vault total within it -> an error, not a result code. -/
lemma LendingLedger.loanSet_value_exception_mpt_witness :
    ∃ (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (rate periodicPayment : Number),
      l.Reachable ∧ (∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) ∧
      l.vault.numericType = NumericType.int64 ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat ∧
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate ∧
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment ∧
      (l.vault.numericType.maxValue.toNat : ℚ) <
        periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ∧
      (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .error .overflow := by
  have h := nsMptValueCheck_true
  unfold nsMptValueCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i rate periodicPayment hpay
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hcount, hnt⟩, htotal⟩, hvalue⟩, herr⟩ := h
  obtain ⟨hrate, hpp⟩ := nsPayment_spec hpay
  exact ⟨l, 0, nsMptPrincipal, nsRates 100000 0, nsFees, some 470000000, some 1, some 60, 0, false, false, rate,
    periodicPayment, LendingLedger.Reachable.of_run nsMptGenesis_genesis hl, nsCountOk_spec hcount, hnt, htotal,
    hrate, hpp, hvalue, nsEndsIn_spec herr⟩

end XRPL.Model.Lending
