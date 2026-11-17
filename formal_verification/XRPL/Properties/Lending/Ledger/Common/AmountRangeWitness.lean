import XRPL.Properties.Lending.Ledger.Common.ReachableProofs

/-! # Witnesses for amounts above the XRP range

Runs from a new closed-ended XRP vault, checked by `native_decide`. The largest XRP amount is `10^17` drops, and
the model ends in an error where C++ throws while it builds a larger one.

* LoanSet: a vault of `3.3·10^15` drops, a loan of all of it at 100% with one payment after `943000000` seconds. Its
  total value is above `10^17` drops, and computing the loan ends in an error before the Open limit check.
* Donation: a vault of `9·10^15` drops lent in two loans of `4.5·10^15` at a LateInterestRate of 100%. The first is
  paid 20 years late, so AssetsTotal is `9.9·10^16` drops. A donation of `4.5·10^15` takes it above `10^17`, and the
  Open limit check ends in an error. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended XRP vault, subscription until 1000, redemption about 30 years later. -/
private def arSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `arSchedule`. -/
private def arRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := .native, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some arSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def arVault : Vault := ⟨arRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def arGenesis : LendingLedger := { vault := arVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma arGenesis_genesis : arGenesis.Genesis where
  created := ⟨none, none, arSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨arVault.wf, arVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An XRP amount of `n` drops. -/
private def arDrops (n : UInt64) : STAmount := STAmount.unchecked .native n 0 false

private def arFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero,
    closePaymentFee := Number.zero }

/-- Rates with the given InterestRate and LateInterestRate, in tenth bips. -/
private def arRates (interestRate lateInterestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := lateInterestRate, closeInterestRate := 0,
    overpaymentInterestRate := 0, overpaymentFee := 0 }

/-- A deposit of `deposit` drops, then at close time `1001` a broker with no fee and no cover requirement. -/
private def arSetup (deposit : UInt64) : List LendingTx :=
  [.vaultDeposit 0 (arDrops deposit) false, .close 1001, .loanBrokerCreate ⟨none, none, none, none⟩]

/-- True when a run ended in the model's out-of-range error. -/
private def arOutOfRange (r : Except Error (Except TER LendingLedger)) : Bool :=
  match r with
  | .error .outOfRange => true
  | _ => false

private lemma arOutOfRange_spec {r : Except Error (Except TER LendingLedger)} (h : arOutOfRange r = true) :
    r = .error .outOfRange := by
  unfold arOutOfRange at h
  split at h
  · rfl
  · cases h

/-- A LoanSet of `3.3·10^15` drops at 100% with one payment after `943000000` seconds. -/
private def arLoanSet : LendingTx :=
  .loanSet 0 ⟨false, 3300000000000000000, -3⟩ (arRates 100000 0) arFees (some 943000000) (some 1) (some 60) 0 false
    false

/-- The vault holds less than `10^16` drops and the LoanSet ends in the out-of-range error. -/
private def arLoanSetCheck : Bool :=
  match arGenesis.run (arSetup 3300000000000000) with
  | .ok l =>
    decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) && arOutOfRange (l.apply arLoanSet).run
  | .error _ => false

private lemma arLoanSetCheck_true : arLoanSetCheck = true := by native_decide

/-- LoanSet on a reachable XRP ledger whose loan has a total value above the largest XRP amount -> an error, not a
result code. -/
lemma LendingLedger.loanSet_out_of_range_witness :
    ∃ (l : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool),
      l.Reachable ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .error .outOfRange := by
  have h := arLoanSetCheck_true
  unfold arLoanSetCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hroom, herr⟩ := h
  exact ⟨l, _, _, _, _, _, _, _, _, _, _, LendingLedger.Reachable.of_run arGenesis_genesis hl, hroom,
    arOutOfRange_spec herr⟩

/-- A loan of `4.5·10^15` drops with one payment after 120 seconds and a LateInterestRate of 100%. -/
private def arLateLoan : LendingTx :=
  .loanSet 0 ⟨false, 4500000000000000000, -3⟩ (arRates 0 100000) arFees (some 120) (some 1) (some 60) 0 false false

/-- A vault of `9·10^15` drops lent in two loans. The first is paid 20 years after its due date. -/
private def arDonateSetup : List LendingTx :=
  arSetup 9000000000000000 ++
    [arLateLoan, arLateLoan, .close (1001 + 120 + 630720000), .loanPay 0 .late ⟨false, 1000000000000000000, -1⟩]

/-- A donation of `4.5·10^15` drops by holder `0`. -/
private def arDonation : STAmount := arDrops 4500000000000000

/-- The donation passes preflight, AssetsTotal + amount is above `10^17` drops and the run ends in the out-of-range
error. -/
private def arDonateCheck : Bool :=
  match arGenesis.run arDonateSetup with
  | .ok l =>
    match l.vault.assetsTotal with
    | .ok assetsTotal =>
      decide ((LendingTx.vaultDeposit 0 arDonation true).preflight l = .tesSUCCESS) &&
        decide ((10 : ℚ) ^ 17 < assetsTotal.toRat + arDonation.toRat) &&
        arOutOfRange (l.apply (.vaultDeposit 0 arDonation true)).run
    | .error _ => false
  | .error _ => false

private lemma arDonateCheck_true : arDonateCheck = true := by native_decide

/-- Donation on a reachable XRP ledger that takes AssetsTotal above the largest XRP amount -> an error, not
`tecLIMIT_EXCEEDED`. -/
lemma LendingLedger.vaultDonate_out_of_range_witness :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (assetsTotal : Number),
      l.Reachable ∧ (LendingTx.vaultDeposit h amount true).preflight l = .tesSUCCESS ∧
      l.vault.assetsTotal = .ok assetsTotal ∧ (10 : ℚ) ^ 17 < assetsTotal.toRat + amount.toRat ∧
      (l.apply (.vaultDeposit h amount true)).run = .error .outOfRange := by
  have h := arDonateCheck_true
  unfold arDonateCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i assetsTotal htotal
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpre, hsum⟩, herr⟩ := h
  exact ⟨l, 0, arDonation, assetsTotal, LendingLedger.Reachable.of_run arGenesis_genesis hl, hpre, htotal, hsum,
    arOutOfRange_spec herr⟩

end XRPL.Model.Lending
