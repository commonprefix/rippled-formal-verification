import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Ledger.Common.ReachableProofs

/-! # Witnesses for a VaultDeposit that ends in an exception

Runs from a new closed-ended vault, checked by `native_decide`. A vault of `9·10^15` units is lent in two loans of
`4.5·10^15` at a LateInterestRate of 100%. The first is paid 20 years late, so AssetsTotal is `9.9·10^16` units.

* XRP: a donation of `4.5·10^15` drops takes AssetsTotal plus the amount above `10^17` drops, the largest XRP
  amount, and the Open limit check ends in the out-of-range error.
* MPT: a donation of `9128872036854775807` units takes it above `2^63 - 1`, the largest MPT amount, and the Open
  limit check ends in an overflow error.

For an IOU no reachable ledger is known where AssetsTotal plus the amount passes the largest IOU amount. The last
lemma shows the error on a lawful IOU vault that holds `10^80`, which no run here reaches. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended vault schedule, subscription until 1000, redemption about 30 years later. -/
private def dwSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `dwSchedule` and an XRP or MPT asset. -/
private def dwRawVault (nt : NumericType) : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := nt, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some dwSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def dwXrpVault : Vault := ⟨dwRawVault .native, by native_decide, by native_decide⟩

private def dwMptVault : Vault := ⟨dwRawVault .int64, by native_decide, by native_decide⟩

/-- The ledgers right after VaultCreate. -/
private def dwXrpGenesis : LendingLedger :=
  { vault := dwXrpVault, shares := [], brokers := [], loans := [], now := 0 }

private def dwMptGenesis : LendingLedger :=
  { vault := dwMptVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma dwXrpGenesis_genesis : dwXrpGenesis.Genesis where
  created := ⟨none, none, dwSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨dwXrpVault.wf, dwXrpVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private lemma dwMptGenesis_genesis : dwMptGenesis.Genesis where
  created := ⟨none, none, dwSchedule, none, false, .int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨dwMptVault.wf, dwMptVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- A whole amount of `n` units of the asset. -/
private def dwUnits (nt : NumericType) (n : UInt64) : STAmount := STAmount.unchecked nt n 0 false

private def dwFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero,
    closePaymentFee := Number.zero }

/-- No interest, a LateInterestRate of 100%. -/
private def dwRates : LoanRates :=
  { interestRate := 0, lateInterestRate := 100000, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A loan of `4.5·10^15` units with one payment after 120 seconds. -/
private def dwLateLoan : LendingTx :=
  .loanSet 0 ⟨false, 4500000000000000000, -3⟩ dwRates dwFees (some 120) (some 1) (some 60) 0 false false

/-- A deposit of `9·10^15` units, a broker with no fee and no cover requirement, two loans, and the first loan
paid 20 years after its due date. -/
private def dwSetup (nt : NumericType) : List LendingTx :=
  [.vaultDeposit 0 (dwUnits nt 9000000000000000) false, .close 1001, .loanBrokerCreate ⟨none, none, none, none⟩,
    dwLateLoan, dwLateLoan, .close (1001 + 120 + 630720000), .loanPay 0 .late ⟨false, 1000000000000000000, -1⟩]

/-- The donation passes preflight on the vault's asset, AssetsTotal plus the amount is above the largest amount of
the asset and the run ends in the error `bad` accepts. -/
private def dwCheck (genesis : LendingLedger) (nt : NumericType) (amount : STAmount) (bad : Error → Bool) : Bool :=
  match genesis.run (dwSetup nt) with
  | .ok l =>
    decide (l.vault.numericType = nt) &&
      decide ((LendingTx.vaultDeposit 0 amount true).preflight l = .tesSUCCESS) &&
      decide (l.vault.numericType.maxAmount <
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + amount.toRat) &&
      (match (l.apply (.vaultDeposit 0 amount true)).run with
        | .error e => bad e
        | .ok _ => false)
  | .error _ => false

/-- A successful check gives a reachable ledger with the three facts and the failing run. -/
private lemma dwCheck_spec {genesis : LendingLedger} {nt : NumericType} {amount : STAmount} {bad : Error → Bool}
    (hg : genesis.Genesis) (h : dwCheck genesis nt amount bad = true) :
    ∃ (l : LendingLedger) (e : Error), l.Reachable ∧ l.vault.numericType = nt ∧
      (LendingTx.vaultDeposit 0 amount true).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < l.vault.toExact.assetsTotal + amount.toRat ∧
      (l.apply (.vaultDeposit 0 amount true)).run = .error e ∧ bad e = true := by
  unfold dwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnt, hpre⟩, hsum⟩, herr⟩ := h
  split at herr
  case h_2 => cases herr
  rename_i e he
  exact ⟨l, e, LendingLedger.Reachable.of_run hg hl, hnt, hpre, hsum, he, herr⟩

/-- A donation of `4.5·10^15` drops. -/
private def dwXrpDonation : STAmount := dwUnits .native 4500000000000000

/-- A donation of `9128872036854775807` MPT units. -/
private def dwMptDonation : STAmount := dwUnits .int64 9128872036854775807

private def dwIsOutOfRange : Error → Bool
  | .outOfRange => true
  | _ => false

private def dwIsOverflow : Error → Bool
  | .overflow => true
  | _ => false

private lemma dwXrpCheck_true : dwCheck dwXrpGenesis .native dwXrpDonation dwIsOutOfRange = true := by
  native_decide

private lemma dwMptCheck_true : dwCheck dwMptGenesis .int64 dwMptDonation dwIsOverflow = true := by
  native_decide

/-- VaultDeposit on a reachable XRP ledger with AssetsTotal plus the amount above the largest XRP amount -> an
error, not a result code. -/
lemma LendingLedger.vaultDeposit_exception_xrp_witness :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool),
      l.Reachable ∧ l.vault.numericType = NumericType.native ∧
      (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < l.vault.toExact.assetsTotal + amount.toRat ∧
      (l.apply (.vaultDeposit h amount isDonation)).run = .error .outOfRange := by
  obtain ⟨l, e, hr, hnt, hpre, hsum, he, hbad⟩ := dwCheck_spec dwXrpGenesis_genesis dwXrpCheck_true
  have hk : e = .outOfRange := by cases e <;> first | rfl | cases hbad
  exact ⟨l, 0, dwXrpDonation, true, hr, hnt, hpre, hsum, hk ▸ he⟩

/-- VaultDeposit on a reachable MPT ledger with AssetsTotal plus the amount above the largest MPT amount -> an
error, not a result code. -/
lemma LendingLedger.vaultDeposit_exception_mpt_witness :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool),
      l.Reachable ∧ l.vault.numericType = NumericType.int64 ∧
      (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < l.vault.toExact.assetsTotal + amount.toRat ∧
      (l.apply (.vaultDeposit h amount isDonation)).run = .error .overflow := by
  obtain ⟨l, e, hr, hnt, hpre, hsum, he, hbad⟩ := dwCheck_spec dwMptGenesis_genesis dwMptCheck_true
  have hk : e = .overflow := by cases e <;> first | rfl | cases hbad
  exact ⟨l, 0, dwMptDonation, true, hr, hnt, hpre, hsum, hk ▸ he⟩

/-- A lawful IOU vault that holds `10^80` in cash and `10^6` shares. No run from a new vault is known to reach it. -/
private def dwIouRawVault : RawVault :=
  { assetsAvailable := ⟨false, 1000000000000000000, 62⟩, assetsDeployed := Number.zero,
    assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0,
    sharesTotal := ⟨false, 1000000000000000000, -12⟩, lossUnrealized := Number.zero,
    yieldUnrealized := Number.zero, schedule := none, earlyExitFeeRate := none, ownerCanBlockDeposit := false,
    depositBlocked := false }

private def dwIouVault : Vault := ⟨dwIouRawVault, by native_decide, by native_decide⟩

/-- The largest IOU amount, `(10^16 - 1)·10^80`. -/
private def dwIouAmount : STAmount := STAmount.unchecked .fractional 9999999999999999 80 false

/-- The amount is a canonical IOU amount above zero, AssetsTotal plus the amount is above the largest IOU amount
and the deposit ends in an overflow error. -/
private def dwIouCheck : Bool :=
  if hpos : 0 < dwIouAmount.toRat then
    isCanonicalAmount dwIouAmount dwIouVault.numericType &&
      decide (dwIouVault.numericType.maxAmount <
        dwIouVault.assetsAvailable.toRat + dwIouVault.assetsDeployed.toRat + dwIouAmount.toRat) &&
      (match (dwIouVault.deposit dwIouAmount false 0 hpos).run with
        | .error e => dwIsOverflow e
        | .ok _ => false)
  else false

private lemma dwIouCheck_true : dwIouCheck = true := by native_decide

/-- Deposit of the largest IOU amount on a lawful IOU vault that holds `10^80` -> an overflow error, not a result
code. The vault is not known to be reachable. -/
lemma Vault.deposit_exception_iou_lawful_witness :
    ∃ (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      v.numericType = .fractional ∧ isCanonicalAmount amount v.numericType = true ∧
      v.numericType.maxAmount < v.toExact.assetsTotal + amount.toRat ∧
      (v.deposit amount isDonation t hpos).run = .error .overflow := by
  have h := dwIouCheck_true
  unfold dwIouCheck at h
  split at h
  case isFalse => cases h
  rename_i hpos
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hcan, hsum⟩, herr⟩ := h
  split at herr
  case h_2 => cases herr
  rename_i e he
  have hk : e = .overflow := by cases e <;> first | rfl | cases herr
  exact ⟨dwIouVault, dwIouAmount, false, 0, hpos, rfl, hcan, hsum, hk ▸ he⟩

end XRPL.Model.Lending
