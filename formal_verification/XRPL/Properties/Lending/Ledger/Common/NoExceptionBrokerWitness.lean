import XRPL.Properties.Lending.Ledger.Common.BrokerProofs

/-! # Witnesses for a LoanBrokerCoverDeposit above the asset's range

Runs from a new closed-ended vault, checked by `native_decide`. A broker is created and takes a first cover deposit.
A second deposit that takes CoverAvailable above the asset's maximum ends in an error where C++ throws while it
builds the new cover as an amount of the asset, before the Open limit check.

* XRP: CoverAvailable is 1 drop and the amount is `10^17` drops, the largest XRP amount.
* MPT: CoverAvailable is 2 units and the amount is `2^63 - 1` units, the largest MPT amount. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended vault schedule, subscription until 1000, redemption about 30 years later. -/
private def bwSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `bwSchedule` and the asset `nt`. -/
private def bwRawVault (nt : NumericType) : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := nt, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some bwSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def bwXrpVault : Vault := ⟨bwRawVault .native, by native_decide, by native_decide⟩

private def bwMptVault : Vault := ⟨bwRawVault .int64, by native_decide, by native_decide⟩

/-- The XRP ledger right after VaultCreate. -/
private def bwXrpGenesis : LendingLedger :=
  { vault := bwXrpVault, shares := [], brokers := [], loans := [], now := 0 }

/-- The MPT ledger right after VaultCreate. -/
private def bwMptGenesis : LendingLedger :=
  { vault := bwMptVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma bwXrpGenesis_genesis : bwXrpGenesis.Genesis where
  created := ⟨none, none, bwSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨bwXrpVault.wf, bwXrpVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private lemma bwMptGenesis_genesis : bwMptGenesis.Genesis where
  created := ⟨none, none, bwSchedule, none, false, .int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨bwMptVault.wf, bwMptVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An amount of `n` units of the asset `nt`. -/
private def bwUnits (nt : NumericType) (n : UInt64) : STAmount := STAmount.unchecked nt n 0 false

/-- A broker with no fee and no cover requirement, then a cover deposit of `first` units. -/
private def bwSetup (nt : NumericType) (first : UInt64) : List LendingTx :=
  [.loanBrokerCreate ⟨none, none, none, none⟩, .loanBrokerCoverDeposit 0 (bwUnits nt first)]

/-- True when a run ended in the model error `e`. -/
private def bwEndsIn (e : Error) (r : Except Error (Except TER LendingLedger)) : Bool :=
  match r with
  | .error e' => e' == e
  | _ => false

private lemma bwEndsIn_spec {e : Error} {r : Except Error (Except TER LendingLedger)} (h : bwEndsIn e r = true) :
    r = .error e := by
  unfold bwEndsIn at h
  split at h
  · rw [beq_iff_eq.mp h]
  · cases h

/-- After the setup the deposit of `amount` passes preflight, CoverAvailable plus the amount is above the asset's
maximum, and the run ends in the error `e`. -/
private def bwCheck (genesis : LendingLedger) (nt : NumericType) (first amount : UInt64) (e : Error) : Bool :=
  match genesis.run (bwSetup nt first) with
  | .ok l =>
    match l.broker? 0 with
    | some b =>
      decide (l.vault.numericType = nt) &&
        decide ((LendingTx.loanBrokerCoverDeposit 0 (bwUnits nt amount)).preflight l = .tesSUCCESS) &&
        decide (l.vault.numericType.maxAmount < b.coverAvailable.toRat + (bwUnits nt amount).toRat) &&
        bwEndsIn e (l.apply (.loanBrokerCoverDeposit 0 (bwUnits nt amount))).run
    | none => false
  | .error _ => false

private lemma bwXrpCheck_true :
    bwCheck bwXrpGenesis .native 1 100000000000000000 .outOfRange = true := by native_decide

private lemma bwMptCheck_true :
    bwCheck bwMptGenesis .int64 2 9223372036854775807 .overflow = true := by native_decide

/-- What a true `bwCheck` gives: a reachable ledger of the asset `nt` where the deposit ends in `e`. -/
private lemma bwCheck_spec {genesis : LendingLedger} (hg : genesis.Genesis) {nt : NumericType} {first amount : UInt64}
    {e : Error} (h : bwCheck genesis nt first amount e = true) :
    ∃ (l : LendingLedger) (i : Nat) (a : STAmount) (b : LoanBroker), l.Reachable ∧ l.vault.numericType = nt ∧
      l.broker? i = some b ∧ (LendingTx.loanBrokerCoverDeposit i a).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < b.coverAvailable.toRat + a.toRat ∧
      (l.apply (.loanBrokerCoverDeposit i a)).run = .error e := by
  unfold bwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i b hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnt, hpre⟩, hsum⟩, herr⟩ := h
  exact ⟨l, 0, _, b, LendingLedger.Reachable.of_run hg hl, hnt, hb, hpre, hsum, bwEndsIn_spec herr⟩

/-- LoanBrokerCoverDeposit on a reachable XRP ledger with CoverAvailable plus the amount above the largest XRP
amount -> an error, not a result code. -/
lemma LendingLedger.loanBrokerCoverDeposit_exception_witness :
    ∃ (l : LendingLedger) (i : Nat) (amount : STAmount) (b : LoanBroker), l.Reachable ∧
      l.vault.numericType = NumericType.native ∧ l.broker? i = some b ∧
      (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < b.coverAvailable.toRat + amount.toRat ∧
      (l.apply (.loanBrokerCoverDeposit i amount)).run = .error .outOfRange :=
  bwCheck_spec bwXrpGenesis_genesis bwXrpCheck_true

/-- The same on an MPT ledger: CoverAvailable of 2 units and an amount of `2^63 - 1` units end in an error. -/
lemma LendingLedger.loanBrokerCoverDeposit_exception_witness_mpt :
    ∃ (l : LendingLedger) (i : Nat) (amount : STAmount) (b : LoanBroker), l.Reachable ∧
      l.vault.numericType = NumericType.int64 ∧ l.broker? i = some b ∧
      (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < b.coverAvailable.toRat + amount.toRat ∧
      (l.apply (.loanBrokerCoverDeposit i amount)).run = .error .overflow :=
  bwCheck_spec bwMptGenesis_genesis bwMptCheck_true

end XRPL.Model.Lending
