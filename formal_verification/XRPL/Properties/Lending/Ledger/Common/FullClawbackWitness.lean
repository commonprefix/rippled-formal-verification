import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A full clawback that would leave cash in a vault with no shares

Late interest takes an MPT vault past `10^18` units. A clawback of every share prices them with 19-digit Numbers
and recovers one unit less than the cash. That would leave the unit in a vault with no shares, so the clawback fails
its lawfulness re-check. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule VaultAmounts computeClawback)

/-- A closed-ended MPT vault, subscription until 1000, redemption a day later. -/
private def fcSchedule : VaultSchedule := ⟨1000, 1000 + 86400⟩

/-- The new vault VaultCreate makes for `fcSchedule` on an MPT. -/
private def fcRawVault : RawVault :=
  { cwRawVault with numericType := .int64, scale := 0, schedule := some fcSchedule }

private def fcVault : Vault := ⟨fcRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def fcGenesis : LendingLedger := { vault := fcVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma fcGenesis_genesis : fcGenesis.Genesis where
  created := ⟨none, none, fcSchedule, none, false, .int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨fcVault.wf, fcVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An MPT amount of `n` units. -/
private def fcAmount (n : UInt64) : STAmount := STAmount.unchecked .int64 n 0 false

/-- A deposit of 8999999999999987 units, a broker without fees or cover, a loan of all of it at no interest and
a 100% late rate in 150 payments 60 seconds apart, then each instalment paid two years late. -/
private def fcTxs : List LendingTx :=
  [.vaultDeposit 0 (fcAmount 8999999999999987) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 8999999999999987000, -3⟩ (cwRates 100000) cwFees (some 60) (some 150) (some 60) 0 false false,
   .close (1001 + 2 * 31536000)] ++
  List.replicate 150 (.loanPay 0 .late ⟨false, 9000000000000000000, 0⟩)

/-- The clawback of every share holder 0 owns. -/
private def fcClawback : LendingTx := .vaultClawback 0 (fcAmount 0)

/-- The run succeeds, holder 0 holds a whole number of shares within SharesTotal and owns the shares the clawback
destroys, and the clawback then fails its lawfulness re-check. -/
private def fcCheck : Bool :=
  match fcGenesis.run fcTxs with
  | .ok l =>
    decide ((l.sharesOf 0).toRat.den = 1) && decide (0 ≤ (l.sharesOf 0).toRat) &&
      decide ((l.sharesOf 0).toRat ≤ l.vault.sharesTotal.toRat) &&
      (match STAmount.ofNumber .int64 (l.sharesOf 0) .to_nearest with
        | .ok hs =>
          match (computeClawback l.vault (fcAmount 0) hs (l.isSoleShareholder 0)).run with
          | .ok (.ok amounts) => decide (amounts.shares.toRat ≤ (l.sharesOf 0).toRat)
          | _ => true
        | .error _ => true) &&
      match (l.apply fcClawback).run with
      | .error .notLawful => true
      | _ => false
  | .error _ => false

private lemma fcCheck_true : fcCheck = true := by native_decide

/-- A reachable full clawback that fails its lawfulness re-check. The MPT vault holds 1367934497716893152
units and 8999999999999987 shares, and the clawback of every share recovers one unit less. -/
lemma LendingLedger.vaultClawback_lawful_witness :
    ∃ (l : LendingLedger) (h : Nat) (assets : STAmount), l.Reachable ∧
      ((l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧ (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) ∧
      (∀ (hs : STAmount) (amounts : VaultAmounts), STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
        (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
        amounts.shares.toRat ≤ (l.sharesOf h).toRat) ∧
      (l.apply (.vaultClawback h assets)).run = .error .notLawful := by
  have hc := fcCheck_true
  unfold fcCheck at hc
  split at hc
  case h_2 => cases hc
  rename_i l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hden, h0⟩, hle⟩, hheld⟩, hcl⟩ := hc
  refine ⟨l, 0, fcAmount 0, LendingLedger.Reachable.of_run fcGenesis_genesis hl, ⟨hden, h0, hle⟩, ?_, ?_⟩
  · intro hs amounts hof hcomp
    rw [hof] at hheld
    simp only at hheld
    rw [hcomp] at hheld
    simpa using hheld
  · split at hcl
    · assumption
    · cases hcl

end XRPL.Model.Lending
