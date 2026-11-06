import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A reachable ledger whose CoverAvailable the asset does not store exactly

LoanPay adds a fee to a cover below its minimum with no Open-zone check. On an IOU vault a later default then
leaves a cover of 17 digits. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 10, subscription until 1000, redemption 900 days later. -/
private def rcSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new vault VaultCreate makes for `rcSchedule`. -/
private def rcRawVault : RawVault := { cwRawVault with scale := 10, schedule := some rcSchedule }

private def rcVault : Vault := ⟨rcRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def rcGenesis : LendingLedger := { vault := rcVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma rcGenesis_genesis : rcGenesis.Genesis where
  created := ⟨some 10, none, rcSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨rcVault.wf, rcVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- No fees but the given LoanServiceFee. -/
private def rcFees (service : Number) : LoanFees := { cwFees with serviceFee := service }

/-- A broker at 10% minimum cover and 100% liquidation lends loans A and B. Defaulting A leaves a cover of 1,
so B's first instalment adds its fee of 2000000 to the cover. Then loan C of 1.0000000001. -/
private def rcTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8000000000000000 (-10)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 10000, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 1000100000000000 (-11)),
   .loanSet 0 ⟨false, 9000000000000000000, -14⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 1000000000000000000, -14⟩ (cwRates 0) (rcFees ⟨false, 2000000000000000000, -12⟩)
     (some 86400) (some 2) (some 60) 0 false false,
   .close 1300,
   .loanManage 0 .default,
   .loanPay 1 .regular ⟨false, 2005000000000000000, -12⟩,
   .loanSet 0 ⟨false, 1000000000100000000, -18⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .close 1500]

/-- Defaulting loan C takes 1.0000000001 off the cover of 2000001, which leaves 1999999.9999999999. -/
private def rcCheck : Bool :=
  match rcGenesis.run rcTxs with
  | .ok l =>
    match (l.apply (.loanManage 2 .default)).run, l.broker? 0 with
    | .ok (.ok l'), some b =>
      match l'.broker? 0 with
      | some b' => !STAmount.isRounded l.vault.numericType b.coverAvailable &&
          STAmount.isRounded l'.vault.numericType b'.coverAvailable &&
          decide (b'.coverAvailable.toRat = 19999999999999999 / 10 ^ 10)
      | none => false
    | _, _ => false
  | .error _ => false

private lemma rcCheck_true : rcCheck = true := by native_decide

/-- A default on a reachable IOU ledger can leave a CoverAvailable of 17 digits. C++ `associateAsset` rounds
it to the 16 digits of the asset. -/
lemma LendingLedger.cover_rounded_reachable :
    ∃ (l l' : LendingLedger) (b b' : LoanBroker), l.Reachable ∧
      (l.apply (.loanManage 2 .default)).run = .ok (.ok l') ∧ l.broker? 0 = some b ∧ l'.broker? 0 = some b' ∧
      STAmount.isRounded l.vault.numericType b.coverAvailable = false ∧
      STAmount.isRounded l'.vault.numericType b'.coverAvailable = true ∧
      b'.coverAvailable.toRat = 19999999999999999 / 10 ^ 10 := by
  have h := rcCheck_true
  unfold rcCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i l' b hl' hb
      split at h
      · rename_i b' hb'
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
        exact ⟨l, l', b, b', LendingLedger.Reachable.of_run rcGenesis_genesis hl, hl', hb, hb', h.1.1, h.1.2, h.2⟩
      · cases h
    · cases h
  · cases h

end XRPL.Model.Lending
