import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Support.ReachableHistory

/-! # Witness for `Vault.Reachable.canEmpty` on a lawful vault (CanEmpty.lean)

* A lawful int64 vault holding `9223372036854775806` with `3` shares: redeeming all three
  shares prices one unit above `assetsAvailable`, so the funds guard rejects the full
  exit with `tecINSUFFICIENT_FUNDS`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.UnprovableWit

open XRPL.Model.Protocol

/-- An int64 vault holding `9223372036854775806`, all of it available, with `3` shares. -/
def ce : RawVault :=
  { assetsAvailable := ⟨false, 9223372036854775806, 0⟩
  , assetsDeployed := Number.zero, assetsReserved := Number.zero, assetsMaximum := none
  , numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 3000000000000000000, -18⟩
  , lossUnrealized := Number.zero, yieldUnrealized := Number.zero
  , schedule := none, earlyExitFeeRate := none
  , ownerCanBlockDeposit := false, depositBlocked := false }

def ceL : Vault := ⟨ce, by native_decide, by native_decide⟩

/-- The share total as an amount, computed by the model. -/
def ceShares : STAmount :=
  (STAmount.ofNumber .int64 ceL.sharesTotal .to_nearest).toOption.getD (STAmount.zero .int64)

lemma ceShares_pos : 0 < (WithdrawAmount.vaultShares ceShares).amount.toRat := by native_decide

/-- The `TER` a run rejects with, if any. -/
def rejectedTer : Except Error (Except TER VaultWithAmounts) → Option TER
  | .ok (.error ter) => some ter
  | _ => none

lemma eq_of_rejectedTer (x : Except Error (Except TER VaultWithAmounts)) (ter : TER)
    (h : rejectedTer x = some ter) : x = .ok (.error ter) := by
  rcases x with e | (t | r) <;> simp_all [rejectedTer]

end XRPL.Model.SingleAssetVault.UnprovableWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol UnprovableWit

lemma Vault.Reachable.canEmpty_witness :
    ∃ (v : Vault) (t : UInt32) (shares : STAmount) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat),
      v.assetsDeployed = Number.zero ∧ (v.earlyExitFeeRate.isSome = true ∨ v.phase t ≠ .investment) ∧
      shares.Canonical ∧ shares.mNumericType = .int64 ∧ shares.toRat = v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares shares) false t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS) :=
  ⟨ceL, 0, ceShares, ceShares_pos, rfl, Or.inr (by native_decide),
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    eq_of_rejectedTer _ _ (by native_decide)⟩

end XRPL.Model.SingleAssetVault
