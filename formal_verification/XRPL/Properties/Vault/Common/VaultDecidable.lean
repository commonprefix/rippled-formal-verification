import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback

/-! # Shared `DecidableEq` derivations for the vault witness leaves

The `native_decide` witness files compare concrete vault states and operation results, so they need `DecidableEq`
for `RawVault`, `VaultAmounts`, `VaultWithAmounts`, and `Except`. Deriving these in one shared module emits each
generated `decEq` helper once, so the witness files load together under the `Properties` aggregator. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

deriving instance DecidableEq for Except
deriving instance DecidableEq for RawVault

-- `Vault` carries proof fields (`wf`, `valid`), so it cannot derive `DecidableEq`. Two lawful vaults
-- are equal exactly when their raw records are.
instance : DecidableEq Vault := fun a b =>
  decidable_of_iff (a.toRawVault = b.toRawVault)
    ⟨fun h => by obtain ⟨av, _, _⟩ := a; obtain ⟨bv, _, _⟩ := b; cases h; rfl,
     fun h => by rw [h]⟩

deriving instance DecidableEq for VaultAmounts
deriving instance DecidableEq for VaultWithAmounts

end XRPL.Model.SingleAssetVault
