import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultDelete

/-! # `canVaultDelete` on lawful states -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The exits of `canVaultDelete`. -/
theorem Vault.canVaultDelete_exits (v : Vault) :
    ((v.assetsAvailable ≠ Number.zero ∨ v.assetsDeployed ≠ Number.zero ∨ v.sharesTotal ≠ Number.zero) →
      v.canVaultDelete = .ok .tecHAS_OBLIGATIONS) ∧
    (v.assetsAvailable = Number.zero → v.assetsDeployed = Number.zero → v.sharesTotal = Number.zero →
      v.canVaultDelete = .ok .tesSUCCESS) := by
  sorry

/-- A lawful vault passes the delete check exactly when it holds no assets and has no shares. -/
theorem Vault.canVaultDelete_lawful_iff (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ↔
      v.toExact.assetsTotal = 0 ∧ v.toExact.sharesTotal = 0 := by
  sorry

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection `canVaultDelete` can
return. -/
theorem Vault.canVaultDelete_error_codes (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ∨
    v.canVaultDelete = .ok .tecHAS_OBLIGATIONS := by
  sorry

end XRPL.Model.SingleAssetVault
