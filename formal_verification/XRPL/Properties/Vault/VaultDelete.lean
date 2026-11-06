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
      v.canVaultDelete = .ok .tesSUCCESS) :=
  ⟨(Vault.canVaultDelete_has_obligations_iff_proof v).mpr, fun hAA hAD hST =>
    (Vault.canVaultDelete_error_codes_proof v).resolve_right fun h =>
      ((Vault.canVaultDelete_has_obligations_iff_proof v).mp h).elim (· hAA) (Or.elim · (· hAD) (· hST))⟩

/-- A lawful vault passes the delete check exactly when it holds no assets and has no shares. -/
theorem Vault.canVaultDelete_lawful_iff (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ↔
      v.toExact.assetsTotal = 0 ∧ v.toExact.sharesTotal = 0 :=
  Vault.canVaultDelete_lawful_iff_proof v

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection `canVaultDelete` can
return. -/
theorem Vault.canVaultDelete_error_codes (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ∨
    v.canVaultDelete = .ok .tecHAS_OBLIGATIONS :=
  Vault.canVaultDelete_error_codes_proof v

end XRPL.Model.SingleAssetVault
