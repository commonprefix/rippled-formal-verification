import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultDelete

/-! # `canVaultDelete` on lawful states -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.lawful_canVaultDelete_iff (v : Vault)
    (hv : v.Lawful) : -- the vault is lawful
    v.canVaultDelete = .tesSUCCESS ↔
      v.assetsTotal.toRat = 0 ∧ v.sharesTotal.toRat = 0 :=
  Vault.lawful_canVaultDelete_iff_proof v hv

/-! ## `canVaultDelete` on arbitrary states -/

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection
`canVaultDelete` can return. -/
theorem Vault.canVaultDelete_error_codes (v : Vault) :
    v.canVaultDelete = .tesSUCCESS ∨
    v.canVaultDelete = .tecHAS_OBLIGATIONS :=
  Vault.canVaultDelete_error_codes_proof v

/-- The check returns `tecHAS_OBLIGATIONS` exactly when one of the three stored
quantities differs from `Number.zero`. The vault is arbitrary and the comparison
is on the stored records. -/
theorem Vault.canVaultDelete_has_obligations_iff (v : Vault) :
    v.canVaultDelete = .tecHAS_OBLIGATIONS ↔
      (v.assetsAvailable ≠ Number.zero ∨ v.assetsTotal ≠ Number.zero ∨
        v.sharesTotal ≠ Number.zero) :=
  Vault.canVaultDelete_has_obligations_iff_proof v

end XRPL.Model.SingleAssetVault
