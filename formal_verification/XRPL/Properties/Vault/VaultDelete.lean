import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultDelete

/-! # `canVaultDelete` on lawful states -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem LawfulVault.lawful_canVaultDelete_iff (lv : LawfulVault) :
    lv.canVaultDelete = .tesSUCCESS ↔
      lv.toExact.assetsTotal = 0 ∧ lv.toExact.sharesTotal = 0 :=
  LawfulVault.lawful_canVaultDelete_iff_proof lv

/-! ## `canVaultDelete` on arbitrary states -/

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection
`canVaultDelete` can return. -/
theorem LawfulVault.canVaultDelete_error_codes (lv : LawfulVault) :
    lv.canVaultDelete = .tesSUCCESS ∨
    lv.canVaultDelete = .tecHAS_OBLIGATIONS :=
  LawfulVault.canVaultDelete_error_codes_proof lv

/-- The check returns `tecHAS_OBLIGATIONS` exactly when one of the three stored
quantities differs from `Number.zero`. The comparison is on the stored
records. -/
theorem LawfulVault.canVaultDelete_has_obligations_iff (lv : LawfulVault) :
    lv.canVaultDelete = .tecHAS_OBLIGATIONS ↔
      (lv.assetsAvailable ≠ Number.zero ∨ lv.assetsTotal ≠ Number.zero ∨
        lv.sharesTotal ≠ Number.zero) :=
  LawfulVault.canVaultDelete_has_obligations_iff_proof lv

end XRPL.Model.SingleAssetVault
