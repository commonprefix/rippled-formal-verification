import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultSet

/-! # `RawVault.canVaultSet` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)

/-! ## `LawfulVault.canVaultSet` -/

/-- A nonzero new maximum below the current assets total: `tecLIMIT_EXCEEDED`. -/
theorem LawfulVault.canVaultSet_below_total (assetsMaximum : Number)
    (hne : assetsMaximum.operator_ne Number.zero = true) -- the new maximum is nonzero
    (hlt : assetsMaximum.operator_lt lv.assetsTotal = true) : -- and compares below the assets total
    lv.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED :=
  LawfulVault.canVaultSet_below_total_proof lv assetsMaximum hne hlt

/-- A new maximum that compares equal to zero, or does not compare below the
current assets total, passes. Zero requests removing the cap. -/
theorem LawfulVault.canVaultSet_success (assetsMaximum : Number)
    -- the failure guard is off: the maximum is zero or not below the assets total
    (hok : (assetsMaximum.operator_ne Number.zero &&
        assetsMaximum.operator_lt lv.assetsTotal) = false) :
    lv.canVaultSet assetsMaximum = .tesSUCCESS :=
  LawfulVault.canVaultSet_success_proof lv assetsMaximum hok

/-- Every outcome of the check: `tecLIMIT_EXCEEDED` is the only rejection
`canVaultSet` can return. -/
theorem LawfulVault.canVaultSet_error_codes (assetsMaximum : Number) :
    lv.canVaultSet assetsMaximum = .tesSUCCESS ∨
    lv.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED :=
  LawfulVault.canVaultSet_error_codes_proof lv assetsMaximum

/-- On a lawful vault, a normalized new maximum passes exactly when it is zero
or at least the exact assets total. -/
theorem LawfulVault.lawful_canVaultSet_iff (lv : LawfulVault)
    (assetsMaximum : Number)
    (hnorm : assetsMaximum.isNormalized) : -- the new maximum is normalized
    lv.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ lv.toExact.assetsTotal ≤ assetsMaximum.toRat :=
  LawfulVault.lawful_canVaultSet_iff_proof lv assetsMaximum hnorm

end XRPL.Model.SingleAssetVault
