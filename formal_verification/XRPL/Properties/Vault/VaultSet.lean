import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.CanVaultUpdate
import XRPL.Model.Vault.VaultSet

/-! # `Vault.canVaultUpdate` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- The exits of `canVaultUpdate`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.canVaultUpdate_exits (blockDeposit : Option Bool) :
    (∀ m : Number, m.isOnExponentGrid v.baseExponent v.numericType = .ok false →
      v.canVaultUpdate (some m) blockDeposit = .ok .tecPRECISION_LOSS) ∧
    (∀ assetsMaximum : Option Number,
      (∀ m ∈ assetsMaximum, m.isOnExponentGrid v.baseExponent v.numericType = .ok true) →
      v.ownerCanBlockDeposit = false → blockDeposit.isSome = true →
      v.canVaultUpdate assetsMaximum blockDeposit = .ok .tecNO_PERMISSION) ∧
    ∀ m assetsTotal : Number, m.isOnExponentGrid v.baseExponent v.numericType = .ok true →
      (!v.ownerCanBlockDeposit && blockDeposit.isSome) = false → v.assetsTotal = .ok assetsTotal →
      m.operator_ne Number.zero = true → m.operator_lt assetsTotal = true →
      v.canVaultUpdate (some m) blockDeposit = .ok .tecLIMIT_EXCEEDED :=
  ⟨fun m => Vault.canVaultUpdate_off_grid_proof v m blockDeposit,
    fun assetsMaximum => Vault.canVaultUpdate_no_permission_proof v assetsMaximum blockDeposit,
    fun m assetsTotal => Vault.canVaultUpdate_below_total_proof v m assetsTotal blockDeposit⟩

/-- Every outcome of the check: `tecPRECISION_LOSS`, `tecNO_PERMISSION` and `tecLIMIT_EXCEEDED` are
the only rejections `canVaultUpdate` can return. -/
theorem Vault.canVaultUpdate_error_codes (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    (ter : TER) (hok : v.canVaultUpdate assetsMaximum blockDeposit = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecNO_PERMISSION ∨
      ter = .tecLIMIT_EXCEEDED :=
  Vault.canVaultUpdate_error_codes_proof v assetsMaximum blockDeposit ter hok

/-- A vault update setting a new maximum passes exactly when the maximum is on the asset's grid, the deposit flags are
permitted, and the maximum is zero or at least the total the check computes (cash plus deployed, rounded down). -/
theorem Vault.canVaultUpdate_lawful_iff (m assetsTotal : Number) (blockDeposit : Option Bool)
    (hnorm : m.isNormalized) -- the transaction's maximum, a normalized `Number`
    (hat : v.assetsTotal = .ok assetsTotal) :
    v.canVaultUpdate (some m) blockDeposit = .ok .tesSUCCESS ↔
      m.isOnExponentGrid v.baseExponent v.numericType = .ok true ∧
      (!v.ownerCanBlockDeposit && blockDeposit.isSome) = false ∧
      (m.toRat = 0 ∨ assetsTotal.toRat ≤ m.toRat) :=
  Vault.canVaultUpdate_lawful_iff_proof v m assetsTotal blockDeposit hnorm hat

end XRPL.Model.SingleAssetVault
