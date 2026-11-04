import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.CanVaultUpdate
import XRPL.Model.Vault.VaultSet

/-! # `Vault.canVaultUpdate` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- The exits of `canVaultUpdate`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.canVaultUpdate_exits (blockDeposit unblockDeposit : Bool) :
    (∀ m : Number, m.isOnExponentGrid v.baseExponent v.numericType = .ok false →
      v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tecPRECISION_LOSS) ∧
    (∀ assetsMaximum : Option Number,
      (∀ m ∈ assetsMaximum, m.isOnExponentGrid v.baseExponent v.numericType = .ok true) →
      v.ownerCanBlockDeposit = false → (blockDeposit || unblockDeposit) = true →
      v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tecNO_PERMISSION) ∧
    ∀ m assetsTotal : Number, m.isOnExponentGrid v.baseExponent v.numericType = .ok true →
      (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false → v.assetsTotal = .ok assetsTotal →
      m.operator_ne Number.zero = true → m.operator_lt assetsTotal = true →
      v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tecLIMIT_EXCEEDED :=
  ⟨fun m => Vault.canVaultUpdate_off_grid_proof v m blockDeposit unblockDeposit,
    fun assetsMaximum => Vault.canVaultUpdate_no_permission_proof v assetsMaximum blockDeposit unblockDeposit,
    fun m assetsTotal => Vault.canVaultUpdate_below_total_proof v m assetsTotal blockDeposit unblockDeposit⟩

/-- Every outcome of the check: `tecPRECISION_LOSS`, `tecNO_PERMISSION` and `tecLIMIT_EXCEEDED` are
the only rejections `canVaultUpdate` can return. -/
theorem Vault.canVaultUpdate_error_codes (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    (ter : TER) (hok : v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecNO_PERMISSION ∨
      ter = .tecLIMIT_EXCEEDED :=
  Vault.canVaultUpdate_error_codes_proof v assetsMaximum blockDeposit unblockDeposit ter hok

/-- A vault update setting a new maximum on the asset's grid, with permitted deposit flags, passes exactly
when the maximum is zero or at least the total the check computes (cash plus deployed, rounded down). -/
theorem Vault.canVaultUpdate_lawful_iff (m assetsTotal : Number) (blockDeposit unblockDeposit : Bool)
    (hnorm : m.isNormalized) -- the transaction's maximum, a normalized `Number`
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false)
    (hat : v.assetsTotal = .ok assetsTotal) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS ↔
      m.toRat = 0 ∨ assetsTotal.toRat ≤ m.toRat :=
  Vault.canVaultUpdate_lawful_iff_proof v m assetsTotal blockDeposit unblockDeposit hnorm hgrid hperm hat

/-- On a reachable vault, an update setting a new maximum on the asset's grid, with permitted deposit
flags, passes exactly when the maximum is zero or at least the vault's exact total. -/
theorem Vault.Reachable.canVaultUpdate_iff (t : UInt32) (hr : Vault.Reachable v t) (m : Number)
    (blockDeposit unblockDeposit : Bool)
    (hnorm : m.isNormalized) -- the transaction's maximum, a normalized `Number`
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS ↔
      m.toRat = 0 ∨ v.toExact.assetsTotal ≤ m.toRat :=
  Vault.Reachable.canVaultUpdate_iff_proof v t hr m blockDeposit unblockDeposit hnorm hgrid hperm

end XRPL.Model.SingleAssetVault
