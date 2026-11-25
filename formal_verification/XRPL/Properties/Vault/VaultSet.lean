import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.CanVaultUpdate
import XRPL.Model.Vault.VaultSet
import XRPL.Properties.Vault.Proofs.CreateUpdate
import XRPL.Properties.Vault.Proofs.Frame

/-! # `Vault.canVaultUpdate` and `Vault.update`

The exits of `canVaultUpdate`. An update changes only AssetsMaximum and the deposit block. -/

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
      v.canVaultUpdate (some m) blockDeposit = .ok .tecLIMIT_EXCEEDED := by
  sorry

/-- Every outcome of the check: `tecPRECISION_LOSS`, `tecNO_PERMISSION` and `tecLIMIT_EXCEEDED` are
the only rejections `canVaultUpdate` can return. -/
theorem Vault.canVaultUpdate_error_codes (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    (ter : TER) (hok : v.canVaultUpdate assetsMaximum blockDeposit = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecNO_PERMISSION ∨
      ter = .tecLIMIT_EXCEEDED := by
  sorry

/-- A vault update setting a new maximum passes exactly when the maximum is on the asset's grid, the deposit flags are
permitted, and the maximum is zero or at least the total the check computes (cash plus deployed, rounded down). -/
theorem Vault.canVaultUpdate_lawful_iff (m assetsTotal : Number) (blockDeposit : Option Bool)
    (hnorm : m.isNormalized) -- the transaction's maximum, a normalized `Number`
    (hat : v.assetsTotal = .ok assetsTotal) :
    v.canVaultUpdate (some m) blockDeposit = .ok .tesSUCCESS ↔
      m.isOnExponentGrid v.baseExponent v.numericType = .ok true ∧
      (!v.ownerCanBlockDeposit && blockDeposit.isSome) = false ∧
      (m.toRat = 0 ∨ assetsTotal.toRat ≤ m.toRat) := by
  sorry

/-- Vault update with a new AssetsMaximum and deposit flags that pass the lawfulness check -> it succeeds and only they
change, a maximum that passes the checks is stored exactly, and no change keeps the vault as it is. -/
theorem Vault.update_success :
    (∀ (assetsMaximum : Option Number) (blockDeposit : Option Bool),
      (∀ m ∈ assetsMaximum, m.operator_eq Number.zero = false →
        m.isNormalized ∧ Number.zero.operator_lt m = true) →
      (blockDeposit = some true → v.ownerCanBlockDeposit = true) →
      ∃ v', v.update assetsMaximum blockDeposit = .ok v' ∧
        ∃ assetsMaximum' depositBlocked', v'.toRawVault =
          { v.toRawVault with assetsMaximum := assetsMaximum', depositBlocked := depositBlocked' }) ∧
    (∀ (m : Number) (blockDeposit : Option Bool),
      v.canVaultUpdate (some m) blockDeposit = .ok .tesSUCCESS →
      STAmount.isRounded v.numericType m = false) ∧
    v.update none none = .ok v := by
  sorry

/-- A field out of range -> `update` returns notLawful, one line per field rule. -/
theorem Vault.update_not_lawful (assetsMaximum : Option Number) (blockDeposit : Option Bool) :
    (∀ m : Number, assetsMaximum = some m → m.operator_eq Number.zero = false →
      ¬ m.isNormalized ∨ Number.zero.operator_lt m = false →
      v.update assetsMaximum blockDeposit = .error .notLawful) ∧
    (blockDeposit = some true → v.ownerCanBlockDeposit = false →
      v.update assetsMaximum blockDeposit = .error .notLawful) := by
  sorry

end XRPL.Model.SingleAssetVault
