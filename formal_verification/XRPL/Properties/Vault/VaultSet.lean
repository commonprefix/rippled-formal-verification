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

/-- Vault update with a new AssetsMaximum and deposit flags that pass the lawfulness check -> it succeeds and only they
change, a maximum that passes the checks is stored exactly, and no change keeps the vault as it is. -/
theorem Vault.update_success :
    (∀ (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool),
      (∀ m ∈ assetsMaximum, m.operator_eq Number.zero = false →
        m.isNormalized ∧ Number.zero.operator_lt m = true) →
      (blockDeposit = true → v.ownerCanBlockDeposit = true) →
      ∃ v', v.update assetsMaximum blockDeposit unblockDeposit = .ok v' ∧
        ∃ assetsMaximum' depositBlocked', v'.toRawVault =
          { v.toRawVault with assetsMaximum := assetsMaximum', depositBlocked := depositBlocked' }) ∧
    (∀ (m : Number) (blockDeposit unblockDeposit : Bool),
      v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS →
      STAmount.isRounded v.numericType m = false) ∧
    v.update none false false = .ok v :=
  ⟨fun assetsMaximum blockDeposit unblockDeposit hmax hblock =>
      have ⟨v', hok⟩ := Vault.update_success_proof v assetsMaximum blockDeposit unblockDeposit hmax hblock
      ⟨v', hok, Vault.update_frame v assetsMaximum blockDeposit unblockDeposit v' hok⟩,
    Vault.canVaultUpdate_assetsMaximum_not_rounded_proof v, Vault.update_none_proof v⟩

/-- A field out of range -> `update` returns notLawful, one line per field rule. -/
theorem Vault.update_not_lawful (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool) :
    (∀ m : Number, assetsMaximum = some m → m.operator_eq Number.zero = false →
      ¬ m.isNormalized ∨ Number.zero.operator_lt m = false →
      v.update assetsMaximum blockDeposit unblockDeposit = .error .notLawful) ∧
    (blockDeposit = true → v.ownerCanBlockDeposit = false →
      v.update assetsMaximum blockDeposit unblockDeposit = .error .notLawful) :=
  ⟨fun m hm => hm ▸ Vault.update_assetsMaximum_out_of_range_proof v m blockDeposit unblockDeposit,
    fun hb hocb => hb ▸ Vault.update_block_not_permitted_proof v assetsMaximum unblockDeposit hocb⟩

end XRPL.Model.SingleAssetVault
