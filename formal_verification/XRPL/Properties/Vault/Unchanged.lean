import XRPL.Properties.Vault.Common.Unchanged

/-! # A rejected operation changes nothing and reports nothing

When an operation returns a `TER` in its result, the vault is the starting
vault and both amount fields are zero: nothing moved and the record says so.
A thrown error needs no theorem because the model returns no result at all. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem LawfulVault.deposit_error_unchanged (lv : LawfulVault) (amount : STAmount) (isDonation : Bool)
    (r : DepositResult) (hok : lv.deposit amount isDonation = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.amountDeposit' = STAmount.zero lv.numericType ∧
    r.sharesIssued = STAmount.zero .int64 :=
  LawfulVault.deposit_error_rejected_proof lv amount isDonation r hok herr

theorem LawfulVault.withdraw_error_unchanged (lv : LawfulVault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.assets' = STAmount.zero lv.numericType ∧
    r.sharesBurned = STAmount.zero .int64 :=
  LawfulVault.withdraw_error_rejected_proof lv amount waiveUnrealizedLoss r hok herr

theorem LawfulVault.clawback_error_unchanged (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : lv.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.assetsRecovered = STAmount.zero lv.numericType ∧
    r.sharesDestroyed = STAmount.zero .int64 :=
  LawfulVault.clawback_error_rejected_proof lv assets holderShares r hok herr

end XRPL.Model.SingleAssetVault
