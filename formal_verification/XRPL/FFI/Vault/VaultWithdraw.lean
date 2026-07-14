import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Protocol.STAmount

open XRPL.Model.Protocol (STAmount)
open XRPL.Model.SingleAssetVault

@[export lean_shares_to_assets_withdraw]
def lean_shares_to_assets_withdraw
    (vault : Vault) (shares : STAmount) (waiveUnrealizedLoss : UInt8) : Except String STAmount :=
  vault.sharesToAssetsWithdraw shares (waiveUnrealizedLoss != 0)

@[export lean_vault_withdraw]
def lean_vault_withdraw (vault : Vault) (amount : STAmount) : Except String WithdrawResult :=
  vault.withdraw amount

@[export lean_withdraw_result_assets]
def lean_withdraw_result_assets (r : WithdrawResult) : STAmount := r.assets'
@[export lean_withdraw_result_shares]
def lean_withdraw_result_shares (r : WithdrawResult) : STAmount := r.sharesBurned
@[export lean_withdraw_result_vault]
def lean_withdraw_result_vault (r : WithdrawResult) : Vault := r.vault'
@[export lean_withdraw_result_error]
def lean_withdraw_result_error (r : WithdrawResult) : Option Int32 := r.error.map (·.code)
