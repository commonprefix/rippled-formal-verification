import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultWithdraw

open XRPL.Model.Protocol (Number STAmount TER Error)
open XRPL.Model.SingleAssetVault

@[export lean_shares_to_assets_withdraw]
def lean_shares_to_assets_withdraw (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : UInt8) : Except Error STAmount :=
  v.sharesToAssetsWithdraw shares (waiveUnrealizedLoss != 0)

-- build a WithdrawAmount from C++ (byShares != 0 selects vault shares over vault assets).
@[export lean_mk_withdraw_amount]
def lean_mk_withdraw_amount (amount : STAmount) (byShares : UInt8) : WithdrawAmount :=
  if byShares != 0 then .vaultShares amount else .vaultAssets amount

@[export lean_vault_withdraw]
-- `.error .badInput`: the amount would have failed preflight (`sfAmount > 0`).
def lean_vault_withdraw (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : UInt8)
    (parentCloseTime : UInt32) (holderShares : Option Number) : Except Error (Except TER VaultWithAmounts) :=
  if h : 0 < amount.amount.toRat then
    (v.withdraw amount (waiveUnrealizedLoss != 0) parentCloseTime h holderShares).run
  else .error .badInput
