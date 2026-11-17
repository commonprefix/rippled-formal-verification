import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultDeposit

open XRPL.Model.Protocol (STAmount TER Error)
open XRPL.Model.SingleAssetVault

@[export lean_rounded_deposit_amount]
def lean_rounded_deposit_amount (v : Vault) (amountDeposit : STAmount) : Except Error (Except TER STAmount) :=
  (v.roundedDepositAmount amountDeposit).run

@[export lean_vault_is_insolvent]
def lean_vault_is_insolvent (v : Vault) : Bool :=
  v.isInsolvent

@[export lean_vault_deposit]
-- `.error .badInput`: the amount would have failed preflight (`sfAmount > 0`).
def lean_vault_deposit (v : Vault) (amountDeposit : STAmount) (isDonation : UInt8) (parentCloseTime : UInt32)
    : Except Error (Except TER VaultWithAmounts) :=
  if h : 0 < amountDeposit.toRat then (v.deposit amountDeposit (isDonation != 0) parentCloseTime h).run
  else .error .badInput
