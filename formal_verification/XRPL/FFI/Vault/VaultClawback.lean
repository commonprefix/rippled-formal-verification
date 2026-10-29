import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultClawback

open XRPL.Model.Protocol (STAmount TER Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_clawback]
-- `.error .badInput`: the amount would have failed preflight (`sfAmount >= 0`).
def lean_vault_clawback (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : UInt8)
    : Except Error (Except TER VaultWithAmounts) :=
  if h : 0 ≤ assets.toRat then (v.clawback assets holderShares (waiveUnrealizedLoss != 0) h).run
  else .error .badInput
