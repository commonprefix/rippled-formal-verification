import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.VaultClawback

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_clawback]
-- `.error .badInput`: the amount would have failed preflight (`sfAmount >= 0`).
def lean_vault_clawback (v : Vault) (assets holderShares : STAmount) : Except Error ClawbackResult :=
  if h : 0 ≤ assets.toRat then v.clawback assets holderShares h
  else .error .badInput

@[export lean_clawback_result_assets]
def lean_clawback_result_assets (r : ClawbackResult) : STAmount := r.assetsRecovered
@[export lean_clawback_result_shares]
def lean_clawback_result_shares (r : ClawbackResult) : STAmount := r.sharesDestroyed
@[export lean_clawback_result_vault]
def lean_clawback_result_vault (r : ClawbackResult) : Vault := r.vault'
@[export lean_clawback_result_error]
def lean_clawback_result_error (r : ClawbackResult) : Option Int32 := r.error.map (·.code)
