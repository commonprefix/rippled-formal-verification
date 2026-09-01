import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.VaultClawback

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_clawback]
def lean_vault_clawback (lv : LawfulVault) (assets holderShares : STAmount) : Except Error ClawbackResult :=
  lv.clawback assets holderShares

@[export lean_clawback_result_assets]
def lean_clawback_result_assets (r : ClawbackResult) : STAmount := r.assetsRecovered
@[export lean_clawback_result_shares]
def lean_clawback_result_shares (r : ClawbackResult) : STAmount := r.sharesDestroyed
@[export lean_clawback_result_vault]
def lean_clawback_result_vault (r : ClawbackResult) : LawfulVault := r.vault'
@[export lean_clawback_result_error]
def lean_clawback_result_error (r : ClawbackResult) : Option Int32 := r.error.map (·.code)
