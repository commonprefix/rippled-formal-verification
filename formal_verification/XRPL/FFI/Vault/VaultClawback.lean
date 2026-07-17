import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.VaultClawback

open XRPL.Model.Protocol (STAmount)
open XRPL.Model.SingleAssetVault

@[export lean_vault_clawback]
def lean_vault_clawback (vault : Vault) (assets : STAmount) : Except String ClawbackResult :=
  vault.clawback assets

@[export lean_vault_burn_shares]
def lean_vault_burn_shares (vault : Vault) (sharesDestroyed : STAmount) : Except String Vault :=
  vault.burnShares sharesDestroyed

@[export lean_clawback_result_assets]
def lean_clawback_result_assets (r : ClawbackResult) : STAmount := r.assetsRecovered
@[export lean_clawback_result_shares]
def lean_clawback_result_shares (r : ClawbackResult) : STAmount := r.sharesDestroyed
@[export lean_clawback_result_vault]
def lean_clawback_result_vault (r : ClawbackResult) : Vault := r.vault'
@[export lean_clawback_result_error]
def lean_clawback_result_error (r : ClawbackResult) : Option Int32 := r.error.map (·.code)

@[export lean_can_clawback_vault_shares]
def lean_can_clawback_vault_shares (vault : Vault) : Except String CanClawbackVaultSharesResult :=
  vault.canClawbackVaultShares

@[export lean_can_clawback_result_assets]
def lean_can_clawback_result_assets (r : CanClawbackVaultSharesResult) : Option STAmount :=
  match r with
  | .assets s => some s
  | .error _ => none
@[export lean_can_clawback_result_code]
def lean_can_clawback_result_code (r : CanClawbackVaultSharesResult) : Option Int32 :=
  match r with
  | .error t => some t.code
  | .assets _ => none
