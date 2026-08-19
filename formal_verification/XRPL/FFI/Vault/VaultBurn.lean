import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.VaultBurn

open XRPL.Model.Protocol (STAmount Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_burn_shares]
def lean_vault_burn_shares (vault : Vault) (sharesDestroyed : STAmount) : Except Error Vault :=
  vault.burnShares sharesDestroyed

@[export lean_can_burn_shares]
def lean_can_burn_shares (vault : Vault) : Except Error CanBurnSharesResult :=
  vault.canBurnShares

@[export lean_can_burn_result_assets]
def lean_can_burn_result_assets (r : CanBurnSharesResult) : Option STAmount :=
  match r with
  | .assets s => some s
  | .error _ => none
@[export lean_can_burn_result_code]
def lean_can_burn_result_code (r : CanBurnSharesResult) : Option Int32 :=
  match r with
  | .error t => some t.code
  | .assets _ => none
