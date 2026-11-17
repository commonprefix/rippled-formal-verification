import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultBurn

open XRPL.Model.Protocol (STAmount TER Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_burn_shares]
def lean_vault_burn_shares (v : Vault) (sharesDestroyed : STAmount) : Except Error (Except TER Vault) :=
  (v.burnShares sharesDestroyed).run

@[export lean_can_burn_shares]
def lean_can_burn_shares (v : Vault) (amount holderShares : STAmount) : Except Error (Except TER STAmount) :=
  (v.canBurnShares amount holderShares).run
