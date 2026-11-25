import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

open XRPL.Model.Protocol (Number NumericType STAmount TER Error)
open XRPL.Model.SingleAssetVault

-- The schedule dates are set together or not at all, `.error .badInput` otherwise.
def scheduleOf (subscriptionDate redemptionDate : Option UInt32) : Except Error (Option VaultSchedule) :=
  match subscriptionDate, redemptionDate with
  | some subscriptionDate, some redemptionDate => pure (some { subscriptionDate, redemptionDate })
  | none, none => pure none
  | _, _ => throw .badInput

-- Build a lawful vault from the raw C++ fields, validating at the boundary.
-- `.error .notLawful` is the untrusted-boundary rejection (the state is not lawful).
@[export lean_vault_build]
def lean_vault_build (assetsAvailable assetsDeployed assetsReserved : Number)
    (assetsMaximum : Option Number) (numericType : NumericType) (scale : UInt8)
    (sharesTotal lossUnrealized yieldUnrealized : Number)
    (subscriptionDate redemptionDate : Option UInt32) (earlyExitFeeRate : Option UInt32)
    (ownerCanBlockDeposit depositBlocked : UInt8) : Except Error Vault := do
  let schedule ← scheduleOf subscriptionDate redemptionDate
  let raw : RawVault :=
    { assetsAvailable, assetsDeployed, assetsReserved, assetsMaximum, numericType, scale,
      sharesTotal, lossUnrealized, yieldUnrealized, schedule, earlyExitFeeRate,
      ownerCanBlockDeposit := ownerCanBlockDeposit != 0,
      depositBlocked := depositBlocked != 0 }
  raw.to_lawful

@[export lean_vault_assets_total]
def lean_vault_assets_total (v : Vault) : Except Error Number := v.assetsTotal
@[export lean_vault_assets_available]
def lean_vault_assets_available (v : Vault) : Number := v.assetsAvailable
@[export lean_vault_assets_deployed]
def lean_vault_assets_deployed (v : Vault) : Number := v.assetsDeployed
@[export lean_vault_assets_reserved]
def lean_vault_assets_reserved (v : Vault) : Number := v.assetsReserved
@[export lean_vault_assets_maximum]
def lean_vault_assets_maximum (v : Vault) : Option Number := v.assetsMaximum
@[export lean_vault_numeric_type]
def lean_vault_numeric_type (v : Vault) : NumericType := v.numericType
-- 3-way tag: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
@[export lean_vault_numeric_tag]
def lean_vault_numeric_tag (v : Vault) : UInt8 :=
  match v.numericType with
  | .fractional => 2
  | .integral maxValue _ _ _ => if maxValue == 100000000000000000 then 0 else 1
@[export lean_vault_scale]
def lean_vault_scale (v : Vault) : UInt8 := v.scale
@[export lean_vault_shares_total]
def lean_vault_shares_total (v : Vault) : Number := v.sharesTotal
@[export lean_vault_loss_unrealized]
def lean_vault_loss_unrealized (v : Vault) : Number := v.lossUnrealized
@[export lean_vault_yield_unrealized]
def lean_vault_yield_unrealized (v : Vault) : Number := v.yieldUnrealized
@[export lean_vault_subscription_date]
def lean_vault_subscription_date (v : Vault) : Option UInt32 := v.schedule.map (·.subscriptionDate)
@[export lean_vault_redemption_date]
def lean_vault_redemption_date (v : Vault) : Option UInt32 := v.schedule.map (·.redemptionDate)
@[export lean_vault_early_exit_fee_rate]
def lean_vault_early_exit_fee_rate (v : Vault) : Option UInt32 := v.earlyExitFeeRate
@[export lean_vault_owner_can_block_deposit]
def lean_vault_owner_can_block_deposit (v : Vault) : UInt8 := if v.ownerCanBlockDeposit then 1 else 0
@[export lean_vault_deposit_blocked]
def lean_vault_deposit_blocked (v : Vault) : UInt8 := if v.depositBlocked then 1 else 0

-- A `TerExcept α` reaches C++ as `Except Error (Except TER α)` (its `.run`): the outer layer is a
-- model error, the inner one is the TER that rejects the transaction.
def terCode {α : Type} : Except TER α → Option Int32
  | .error t => some t.code
  | .ok _ => none

def terValue {α : Type} : Except TER α → Option α
  | .error _ => none
  | .ok a => some a

@[export lean_ter_amount_code]
def lean_ter_amount_code (r : Except TER STAmount) : Option Int32 := terCode r
@[export lean_ter_amount_value]
def lean_ter_amount_value (r : Except TER STAmount) : Option STAmount := terValue r

@[export lean_ter_vault_code]
def lean_ter_vault_code (r : Except TER Vault) : Option Int32 := terCode r
@[export lean_ter_vault_value]
def lean_ter_vault_value (r : Except TER Vault) : Option Vault := terValue r

@[export lean_ter_vault_amounts_code]
def lean_ter_vault_amounts_code (r : Except TER VaultWithAmounts) : Option Int32 := terCode r
@[export lean_ter_vault_amounts_value]
def lean_ter_vault_amounts_value (r : Except TER VaultWithAmounts) : Option VaultWithAmounts :=
  terValue r

@[export lean_vault_amounts_assets]
def lean_vault_amounts_assets (r : VaultWithAmounts) : STAmount := r.assets
@[export lean_vault_amounts_shares]
def lean_vault_amounts_shares (r : VaultWithAmounts) : STAmount := r.shares
@[export lean_vault_amounts_vault]
def lean_vault_amounts_vault (r : VaultWithAmounts) : Vault := r.vault'
