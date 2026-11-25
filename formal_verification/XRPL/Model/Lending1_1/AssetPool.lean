import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultBalances
import XRPL.Model.Lending.AssetPool

namespace XRPL.Model.Lending1_1

open XRPL.Model.Protocol (TerExcept)
open XRPL.Model.Lending (AssetPool PoolAmounts PoolBalanceChange)
open XRPL.Model.SingleAssetVault (Vault)

private def adjustVaultBalances (v : Vault) (change : PoolBalanceChange) : TerExcept Vault := do
  let rawVault' ← v.adjustBalances change
  rawVault'.to_lawful

-- A vault is the asset pool of the lending protocol. Writing the balances back re-checks the vault.
instance : AssetPool Vault where
  amounts v := {
    assetsAvailable := v.assetsAvailable
    assetsDeployed := v.assetsDeployed
    assetsReserved := v.assetsReserved
    lossUnrealized := v.lossUnrealized
    yieldUnrealized := v.yieldUnrealized }
  assetsTotal v := v.assetsTotal
  baseExponent v := v.baseExponent
  phase v := v.phase
  redemptionDate v := v.schedule.map (·.redemptionDate)
  openLimit v := v.openLimit
  exceedsOpenLimit v := v.exceedsOpenLimit
  adjustBalances := adjustVaultBalances

end XRPL.Model.Lending1_1
