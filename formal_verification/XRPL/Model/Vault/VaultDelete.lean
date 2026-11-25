import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- Checks from VaultDelete::preclaim, in C++ order.
def Vault.canVaultDelete (v : Vault) : Except Error TER := do
  if v.assetsAvailable.operator_ne Number.zero then
    return .tecHAS_OBLIGATIONS

  let assetsTotal ← v.assetsTotal
  if assetsTotal.operator_ne Number.zero then
    return .tecHAS_OBLIGATIONS
  if v.sharesTotal.operator_ne Number.zero then
    return .tecHAS_OBLIGATIONS
  return .tesSUCCESS

end XRPL.Model.SingleAssetVault
