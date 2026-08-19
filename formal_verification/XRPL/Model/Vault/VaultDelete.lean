import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- Vault related checks from VaultDelete::preclaim, in C++ order.
def Vault.canVaultDelete (vault : Vault) : TER :=
  if vault.assetsAvailable.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if vault.assetsTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if vault.sharesTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else
    .tesSUCCESS

end XRPL.Model.SingleAssetVault
