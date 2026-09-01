import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- Checks from VaultDelete::preclaim, in C++ order.
def LawfulVault.canVaultDelete (lv : LawfulVault) : TER :=
  if lv.assetsAvailable.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if lv.assetsTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if lv.sharesTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else
    .tesSUCCESS

end XRPL.Model.SingleAssetVault
