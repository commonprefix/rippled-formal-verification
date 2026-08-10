import XRPL.Model.Vault.Vault

/-! State initialization of `VaultCreate`. Trivial, but it lets `create_lawful` show
every vault starts lawful, which anchors theorems about a series of operations. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def Vault.create (nt : NumericType) (scale : UInt8) (assetsMaximum : Option Number) : Vault where
  assetsTotal := Number.zero
  assetsAvailable := Number.zero
  assetsReserved := Number.zero
  assetsMaximum := assetsMaximum
  numericType := nt
  scale := scale
  sharesTotal := Number.zero
  lossUnrealized := Number.zero

end XRPL.Model.SingleAssetVault
