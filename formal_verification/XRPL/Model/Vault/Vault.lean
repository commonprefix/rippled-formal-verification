import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- The vault tracks only the asset's `numericType` (integral vs fractional), not its account or
-- currency. Shares are always integral (an MPT), so they need no field.
structure Vault where
  assetsTotal : Number
  assetsAvailable : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  interestUnrealized : Number
  lossUnrealized : Number

def Vault.hasCap (vault : Vault) : Bool :=
  vault.assetsMaximum.isSome

def Vault.isInsolvent (vault : Vault) : Bool :=
  vault.assetsTotal.mantissa_ = 0 && vault.sharesTotal.signum = 1

-- Detect an overflow exception surfaced as a String error from arithmetic ops.
def isOverflow (s : String) : Bool := (s.splitOn "overflow").length ≥ 2

end XRPL.Model.SingleAssetVault
