import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER

open XRPL.Model.Protocol

-- Assets are modeled in the vault, but might be abstracted in the future
-- to remove the coupling with xrpld
structure Vault where
  assetsTotal : Number
  assetsAvailable : Number
  asset : Asset -- modeled for now
  scale : UInt8
  sharesTotal : Number -- shares MPT sfOutstandingAmount
  sharesAsset : Asset -- modeled for now
  interestUnrealized : Number
  lossUnrealized : Number
