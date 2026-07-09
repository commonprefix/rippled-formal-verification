import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER

open XRPL.Model.Protocol

structure Vault where
  assetsTotal : Number
  assetsAvailable : Number
  asset : Asset
  scale : UInt8
  sharesTotal : Number -- shares MPT sfOutstandingAmount
  sharesAsset : Asset
  interestUnrealized : Number
