import XRPL.Model.tx.Transactor


namespace XRPL.Model.tx.Alt

open XRPL.Model.Protocol
open XRPL.Model.tx (TxnType validDataLength)

structure Transactor where
  txID : String
  account : AccountID
  preFeeBalance : XRPAmount
  txnType : TxnType
  amount : Option STAmount := none
  destination : Option AccountID := none
  holder : Option AccountID := none
  delegate : Option AccountID := none

structure VaultCreateTx extends Transactor where
  sequence : UInt32
  asset : Asset
  flags : UInt32
  data : Option Blob := none
  withdrawalPolicy : Option UInt8 := none
  domainID : Option UInt256 := none
  assetsMaximum : Option STNumber := none
  mptokenMetadata : Option Blob := none
  scale : Option UInt8 := none

structure VaultDepositTx extends Transactor where
  vaultID : UInt256

structure PreflightContext (α : Type) where
  tx : α
structure PreclaimContext (α : Type) where
  tx : α
structure ApplyContext (α : Type) where
  tx : α

def PreflightAny (f : Transactor) : TER :=
  if f.txID = "" then .temMALFORMED else .tesSUCCESS

def VaultCreateTr.Preflight (ctx : PreflightContext VaultCreateTx) : TER := Id.run do
  if ctx.tx.txID = "" then
    return .temMALFORMED
  if !validDataLength ctx.tx.data kMaxDataPayloadLength then
    return .temMALFORMED
  return .tesSUCCESS

def finalizeCommon (f : Transactor) : Bool :=
  f.txnType.mustModifyVault || f.txnType.mayModifyVault

example (tx : VaultCreateTx) : Bool := finalizeCommon tx.toTransactor
example (tx : VaultCreateTx) : TER := PreflightAny tx.toTransactor

def VaultCreateTx.mk' (txID : String) (account : AccountID) (preFeeBalance : XRPAmount)
    (sequence : UInt32) (asset : Asset) (flags : UInt32) : VaultCreateTx :=
  { txID, account, preFeeBalance, txnType := .vaultCreate, sequence, asset, flags }

end XRPL.Model.tx.Alt
