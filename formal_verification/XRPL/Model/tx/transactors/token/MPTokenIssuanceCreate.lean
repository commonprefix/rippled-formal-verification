import XRPL.Model.Ledger.ApplyView
import XRPL.Model.Ledger.Helpers.AccountRootHelpers
import XRPL.Model.Protocol.Indexes
import XRPL.Model.Protocol.LedgerEntries.MPTokenIssuance
import XRPL.Model.Protocol.MPTIssue
import XRPL.Model.Protocol.TxFlags


namespace XRPL.Model.tx

open XRPL.Model.Ledger
open XRPL.Model.Ledger.Helpers
open XRPL.Model.Protocol

structure MPTCreateArgs where
  account : AccountID
  priorBalance : Option XRPAmount := none
  sequence : UInt32 := 0
  flags : UInt32 := 0
  maxAmount : Option UInt64 := none
  assetScale : Option UInt8 := none
  transferFee : Option UInt16 := none
  metadata : Option Blob := none
  domainId : Option UInt256 := none
  mutableFlags : Option UInt32 := none
  referenceHolding : Option UInt256 := none

def MPTokenIssuanceCreate.create (args : MPTCreateArgs) : ApplyView (Except TER MPTID) := do
  let some (.accountRoot acct) ← ApplyView.peek (Keylet.account args.account)
    | return .error .tecINTERNAL
  match args.priorBalance with
  | some pb =>
    let sb ← get
    if pb.operator_lt (sb.fees.accountReserve (acct.ownerCount + 1)) then
      return .error .tecINSUFFICIENT_RESERVE
  | none => pure ()
  let mptId := makeMptID args.sequence args.account
  let issuanceKeylet := Keylet.mptIssuance mptId
  let some ownerNode ← ApplyView.dirInsertStub args.account issuanceKeylet.key
    | return .error .tecDIR_FULL
  let refHolding : Option UInt256 ← match args.referenceHolding with
    | none => pure none
    | some refKey =>
      match (← get).readUnchecked refKey with
      | none => return .error .tecINTERNAL
      | some (.mptoken _) => pure (some refKey)
      | some (.rippleState _) => pure (some refKey)
      | some _ => return .error .tecINTERNAL
  let issuance : MPTokenIssuance :=
    { key := issuanceKeylet.key
    , flags := args.flags &&& ~~~tfUniversal
    , issuer := args.account
    , sequence := args.sequence
    , ownerNode := ownerNode
    , outstandingAmount := 0
    , maximumAmount := args.maxAmount
    , assetScale := args.assetScale.getD 0
    , transferFee := args.transferFee.getD 0
    , mptokenMetadata := args.metadata
    , domainID := args.domainId
    , mutableFlags := args.mutableFlags.getD 0
    , referenceHolding := refHolding }
  ApplyView.insert (.mptokenIssuance issuance)
  adjustOwnerCount (some acct) 1
  return .ok mptId

end XRPL.Model.tx
