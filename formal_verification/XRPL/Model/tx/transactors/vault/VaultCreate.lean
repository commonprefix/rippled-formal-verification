import XRPL.Model.tx.ApplyContext
import XRPL.Model.tx.transactors.token.MPTokenIssuanceCreate
import XRPL.Model.Ledger.Helpers.TokenHelpers
import XRPL.Model.Ledger.Helpers.MPTokenHelpers
import XRPL.Model.Ledger.Helpers.AccountRootHelpers
import XRPL.Model.Protocol.LedgerEntries.Vault
import XRPL.Model.Protocol.LedgerFormats
import XRPL.Model.Protocol.Protocol
import XRPL.Model.Protocol.STNumber
import XRPL.Model.Protocol.TxFlags


namespace XRPL.Model.Protocol

open XRPL.Model.Ledger
open XRPL.Model.Ledger.Helpers
open XRPL.Model.tx

structure VaultCreateTx where
  txID : String
  account : AccountID
  preFeeBalance : XRPAmount
  sequence : UInt32
  asset : Asset
  flags : UInt32
  data : Option Blob := none
  withdrawalPolicy : Option UInt8 := none
  domainID : Option UInt256 := none
  assetsMaximum : Option STNumber := none
  mptokenMetadata : Option Blob := none
  scale : Option UInt8 := none

instance : Transactor VaultCreateTx where
  txID := (·.txID)
  account := (·.account)
  preFeeBalance := (·.preFeeBalance)
  txnType := fun _ => .vaultCreate

def VaultCreateTr.Preflight (ctx : PreflightContext VaultCreateTx) : TER := Id.run do
  let tx := ctx.tx
  if !validDataLength tx.data kMaxDataPayloadLength then
    return .temMALFORMED
  match tx.withdrawalPolicy with
  | some wp => if wp != kVaultStrategyFirstComeFirstServe then return .temMALFORMED
  | none => pure ()
  match tx.domainID with
  | some d =>
    if d == 0 then return .temMALFORMED
    if tx.flags &&& tfVaultPrivate == 0 then return .temMALFORMED
  | none => pure ()
  match tx.assetsMaximum with
  | some am => if am.value.signum < 0 then return .temMALFORMED
  | none => pure ()
  match tx.mptokenMetadata with
  | some md => if md.isEmpty || md.length > kMaxMpTokenMetadataLength then return .temMALFORMED
  | none => pure ()
  match tx.scale with
  | some sc =>
    if tx.asset.holdsMPTIssue || tx.asset.isNative then return .temMALFORMED
    if sc > kVaultMaximumIouScale then return .temMALFORMED
  | none => pure ()
  return .tesSUCCESS

def VaultCreateTr.Preclaim (ctx : PreclaimContext VaultCreateTx) : ReadView TER := do
  let tx := ctx.tx
  let vaultAsset := tx.asset
  let account := tx.account
  let ter ← canAddHoldingAsset vaultAsset
  if ter.operator_bool then
    return ter
  if !vaultAsset.isNative then
    if (← isPseudoAccount vaultAsset.getIssuer) then
      return .tecWRONG_ASSET
  if (← isFrozen account vaultAsset) then
    return (if vaultAsset.holdsIssue then .tecFROZEN else .tecLOCKED)
  match tx.domainID with
  | some d =>
    if (← ReadView.read (Keylet.permissionedDomain d)).isNone then
      return .tecOBJECT_NOT_FOUND
  | none => pure ()
  let accountId ← pseudoAccountAddress (Keylet.vault account tx.sequence).key
  if accountId == xrpAccount then
    return .terADDRESS_COLLISION
  return .tesSUCCESS

def VaultCreateTr.doApply (ctx : ApplyContext VaultCreateTx) : ApplyView TER := do
  let tx := ctx.tx
  let account := tx.account
  let preFeeBalance := tx.preFeeBalance
  let asset := tx.asset
  let vaultKeylet := Keylet.vault account tx.sequence
  let some (.accountRoot owner) ← ApplyView.peek (Keylet.account account)
    | return .tefINTERNAL
  let ter ← ApplyView.dirLinkStub account vaultKeylet.key
  if ter.operator_bool then
    return ter
  adjustOwnerCount (some owner) 2
  let some (.accountRoot owner) ← ApplyView.peek (Keylet.account account)
    | return .tefINTERNAL
  let sb ← get
  if preFeeBalance.operator_lt (sb.fees.accountReserve owner.ownerCount) then
    return .tecINSUFFICIENT_RESERVE
  let pseudo ← match ← createPseudoAccount vaultKeylet.key .vaultID with
    | .error e => return e
    | .ok p => pure p
  let pseudoId := pseudo.account
  let ter ← addEmptyHoldingAsset pseudoId preFeeBalance asset
  if !ter.isTesSuccess then
    return ter
  let scale : UInt8 := if asset.holdsMPTIssue || asset.isNative then 0
    else tx.scale.getD kVaultDefaultIouScale
  let mut mptFlags : UInt32 := 0
  if tx.flags &&& tfVaultShareNonTransferable == 0 then
    mptFlags := mptFlags ||| lsfMPTCanEscrow ||| lsfMPTCanTrade ||| lsfMPTCanTransfer
  if tx.flags &&& tfVaultPrivate != 0 then
    mptFlags := mptFlags ||| lsfMPTRequireAuth
  -- fixCleanup3_2_0 assumed enabled: surface the pseudo's holding on the share
  let referenceHolding : Option UInt256 :=
    if asset.isNative then none
    else match asset with
      | .mptIssue m => some (Keylet.mptoken m.getMptID pseudoId).key
      | .issue i => some (Keylet.line pseudoId i.account i.currency).key
  let mptIssuanceID ← match ← MPTokenIssuanceCreate.create
      { account := pseudoId, sequence := 1, flags := mptFlags, assetScale := some scale,
        metadata := tx.mptokenMetadata, domainId := tx.domainID,
        referenceHolding := referenceHolding } with
    | .error e => return e
    | .ok id => pure id
  let vault : Vault :=
    { key := vaultKeylet.key
    , flags := tx.flags &&& tfVaultPrivate
    , sequence := tx.sequence
    , owner := account
    , pseudoID := pseudoId
    , asset := asset
    , assetsTotal := some (STNumber.ofNumber Number.zero)
    , assetsAvailable := some (STNumber.ofNumber Number.zero)
    , lossUnrealized := some (STNumber.ofNumber Number.zero)
    , assetsMaximum := tx.assetsMaximum
    , shareMPTID := mptIssuanceID
    , data := tx.data
    , withdrawalPolicy := tx.withdrawalPolicy.getD kVaultStrategyFirstComeFirstServe
    , scale := scale }
  ApplyView.insert (.vault vault)
  let err ← authorizeMPToken preFeeBalance mptIssuanceID account 0 none
  if !err.isTesSuccess then
    return err
  if tx.flags &&& tfVaultPrivate != 0 then
    let err ← authorizeMPToken preFeeBalance mptIssuanceID pseudoId 0 (some account)
    if !err.isTesSuccess then
      return err
  -- assets are zero at creation, so the rounding mode is inert here
  match vault.associateAsset asset .to_nearest with
  | .error _ => return .tecINTERNAL
  | .ok v => ApplyView.update (.vault v)
  return .tesSUCCESS

end XRPL.Model.Protocol
