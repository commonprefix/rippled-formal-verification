import XRPL.Model.tx.Transactor
import XRPL.Model.Protocol.MPTAmount


namespace XRPL.Model.tx

open XRPL.Model.Ledger
open XRPL.Model.Protocol

namespace ValidVault

structure VaultSnap where
  key : UInt256
  asset : Asset
  pseudoId : AccountID
  owner : AccountID
  shareMPTID : MPTID
  assetsTotal : Number
  assetsAvailable : Number
  assetsMaximum : Number
  lossUnrealized : Number

structure SharesSnap where
  share : MPTIssue
  sharesTotal : UInt64
  sharesMaximum : UInt64

structure State where
  beforeVault : List VaultSnap := []
  afterVault  : List VaultSnap := []
  beforeMPTs  : List SharesSnap := []
  afterMPTs   : List SharesSnap := []

def numOf (o : Option STNumber) : Number := (o.map (·.value)).getD Number.zero

def VaultSnap.make (v : Vault) : VaultSnap :=
  { key := v.key, asset := v.asset, pseudoId := v.pseudoID, owner := v.owner,
    shareMPTID := v.shareMPTID,
    assetsTotal := numOf v.assetsTotal, assetsAvailable := numOf v.assetsAvailable,
    assetsMaximum := numOf v.assetsMaximum, lossUnrealized := numOf v.lossUnrealized }

def SharesSnap.make (i : MPTokenIssuance) : SharesSnap :=
  { share := { mptID := makeMptID i.sequence i.issuer },
    sharesTotal := i.outstandingAmount,
    sharesMaximum := i.maximumAmount.getD maxMPTokenAmount.toUInt64 }

-- Known model boundaries (intentional divergences from rippled, tracked here):
--   * Balance `deltas` map deferred to Phase 2/3 (only snapshots built below); the
--     universal block + vaultCreate case do not need it.
--   * Directory mechanics are stubbed (ApplyView.dir{Insert,Link}Stub never fail),
--     so tecDIR_FULL / dirLink rejections cannot occur — dir-full vectors are out
--     of scope for differential testing.
--   * Fees are not modeled; amendments are assumed enabled (e.g. fixCleanup3_2_0).
--
-- visitEntry equivalent: over the apply touched-set, collect before/after vault
-- and share-issuance snapshots.
def collect (initial final : Ledger) (touched : List UInt256) : State := Id.run do
  let mut st : State := {}
  for key in touched.dedup do
    match initial.readUnchecked key with
    | some (.vault v) => st := { st with beforeVault := st.beforeVault ++ [VaultSnap.make v] }
    | some (.mptokenIssuance i) => st := { st with beforeMPTs := st.beforeMPTs ++ [SharesSnap.make i] }
    | _ => pure ()
    match final.readUnchecked key with
    | some (.vault v) => st := { st with afterVault := st.afterVault ++ [VaultSnap.make v] }
    | some (.mptokenIssuance i) => st := { st with afterMPTs := st.afterMPTs ++ [SharesSnap.make i] }
    | _ => pure ()
  return st

def nz (n : Number) : Bool := !(n.operator_eq Number.zero)
def ltz (n : Number) : Bool := n.operator_lt Number.zero

private def findShares (mpts : List SharesSnap) (id : MPTID) : Option SharesSnap :=
  mpts.find? (fun e => e.share.getMptID == id)

def finalize {α : Type} [Transactor α] (tx : α) (ret : TER) (_fee : XRPAmount)
    (final : Ledger) (st : State) : Bool := Id.run do
  if !ret.isTesSuccess then
    return true
  let tt := Transactor.txnType tx
  if st.afterVault.isEmpty && st.beforeVault.isEmpty then
    return !tt.mustModifyVault
  if !(tt.mustModifyVault || tt.mayModifyVault) then
    return false
  if st.beforeVault.length > 1 || st.afterVault.length > 1 then
    return false
  -- deletion: the only vault-modifying tx without an "after" vault
  if st.afterVault.isEmpty then
    if tt != .vaultDelete then
      return false
    let some beforeVault := st.beforeVault.head? | return false
    let some deletedShares := findShares st.beforeMPTs beforeVault.shareMPTID | return false
    let mut result := true
    if deletedShares.sharesTotal != 0 then result := false
    if nz beforeVault.assetsTotal then result := false
    if nz beforeVault.assetsAvailable then result := false
    return result
  if tt == .vaultDelete then
    return false
  let some afterVault := st.afterVault.head? | return false
  let updatedShares : Option SharesSnap :=
    match findShares st.afterMPTs afterVault.shareMPTID with
    | some s => some s
    | none => (final.read (Keylet.mptIssuance afterVault.shareMPTID)).bind
                (fun e => e.asMPTokenIssuance.map SharesSnap.make)
  let mut result := true
  -- universal immutable-data check (only when a before-vault exists)
  match st.beforeVault.head? with
  | some bv =>
    if !(Asset.equiv afterVault.asset bv.asset) || afterVault.pseudoId != bv.pseudoId
        || afterVault.shareMPTID != bv.shareMPTID then
      result := false
  | none => pure ()
  let some us := updatedShares | return false
  if us.sharesTotal == 0 then
    if nz afterVault.assetsTotal then result := false
    if nz afterVault.assetsAvailable then result := false
  else if us.sharesTotal > us.sharesMaximum then
    result := false
  if ltz afterVault.assetsAvailable then result := false
  if afterVault.assetsTotal.operator_lt afterVault.assetsAvailable then
    result := false
  else
    match Number.operator_sub afterVault.assetsTotal afterVault.assetsAvailable .to_nearest with
    | .ok diff => if diff.operator_lt afterVault.lossUnrealized then result := false
    | .error _ => result := false
  if ltz afterVault.assetsTotal then result := false
  if ltz afterVault.assetsMaximum then result := false
  if st.beforeVault.isEmpty && tt != .vaultCreate then
    return false
  match st.beforeVault.head? with
  | some bv =>
    if !(afterVault.lossUnrealized.operator_eq bv.lossUnrealized)
        && tt != .loanManage && tt != .loanPay then
      result := false
  | none => pure ()
  let beforeShares : Option SharesSnap :=
    match st.beforeVault.head? with
    | some bv => findShares st.beforeMPTs bv.shareMPTID
    | none => none
  if beforeShares.isNone
      && (tt == .vaultDeposit || tt == .vaultWithdraw || tt == .vaultClawback) then
    return false
  -- per-transaction-type checks
  let caseResult : Bool :=
    match tt with
    | .vaultCreate => Id.run do
      let mut r := true
      if !st.beforeVault.isEmpty then r := false
      if nz afterVault.assetsAvailable || nz afterVault.assetsTotal
          || nz afterVault.lossUnrealized || us.sharesTotal != 0 then
        r := false
      if afterVault.pseudoId != us.share.getIssuer then r := false
      match (final.read (Keylet.account us.share.getIssuer)).bind (·.asAccountRoot) with
      | none => return false
      | some acct =>
        if !acct.isPseudoAccount then r := false
        match acct.vaultID with
        | some vid => if vid != afterVault.key then r := false
        | none => r := false
      return r
    | _ => true
  if !caseResult then result := false
  return result

end ValidVault

-- Faithful enforcement: run a transactor, and on success reject + revert when
-- the vault invariants do not hold (rippled maps this to tecINVARIANT_FAILED).
def applyTxChecked {α : Type} [Transactor α] (tx : α) (fee : XRPAmount)
    (initial : Ledger) (comp : ApplyView TER) : TER × Ledger :=
  match comp.run { ledger := initial } with
  | .ok (.tesSUCCESS, s) =>
    if ValidVault.finalize tx .tesSUCCESS fee s.ledger (ValidVault.collect initial s.ledger s.touched)
    then (.tesSUCCESS, s.ledger)
    else (.tecINVARIANT_FAILED, initial)
  | .ok (ter, _) => (ter, initial)
  | .error _ => (.tecINTERNAL, initial)

end XRPL.Model.tx
