import XRPL.Model.Ledger.ReadView


namespace XRPL.Model.Ledger

open XRPL.Model.Protocol

-- The mutating apply state: the ledger plus the set of keys touched by
-- insert/update/erase (mirrors rippled's apply dirty-set, including
-- identical-content rewrites). The invariant checker consumes `touched`.
structure ApplyState where
  ledger : Ledger
  touched : List UInt256 := []

abbrev ApplyView := StateT ApplyState (Except String)

def ApplyState.read (s : ApplyState) (k : Keylet) : Option LedgerEntry := s.ledger.read k
def ApplyState.readUnchecked (s : ApplyState) (key : UInt256) : Option LedgerEntry := s.ledger.readUnchecked key
def ApplyState.fees (s : ApplyState) : Fees := s.ledger.fees
def ApplyState.parentCloseTime (s : ApplyState) : NetClock.TimePoint := s.ledger.parentCloseTime

def ApplyView.peek (k : Keylet) : ApplyView (Option LedgerEntry) := return (← get).read k

def ApplyView.insert (e : LedgerEntry) : ApplyView Unit := do
  let s ← get
  if (s.read ⟨e.type, e.key⟩).isSome then
    throw "ApplyView.insert: entry already exists"
  set { s with ledger := s.ledger.put e, touched := e.key :: s.touched }
def ApplyView.update (e : LedgerEntry) : ApplyView Unit := do
  let s ← get
  if (s.read ⟨e.type, e.key⟩).isNone then
    throw "ApplyView.update: entry not present"
  set { s with ledger := s.ledger.put e, touched := e.key :: s.touched }
def ApplyView.erase (k : Keylet) : ApplyView Unit := do
  let s ← get
  if (s.read k).isNone then
    throw "ApplyView.erase: entry not present"
  set { s with ledger := s.ledger.remove k.key, touched := k.key :: s.touched }

-- Run a read-only computation against the ledger component.
def ApplyView.ofReadView {α : Type} (x : ReadView α) : ApplyView α := do
  match x.run (← get).ledger with
  | .ok a => return a
  | .error e => throw e

def ApplyView.openStub : ApplyView Bool := pure false
def ApplyView.dirLinkStub {α : Type} (_owner : AccountID) (_object : α) : ApplyView TER := pure .tesSUCCESS
def ApplyView.dirRemoveStub (_owner : AccountID) (_page : UInt64) (_key : UInt256) (_keepRoot : Bool) : ApplyView Bool := pure true
def ApplyView.dirInsertStub (_owner : AccountID) (_key : UInt256) : ApplyView (Option UInt64) := pure (some 0)
def adjustOwnerCountHookStub (_id : AccountID) (_cur _next : UInt32) : ApplyView Unit := pure ()
def creditHookIOUStub (_from _to : AccountID) (_amount _preCreditBalance : STAmount) : ApplyView Unit := pure ()
def creditHookMPTStub (_from _to : AccountID) (_amount : STAmount)
    (_preCreditBalanceHolder : UInt64) (_preCreditBalanceIssuer : Int64) : ApplyView Unit := pure ()
def ownerCountHookStub (_id : AccountID) (count : UInt32) : UInt32 := count
def balanceHookIOUStub (_account _issuer : AccountID) (amount : STAmount) : STAmount := amount
def balanceHookMPTStub (_account : AccountID) (issue : MPTIssue) (amount : Int64)
    : Except String STAmount :=
  -- integral at offset 0: canonicalize exact, mode inert
  STAmount.ofInt64 (.mptIssue issue) amount 0 .to_nearest

def applyTx (initial : Ledger) (computation : ApplyView TER) : TER × Ledger :=
  match computation.run { ledger := initial } with
  | .ok (.tesSUCCESS, s) => (.tesSUCCESS, s.ledger)
  | .ok (ter, _)         => (ter, initial)
  | .error _             => (.tecINTERNAL, initial)

-- Like `applyTx` but also surfaces the touched-key set. Mirrors `applyTx`:
-- mutations are kept only on `tesSUCCESS`; any other result reverts to `initial`
-- (and yields no touched keys), matching rippled discarding the apply view.
def applyTxTouched (initial : Ledger) (computation : ApplyView TER)
    : TER × Ledger × List UInt256 :=
  match computation.run { ledger := initial } with
  | .ok (.tesSUCCESS, s) => (.tesSUCCESS, s.ledger, s.touched)
  | .ok (ter, _)         => (ter, initial, [])
  | .error _             => (.tecINTERNAL, initial, [])

end XRPL.Model.Ledger
