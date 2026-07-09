import XRPL.Model.Protocol.AccountID
import XRPL.Model.Protocol.Digest
import XRPL.Model.Protocol.UintTypes
import XRPL.Model.Basics.Blob

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace XRPL.Model.Protocol

inductive LedgerNameSpace where
  | account | trustLine | mptIssuance | mpToken | credential
  | depositPreauth | depositPreauthCreds | vault | loanBroker | loan
  | permissionedDomain
  deriving DecidableEq, Repr

def LedgerNameSpace.toUInt16 : LedgerNameSpace → UInt16
  | .account             => 'a'.toNat.toUInt16
  | .trustLine           => 'r'.toNat.toUInt16
  | .mptIssuance         => '~'.toNat.toUInt16
  | .mpToken             => 't'.toNat.toUInt16
  | .credential          => 'D'.toNat.toUInt16
  | .depositPreauth      => 'p'.toNat.toUInt16
  | .depositPreauthCreds => 'P'.toNat.toUInt16
  | .vault               => 'V'.toNat.toUInt16
  | .loanBroker          => 'l'.toNat.toUInt16
  | .loan                => 'L'.toNat.toUInt16
  | .permissionedDomain  => 'm'.toNat.toUInt16

def serU16 (x : UInt16) : ByteArray := natToBytesBE 2 x.toNat
def serU32 (x : UInt32) : ByteArray := natToBytesBE 4 x.toNat
def serU64 (x : UInt64) : ByteArray := natToBytesBE 8 x.toNat
def serUInt256 (x : UInt256) : ByteArray := bitVecToBytes x
def serAccountID (id : AccountID) : ByteArray := bitVecToBytes id.val
def serCurrency (c : Currency) : ByteArray := bitVecToBytes c.val
def serMPTID (m : MPTID) : ByteArray := bitVecToBytes m.val
def serBlob (b : Blob) : ByteArray := ⟨b.toArray⟩

def indexHash (space : LedgerNameSpace) (payload : ByteArray) : UInt256 :=
  sha512Half (serU16 space.toUInt16 ++ payload)

-- Lexicographic byte order for blobs, matching std::lexicographical_compare.
def blobLt : Blob → Blob → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then blobLt as bs else a < b


end XRPL.Model.Protocol
