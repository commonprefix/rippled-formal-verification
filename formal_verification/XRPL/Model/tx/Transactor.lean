import XRPL.Model.Ledger.ApplyView
import XRPL.Model.Protocol.LedgerEntries.Vault
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.XRPAmount
import XRPL.Model.Protocol.TER

-- import XRPL.Protocol.STTx
import XRPL.Model.Protocol.Asset
import XRPL.Model.Protocol.AccountID


namespace XRPL.Model.tx

open XRPL.Model.Ledger
open XRPL.Model.Protocol

inductive TxnType where
  | vaultCreate | vaultSet | vaultDeposit | vaultWithdraw | vaultClawback | vaultDelete
  | loanSet | loanManage | loanPay
  deriving DecidableEq, Repr, BEq

-- Mirrors the InvariantCheckPrivilege bits in transactions.macro: every vault
-- tx (and loanSet/loanPay) carries MustModifyVault; loanManage carries MayModifyVault.
def TxnType.mustModifyVault : TxnType → Bool
  | .loanManage => false
  | _ => true
def TxnType.mayModifyVault : TxnType → Bool
  | .loanManage => true
  | _ => false

class Transactor (α : Type) where
  txID : α → String
  account : α → AccountID
  preFeeBalance : α → XRPAmount
  txnType : α → TxnType
  amount : α → Option STAmount := fun _ => none
  destination : α → Option AccountID := fun _ => none
  holder : α → Option AccountID := fun _ => none
  delegate : α → Option AccountID := fun _ => none

structure PreflightContext (α : Type) [Transactor α] where
  tx : α

structure PreclaimContext (α : Type) [Transactor α] where
  tx : α

def validDataLength (slice : Option Blob) (maxLength : Nat) : Bool :=
  match slice with
  | none => true
  | some b => !b.isEmpty && b.length ≤ maxLength

end XRPL.Model.tx
