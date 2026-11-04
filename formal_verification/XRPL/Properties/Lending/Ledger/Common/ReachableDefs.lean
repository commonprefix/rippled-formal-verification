import XRPL.Properties.Lending.Ledger.Defs

/-! # Lending ledger reachability

`LendingLedger.Reaches start txs l` says the transactions `txs` applied in order take `start` to
`l`. Every reachability notion is built on it: `Reachable` from a new closed-ended vault, and
`ReachableBy allowed` when only the transactions `allowed` accepts are used. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultSchedule)

/-- `Reaches start txs l`: applying `txs` in order to `start` succeeds at every step and ends in `l`. -/
inductive LendingLedger.Reaches (start : LendingLedger) : List LendingTx → LendingLedger → Prop where
  | refl : LendingLedger.Reaches start [] start
  | step {txs : List LendingTx} {l l' : LendingLedger} (tx : LendingTx) :
      LendingLedger.Reaches start txs l → (l.apply tx).run = .ok (.ok l') →
      LendingLedger.Reaches start (txs ++ [tx]) l'

/-- A ledger whose closed-ended vault for an IOU, XRP or an MPT was just created by a VaultCreate that passed its
checks, with no holders, no brokers and no loans. -/
structure LendingLedger.Genesis (l : LendingLedger) : Prop where
  created : ∃ (scale : Option UInt8) (assetsMaximum : Option Number) (s : VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType),
      Vault.canCreate scale assetsMaximum (some s) l.now nt = .ok .tesSUCCESS ∧
      Vault.create scale assetsMaximum (some s) earlyExitFeeRate ownerCanBlockDeposit nt = .ok l.vault
  holds_asset : Vault.HoldsAsset l.vault
  no_holders : l.shares = []
  no_brokers : l.brokers = []
  no_loans : l.loans = []
  not_deleted : l.vaultDeleted = false

/-- Ledgers reachable from a new vault using only transactions `allowed` accepts. -/
def LendingLedger.ReachableBy (allowed : LendingTx → Prop) (l : LendingLedger) : Prop :=
  ∃ (genesis : LendingLedger) (txs : List LendingTx), genesis.Genesis ∧
    LendingLedger.Reaches genesis txs l ∧ ∀ tx ∈ txs, allowed tx

/-- Ledgers reachable from a new vault by any sequence of transactions. -/
def LendingLedger.Reachable (l : LendingLedger) : Prop :=
  LendingLedger.ReachableBy (fun _ => True) l

end XRPL.Model.Lending
