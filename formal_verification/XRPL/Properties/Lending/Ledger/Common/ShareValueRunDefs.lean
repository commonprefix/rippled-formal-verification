import XRPL.Properties.Lending.Ledger.Common.BrokerAccountingDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositDefs

/-! # shareValue over a sequence of transactions

The conditions of the sequence row on shareValue = (AssetsTotal − LossUnrealized) / SharesTotal. Each one is read on
every ledger the sequence passes through, like `NotCoarsenedAlong`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The transactions that can lower shareValue: an impair, the default of a loan that is not impaired, and a
VaultWithdraw or VaultClawback of the only holder. -/
def LendingLedger.lowersShareValue (l : LendingLedger) : LendingTx → Bool
  | .loanManage _ .impair => true
  | .loanManage i .default => (l.loan? i).any (!·.loan.isImpaired)
  | .vaultWithdraw h _ | .vaultClawback h _ => l.isSoleShareholder h
  | _ => false

/-- No transaction of `txs` from `start` is one of those that can lower shareValue, each read on the ledger it
runs on. -/
def LendingLedger.KeepsShareValueAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre l → l.lowersShareValue tx = false

/-- SharesTotal is not zero on any ledger the transactions `txs` pass through from `start`, the first and the last
included. -/
def LendingLedger.SharesLeftAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger), pre <+: txs → LendingLedger.Reaches start pre l →
    l.vault.sharesTotal ≠ Number.zero

/-- The shares a VaultDeposit issues, or a VaultWithdraw or VaultClawback removes, are worth a whole number of base
units on `l`. A donation issues no shares, and nothing is asked of any other transaction. -/
def LendingLedger.movesWholeWorth (l : LendingLedger) (tx : LendingTx) : Prop :=
  match tx with
  | .vaultDeposit _ _ false =>
    ∃ k : ℤ, l.vault.idealChargeDeposit (l.sharesCreatedOf tx) = k * 10 ^ l.vault.baseExponent
  | .vaultWithdraw h _ | .vaultClawback h _ =>
    ∃ k : ℤ, l.vault.idealAssetsWithdraw (l.isSoleShareholder h) (l.sharesRemovedOf tx) =
      k * 10 ^ l.vault.baseExponent
  | _ => True

/-- Every VaultDeposit, VaultWithdraw and VaultClawback of `txs` from `start` moves shares worth a whole number of
base units, each read on the ledger it runs on. -/
def LendingLedger.WholeWorthAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre l → l.movesWholeWorth tx

end XRPL.Model.Lending
