import XRPL.Properties.Lending.Ledger.Common.VaultAccountingDefs

/-! # What each transaction moves in or out of SharesTotal and one broker

Each `…Of` reads one amount off the operation a transaction runs on the ledger `l`, and is zero for every other
kind of transaction. The broker amounts count only the transactions on broker `j`: its own cover transactions, a
LoanSet on it and the transactions on its loans. The sum of the same name adds the amount up along a sequence of
transactions, each read on the ledger it runs on. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The shares a VaultDeposit creates. -/
def LendingLedger.sharesCreatedOf (l : LendingLedger) : LendingTx → ℚ
  | .vaultDeposit _ amount isDonation =>
    if hpos : 0 < amount.toRat then
      match (l.vault.deposit amount isDonation l.now hpos).run with
      | .ok (.ok r) => r.shares.toRat
      | _ => 0
    else 0
  | _ => 0

/-- The shares a VaultWithdraw, a VaultClawback or a burn destroys. A burn destroys all the holder's shares. -/
def LendingLedger.sharesRemovedOf (l : LendingLedger) : LendingTx → ℚ
  | .vaultWithdraw h amount =>
    if hpos : 0 < amount.amount.toRat then
      match (l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some (l.sharesOf h))).run with
      | .ok (.ok r) => r.shares.toRat
      | _ => 0
    else 0
  | .vaultClawback h assets =>
    if hnn : 0 ≤ assets.toRat then
      match STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest with
      | .ok holderShares =>
        match (l.vault.clawback assets holderShares (l.isSoleShareholder h) hnn).run with
        | .ok (.ok r) => r.shares.toRat
        | _ => 0
      | .error _ => 0
    else 0
  | .vaultBurnShares h _ =>
    match STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest with
    | .ok holderShares => holderShares.toRat
    | .error _ => 0
  | _ => 0

/-- The loan transaction `tx` is on broker `j`: a LoanSet on it, or a transaction on one of its loans. -/
def LendingLedger.onBroker (l : LendingLedger) (j : Nat) : LendingTx → Bool
  | .loanSet i .. => i == j
  | .loanAccept i | .loanDelete i | .loanManage i _ | .loanPay i .. => (l.loan? i).any (·.brokerIndex == j)
  | _ => false

/-- PrincipalRequested of a new loan on broker `j`. -/
def LendingLedger.brokerLentOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then l.lentOf tx else 0

/-- The principal a LoanPay on a loan of broker `j` pays. -/
def LendingLedger.brokerPrincipalPaidOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then l.principalPaidOf tx else 0

/-- PrincipalOutstanding of a loan of broker `j` that a default writes off. -/
def LendingLedger.brokerDefaultedOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then l.defaultedOf tx else 0

/-- PrincipalOutstanding of a loan of broker `j` that a LoanDelete deletes while it is still pending. -/
def LendingLedger.brokerDeletedPendingOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then l.deletedPendingOf tx else 0

/-- The cover a default of a loan of broker `j` moves from the broker to the vault. -/
def LendingLedger.brokerDefaultCoveredOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then l.defaultCoveredOf tx else 0

/-- The cover a LoanBrokerCoverDeposit on broker `j` adds, the amount rounded down to the cover's grid. -/
def LendingLedger.coverDepositsOf (l : LendingLedger) (j : Nat) : LendingTx → ℚ
  | .loanBrokerCoverDeposit i amount =>
    if i = j then
      match l.broker? j with
      | some b =>
        match (b.coverDeposit l.vault amount).run with
        | .ok (.ok r) => r.amount'.toRat
        | _ => 0
      | none => 0
    else 0
  | _ => 0

/-- The cover a LoanBrokerCoverWithdraw on broker `j` takes out, the amount rounded to the cover's grid. -/
def LendingLedger.coverWithdrawalsOf (l : LendingLedger) (j : Nat) : LendingTx → ℚ
  | .loanBrokerCoverWithdraw i amount =>
    if i = j then
      match l.broker? j with
      | some b =>
        match (b.coverWithdraw l.vault amount).run with
        | .ok (.ok r) => r.amount'.toRat
        | _ => 0
      | none => 0
    else 0
  | _ => 0

/-- The cover a LoanBrokerCoverClawback on broker `j` takes out, capped to keep the minimum cover. -/
def LendingLedger.coverClawbacksOf (l : LendingLedger) (j : Nat) : LendingTx → ℚ
  | .loanBrokerCoverClawback i amount =>
    if i = j then
      match l.broker? j with
      | some b =>
        match (b.coverClawback l.vault amount).run with
        | .ok (.ok r) => r.amount'.toRat
        | _ => 0
      | none => 0
    else 0
  | _ => 0

/-- feePaid of a LoanPay on a loan of broker `j` while the broker's cover is below its minimum. The payment adds
that fee to the cover. -/
def LendingLedger.feesToCoverOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then
    match tx with
    | .loanPay i pt amount =>
      match l.loanRead i with
      | some loan =>
        match loan.broker.hasMinimumCover l.vault.baseExponent, (loan.payInstalments l.vault pt amount l.now).run with
        | .ok false, .ok (.ok p) => p.amounts.feePaid.toRat
        | _, _ => 0
      | none => 0
    | _ => 0
  else 0

/-- One for a LoanSet on broker `j`. -/
def LendingLedger.newLoansOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then
    match tx with
    | .loanSet .. => 1
    | _ => 0
  else 0

/-- One for a LoanDelete of a loan of broker `j`. -/
def LendingLedger.deletedLoansOf (l : LendingLedger) (j : Nat) (tx : LendingTx) : ℚ :=
  if l.onBroker j tx then
    match tx with
    | .loanDelete _ => 1
    | _ => 0
  else 0

/-- The shares a VaultWithdraw redeems. -/
def LendingLedger.sharesRedeemedOf (l : LendingLedger) (tx : LendingTx) : ℚ :=
  match tx with
  | .vaultWithdraw .. => l.sharesRemovedOf tx
  | _ => 0

/-- The shares a VaultClawback or a burn destroys. A burn destroys all the holder's shares. -/
def LendingLedger.sharesDestroyedOf (l : LendingLedger) (tx : LendingTx) : ℚ :=
  match tx with
  | .vaultClawback .. | .vaultBurnShares .. => l.sharesRemovedOf tx
  | _ => 0

/-- The shares a transaction removes are the shares it redeems plus the shares it destroys. -/
lemma LendingLedger.sharesRemovedOf_eq (l : LendingLedger) (tx : LendingTx) :
    l.sharesRemovedOf tx = l.sharesRedeemedOf tx + l.sharesDestroyedOf tx := by
  cases tx <;> simp [LendingLedger.sharesRedeemedOf, LendingLedger.sharesDestroyedOf, LendingLedger.sharesRemovedOf]

/-- Σ sharesCreated over the transactions `txs` applied in order from `l`. -/
def LendingLedger.sharesCreated (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.sharesCreatedOf txs

/-- Σ sharesRedeemed over the transactions `txs` applied in order from `l`. -/
def LendingLedger.sharesRedeemed (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.sharesRedeemedOf txs

/-- Σ sharesDestroyed over the transactions `txs` applied in order from `l`. -/
def LendingLedger.sharesDestroyed (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.sharesDestroyedOf txs

/-- Σ lent on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.brokerLent (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.brokerLentOf j) txs

/-- Σ principalPaid on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.brokerPrincipalPaid (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.brokerPrincipalPaidOf j) txs

/-- Σ defaulted on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.brokerDefaulted (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.brokerDefaultedOf j) txs

/-- Σ deletedPending on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.brokerDeletedPending (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.brokerDeletedPendingOf j) txs

/-- Σ defaultCovered on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.brokerDefaultCovered (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.brokerDefaultCoveredOf j) txs

/-- Σ coverDeposits on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.coverDeposits (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.coverDepositsOf j) txs

/-- Σ coverWithdrawals on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.coverWithdrawals (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.coverWithdrawalsOf j) txs

/-- Σ coverClawbacks on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.coverClawbacks (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.coverClawbacksOf j) txs

/-- Σ feesToCover on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.feesToCover (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.feesToCoverOf j) txs

/-- The number of new loans on broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.newLoans (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.newLoansOf j) txs

/-- The number of deleted loans of broker `j` over the transactions `txs` applied in order from `l`. -/
def LendingLedger.deletedLoans (l : LendingLedger) (j : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ => l₀.deletedLoansOf j) txs

/-- Every VaultDeposit along the transactions `txs` from `start` keeps SharesTotal plus the shares it issues within
the share MPT maximum `2^63 − 1`, which C++ accountSend enforces and the model does not run. -/
def LendingLedger.SharesFitAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre l → l.vault.sharesTotal.toRat + l.sharesCreatedOf tx ≤ 2 ^ 63 - 1

/-- Broker `j`'s cover is never coarsened along `txs` from `start`: before each step its CoverAvailable plus what the
step pays in (a deposit, a fee, or a default's cover that rounds below zero) stays below `10^16` base units. -/
def LendingLedger.CoverNotCoarsenedAlong (start : LendingLedger) (j : Nat) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger) (tx : LendingTx) (b : LoanBroker), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre l → l.broker? j = some b →
    b.coverAvailable.toRat + l.coverDepositsOf j tx + l.feesToCoverOf j tx < 10 ^ 16 * 10 ^ l.vault.baseExponent ∧
      b.coverAvailable.toRat - l.brokerDefaultCoveredOf j tx < 10 ^ 16 * 10 ^ l.vault.baseExponent

end XRPL.Model.Lending
