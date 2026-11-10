import XRPL.Properties.Lending.Ledger.Common.VaultAccounting
import XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
import XRPL.Properties.Lending.Ledger.Common.LoanAccounting

/-! # Every field over a sequence of transactions

The vault, share, broker and loan parts of `Lending.Reachable.accounting` put together. -/

namespace XRPL.Model.Lending

/-- Proof body of `Lending.Reachable.accounting`. -/
lemma LendingLedger.accounting_proof {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    (start.NotCoarsenedAlong txs →
      l.vault.toRawVault.toExact.assetsTotal = start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs) ∧
    (start.NotCoarsenedAlong txs →
      l.vault.assetsAvailable.toRat = start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.amountToPool txs + start.defaultCovered txs +
        start.deletedPending txs) ∧
    l.vault.assetsDeployed.toRat = start.vault.assetsDeployed.toRat + start.lent txs - start.principalPaid txs -
      start.defaulted txs - start.deletedPending txs ∧
    l.vault.assetsReserved.toRat = start.vault.assetsReserved.toRat + start.lentPending txs - start.accepted txs -
      start.deletedPending txs ∧
    l.vault.lossUnrealized.toRat = start.vault.lossUnrealized.toRat + start.impaired txs - start.unimpaired txs ∧
    l.vault.yieldUnrealized.toRat = start.vault.yieldUnrealized.toRat + start.interestBooked txs -
      start.interestRemoved txs - start.interestDefaulted txs ∧
    (start.SharesFitAlong txs →
      l.vault.sharesTotal.toRat = start.vault.sharesTotal.toRat + start.sharesCreated txs - start.sharesRedeemed txs -
        start.sharesDestroyed txs) ∧
    (∀ (j : Nat) (b b' : LoanBroker), start.broker? j = some b → l.broker? j = some b' →
      b'.debtTotal.toRat = b.debtTotal.toRat + start.brokerLent j txs - start.brokerPrincipalPaid j txs -
        start.brokerDefaulted j txs - start.brokerDeletedPending j txs ∧
      (start.CoverNotCoarsenedAlong j txs →
        b'.coverAvailable.toRat = b.coverAvailable.toRat + start.coverDeposits j txs - start.coverWithdrawals j txs -
          start.coverClawbacks j txs + start.feesToCover j txs - start.brokerDefaultCovered j txs) ∧
      (b'.loanCount.toNat : ℚ) = b.loanCount.toNat + start.newLoans j txs - start.deletedLoans j txs) ∧
    (∀ (i : Nat) (loan loan' : Loan), start.LoanAt i loan → l.LoanAt i loan' →
      loan'.principalOutstanding.toRat =
          loan.principalOutstanding.toRat - start.loanPrincipalPaid i txs - start.defaultPrincipal i txs ∧
        loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat - start.scheduledValue i txs -
          start.overpaymentValue i txs - start.fullPaymentValue i txs - start.defaultValue i txs ∧
        loan'.managementFeeOutstanding.toRat = loan.managementFeeOutstanding.toRat - start.scheduledFee i txs -
          start.overpaymentFee i txs - start.fullPaymentFee i txs - start.defaultFee i txs ∧
        (loan'.paymentRemaining.toNat : ℚ) = loan.paymentRemaining.toNat - start.scheduledPayments i txs -
          start.fullPaymentPayments i txs - start.defaultPayments i txs) :=
  let v := LendingLedger.vault_accounting_proof hr hrun
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2, LendingLedger.shares_accounting_proof hr hrun,
    LendingLedger.broker_accounting_proof hr hrun, LendingLedger.loan_accounting_proof hr hrun⟩

end XRPL.Model.Lending
