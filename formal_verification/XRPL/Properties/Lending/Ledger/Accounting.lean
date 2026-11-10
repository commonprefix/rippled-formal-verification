import XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
import XRPL.Properties.Lending.Ledger.Common.ShareValueWitness
import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalBoundWitness
import XRPL.Properties.Lending.Ledger.Common.SequenceAccounting
import XRPL.Properties.Lending.Ledger.Common.VaultAccountingWitness
import XRPL.Properties.Lending.Ledger.Common.BrokerAccountingWitness
import XRPL.Properties.Lending.Ledger.Common.ExtraInterestSum

/-! # Accounting over many transactions

Over any sequence of transactions every vault, broker and loan field moves only by the sums of what flowed in and out.
While the vault is not coarsened, only a default, a VaultWithdraw or a VaultClawback lowers AssetsTotal. Witnesses
for the claims that fail: a payment and a pending delete on a coarsened vault, a default on a coarsened cover. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

/-- Over any sequence of transactions from a reachable ledger -> every vault, broker and loan field = its start value
plus the sums of what moved in and out, minus the sums of what moved out. -/
theorem Lending.Reachable.accounting (start l : LendingLedger) (txs : List LendingTx) (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    -- AssetsTotal and AssetsAvailable: the vault is not coarsened before or after any step
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
    -- SharesTotal: the share supply limit, every deposit leaves SharesTotal at most 2^63 − 1
    (start.SharesFitAlong txs →
      l.vault.sharesTotal.toRat = start.vault.sharesTotal.toRat + start.sharesCreated txs - start.sharesRedeemed txs -
        start.sharesDestroyed txs) ∧
    -- a broker present before and after the sequence. CoverAvailable: its cover is not coarsened at any step
    (∀ (j : Nat) (b b' : LoanBroker), start.broker? j = some b → l.broker? j = some b' →
      b'.debtTotal.toRat = b.debtTotal.toRat + start.brokerLent j txs - start.brokerPrincipalPaid j txs -
        start.brokerDefaulted j txs - start.brokerDeletedPending j txs ∧
      (start.CoverNotCoarsenedAlong j txs →
        b'.coverAvailable.toRat = b.coverAvailable.toRat + start.coverDeposits j txs - start.coverWithdrawals j txs -
          start.coverClawbacks j txs + start.feesToCover j txs - start.brokerDefaultCovered j txs) ∧
      (b'.loanCount.toNat : ℚ) = b.loanCount.toNat + start.newLoans j txs - start.deletedLoans j txs) ∧
    -- a loan present before and after the sequence
    (∀ (i : Nat) (loan loan' : Loan), start.LoanAt i loan → l.LoanAt i loan' →
      loan'.principalOutstanding.toRat =
          loan.principalOutstanding.toRat - start.loanPrincipalPaid i txs - start.defaultPrincipal i txs ∧
        loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat - start.scheduledValue i txs -
          start.overpaymentValue i txs - start.fullPaymentValue i txs - start.defaultValue i txs ∧
        loan'.managementFeeOutstanding.toRat = loan.managementFeeOutstanding.toRat - start.scheduledFee i txs -
          start.overpaymentFee i txs - start.fullPaymentFee i txs - start.defaultFee i txs ∧
        (loan'.paymentRemaining.toNat : ℚ) = loan.paymentRemaining.toNat - start.scheduledPayments i txs -
          start.fullPaymentPayments i txs - start.defaultPayments i txs) :=
  LendingLedger.accounting_proof hr hrun

/-- Witness: a sequence where AssetsTotal' differs from the sums. On a coarsened vault a late instalment of 1.5
without interest is credited as 1, so AssetsTotal ends 0.5 below. -/
theorem Lending.Reachable.accounting_assetsTotal_attained :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.toRawVault.toExact.assetsTotal ≠ start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs :=
  LendingLedger.accounting_assetsTotal_witness

/-- Witness: a sequence where AssetsAvailable' differs from the sums. On a coarsened vault a LoanDelete of a pending
loan of 0.6 credits 1, so AssetsAvailable ends 0.4 above. -/
theorem Lending.Reachable.accounting_assetsAvailable_attained :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.assetsAvailable.toRat ≠ start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.amountToPool txs + start.defaultCovered txs +
        start.deletedPending txs :=
  LendingLedger.accounting_assetsAvailable_witness

/-- Witness: a sequence where CoverAvailable' differs from the sums. A default covering 1.0000000001 from a cover of
1000000000001 at the scale 10^-10 leaves 10^12. -/
theorem Lending.Reachable.accounting_coverAvailable_attained :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧ ∃ (j : Nat) (b b' : LoanBroker), start.broker? j = some b ∧
        l.broker? j = some b' ∧
        b'.coverAvailable.toRat ≠ b.coverAvailable.toRat + start.coverDeposits j txs -
          start.coverWithdrawals j txs - start.coverClawbacks j txs + start.feesToCover j txs -
          start.brokerDefaultCovered j txs :=
  LendingLedger.accounting_coverAvailable_witness

/-- Witness: runs past both sides. A coarsened pending delete and a withdrawal leave AssetsTotal' 4 ULP above
exactTotal, and a late payment that moves the scale from 10^-1 to 10^1 leaves it 1.99 ULP below. -/
theorem Lending.Reachable.assetsTotal_bounds_attained :
    (∃ (start l : LendingLedger) (txs : List LendingTx), start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      0 < l.vault.toRawVault.toExact.assetsTotal - (start.vault.toRawVault.toExact.assetsTotal +
        start.deposits txs - start.withdrawals txs - start.clawbacks txs + start.interestPaid txs -
        start.defaulted txs + start.defaultCovered txs)) ∧
    ∃ (start l : LendingLedger) (txs : List LendingTx) (total₀ total : Number) (e₀ e : Int),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧ txs.length = 1 ∧
      start.vault.assetsTotal = .ok total₀ ∧ l.vault.assetsTotal = .ok total ∧
      numberExponent total₀ start.vault.baseExponent start.vault.numericType = .ok e₀ ∧
      numberExponent total l.vault.baseExponent l.vault.numericType = .ok e ∧ e₀ < e ∧
      start.vault.toRawVault.toExact.assetsTotal + start.deposits txs - start.withdrawals txs - start.clawbacks txs +
        start.interestPaid txs - start.defaulted txs + start.defaultCovered txs -
        l.vault.toRawVault.toExact.assetsTotal = (199 / 100 : ℚ) * 10 ^ e := by
  refine ⟨?_, ?_⟩
  · obtain ⟨start, l, txs, _, _, _, hr, hrun, _, _, _, h⟩ := LendingLedger.assetsTotal_upper_bound_witness
    have hreach := hrun.reaches_sum.1
    obtain ⟨hd, hw, hc, hi, hdl⟩ := hreach.flows_eq
    refine ⟨start, l, txs, hr, hreach, ?_⟩
    rw [hd, hw, hc, hi, hdl] at h
    rw [show l.vault.toRawVault.toExact.assetsTotal - (start.vault.toRawVault.toExact.assetsTotal +
        start.deposits txs - start.withdrawals txs - start.clawbacks txs + start.interestPaid txs -
        start.defaulted txs + start.defaultCovered txs) = l.vault.toRawVault.toExact.assetsTotal -
        (start.vault.toRawVault.toExact.assetsTotal + start.deposits txs - start.withdrawals txs -
          start.clawbacks txs + start.interestPaid txs - (start.defaulted txs - start.defaultCovered txs)) by ring,
      h]
    positivity
  · obtain ⟨start, l, txs, _, total₀, total, e₀, e, hr, hrun, hlen, ht₀, ht, he₀, he, hlt, h⟩ :=
      LendingLedger.assetsTotal_lower_bound_witness
    have hreach := hrun.reaches_sum.1
    obtain ⟨hd, hw, hc, hi, hdl⟩ := hreach.flows_eq
    rw [hd, hw, hc, hi, hdl] at h
    exact ⟨start, l, txs, total₀, total, e₀, e, hr, hreach, hlen, ht₀, ht, he₀, he, hlt, by linarith⟩

/-- Over any sequence of transactions from a reachable ledger -> AssetsTotal decreases only through VaultWithdraw,
VaultClawback or a default. -/
theorem Lending.Reachable.no_loss_without_default (start l : LendingLedger) (txs : List LendingTx)
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l)
    (hout : ∀ tx ∈ txs, tx.isOutflow = false) -- no default, VaultWithdraw or VaultClawback
    -- the vault is not coarsened before or after any step of the sequence
    (hnc : start.NotCoarsenedAlong txs) :
    start.vault.toRawVault.toExact.assetsTotal ≤ l.vault.toRawVault.toExact.assetsTotal :=
  LendingLedger.no_loss_without_default_proof start l txs _ hr hrun.reachableFromIn_sum hout
    fun pre l₁ _ hp h₁ => hnc pre l₁ hp h₁.reaches_sum.1

/-- Witness: a run where a payment lowers AssetsTotal. On a coarsened vault an instalment of 1.5 without
interest is credited as 1. -/
theorem Lending.Reachable.no_loss_without_default_attained :
    ∃ (start l : LendingLedger) (txs : List LendingTx), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧ (∀ tx ∈ txs, tx.isOutflow = false) ∧
      ¬ start.vault.toRawVault.toExact.assetsTotal ≤ l.vault.toRawVault.toExact.assetsTotal :=
  let ⟨l, l', hr, hok, hlt⟩ := LendingLedger.payment_lowers_assetsTotal_reachable
  ⟨l, l', [.loanPay 3 .late ⟨false, 1500000000000000000, -18⟩], hr, .step _ .refl hok,
    by simp [LendingTx.isOutflow], not_le.mpr hlt⟩

end XRPL.Model
