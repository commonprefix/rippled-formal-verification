import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Ledger.Common.InvestmentLock
import XRPL.Properties.Lending.Ledger.Common.RedemptionDefaultWitness
import XRPL.Properties.Lending.Ledger.Common.RedemptionDebt
import XRPL.Properties.Lending.Ledger.Common.RedemptionMonotone
import XRPL.Properties.Lending.Ledger.Common.RedemptionRecovery
import XRPL.Properties.Lending.Ledger.Common.SubscriptionInv
import XRPL.Properties.Lending.Loan.Common.LifetimeWitness

/-! # Vault phases on the lending ledger

Until SubscriptionDate nothing is lent. Every loan matures at least 60 seconds before RedemptionDate, so in the
redemption phase every loan with payments left is late, and past its grace period passes the default time check. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault VaultSchedule)

variable (l : LendingLedger) (j : Nat) (e : LoanEntry)

/-- Subscription -> no loans, every DebtTotal = 0 and LoanCount = 0, AssetsTotal = AssetsAvailable, and
AssetsDeployed = LossUnrealized = AssetsReserved = YieldUnrealized = 0. -/
theorem Lending.Reachable.subscription_no_loans (hr : l.Reachable) (hsub : l.vault.phase l.now = .subscription) :
    (∀ j, l.loan? j = none) ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.debtTotal = Number.zero ∧ b.loanCount = 0) ∧
      l.vault.assetsTotal = .ok l.vault.assetsAvailable ∧ l.vault.assetsDeployed = Number.zero ∧
      l.vault.lossUnrealized = Number.zero ∧ l.vault.assetsReserved = Number.zero ∧
      l.vault.yieldUnrealized = Number.zero :=
  LendingLedger.subscription_no_loans_proof l hr hsub

/-- Every loan's last due date is at least 60 seconds before RedemptionDate. -/
theorem Lending.Reachable.loans_mature (hr : l.Reachable) (s : VaultSchedule) (hs : l.vault.schedule = some s)
    (he : l.loan? j = some e) :
    e.loan.schedule.startDate.toNat + e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat +
      loanRedemptionBuffer ≤ s.redemptionDate.toNat :=
  LendingLedger.loans_mature_proof l hr s hs j e he

/-- Investment, on a vault that is not coarsened -> AssetsAvailable decreases only through a loan transaction, a
withdrawal, which needs an early-exit fee rate, or a clawback. -/
theorem Lending.investment_lock (l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hinv : l.vault.phase l.now = .investment) (hnc : l.NotCoarsened) (h : (l.apply tx).run = .ok (.ok l'))
    (hdec : l'.vault.assetsAvailable.toRat < l.vault.assetsAvailable.toRat) :
    tx.isLoan = true ∨
      (∃ holder amount, tx = .vaultWithdraw holder amount ∧ l.vault.earlyExitFeeRate.isSome = true) ∨
      ∃ holder assets, tx = .vaultClawback holder assets :=
  LendingLedger.investment_lock_proof l l' tx hr hinv hnc h hdec

/-- Redemption -> DebtTotal, LoanCount, AssetsDeployed, AssetsReserved, SharesTotal and YieldUnrealized never increase,
and AssetsAvailable increases only through a loan payment, a default, deleting a pending loan, or a donation. -/
theorem Lending.redemption_recovery (l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l')) :
    ((∀ (j : Nat) (b b' : LoanBroker), l.broker? j = some b → l'.broker? j = some b' →
      b'.debtTotal.toRat ≤ b.debtTotal.toRat ∧ b'.loanCount.toNat ≤ b.loanCount.toNat) ∧
      l'.vault.assetsDeployed.toRat ≤ l.vault.assetsDeployed.toRat ∧
      l'.vault.assetsReserved.toRat ≤ l.vault.assetsReserved.toRat ∧
      l'.vault.sharesTotal.toRat ≤ l.vault.sharesTotal.toRat ∧
      -- a late payment with late interest takes nonnegative interest off the loan (FV_M4_30)
      ((∀ (i : Nat) (amount : Number) (loan : Loan) (pc : PaymentComponents) (d : Number),
          tx = .loanPay i .late amount → l.LoanAt i loan → loan.rates.lateInterestRate ≠ 0 →
          loan.paymentComponents .late l.now = .ok pc → pc.interestDelta = .ok d → 0 ≤ d.toRat) →
        l'.vault.yieldUnrealized.toRat ≤ l.vault.yieldUnrealized.toRat)) ∧
    (l.vault.assetsAvailable.toRat < l'.vault.assetsAvailable.toRat →
      (∃ i paymentType amount, tx = .loanPay i paymentType amount) ∨ (∃ i, tx = .loanManage i .default) ∨
        (∃ i e, tx = .loanDelete i ∧ l.loan? i = some e ∧ e.loan.isPending = true) ∨
        (∃ holder amount, tx = .vaultDeposit holder amount true)) :=
  ⟨LendingLedger.redemption_monotone_proof l l' tx hr hred h,
    LendingLedger.redemption_recovery_proof l l' tx hr hr.holdsAsset.maxValue_le hred h⟩

/-- Witness: a run where a late payment raises YieldUnrealized. In the redemption phase a late payment at a 100%
LateInterestRate covers an instalment's interest part of −3.24, so YieldUnrealized rises by 3.24. -/
theorem Lending.redemption_recovery_attained :
    ∃ (l l' : LendingLedger) (tx : LendingTx), l.Reachable ∧ l.vault.phase l.now = .redemption ∧
      (l.apply tx).run = .ok (.ok l') ∧ l.vault.yieldUnrealized.toRat < l'.vault.yieldUnrealized.toRat :=
  LendingLedger.redemption_yield_witness

/-- Redemption, loan with payments left -> when NextPaymentDueDate < now, then only a late payment can pay it, and
when now > RedemptionDate + GracePeriod, then now > NextPaymentDueDate + GracePeriod. -/
theorem Lending.Reachable.redemption_loans_late (hr : l.Reachable) (hred : l.vault.phase l.now = .redemption)
    (he : l.loan? j = some e) (hp : e.loan.paymentRemaining ≠ 0) :
    e.loan.isPaymentLate l.now = true ∧
      ∀ s : VaultSchedule, l.vault.schedule = some s →
        s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat →
        e.loan.nextPaymentDueDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat :=
  ⟨LendingLedger.redemption_loans_late_proof l hr hred j e he hp,
    fun s hs ht => LendingLedger.redemption_defaultable_proof l hr s hs j e he hp ht⟩

/-- Witness: a run where a loan with a payment left can't be defaulted yet in the redemption phase. Its payment is
due 60 seconds before RedemptionDate and its GracePeriod is longer, so the default returns tecTOO_SOON. -/
theorem Lending.Reachable.redemption_loans_late_attained :
    ∃ (l : LendingLedger) (j : Nat) (e : LoanEntry) (s : VaultSchedule), l.Reachable ∧
      l.vault.phase l.now = .redemption ∧ l.loan? j = some e ∧ e.loan.paymentRemaining ≠ 0 ∧
      l.vault.schedule = some s ∧ s.redemptionDate.toNat < l.now.toNat ∧
      l.now.toNat ≤ e.loan.nextPaymentDueDate.toNat + e.loan.schedule.gracePeriod.toNat ∧
      (l.apply (.loanManage j .default)).run = .ok (.error .tecTOO_SOON) :=
  LendingLedger.redemption_default_witness

end XRPL.Model
