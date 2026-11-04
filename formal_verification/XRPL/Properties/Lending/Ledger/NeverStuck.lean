import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
import XRPL.Properties.Lending.Ledger.Common.PendingDelete
import XRPL.Properties.Lending.Ledger.Common.StuckLoan
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.AcceptTotal
import XRPL.Properties.Lending.Ledger.Common.IsolationWitness
import XRPL.Properties.Lending.Ledger.Common.LoanClosable
import XRPL.Properties.Lending.Ledger.Common.PaymentTotal
import XRPL.Properties.Lending.Ledger.Common.PaymentTotalWitness
import XRPL.Properties.Lending.Ledger.Common.ImpairedTotal
import XRPL.Properties.Lending.Ledger.Common.PayoffRun
import XRPL.Properties.Lending.Ledger.Common.PayoffStuckWitness
import XRPL.Properties.Lending.Loan.Common.PayoffLedger

/-! # Loans that can always move on

A pending loan can be deleted, a late loan impaired and a loan past its grace period defaulted. Witnesses for
the claims that fail: a reachable loan that no payment can pay. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

/-- Every loan can always move on -> it can be deleted, at once or after the grace period and a default, an active loan
past its grace period can be defaulted, and a pending loan can be accepted before its StartDate. -/
theorem Lending.Reachable.loan_resolvable (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) :
    -- a pending loan's principal fits beside AssetsAvailable. C++ ValidVault rejects the delete otherwise
    -- (FV_M4_22), and the model does not track the XRP and MPT supply
    ((e.loan.isPending = true → STAmount.Representable l.vault.numericType
        (l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat)) →
      -- for an active loan: the grace period ends before the last second the 32-bit ledger clock can show
      (e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
        e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < maxTime) →
      -- for an active loan, what the default below needs: the vault is not coarsened, where C++ can reject the
      -- transfer of the default (FV_M4_27), and the cover is an amount the broker holds
      (e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) →
      (e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
        ∀ b, l.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      ∃ (txs : List LendingTx) (l' l'' : LendingLedger), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, (∃ t, tx = .close t) ∨ tx = .loanManage i .default) ∧
        (l'.apply (.loanDelete i)).run = .ok (.ok l'')) ∧
    (e.loan.isPending = false → e.loan.isDefault = false → e.loan.paymentRemaining ≠ 0 →
      e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < l.now →
      -- the vault is not coarsened. There the cover a default pays the vault can turn negative, and C++ rejects its
      -- transfer (FV_M4_27), a step the model does not run
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      -- the broker holds its cover as an amount of the asset, a balance the model does not track
      (∀ b, l.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      ∃ l', (l.apply (.loanManage i .default)).run = .ok (.ok l')) ∧
    (e.loan.isPending = true → l.now < e.loan.schedule.startDate →
      -- the loan's interest still fits the Open limit. Accepting another pending loan can use up that room
      -- (Question FV_M4_33)
      (∀ x, e.loan.interestDue = .ok x → l.vault.exceedsOpenLimit x = .ok false) →
      ∃ l', (l.apply (.loanAccept i)).run = .ok (.ok l')) :=
  ⟨LendingLedger.loan_closable_proof l hr hnd i e he,
    fun hp hd hrem hlate htotal hca => LendingLedger.default_possible_proof l hr hnd hr.holdsAsset i e he hp hd hrem
      hlate htotal (hr.assetsAvailable_units hr.holdsAsset) hr.yield_lt (hr.interest_le_yield he hp) hca,
    LendingLedger.accept_before_start_proof l hr hnd i e he⟩

/-- Witness: a run where a pending loan can't be accepted before its StartDate. Two pending loans each fit the Open
limit, and once one is accepted and books its interest the other one exceeds it. -/
theorem Lending.Reachable.loan_resolvable_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.isPending = true ∧ l.now < e.loan.schedule.startDate ∧
      (l.apply (.loanAccept i)).run = .ok (.error .tecLIMIT_EXCEEDED) :=
  LendingLedger.accept_before_start_witness

/-- Loan transaction that passes its checks -> succeeds: a payment, an impair, a LoanAccept, and on an impaired loan
a LoanManage and a LoanDelete. -/
theorem Lending.loan_ops_total (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) :
    (∀ (b : LoanBroker) (loan : Loan) (pt : LoanPaymentType) (pc : PaymentComponents) (td amount : Number),
      l.broker? e.brokerIndex = some b → e.loan.withBroker b = .ok loan →
      loan.canPay pt = .tesSUCCESS → -- LoanPay preclaim
      -- a late payment exactly when the loan is late, and a full payment never for the last instalment
      (pt = .late ↔ loan.isPaymentLate l.now = true) → (pt = .full → loan.paymentRemaining ≠ 1) →
      loan.paymentComponents pt l.now = .ok pc → pc.totalDue = .ok td →
      -- the amount covers the amount due of the first instalment. The proof covers an overpayment only of exactly
      -- that amount
      td.toRat ≤ amount.toRat → (pt = .overpayment → amount = td) →
      (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS → -- LoanPay preflight
      -- the vault is not coarsened (the dust guard, FV_M4_21)
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      -- the payment has no negative interest part (FV_M4_29)
      (∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) →
      -- the vault gets principal or interest, or the loan is paid off (FV_M4_34)
      (∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
        0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) →
      -- an XRP loan owes less than 600 million XRP, the range of the proof
      (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) →
      -- the broker holds its cover as an amount of the asset, a balance the model does not track
      b.coverAvailable.toRat < 10 ^ 96 →
      -- the credit fits the XRP or MPT supply, and the fee fits beside the cover, which the model does not track
      l.CreditFits i pt amount → l.FeeFits i pt amount →
      -- the model does not run C++ LoanInvariant, which rejects a late payment that takes nothing off the loan
      -- (FV_M4_35)
      ∃ l', (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) ∧
    (e.loan.canManage .impair l.now = .tesSUCCESS → -- LoanManage preclaim
      e.loan.nextPaymentDueDate < l.now → -- an impair needs a late loan
      ∃ l', (l.apply (.loanManage i .impair)).run = .ok (.ok l')) ∧
    (e.loan.canAccept l.vault l.now = .ok .tesSUCCESS → -- LoanAccept preclaim
      ∃ l', (l.apply (.loanAccept i)).run = .ok (.ok l')) ∧
    (∀ (b : LoanBroker) (loan : Loan), l.broker? e.brokerIndex = some b → e.loan.withBroker b = .ok loan →
      e.loan.isImpaired = true →
      -- the vault is not coarsened, where C++ can reject the transfer of a default (FV_M4_27)
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      -- the broker holds its cover as an amount of the asset, a balance the model does not track
      b.coverAvailable.toRat < 10 ^ 96 →
      (∀ action, loan.canManage action l.now = .tesSUCCESS →
        ∃ l', (l.apply (.loanManage i action)).run = .ok (.ok l')) ∧
      (loan.canDelete = .tesSUCCESS → ∃ l', (l.apply (.loanDelete i)).run = .ok (.ok l'))) :=
  ⟨fun b loan pt pc td amount hb hw hc hlate hfull hpc htd hamt hover hpre htotal hparts hcredit hxrp hca hfit hfee =>
      LendingLedger.payment_total_proof l hr hnd i e b loan pt pc td amount he hb hw hc hlate hfull hpc htd hamt hover
        hpre htotal hparts hcredit hxrp hca hfit hfee,
    LendingLedger.impair_total_proof l hr hnd hr.holdsAsset.maxValue_le i e he,
    LendingLedger.accept_total_proof l hr hnd i e he,
    fun b loan hb hw himp htotal hca =>
      let h := LendingLedger.impaired_ops_total_proof l hr hnd i e b loan he hb hw himp htotal hca
      ⟨h.2.1, h.2.2.1⟩⟩

/-- Witness: a run on a coarsened vault where a payment that passes its checks fails. Loan C is late, and its late
payment of exactly totalDue rounds to no credit. -/
theorem Lending.loan_ops_total_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 2 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .late = .tesSUCCESS ∧ loan.isPaymentLate l.now = true ∧
        loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 2 .late td).preflight l = .tesSUCCESS ∧ l.CreditFits 2 .late td ∧
        l.FeeFits 2 .late td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        (∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) ∧
        (∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        (l.apply (.loanPay 2 .late td)).run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.payment_total_witness

/-- Witness: a run where a payment whose principal part is larger than its instalment fails. The third instalment of
a loan at a tiny rate has a negative interest part, so paying exactly its amount due fails with tecLIMIT_EXCEEDED. -/
theorem Lending.loan_ops_total_negative_interest_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 0 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .regular = .tesSUCCESS ∧
        loan.isPaymentLate l.now = false ∧ loan.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 0 .regular td).preflight l = .tesSUCCESS ∧ l.CreditFits 0 .regular td ∧
        l.FeeFits 0 .regular td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
        (∀ p, (loan.payInstalments l.vault .regular td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        (l.apply (.loanPay 0 .regular td)).run = .ok (.error .tecLIMIT_EXCEEDED) :=
  LendingLedger.payment_total_negative_interest_witness

/-- Witness: a run where a payment of an instalment that is only management fee fails. Instalment 9 of a loan of 2 at
45.5% in twelve yearly payments with a 10% management fee is only fee, so AssetsAvailable does not move. -/
theorem Lending.loan_ops_total_fee_only_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 0 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .regular = .tesSUCCESS ∧
        loan.isPaymentLate l.now = false ∧ loan.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 0 .regular td).preflight l = .tesSUCCESS ∧ l.CreditFits 0 .regular td ∧
        l.FeeFits 0 .regular td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
        (∀ p, (loan.payInstalments l.vault .regular td l.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (l.apply (.loanPay 0 .regular td)).run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.payment_total_fee_only_witness

/-- Every active loan -> it can be paid off, and when now ≤ NextPaymentDueDate one payment pays it off. At one close
time a late loan takes late payments and then regular ones, each of exactly the amount due of its next instalment. -/
theorem Lending.Reachable.payoff_reachable (l : LendingLedger) (hr : l.Reachable) (i : Nat) :
    (∀ e : LoanEntry, l.vaultDeleted = false → l.loan? i = some e → e.loan.isPending = false →
      -- InterestRate ≤ 80%, a PaymentInterval of at least two hours, or at most 25 years of payments, where
      -- principal is left while payments are left (`Loan.principal_left_proof`)
      Loan.FallingFactorTerms e.loan.rates e.loan.schedule →
      -- an XRP loan owes less than 300 million XRP, the range of the proof
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) →
      -- each next payment meets the conditions of `loan_ops_total`: not coarsened (FV_M4_21), no negative interest
      -- part (FV_M4_29), a credit or a payoff (FV_M4_34), the preflight, and a cover, credit and fee that fit
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        L.PaymentConditions i loan (loan.nextPaymentType L.now) td) →
      -- the model does not run C++ LoanInvariant, which rejects a late payment that takes nothing off the loan
      -- (FV_M4_35)
      ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0) ∧
    -- the loan is accepted and not paid off
    (∀ loan : Loan, l.LoanAt i loan → loan.canPay .regular = .tesSUCCESS → l.now ≤ loan.nextPaymentDueDate →
      -- IOU amounts below 10^80, the range of the proof
      (l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat +
        loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat < 10 ^ 80) →
      -- the XRP and MPT supply limit
      (l.vault.numericType.isIntegral = true →
        l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
          loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤ l.vault.numericType.maxValue.toNat ∧
        ∀ fi, loan.payoffInterest l.now = .ok fi →
          l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
            fi.toRat + loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤
            l.vault.numericType.maxValue.toNat) →
      ∃ (paymentType : LoanPaymentType) (amount : Number) (l' : LendingLedger) (loan' : Loan),
        (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l'.LoanAt i loan' ∧
          loan'.paymentRemaining = 0) :=
  ⟨fun e hnd he hp hterms hxrp hrun => LendingLedger.payoff_reachable_proof l hr hnd i e he hp hterms hxrp hrun,
    fun loan hat hactive hnl hroom hsupply =>
      LendingLedger.payoff_possible_proof l hr i loan hat hactive hnl hroom hsupply⟩

/-- Witness: a run on a coarsened vault where a late loan can't be paid off. Active loan C is late, and every payment
of any type and amount fails. -/
theorem Lending.Reachable.payoff_reachable_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 :=
  LendingLedger.payoff_reachable_witness

/-- Witness: a run where a late loan's principal part is larger than its instalment, and the loan can't be paid off.
A tiny-rate loan is late on its third instalment, and every payment of any type and amount fails. -/
theorem Lending.Reachable.payoff_reachable_negative_interest_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 :=
  LendingLedger.payoff_reachable_negative_interest_witness

/-- Witness: a run where a late loan's instalment is only management fee, and the loan can't be paid off. The loan
of 2 at 45.5% is late on instalment 9, and every payment of any type and amount fails. -/
theorem Lending.Reachable.payoff_reachable_fee_only_attained :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 :=
  LendingLedger.payoff_reachable_fee_only_witness

end XRPL.Model
