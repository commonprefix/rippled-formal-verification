import XRPL.Properties.Lending.Ledger.Common.PaymentTotal
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.ClosedLoans

/-! # Every transaction on an impaired loan that passes its checks succeeds

An impaired loan is active. Its LoanAccept and impair never pass their checks, its unimpair succeeds, its default
succeeds while the vault is not coarsened, its LoanDelete passes only once no payment is left and then succeeds, and
its payment is a payment of `loan_ops_total`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private LendingLedger.apply_manage_ok from XRPL.Properties.Lending.Ledger.Common.ManageTotal

/-- Every transaction on an impaired loan that passes its checks succeeds. The impaired-loan line of
`Lending.loan_ops_total` reads its LoanManage and LoanDelete parts. -/
lemma LendingLedger.impaired_ops_total_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (b : LoanBroker) (loan : Loan) (he : l.loan? i = some e)
    (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan) (himp : e.loan.isImpaired = true)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hca : b.coverAvailable.toRat < 10 ^ 96) :
    (loan.canAccept l.vault l.now = .ok .tesSUCCESS → ∃ l', (l.apply (.loanAccept i)).run = .ok (.ok l')) ∧
    (∀ action, loan.canManage action l.now = .ok .tesSUCCESS →
      ∃ l', (l.apply (.loanManage i action)).run = .ok (.ok l')) ∧
    (loan.canDelete = .tesSUCCESS → ∃ l', (l.apply (.loanDelete i)).run = .ok (.ok l')) ∧
    (∀ (pt : LoanPaymentType) (pc : PaymentComponents) (td amount : Number), loan.canPay pt = .tesSUCCESS →
      (pt = .late ↔ loan.isPaymentLate l.now = true) → (pt = .full → loan.paymentRemaining ≠ 1) →
      loan.paymentComponents pt l.now = .ok pc → pc.totalDue = .ok td → td.toRat ≤ amount.toRat →
      (pt = .overpayment → amount = td) → (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS →
      (∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) →
      (∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
        0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) →
      (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) →
      l.CreditFits i pt amount → l.FeeFits i pt amount →
      ∃ l', (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) := by
  have hraw := Loan.withBroker_eq hw
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hnp : e.loan.isPending = false := by
    cases h : e.loan.isPending
    · rfl
    · rw [hr.lossInv.active i e he h] at himp; cases himp
  have hnp' : loan.isPending = false := by rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw]; exact hnp
  have himp' : loan.isImpaired = true := by
    rw [show loan.isImpaired = loan.toRawLoan.isImpaired from rfl, hraw]; exact himp
  refine ⟨fun hc => ?_, fun action hc => ?_, fun hc => ?_, fun pt pc td amount hc hlate hfull hpc htd hamt hover hpre
    hparts hcredit hxrp hfit hfee => LendingLedger.payment_total_proof l hr hnd i e b loan pt pc td amount he hb hw hc
      hlate hfull hpc htd hamt hover hpre htotal hparts hcredit hxrp hca hfit hfee⟩
  · -- LoanAccept takes only a pending loan
    unfold Loan.canAccept at hc
    simp [hnp'] at hc
  · cases action with
    | impair =>
      -- an impaired loan can't be impaired again
      unfold Loan.canManage at hc
      simp [hnp', himp'] at hc
    | unimpair =>
      obtain ⟨r, hrun⟩ := hr.manageUnimpair_ok hat himp'
      exact ⟨_, LendingLedger.apply_manage_ok l hnd i e b loan .unimpair r he hb hw hc hrun⟩
    | default =>
      -- the checks of a default read the loan only
      have hc' : e.loan.canManage .default l.now = .ok .tesSUCCESS := by
        have : loan.canManage .default l.now = e.loan.canManage .default l.now := by
          unfold Loan.canManage; rw [hraw]
        rw [← this]; exact hc
      unfold Loan.canManage at hc'
      cases hd : e.loan.isDefault
      · have hrem : e.loan.paymentRemaining ≠ 0 := by
          intro h0
          simp [hnp, hd, h0] at hc'
        have hlate : e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < l.now := by
          by_contra hn
          simp [hnp, hd, hrem, hn, UInt32.addChecked_of_lt e.loan.gracePeriodEnd_lt, bind, Except.bind] at hc'
        exact LendingLedger.default_possible_proof l hr hnd hr.holdsAsset i e he hnp hd hrem hlate htotal
          (hr.assetsAvailable_units hr.holdsAsset) hr.yield_lt (hr.interest_le_yield he hnp)
          (fun b' hb' => by rw [hb] at hb'; obtain rfl := Option.some.inj hb'; exact hca)
      · simp [hnp, hd] at hc'
  · -- LoanDelete takes an active loan only once no payment is left
    have hrem : e.loan.paymentRemaining = 0 := by
      unfold Loan.canDelete at hc
      have hpr : loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
      by_contra h0
      have : 0 < loan.paymentRemaining := by
        rw [hpr]; exact UInt32.pos_iff_ne_zero.mpr h0
      simp [hnp', this] at hc
    exact LendingLedger.closed_loan_deletable l hr hnd i e he hrem hnp

end XRPL.Model.Lending
