import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayDue
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPaySettle
import XRPL.Properties.Lending.Ledger.Common.RecheckPay

/-! # A LoanPay never ends in a model error

A late payment on XRP needs its late interest to fit (FV_M4_53), and on XRP or an MPT the new vault total must fit
(FV_M4_59). An overpayment is covered only up to the amount due of the next instalment. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- Proof body of the LoanPay "never throws" theorem. -/
lemma LendingLedger.loanPay_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (pt : LoanPaymentType) (amount : Number)
    -- an overpayment pays at most the amount due of the next instalment, so nothing is left to re-amortize
    (hover : pt = .overpayment → ∀ loan pc td, l.LoanAt i loan → loan.paymentComponents .overpayment l.now = .ok pc →
      pc.totalDue = .ok td → amount.toRat ≤ td.toRat)
    -- a late payment on XRP: the late interest is two drops below the largest XRP amount (FV_M4_53)
    (hlate : l.vault.numericType = .native → pt = .late → ∀ loan, l.LoanAt i loan →
      loan.lateInterestExact l.now + 2 ≤ 10 ^ 17)
    -- a full payment on an IOU: the ClosePaymentFee is below `10^90`
    (hcfi : l.vault.numericType = .fractional → pt = .full → ∀ loan, l.LoanAt i loan →
      loan.fees.closePaymentFee.toRat < 10 ^ 90)
    -- the cover is a balance of the asset, and the fee fits beside it
    (hca : ∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 10 ^ 96)
    -- on XRP or an MPT the vault total after the payment is an amount of the asset (FV_M4_59)
    (hfit : l.CreditFits i pt amount) (hfee : l.FeeFits i pt amount)
    (hAA : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat < 10 ^ 88) :
    ∃ r, (l.apply (.loanPay i pt amount)).run = .ok r := by
  rcases hrun : (l.apply (.loanPay i pt amount)).run with e | r
  swap
  · exact ⟨r, rfl⟩
  exfalso
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error hrun
  simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte] at ha
  split at ha
  · cases ha
  have ha := TerExcept.map_error ha
  simp only [LendingLedger.applyLoan] at ha
  unfold_ter at ha
  walk_ok'
  · -- the stored loan takes the ledger's broker
    rename_i hwb
    obtain ⟨loan', hl'⟩ := Loan.withBroker_ok _ _ (hr.scaleInv.broker_asset ‹l.loan? i = _› ‹l.broker? _ = _›)
    rw [hl'] at hwb
    cases hwb
  · rename_i e' he _ b hb _ _ loan hw _ hc _ hpay
    have hat : l.LoanAt i loan := ⟨e', b, he, hb, hw⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    have hc' := (TER.isTesSuccess_iff _).mp hc
    have hnp : loan.isPending = false := by
      have hc'' := hc'
      unfold Loan.canPay at hc''
      cases hpend : loan.isPending
      · rfl
      · rw [hpend, ite_eq_left rfl] at hc''; cases hc''
    obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
    obtain ⟨-, hntl⟩ := hr.loanAt_scale hat
    have hroom : loan.PayRoom := hr.payRoom hat
    obtain ⟨hamtN, hamt0, hrep⟩ := LendingTx.loanPay_preflight_ok hpre
    have hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair l.vault).run = .ok (.ok r) :=
      fun himp => hr.manageUnimpair_ok hat himp
    have hpay' : (loan.pay l.vault pt amount l.now).run = .error e := by simp only [ExceptT.run]; exact hpay
    rcases hreach.pay_rejected_or_instalments hroom l.vault l.now pt amount hc' hamtN hamt0.le
        (by rw [hntl]; exact hrep) (fun hp pc td hpc htd => hover hp loan pc td hat hpc htd) hunimpair
        (fun hn hp => hlate (by rw [← hntl]; exact hn) hp loan hat)
        (fun hn hp => hcfi (by rw [← hntl]; exact hn) hp loan hat) with ⟨ter, hter⟩ | ⟨q, hq, hqF⟩
    · rw [hter] at hpay'
      cases hpay'
    · obtain rfl := hr.pay_settle_error hat pt amount q hq hqF (hca loan hat) hfit hfee hAA e hpay'
      exact LendingLedger.Reachable.pay_ne_notLawful_at hr hat hnp pt amount hpay'

end XRPL.Model.Lending
