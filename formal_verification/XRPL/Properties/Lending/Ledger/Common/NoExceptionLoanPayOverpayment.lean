import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPay
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayOverpaymentTail

/-! # A LoanPay of any type never ends in a model error

Extends `LendingLedger.loanPay_no_exception_proof` to the whole overpayment tail. On XRP the re-amortization needs a
bound on the payments left and the value owed, a range of this proof and not a known exception. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.payScheduledInstalments UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private PaymentAmounts.zero_norm from XRPL.Properties.Lending.Loan.Common.PayBounds
open private STAmount.representable_lt from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPaySettle

set_option maxHeartbeats 800000 in
-- one proof takes the overpayment from the ledger through the instalment loop, the tail and the settlement
/-- Proof body of the LoanPay "never throws" theorem for every payment type. -/
lemma LendingLedger.loanPay_no_exception_full_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (pt : LoanPaymentType) (amount : Number)
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
    (hAA : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat < 10 ^ 88)
    -- an overpayment on XRP: the re-amortized total value is an XRP amount (a range of this proof)
    (hxrp : l.vault.numericType = .native → pt = .overpayment → ∀ loan, l.LoanAt i loan →
      20 * ((loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat) +
        16 * loan.totalValueOutstanding.toRat + 100 ≤ 10 ^ 17) :
    ∃ r, (l.apply (.loanPay i pt amount)).run = .ok r := by
  by_cases hpt : pt = .overpayment
  swap
  · exact LendingLedger.loanPay_no_exception_proof l hr i pt amount (fun h => absurd h hpt) hlate hcfi hca hfit
      hfee hAA
  subst hpt
  rcases hrun : (l.apply (.loanPay i .overpayment amount)).run with e | r
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
    have hpay' : (loan.pay l.vault .overpayment amount l.now).run = .error e := by
      simp only [ExceptT.run]; exact hpay
    have hnotLawful := LendingLedger.Reachable.pay_ne_notLawful_at hr hat hnp .overpayment amount
    obtain ⟨-, hrem, hpo⟩ := Loan.canPay_active hc'
    have hdd := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hreach hrem

    -- the checks and the first instalment
    by_cases hl : loan.nextPaymentDueDate < l.now
    · have h1 : (loan.pay l.vault .overpayment amount l.now).run = .ok (.error .tecEXPIRED) :=
        Loan.overpayment_late_proof loan l.vault amount l.now hrem hpo (fun _ => hdd) hl
      rw [h1] at hpay'
      cases hpay'
    have hnl : loan.isPaymentLate l.now = false := by simp [Loan.isPaymentLate, hl]
    have hchecks : loan.PayChecks .overpayment l.now :=
      ⟨hrem, hpo, hdd, ⟨nofun, fun h => absurd h hl⟩, nofun⟩
    obtain ⟨pc, td, hpc, htd, htdN⟩ := hroom.regularDue_computes l.now hrem
    have hpc' : loan.paymentComponents .overpayment l.now = .ok pc := hpc
    by_cases hlt : amount.operator_lt td = true
    · rw [Loan.payment_insufficient_proof loan l.vault amount l.now .overpayment pc td hchecks hunimpair hpc' htd
        hlt] at hpay'
      cases hpay'
    have hge := (Number.operator_lt_eq_false_iff amount td hamtN htdN).mp (by simpa using hlt)

    -- the scheduled instalments, and what the loop leaves
    obtain ⟨q, hq, -, -, -⟩ := Loan.regularPayInstalments_due_room loan hroom l.vault l.now
      (Loan.canPay_regular_of_overpayment hc') hdd hnl hunimpair pc td amount hpc htd hamtN hge
    obtain ⟨si, -, hloop, hcount⟩ := Loan.payScheduled_loop loan l.vault amount l.now q hq
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now q hq
    obtain ⟨hbT, -, -, -, -⟩ := Loan.payInstalments_below loan l.vault .regular amount l.now q hq
    obtain ⟨-, hcnt, -, -⟩ := UnsettledPayment.payInstalments_count _ _ _ _ hloop
    obtain ⟨p', hp', -, ht0, -, htN, hqN, hqP, hqI, hqF, hqc, hqpp, hqroom⟩ :=
      UnsettledPayment.payInstalments_bounds_room amount maxPaymentsPerTransaction
        { loan := loan.unimpaired, pool := q.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
          count := 0, scheduledInterest := si }
        hroom.unimpaired (by simp [maxPaymentsPerTransaction]) Number.zero_isNormalized
        (by simp [Number.toRat_zero]) PaymentAmounts.zero_norm (by simp [PaymentAmounts.zero, Number.toRat_zero])
        (by simp [PaymentAmounts.zero, Number.toRat_zero]) (by simp [PaymentAmounts.zero, Number.toRat_zero])
        (by simp [PaymentAmounts.zero, Number.toRat_zero])
    rw [hloop] at hp'
    obtain rfl := Except.ok.inj hp'
    simp only [Number.toRat_zero] at ht0
    simp only [zero_add] at hqc hcnt
    have hqpp' : q.loan.periodicPayment = loan.periodicPayment := hqpp
    have hqb : q.loan.broker = loan.broker := hst.broker
    have hqs : q.loan.loanScale = loan.loanScale := hst.loanScale
    have hpp0 : 0 ≤ loan.periodicPayment.toRat := loan.exact.periodicPayment_pos.le
    have hT0q : 0 ≤ q.loan.totalValueOutstanding.toRat := q.loan.exact.totalValueOutstanding_nonneg
    have hTle := hroom.value
    have hc100 : (q.count : ℚ) ≤ 100 := by
      have : q.count ≤ 100 := by simpa [maxPaymentsPerTransaction] using hqc
      exact_mod_cast this
    have hb102 : (q.count : ℚ) * (2 * 10 ^ 99) ≤ 10 ^ 102 := by nlinarith
    -- the payments left after the loop are fewer than before it
    have hnle : (q.loan.paymentRemaining.toNat : ℚ) ≤ loan.paymentRemaining.toNat := by
      have hu : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
      rw [hu] at hcnt
      have : q.loan.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat := by omega
      exact_mod_cast this
    have hB : q.loan.paymentRemaining ≠ 0 →
        (q.loan.paymentRemaining.toNat : ℚ) * q.loan.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1) := by
      intro hq0
      have hu : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
      rw [hu] at hcnt
      have hqn : q.loan.paymentRemaining.toNat ≠ 0 := fun h0 => hq0 (UInt32.toNat_inj.mp (by simpa using h0))
      have h2 : 2 ≤ loan.paymentRemaining.toNat := by omega
      have := hroom.payments h2
      rw [hqpp']
      nlinarith
    have hamt97 : amount.toRat < 10 ^ 97 := STAmount.representable_lt _ _ hamtN hamt0.le hrep

    -- the overpayment tail ends in a payment, or the payment fails its loan re-check
    have hq' : Loan.payScheduledInstalments loan l.vault amount l.now = .ok (.ok q) := hq
    rcases happ : UnsettledPayment.applyOverpayment q amount with ea | p2
    · obtain rfl := UnsettledPayment.applyOverpayment_error q amount hamtN hamt0.le hamt97
        (by rw [hqb, hntl]; exact hrep) (by rw [hqb]; exact hroom.asset)
        (by rw [hqs]; exact hreach.loanScale_facts.1) (by rw [hqs]; exact hroom.scale)
        (by rw [hqb, hqs]; exact hreach.loanScale_integral) (by linarith) hqroom hB htN ht0 hqN (by linarith)
        (by linarith) (by linarith)
        (fun hn _ => by
          have hx := hxrp (by rw [← hntl, ← hqb]; exact hn) rfl loan hat
          rw [hqpp']
          nlinarith) ea happ
      apply hnotLawful
      rw [Loan.pay_run]
      simp only [Loan.payInstalments]
      unfold_ter
      simp [hq', happ]
    have hp2 : (loan.payInstalments l.vault .overpayment amount l.now).run = .ok (.ok p2) := by
      simp only [Loan.payInstalments]
      unfold_ter
      simp [hq', happ]

    -- the settlement
    by_cases hneg : p2.amounts.feePaid.signum < 0
    · rw [Loan.payment_negative_part_proof loan l.vault amount l.now .overpayment p2 hp2
        (Or.inr (Or.inr hneg))] at hpay'
      cases hpay'
    obtain ⟨-, -, hfN⟩ := Loan.payInstalments_norm loan l.vault amount l.now .overpayment p2 hp2
    have hF2 : 0 ≤ p2.amounts.feePaid.toRat := (Number.signum_nonneg_iff_toRat hfN).mp (not_lt.mp hneg)
    obtain rfl := hr.pay_settle_error hat .overpayment amount p2 hp2 hF2 (hca loan hat) hfit hfee hAA e hpay'
    exact hnotLawful hpay'

end XRPL.Model.Lending
