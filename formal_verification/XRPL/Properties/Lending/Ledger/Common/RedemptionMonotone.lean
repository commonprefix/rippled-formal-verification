import XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
import XRPL.Properties.Lending.Ledger.Common.VaultAccounting

/-! # Balances that never increase in the redemption phase

The redemption phase allows no LoanSet, no LoanAccept and no deposit that issues shares, and every payment is late.
So each transaction only takes principal, interest, loans and shares off the vault and the brokers. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault computeDeposit_donation_reduces computeClawback_amounts_form)

open private LendingLedger.LoanAt.loanRead from XRPL.Properties.Lending.Ledger.Common.VaultAccounting
open private LendingLedger.sharesTotal_step LendingLedger.holderShares_balance
  from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting

/-- In the redemption phase no LoanSet and no LoanAccept succeeds, so nothing is lent, booked or counted as a new
loan. -/
private lemma LendingLedger.redemption_no_create (l l' : LendingLedger) (tx : LendingTx)
    (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l')) :
    l.lentOf tx = 0 ∧ l.interestBookedOf tx = 0 ∧ ∀ j, l.newLoansOf j tx = 0 := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    exfalso
    obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl h
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨_, _, -, hc, -⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with h | ⟨h, -⟩ <;> rw [hred] at h <;> cases h
  | loanAccept i =>
    exfalso
    obtain ⟨-, loan, -, -, -, hc, -⟩ := LendingLedger.loanAccept_ok h
    exact Loan.canAccept_not_redemption loan l.vault l.now hred hc
  | _ => exact ⟨rfl, rfl, fun j => by simp [LendingLedger.newLoansOf]⟩

/-- A successful transaction takes at least zero principal off AssetsDeployed by a payment, a default or a delete. -/
private lemma LendingLedger.deployed_outflows_nonneg (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) :
    0 ≤ l.principalPaidOf tx ∧ 0 ≤ l.defaultedOf tx ∧ 0 ≤ l.deletedPendingOf tx := by
  cases tx with
  | loanPay i pt amount =>
    refine ⟨?_, le_refl _, le_refl _⟩
    obtain ⟨-, loan, -, -, hat, -⟩ := LendingLedger.loanPay_ok h
    simp only [LendingLedger.principalPaidOf, LendingLedger.LoanAt.loanRead hat]
    split
    · obtain ⟨-, h0, -⟩ := Loan.payInstalments_paidOn loan l.vault pt amount l.now _ (hr.loanScale_range hat)
        ‹_›
      exact h0
    · exact le_refl _
  | loanManage i action =>
    refine ⟨le_refl _, ?_, le_refl _⟩
    cases action with
    | default =>
      simp only [LendingLedger.defaultedOf]
      cases l.loanRead i with
      | none => exact le_refl _
      | some loan => exact loan.exact.principalOutstanding_nonneg
    | _ => exact le_refl _
  | loanDelete i =>
    refine ⟨le_refl _, le_refl _, ?_⟩
    simp only [LendingLedger.deletedPendingOf]
    cases l.loanRead i with
    | none => exact le_refl _
    | some loan =>
      dsimp only
      split
      · exact loan.exact.principalOutstanding_nonneg
      · exact le_refl _
  | _ => exact ⟨le_refl _, le_refl _, le_refl _⟩

/-- In the redemption phase a successful payment is a late payment, as every loan with payments left is late. -/
private lemma LendingLedger.redemption_pay_late {l : LendingLedger} (hr : l.Reachable)
    (hred : l.vault.phase l.now = .redemption) {i : Nat} {loan : Loan} (hat : l.LoanAt i loan)
    {pt : LoanPaymentType} {amount : Number} {r : LoanWithAmounts Vault}
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r)) : pt = .late := by
  obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  have hc := (Loan.payInstalments_ok loan l.vault pt amount l.now p hp).1
  obtain ⟨e, b, he, -, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hrem : e.loan.paymentRemaining ≠ 0 := by
    rw [show e.loan.paymentRemaining = loan.paymentRemaining from (congrArg RawLoan.paymentRemaining hraw :).symm]
    exact hc.remaining
  have hlate := LendingLedger.redemption_loans_late_proof l hr hred i e he hrem
  refine hc.date.mpr ?_
  rw [show loan.nextPaymentDueDate = e.loan.nextPaymentDueDate from (congrArg RawLoan.nextPaymentDueDate hraw :)]
  simpa [Loan.isPaymentLate] using hlate

/-- In the redemption phase a successful transaction takes at least zero interest off YieldUnrealized, when a late
payment with late interest takes at least zero interest off the loan. -/
private lemma LendingLedger.redemption_yield_outflows_nonneg (l l' : LendingLedger) (tx : LendingTx)
    (hr : l.Reachable) (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l'))
    (hlate : ∀ (i : Nat) (amount : Number) (loan : Loan) (pc : PaymentComponents) (d : Number),
      tx = .loanPay i .late amount → l.LoanAt i loan → loan.rates.lateInterestRate ≠ 0 →
      loan.paymentComponents .late l.now = .ok pc → pc.interestDelta = .ok d → 0 ≤ d.toRat) :
    0 ≤ l.interestRemovedOf tx ∧ 0 ≤ l.interestDefaultedOf tx := by
  cases tx with
  | loanPay i pt amount =>
    refine ⟨?_, le_refl _⟩
    obtain ⟨-, loan, r, -, hat, -, -, hok, -⟩ := LendingLedger.loanPay_ok h
    obtain rfl := LendingLedger.redemption_pay_late hr hred hat hok
    obtain ⟨hlo, hhi⟩ := hr.loanScale_range hat
    obtain ⟨t, -, hre⟩ := hr.loanAt_reachable hat
    have hle := Loan.pay_interestDue_le loan l.vault .late amount l.now r hlo (fun _ => hhi)
      (Loan.Reachable.interestDue_nonneg hre) (fun _ hne pc d hpc hd => hlate i amount loan pc d rfl hat hne hpc hd)
      (fun hpt => by cases hpt) hok
    simp only [LendingLedger.interestRemovedOf, LendingLedger.LoanAt.loanRead hat, hok]
    linarith
  | loanManage i action =>
    refine ⟨le_refl _, ?_⟩
    cases action with
    | default =>
      obtain ⟨-, loan, -, -, hat, -⟩ := LendingLedger.loanDefault_ok h
      obtain ⟨t, -, hre⟩ := hr.loanAt_reachable hat
      simp only [LendingLedger.interestDefaultedOf, LendingLedger.LoanAt.loanRead hat]
      exact Loan.Reachable.interestDue_nonneg hre
    | _ => exact le_refl _
  | _ => exact ⟨le_refl _, le_refl _⟩

/-- In the redemption phase no transaction issues shares: a deposit that is not a donation is refused, and a donation
issues none. -/
private lemma LendingLedger.redemption_sharesCreated (l : LendingLedger) (tx : LendingTx)
    (hred : l.vault.phase l.now = .redemption) : l.sharesCreatedOf tx = 0 := by
  cases tx with
  | vaultDeposit holder amount isDonation =>
    simp only [LendingLedger.sharesCreatedOf]
    split_ifs with hpos
    · cases isDonation with
      | false => rw [Vault.deposit_expired_proof l.vault amount l.now hpos (by rw [hred]; decide)]
      | true =>
        split
        · obtain ⟨_, amounts, -, -, hcomp, -, -, -, -, hrs⟩ := Vault.deposit_ok_reduces _ _ _ _ hpos _ ‹_›
          obtain ⟨-, hsh, -⟩ := computeDeposit_donation_reduces _ _ _ hcomp
          rw [hrs, hsh, STAmount.zero_toRat]
        · rfl
    · rfl
  | _ => rfl

/-- A successful transaction removes at least zero shares. -/
private lemma LendingLedger.sharesRemoved_nonneg (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) : 0 ≤ l.sharesRemovedOf tx := by
  have hpre := LendingLedger.apply_preflight h
  cases tx with
  | vaultWithdraw holder amount =>
    obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset holder amount hpre
    simp only [LendingLedger.sharesRemovedOf]
    split_ifs with hpos
    · split
      · have hwh := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
        exact (Vault.withdraw_shares_form _ _ _ _ hpos hc hty _ hwh).2.2.le
      · exact le_refl _
    · exact le_refl _
  | vaultClawback holder assets =>
    have hc := LendingTx.preflight_vaultClawback_canonical l hr.holdsAsset holder assets hpre
    simp only [LendingLedger.sharesRemovedOf]
    split_ifs with hnn
    · split
      · rename_i hs hof
        split
        · obtain ⟨amounts, -, hcomp, -, -, -, hrs⟩ := Vault.clawback_ok_reduces _ _ _ _ hnn _ ‹_›
          obtain ⟨hhs, -, -⟩ := LendingLedger.holderShares_balance l hr holder hs hof
          rw [hrs]
          exact (computeClawback_amounts_form _ _ _ _ _ hc hnn hhs hr.holdsAsset.maxValue_le hcomp).2.2.1
        · exact le_refl _
      · exact le_refl _
    · exact le_refl _
  | vaultBurnShares holder amount =>
    simp only [LendingLedger.sharesRemovedOf]
    split
    · exact (LendingLedger.holderShares_balance l hr holder _ ‹_›).2.2
    · exact le_refl _
  | _ => exact le_refl _

/-- Proof body of the never-increase line of `Lending.redemption_recovery`. -/
lemma LendingLedger.redemption_monotone_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l')) :
    (∀ (j : Nat) (b b' : LoanBroker), l.broker? j = some b → l'.broker? j = some b' →
      b'.debtTotal.toRat ≤ b.debtTotal.toRat ∧ b'.loanCount.toNat ≤ b.loanCount.toNat) ∧
      l'.vault.assetsDeployed.toRat ≤ l.vault.assetsDeployed.toRat ∧
      l'.vault.assetsReserved.toRat ≤ l.vault.assetsReserved.toRat ∧
      l'.vault.sharesTotal.toRat ≤ l.vault.sharesTotal.toRat ∧
      ((∀ (i : Nat) (amount : Number) (loan : Loan) (pc : PaymentComponents) (d : Number),
          tx = .loanPay i .late amount → l.LoanAt i loan → loan.rates.lateInterestRate ≠ 0 →
          loan.paymentComponents .late l.now = .ok pc → pc.interestDelta = .ok d → 0 ≤ d.toRat) →
        l'.vault.yieldUnrealized.toRat ≤ l.vault.yieldUnrealized.toRat) := by
  have hrun := LendingLedger.Reaches.single h
  obtain ⟨hlent, hbooked, hnew⟩ := l.redemption_no_create l' tx hred h
  obtain ⟨hdebt, hAR⟩ := LendingLedger.redemption_no_new_debt_proof l l' tx hred h
  obtain ⟨-, -, hAD, -, -, hYU⟩ := LendingLedger.vault_accounting_proof hr hrun
  simp only [LendingLedger.lent, LendingLedger.principalPaid, LendingLedger.defaulted, LendingLedger.deletedPending,
    LendingLedger.interestBooked, LendingLedger.interestRemoved, LendingLedger.interestDefaulted,
    LendingLedger.runSum, h, add_zero] at hAD hYU
  refine ⟨fun j b b' hb hb' => ⟨hdebt j b b' hb hb', ?_⟩, ?_, hAR, ?_, fun hlate => ?_⟩
  · -- a LoanDelete takes one loan off its broker and nothing adds one
    have hc := (LendingLedger.broker_accounting_proof hr hrun j b b' hb hb').2.2
    simp only [LendingLedger.newLoans, LendingLedger.deletedLoans, LendingLedger.runSum, h, add_zero, hnew] at hc
    have hd : 0 ≤ l.deletedLoansOf j tx := by
      unfold LendingLedger.deletedLoansOf
      split
      · split <;> norm_num
      · exact le_refl _
    exact_mod_cast (show (b'.loanCount.toNat : ℚ) ≤ b.loanCount.toNat by linarith)
  · obtain ⟨h1, h2, h3⟩ := l.deployed_outflows_nonneg l' tx hr h
    linarith
  · -- no deposit issues shares, so SharesTotal stays within the share MPT maximum
    have hcreated := l.redemption_sharesCreated tx hred
    have hST := LendingLedger.sharesTotal_step hr h (by rw [hcreated, add_zero]; exact l.vault.sharesTotal_le_maxRep)
    have hrem := l.sharesRemoved_nonneg l' tx hr h
    linarith
  · obtain ⟨h1, h2⟩ := l.redemption_yield_outflows_nonneg l' tx hr hred h hlate
    linarith

end XRPL.Model.Lending
