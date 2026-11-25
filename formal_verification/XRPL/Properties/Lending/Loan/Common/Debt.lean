import XRPL.Properties.Lending.Loan.Common.LoanCount
import XRPL.Properties.Lending.Loan.Common.PayPrincipal

/-! # What loan operations do to DebtTotal and AssetsDeployed

A LoanSet adds the principal to both, a default and a pending delete take PrincipalOutstanding off both,
and a payment takes the principal it pays off both. A delete of the broker's last loan zeroes DebtTotal. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A new loan adds PrincipalRequested to DebtTotal and AssetsDeployed. -/
lemma Loan.create_debtStep (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    broker.debtTotal.operator_add principal .to_nearest = .ok r.loan'.broker.debtTotal ∧
      v.assetsDeployed.operator_add principal .to_nearest = .ok r.pool'.assetsDeployed := by
  obtain ⟨_, _, debtTotal', _, broker', aa', ad', lu', ar', yu', hchecks, -, hsums, hpool, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  refine ⟨?_, ?_⟩
  · have hd : r.loan'.broker.debtTotal = debtTotal' := by
      show r.loan'.toRawLoan.broker.toRawLoanBroker.debtTotal = _; rw [hl]
      show broker'.toRawLoanBroker.debtTotal = _; rw [hb]
    rw [hd]; exact hchecks.debt
  · rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hpool]
    exact hsums.deployed

/-- A default takes PrincipalOutstanding off DebtTotal and AssetsDeployed, and leaves the loan with none. -/
lemma Loan.manageDefault_debtStep (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok r.loan'.broker.debtTotal ∧
      v.assetsDeployed.operator_add loan.principalOutstanding.operator_neg .to_nearest =
        .ok r.pool'.assetsDeployed ∧ r.loan'.principalOutstanding = Number.zero := by
  obtain ⟨_, d, _, raw, b, -, -, hadj, hraw, hdebt, -, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  refine ⟨?_, ?_, ?_⟩
  · have hd : r.loan'.broker.debtTotal = d := by
      rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]
      show b.toRawLoanBroker.debtTotal = _
      rw [hb]; rfl
    rw [hd]; exact hdebt
  · rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw, heq]
    exact hs.deployed
  · show r.loan'.toRawLoan.principalOutstanding = _; rw [hloan]; rfl

/-- Releasing a loan sets DebtTotal to the given value, or to zero with the broker's last loan. -/
private lemma LoanBroker.releaseLoan_debtTotal (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.debtTotal = if lb.loanCount - 1 == 0 then Number.zero else d := by
  unfold LoanBroker.releaseLoan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i _ hc
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
  exact (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok h).1 :)

/-- A delete's DebtTotal and AssetsDeployed. A pending loan takes PrincipalOutstanding off both, an active
one leaves the vault, and the broker's last loan zeroes DebtTotal. -/
lemma Loan.delete_debtStep (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) :
    (loan.isPending = true →
      v.assetsDeployed.operator_add loan.principalOutstanding.operator_neg .to_nearest =
          .ok r.pool'.assetsDeployed ∧
        ∃ d, loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok d ∧
          r.broker'.debtTotal = if loan.broker.loanCount - 1 == 0 then Number.zero else d) ∧
      (loan.isPending = false → r.pool' = v ∧
        r.broker'.debtTotal = if loan.broker.loanCount - 1 == 0 then Number.zero else loan.broker.debtTotal) := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨principal', raw, d, -, hadj, hv', hdebt, hrel⟩ := Loan.delete_pending_ok_inv loan v r hp h
    obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
    refine ⟨?_, d, hdebt, LoanBroker.releaseLoan_debtTotal _ _ _ hrel⟩
    rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl,
      (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1, heq]
    exact hs.deployed
  · refine ⟨Loan.delete_active_vault loan v r hp h, ?_⟩
    simp only [Loan.delete] at h
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact LoanBroker.releaseLoan_debtTotal _ _ _ ‹Loan.deleteActive _ = Except.ok _›

end XRPL.Model.Lending
