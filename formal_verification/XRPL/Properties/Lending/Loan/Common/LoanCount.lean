import XRPL.Properties.Lending.Loan.Common.BrokerDebt
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # What loan operations do to the broker's LoanCount

A LoanSet adds one to LoanCount, a delete takes one off, and every other loan operation keeps it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A new loan adds one to its broker's LoanCount. The count never wraps, because a broker without
loans has no debt. -/
lemma Loan.create_loanCount (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (h : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.loan'.broker.loanCount.toNat = broker.loanCount.toNat + 1 := by
  obtain ⟨_, _, d, _, b, hc, -, -, hb, hloan⟩ := Loan.create_ok_inv _ _ _ _ _ _ _ _ r h
  have hbr : r.loan'.broker = b := (congrArg RawLoan.broker (RawLoan.to_lawful_ok hloan).1 :)
  have hraw := (RawLoanBroker.to_lawful_ok hb).1
  have hcount : b.loanCount = broker.loanCount + 1 := (congrArg RawLoanBroker.loanCount hraw :)
  have hdebt : b.debtTotal = d := (congrArg RawLoanBroker.debtTotal hraw :)
  rw [hbr, hcount, UInt32.toNat_add]
  by_cases hlt : broker.loanCount.toNat + 1 < 2 ^ 32
  · rw [show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt]
  · -- a wrapped count is zero, so the new broker would hold no debt
    exfalso
    have hzero : b.loanCount = 0 := by
      apply UInt32.toNat_inj.mp
      rw [hcount, UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
      have := broker.loanCount.toNat_lt
      rw [show broker.loanCount.toNat + 1 = 2 ^ 32 by omega]
      rfl
    have hd0 := b.valid.empty_broker hzero
    rw [hdebt] at hd0
    have hge := operator_add_ge_of_ge_normalized broker.debtTotal principal d principal broker.wf.debtTotal_norm
      hp hc.debt hp (by
        have : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
        linarith)
    rw [hd0, Number.toRat_zero] at hge
    linarith

/-- A default keeps the broker's LoanCount. -/
lemma Loan.manageDefault_loanCount (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : r.loan'.broker.loanCount = loan.broker.loanCount := by
  obtain ⟨_, d, c, raw, b, -, -, -, -, -, -, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  have hbr : r.loan'.broker = b := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]; rfl
  rw [hbr, show b.loanCount = b.toRawLoanBroker.loanCount from rfl, hb]
  rfl

/-- Releasing a loan takes one off LoanCount. -/
private lemma LoanBroker.releaseLoan_loanCount (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.loanCount = lb.loanCount - 1 := by
  unfold LoanBroker.releaseLoan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i _ hc
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
  exact (congrArg RawLoanBroker.loanCount (RawLoanBroker.to_lawful_ok h).1 :)

/-- A delete takes one off the broker's LoanCount. -/
lemma Loan.delete_loanCount (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : r.broker'.loanCount = loan.broker.loanCount - 1 := by
  by_cases hp : loan.isPending = true
  · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan v r hp h
    exact LoanBroker.releaseLoan_loanCount _ _ _ hrel
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact LoanBroker.releaseLoan_loanCount _ _ _ ‹Loan.deleteActive _ = Except.ok _›

end XRPL.Model.Lending
