import XRPL.Properties.Lending.Ledger.Common.BrokerSteps
import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Loan.Common.BrokerDebt
import XRPL.Properties.Lending.Loan.Common.PayMonotone

/-! # No new debt in the redemption phase

The redemption phase allows no LoanSet and no LoanAccept. Every other loan transaction pays down, impairs, unimpairs,
defaults or deletes a loan, and no other transaction adds debt, so no DebtTotal and no AssetsReserved goes up. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A management action never raises DebtTotal and keeps AssetsReserved. -/
lemma Loan.manage_debt (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) :
    r.loan'.broker.debtTotal.toRat ≤ loan.broker.debtTotal.toRat ∧ r.pool'.assetsReserved = v.assetsReserved := by
  cases action with
  | impair =>
    obtain ⟨hb, hr⟩ := Loan.manageImpair_debt loan v now r h
    exact ⟨by rw [hb], hr⟩
  | unimpair =>
    obtain ⟨hb, hr⟩ := Loan.manageUnimpair_debt loan v r h
    exact ⟨by rw [hb], hr⟩
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok
    exact Loan.manageDefault_debt loan v _ ‹_›

/-- What a loan transaction in the redemption phase writes: a broker with no more debt than the
ledger's copy, and no more AssetsReserved. -/
private lemma LendingLedger.applyLoan_redemption_debt (l : LendingLedger) (tx : LendingTx) (u : LoanEffect)
    (hred : l.vault.phase l.now = .redemption) (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    ∃ b, l.broker? u.brokerIndex = some b ∧ u.broker.debtTotal.toRat ≤ b.debtTotal.toRat ∧
      u.vault.assetsReserved.toRat ≤ l.vault.assetsReserved.toRat := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, -, hc, -⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with h | ⟨h, -⟩ <;> rw [hred] at h <;> cases h
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, -, -, -, hc, -⟩ := l.applyLoan_accept_inv u i hu
    exact (Loan.canAccept_not_redemption loan l.vault l.now hred hc).elim
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    obtain ⟨hd, har⟩ := Loan.manage_debt loan action l.vault l.now r hr
    exact ⟨broker, hb, hlb ▸ hd, le_of_eq (congrArg Number.toRat har)⟩
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    obtain ⟨hd, har⟩ := Loan.pay_debt loan l.vault paymentType amount l.now r hr
    exact ⟨broker, hb, hlb ▸ hd, le_of_eq (congrArg Number.toRat har)⟩
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    obtain ⟨hd, har⟩ := Loan.delete_debt loan l.vault r hr
    exact ⟨broker, hb, hlb ▸ hd, har⟩
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- In the redemption phase a transaction raises no DebtTotal and no AssetsReserved. -/
lemma LendingLedger.redemption_no_new_debt_proof (l l' : LendingLedger) (tx : LendingTx)
    (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l')) :
    (∀ (j : Nat) (b b' : LoanBroker), l.broker? j = some b → l'.broker? j = some b' →
      b'.debtTotal.toRat ≤ b.debtTotal.toRat) ∧ l'.vault.assetsReserved.toRat ≤ l.vault.assetsReserved.toRat := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).brokers = l.brokers ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    refine ⟨fun j b b' hb hb' => ?_, ?_⟩
    · unfold LendingLedger.broker? at hb'; rw [hrest.1] at hb'
      rw [show l.broker? j = (l.brokers[j]?).join from rfl, hb'] at hb; cases hb; exact le_refl _
    · rw [hrest.2, hk.assetsReserved]
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    refine ⟨fun j b b' hb hb' => ?_, le_refl _⟩
    rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj] at hb'
      have hlt : u.index < l.brokers.length := by
        by_contra hge
        rw [if_neg hge] at hj
        subst hj
        unfold LendingLedger.broker? at hb
        rw [List.getElem?_eq_none (le_refl _)] at hb
        cases hb
      rw [if_pos hlt] at hj
      subst hj
      rcases LendingLedger.applyBroker_debt l tx u hu b' hb' with h0 | ⟨b0, hb0, hd⟩
      · rw [h0, Number.toRat_zero]
        exact (b.exact.debtTotal_nonneg : 0 ≤ b.debtTotal.toRat)
      · rw [hb0] at hb; cases hb; rw [hd]
    · rw [if_neg hj] at hb'; rw [hb'] at hb; cases hb; exact le_refl _
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    obtain ⟨b0, hb0, hd, har⟩ := l.applyLoan_redemption_debt tx u hred hu
    refine ⟨fun j b b' hb hb' => ?_, har⟩
    rw [LendingLedger.broker?_commitLoan l u b0 hb0] at hb'
    split at hb'
    · subst_vars; rw [hb0] at hb; cases hb; cases hb'; exact hd
    · rw [hb'] at hb; cases hb; exact le_refl _
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨fun j b b' hb hb' => by rw [show ({ l with vaultDeleted := true } : LendingLedger).broker? j =
      l.broker? j from rfl, hb] at hb'; cases hb'; exact le_refl _, le_refl _⟩
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨fun j b b' hb hb' => by rw [show ({ l with now := max l.now _ } : LendingLedger).broker? j =
      l.broker? j from rfl, hb] at hb'; cases hb'; exact le_refl _, le_refl _⟩

end XRPL.Model.Lending
