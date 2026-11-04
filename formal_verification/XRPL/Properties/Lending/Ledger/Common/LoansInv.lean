import XRPL.Properties.Lending.Ledger.Common.ScaleInv
import XRPL.Properties.Lending.Loan.Common.Schedule
import XRPL.Properties.Lending.Loan.Common.SetPhase

/-! # The loans of a reachable ledger

Every stored loan is a reachable loan, as of a close time no later than the ledger's, the vault keeps
its schedule, and every loan's last payment is due at least 60 seconds before RedemptionDate. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- Taking the ledger's copy of the broker, of the same asset, keeps a loan reachable. -/
lemma Loan.Reachable.withBroker {loan loan' : Loan} {t : UInt32} {broker : LoanBroker} (hr : loan.Reachable t)
    (hnt : broker.numericType = loan.broker.numericType) (h : loan.withBroker broker = .ok loan') :
    loan'.Reachable t := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  exact ⟨start, t₀, hc, .refresh _ _ _ broker hr hnt h⟩

/-- The ledger's copy of a stored loan's broker has the loan's asset. -/
lemma LendingLedger.ScaleInv.broker_asset {l : LendingLedger} (hscale : l.ScaleInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some broker) :
    broker.numericType = e.loan.broker.numericType :=
  (hscale.brokers _ broker hb).trans (hscale.loanBroker i e he).symm

/-- A management action that passed its check keeps a loan reachable. -/
lemma Loan.Reachable.manage {loan : Loan} {t t' : UInt32} (hr : loan.Reachable t) (hle : t ≤ t')
    (action : LoanManageAction) (v : Vault) (r : LoanWithPool Vault)
    (hc : loan.canManage action t' = .tesSUCCESS) (h : (loan.manage action v t').run = .ok (.ok r)) :
    r.loan'.Reachable t' := by
  obtain ⟨start, t₀, hcr, hr⟩ := hr
  refine ⟨start, t₀, hcr, ?_⟩
  cases action with
  | impair => exact .impair _ _ _ _ _ hr hle hc h
  | unimpair => exact .unimpair _ _ _ _ _ hr hle hc h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok
    exact .default _ _ _ _ _ hr hle hc ‹_›

/-- A payment that passed its check keeps a loan reachable. -/
lemma Loan.Reachable.pay {loan : Loan} {t t' : UInt32} (hr : loan.Reachable t) (hle : t ≤ t')
    (paymentType : LoanPaymentType) (v : Vault) (amount : Number) (r : LoanWithAmounts Vault)
    (hc : loan.canPay paymentType = .tesSUCCESS) (h : (loan.pay v paymentType amount t').run = .ok (.ok r)) :
    r.loan'.Reachable t' := by
  obtain ⟨start, t₀, hcr, hr⟩ := hr
  refine ⟨start, t₀, hcr, ?_⟩
  cases paymentType with
  | regular => exact .regularPayment _ _ _ _ _ _ hr hle hc h
  | late => exact .latePayment _ _ _ _ _ _ hr hle hc h
  | full => exact .fullPayment _ _ _ _ _ _ hr hle hc h
  | overpayment => exact .overpayment _ _ _ _ _ _ hr hle hc h
/-- What every reachable ledger keeps about its loans: the vault keeps its schedule, every stored loan is
reachable by the ledger's close time, and its last payment is due at least 60 seconds before RedemptionDate. -/
structure LendingLedger.LoansInv (l : LendingLedger) (s : VaultSchedule) : Prop where
  schedule : l.vault.schedule = some s
  reachable : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → ∃ t, t ≤ l.now ∧ e.loan.Reachable t
  mature : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e →
    e.loan.schedule.startDate.toNat + e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat +
      loanRedemptionBuffer ≤ s.redemptionDate.toNat

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.LoansInv.loan_step {l : LendingLedger} {s : VaultSchedule} (hinv : l.LoansInv s)
    (hscale : l.ScaleInv) {tx : LendingTx} {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).LoansInv s := by
  have hs := l.applyLoan_keepsSettings tx u hu
  have hnew : ∀ e', u.loan = some e' → e'.loan.Reachable l.now ∧
      e'.loan.schedule.startDate.toNat + e'.loan.schedule.paymentInterval.toNat * e'.loan.schedule.paymentTotal.toNat +
        loanRedemptionBuffer ≤ s.redemptionDate.toNat := by
    intro e' he'
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      simp only [LoanEffect.ofCreate, Option.some.injEq] at he'
      subst he'
      refine ⟨⟨r.loan', l.now, ⟨broker, l.vault, principal, rates, fees, pi, pt, gp, sd, twoStep, ao, r, hc, hcr,
        rfl⟩, .refl⟩, ?_⟩
      obtain ⟨_, _, _, _, _, -, -, -, -, hloan⟩ := Loan.create_ok_inv _ _ _ _ _ _ _ _ r hcr
      have hsch := (congrArg RawLoan.schedule (RawLoan.to_lawful_ok hloan).1 :)
      dsimp only at hsch ⊢
      rw [hsch]
      rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with hph | ⟨_, hfit⟩
      · simp only [XRPL.Model.SingleAssetVault.Vault.phase, hinv.schedule, ge_iff_le] at hph
        split at hph <;> [skip; split at hph] <;> cases hph
      · exact hfit s hinv.schedule
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      obtain ⟨t, hle, hre⟩ := hinv.reachable i e he
      have hre' := hre.withBroker (hscale.broker_asset he hb) hw
      obtain ⟨start, t₀, hcr, hrf⟩ := hre'
      refine ⟨⟨start, t₀, hcr, .accept _ _ _ _ _ hrf hle hc hr⟩, ?_⟩
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.accept_keepsTerms _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.mature i e he
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
      cases he'
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      obtain ⟨t, hle, hre⟩ := hinv.reachable i e he
      refine ⟨(hre.withBroker (hscale.broker_asset he hb) hw).manage hle action _ r hc hr, ?_⟩
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.manage_keepsTerms _ _ _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.mature i e he
    | loanPay i paymentType amount =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      obtain ⟨t, hle, hre⟩ := hinv.reachable i e he
      refine ⟨(hre.withBroker (hscale.broker_asset he hb) hw).pay hle paymentType _ amount r hc hr, ?_⟩
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.pay_keepsTerms _ _ _ _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.mature i e he
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  refine ⟨by rw [← hinv.schedule]; exact hs.schedule, fun j e he => ?_, fun j e he => ?_⟩
  · rw [LendingLedger.loan?_commitLoan] at he
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he
      exact ⟨l.now, UInt32.le_iff_toNat_le.mpr (le_refl _), (hnew e he).1⟩
    · rw [if_neg hj] at he
      obtain ⟨t, hle, hr⟩ := hinv.reachable j e he
      exact ⟨t, hle, hr⟩
  · rw [LendingLedger.loan?_commitLoan] at he
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he
      exact (hnew e he).2
    · rw [if_neg hj] at he
      exact hinv.mature j e he
/-- Every transaction keeps the invariant. -/
lemma LendingLedger.LoansInv.step {l l' : LendingLedger} {s : VaultSchedule} (hinv : l.LoansInv s)
    (hscale : l.ScaleInv) {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) : l'.LoansInv s := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hloans : (l.commitVault u).loans = l.loans := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hnow : (l.commitVault u).now = l.now := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hloan : ∀ j, (l.commitVault u).loan? j = l.loan? j := fun j => by
      unfold LendingLedger.loan?; rw [hloans]
    refine ⟨by rw [hvault, hk.schedule]; exact hinv.schedule, fun j e he => ?_, fun j e he => ?_⟩
    · rw [hloan] at he; rw [hnow]; exact hinv.reachable j e he
    · rw [hloan] at he; exact hinv.mature j e he
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hinv.schedule, hinv.reachable, hinv.mature⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hscale hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hinv.schedule, hinv.reachable, hinv.mature⟩
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    refine ⟨hinv.schedule, fun j e he => ?_, hinv.mature⟩
    obtain ⟨t, hle, hr⟩ := hinv.reachable j e he
    refine ⟨t, ?_, hr⟩
    show t ≤ max l.now _
    rw [UInt32.le_iff_toNat_le] at hle ⊢
    simp only [max, UInt32.le_iff_toNat_le]
    split <;> omega

/-- A genesis ledger satisfies the invariant with the schedule its vault was created with. -/
lemma LendingLedger.Genesis.loansInv {g : LendingLedger} (hg : g.Genesis) : ∃ s, g.LoansInv s := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hsch := (congrArg RawVault.schedule (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1 :)
  have hnone : ∀ j, g.loan? j = none := fun j => by unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  refine ⟨s, ⟨hsch, fun j e he => ?_, fun j e he => ?_⟩⟩ <;> rw [hnone] at he <;> cases he

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.loansInv {l : LendingLedger} (hr : l.Reachable) : ∃ s, l.LoansInv s := by
  obtain ⟨g, txs, hg, hreach, -⟩ := hr
  obtain ⟨s, hs⟩ := hg.loansInv
  exact ⟨s, (hreach.invariant (Inv := fun l => l.LoansInv s ∧ l.ScaleInv) ⟨hs, hg.scaleInv⟩
    fun _ _ _ _ hi ha => ⟨hi.1.step hi.2 ha, hi.2.step ha⟩).1⟩

/-- The loan read at `i` of a reachable ledger is a reachable loan by the ledger's close time. -/
lemma LendingLedger.Reachable.loanAt_reachable {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) : ∃ t, t ≤ l.now ∧ loan.Reachable t := by
  obtain ⟨e, b, he, hb, hw⟩ := hat
  obtain ⟨s, hls⟩ := hr.loansInv
  obtain ⟨t, hle, hrl⟩ := hls.reachable i e he
  exact ⟨t, hle, hrl.withBroker (hr.scaleInv.broker_asset he hb) hw⟩
end XRPL.Model.Lending
