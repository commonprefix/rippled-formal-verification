import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Loan.Common.Outstanding
import XRPL.Properties.Lending.Loan.Common.SetPhase
import XRPL.Properties.Lending.Loan.Common.SetScale
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # Scales on a reachable ledger

Every broker lends the vault's asset, and every stored loan is kept at the vault's base scale on a broker
of the vault's asset. A LoanSet creates its loan at the base scale and no transaction changes a scale. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private checkPrecisionFields canFundLoan from XRPL.Model.Lending.Loan.LoanSet

/-- A cover transaction keeps the broker's numeric type. -/
private lemma LoanBroker.applyCoverTransaction_numericType (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (r : LoanBrokerCoverResult) (h : lb.applyCoverTransaction d a = .ok r) :
    r.loanBroker'.numericType = lb.numericType := by
  unfold LoanBroker.applyCoverTransaction at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  cases d <;>
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok hb).1 :)

/-- A broker transaction writes a broker of the vault's numeric type, or one that keeps its type. -/
private lemma LendingLedger.applyBroker_numericType (l : LendingLedger) (tx : LendingTx) (u : BrokerEffect)
    (h : (l.applyBroker tx).run = .ok (.ok u)) (b' : LoanBroker) (hb' : u.broker = some b') :
    b'.numericType = l.vault.numericType ∨ ∃ b, l.broker? u.index = some b ∧ b'.numericType = b.numericType := by
  cases tx with
  | loanBrokerCreate ctx =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inl (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok ‹_›).1 :)
  | loanBrokerUpdate i dm =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok ‹_›).1 :)⟩
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverDeposit] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_numericType _ _ _ _ ‹_›⟩
  | loanBrokerCoverWithdraw i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverWithdraw] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_numericType _ _ _ _ ‹_›⟩
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverClawback] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_numericType _ _ _ _ ‹_›⟩
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- A delete keeps the broker's numeric type. -/
private lemma Loan.delete_numericType (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : r.broker'.numericType = loan.broker.numericType := by
  have hrel : ∀ lb lb' d, LoanBroker.releaseLoan lb d = .ok lb' → lb'.numericType = lb.numericType :=
    fun lb lb' d h => by
      unfold LoanBroker.releaseLoan at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      rename_i _ hc
      obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
      exact (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok h).1 :)
  by_cases hp : loan.isPending = true
  · obtain ⟨_, _, _, -, -, -, -, hr⟩ := Loan.delete_pending_ok_inv loan v r hp h
    exact hrel _ _ _ hr
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact hrel _ _ _ ‹Loan.deleteActive _ = Except.ok _›

/-- A management action keeps the broker's numeric type. -/
private lemma Loan.manage_numericType (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) :
    r.loan'.broker.numericType = loan.broker.numericType := by
  cases action with
  | impair => rw [(Loan.manageImpair_debt loan v now r h).1]
  | unimpair => rw [(Loan.manageUnimpair_debt loan v r h).1]
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok
    rename_i rd hd
    obtain ⟨_, d, c, _, b, -, -, -, -, -, -, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v rd hd
    have hbr : rd.loan'.broker = b := by
      rw [show rd.loan'.broker = rd.loan'.toRawLoan.broker from rfl, hloan]; rfl
    show rd.loan'.broker.numericType = _
    rw [hbr, show b.numericType = b.toRawLoanBroker.numericType from rfl, hb]
    rfl

/-- What every reachable ledger keeps about scales: every broker lends the vault's asset, and every stored
loan is kept at the vault's base scale on a broker of the vault's asset. -/
structure LendingLedger.ScaleInv (l : LendingLedger) : Prop where
  brokers : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.numericType = l.vault.numericType
  loanScale : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → e.loan.loanScale = l.vault.baseExponent
  loanBroker : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e →
    e.loan.broker.numericType = l.vault.numericType

/-- A loan effect keeps the invariant when it writes a broker and a loan of the vault's asset and scale. -/
private lemma LendingLedger.ScaleInv.commitLoan {l : LendingLedger} (hinv : l.ScaleInv) {u : LoanEffect}
    {b : LoanBroker} (hb : l.broker? u.brokerIndex = some b) (hs : Vault.KeepsSettings l.vault u.vault)
    (hnt : u.broker.numericType = l.vault.numericType)
    (hloan : ∀ e', u.loan = some e' → e'.loan.loanScale = l.vault.baseExponent ∧
      e'.loan.broker.numericType = l.vault.numericType) :
    (l.commitLoan u).ScaleInv := by
  have hv : (l.commitLoan u).vault = u.vault := rfl
  refine ⟨fun j b' hb' => ?_, fun j e he => ?_, fun j e he => ?_⟩
  · rw [LendingLedger.broker?_commitLoan l u b hb] at hb'
    rw [hv, hs.numericType]
    split at hb'
    · cases hb'; exact hnt
    · exact hinv.brokers j b' hb'
  · rw [LendingLedger.loan?_commitLoan] at he
    rw [hv, hs.baseExponent_eq]
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he; exact (hloan e he).1
    · rw [if_neg hj] at he; exact hinv.loanScale j e he
  · rw [LendingLedger.loan?_commitLoan] at he
    rw [hv, hs.numericType]
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he; exact (hloan e he).2
    · rw [if_neg hj] at he; exact hinv.loanBroker j e he

/-- A loan operation that keeps the loan's terms and its broker's numeric type keeps the invariant. -/
private lemma LendingLedger.ScaleInv.ofLoan {l : LendingLedger} (hinv : l.ScaleInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} {loan loan' : Loan} {v' : Vault} (he : l.loan? i = some e)
    (hb : l.broker? e.brokerIndex = some broker) (hw : e.loan.withBroker broker = .ok loan)
    (hs : Vault.KeepsSettings l.vault v') (ht : Loan.KeepsTerms loan loan')
    (hnt : loan'.broker.numericType = loan.broker.numericType) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).ScaleInv := by
  have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
  have hnt' : loan'.broker.numericType = l.vault.numericType := by
    rw [hnt, hlb]; exact hinv.brokers _ broker hb
  have hwt := Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl
  refine hinv.commitLoan hb hs hnt' fun e' he' => ?_
  simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
  subst he'
  exact ⟨by rw [ht.loanScale, hwt.loanScale]; exact hinv.loanScale i e he, hnt'⟩

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.ScaleInv.loan_step {l : LendingLedger} (hinv : l.ScaleInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).ScaleInv := by
  have hs := l.applyLoan_keepsSettings tx u hu
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hbnt := hinv.brokers i broker hb
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    obtain ⟨_, _, _, b', -, -, hraw⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r hcr
    have hbr : r.loan'.broker.numericType = broker.numericType := by
      obtain ⟨_, _, _, b'', _, hl, hb''⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r hcr
      rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hl]
      show b''.numericType = _
      rw [show b''.numericType = b''.toRawLoanBroker.numericType from rfl, hb'']
    refine hinv.commitLoan hb hs (by show r.loan'.broker.numericType = _; rw [hbr]; exact hbnt) fun e' he' => ?_
    simp only [LoanEffect.ofCreate, Option.some.injEq] at he'
    subst he'
    exact ⟨Loan.create_loanScale_proof _ _ _ _ _ _ _ _ r hpn hpos hst hbnt hcr, by rw [hbr]; exact hbnt⟩
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    exact hinv.ofLoan he hb hw hs (Loan.accept_keepsTerms _ _ _ hr) (by rw [Loan.accept_broker loan _ r hr])
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    exact hinv.ofLoan he hb hw hs (Loan.manage_keepsTerms _ _ _ _ _ hr) (Loan.manage_numericType _ _ _ _ _ hr)
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    exact hinv.ofLoan he hb hw hs (Loan.pay_keepsTerms _ _ _ _ _ _ hr)
      (congrArg RawLoanBroker.numericType (Loan.pay_broker_fields loan _ _ _ _ r hr) :)
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine hinv.commitLoan hb hs ?_ fun e' he' => by cases he'
    show r.broker'.numericType = _
    rw [Loan.delete_numericType loan _ r hr, hlb]
    exact hinv.brokers _ broker hb
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A broker transaction keeps the invariant. -/
lemma LendingLedger.ScaleInv.broker_step {l : LendingLedger} (hinv : l.ScaleInv) {tx : LendingTx}
    {u : BrokerEffect} (hu : (l.applyBroker tx).run = .ok (.ok u)) : (l.commitBroker u).ScaleInv := by
  refine ⟨fun j b' hb' => ?_, fun j e he => hinv.loanScale j e he, fun j e he => hinv.loanBroker j e he⟩
  show b'.numericType = l.vault.numericType
  rw [LendingLedger.broker?_commitBroker] at hb'
  by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
  · rw [if_pos hj] at hb'
    rcases LendingLedger.applyBroker_numericType l tx u hu b' hb' with h0 | ⟨b, hb, hnt⟩
    · exact h0
    · rw [hnt]; exact hinv.brokers _ b hb
  · rw [if_neg hj] at hb'; exact hinv.brokers j b' hb'

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.ScaleInv.step {l l' : LendingLedger} (hinv : l.ScaleInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.ScaleInv := by
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).brokers = l.brokers ∧
        (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    have hb : ∀ j, (l.commitVault u).broker? j = l.broker? j := fun j => by
      unfold LendingLedger.broker?; rw [hrest.2.1]
    have hl : ∀ j, (l.commitVault u).loan? j = l.loan? j := fun j => by
      unfold LendingLedger.loan?; rw [hrest.1]
    refine ⟨fun j b hj => ?_, fun j e he => ?_, fun j e he => ?_⟩ <;> rw [hrest.2.2]
    · rw [hb] at hj; rw [hk.numericType]; exact hinv.brokers j b hj
    · rw [hl] at he; rw [hbe]; exact hinv.loanScale j e he
    · rw [hl] at he; rw [hk.numericType]; exact hinv.loanBroker j e he
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    exact hinv.broker_step hu
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hpre hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hinv.brokers, hinv.loanScale, hinv.loanBroker⟩
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hinv.brokers, hinv.loanScale, hinv.loanBroker⟩

/-- A genesis ledger has no brokers and no loans. -/
lemma LendingLedger.Genesis.scaleInv {g : LendingLedger} (hg : g.Genesis) : g.ScaleInv := by
  have hb : ∀ j, g.broker? j = none := fun j => by unfold LendingLedger.broker?; rw [hg.no_brokers]; rfl
  have hl : ∀ j, g.loan? j = none := fun j => by unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  refine ⟨fun j b h => ?_, fun j e h => ?_, fun j e h => ?_⟩
  · rw [hb] at h; cases h
  · rw [hl] at h; cases h
  · rw [hl] at h; cases h

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.scaleInv {l : LendingLedger} (hr : l.Reachable) : l.ScaleInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.scaleInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- A stored loan on a reachable ledger is at the vault's base scale, on a broker of the vault's asset. -/
lemma LendingLedger.Reachable.loanAt_scale {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (h : l.LoanAt i loan) : loan.loanScale = l.vault.baseExponent ∧ loan.broker.numericType = l.vault.numericType := by
  obtain ⟨e, b, he, hb, hw⟩ := h
  have hraw := Loan.withBroker_eq hw
  refine ⟨?_, ?_⟩
  · rw [show loan.loanScale = loan.toRawLoan.loanScale from rfl, hraw]; exact hr.scaleInv.loanScale i e he
  · rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]; exact hr.scaleInv.brokers _ b hb

/-- The loan at `i` of a reachable ledger is at the base scale, so its scale is between `-81` and `0`, the range the
loan lemmas ask for. -/
lemma LendingLedger.Reachable.loanScale_range {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := by
  have hs := (hr.loanAt_scale hat).1
  obtain ⟨hlo, hhi, -⟩ := Vault.baseExponent_bounds l.vault
  omega

end XRPL.Model.Lending
