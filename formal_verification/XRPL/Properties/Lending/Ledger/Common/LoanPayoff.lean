import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue

/-! # A loan's payments until it is paid off

Along a run that pays the loan at `i` and never defaults it, every other transaction keeps its PrincipalOutstanding,
and a payment that keeps AssetsAvailable plus what it pays below `10^16` base units adds at least the principal it
pays to AssetsAvailable. So once the payments pay the loan off they have added at least the principal it had. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.manageUnimpair_ok_parts from XRPL.Properties.Lending.Loan.Common.ManageProofs

/-- A payment of the loan at `i` keeps AssetsAvailable plus the principal and the interest it pays below `10^16`
base units. -/
def LendingLedger.PaymentFits (l : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) :
    Prop :=
  ∀ (loan : Loan) (payment : UnsettledPayment Vault), l.LoanAt i loan →
    (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) →
    l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent

/-- A run from `start` that never defaults the loan at `i`, with `paid` the sum of AssetsAvailable' −
AssetsAvailable over the LoanPay steps of that loan. Each of those steps satisfies `fits`. -/
inductive LendingLedger.PaysLoan (i : Nat) (fits : LendingLedger → LoanPaymentType → Number → Prop)
    (start : LendingLedger) : LendingLedger → ℚ → Prop where
  | refl : LendingLedger.PaysLoan i fits start start 0
  | pay {l l' : LendingLedger} {paid : ℚ} (paymentType : LoanPaymentType) (amount : Number) :
      LendingLedger.PaysLoan i fits start l paid → fits l paymentType amount →
      (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') →
      LendingLedger.PaysLoan i fits start l'
        (paid + (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat))
  | other {l l' : LendingLedger} {paid : ℚ} (tx : LendingTx) :
      LendingLedger.PaysLoan i fits start l paid → (∀ paymentType amount, tx ≠ .loanPay i paymentType amount) →
      tx ≠ .loanManage i .default → (l.apply tx).run = .ok (.ok l') → LendingLedger.PaysLoan i fits start l' paid

/-- Writing a slot never shortens the list. -/
private lemma storeSlot_length {α : Type} (xs : List (Option α)) (k : Nat) (x : Option α) :
    xs.length ≤ (storeSlot xs k x).length := by
  unfold storeSlot
  split <;> simp

/-- Taking the ledger's copy of the broker keeps the principal. -/
private lemma Loan.withBroker_principal {loan loan' : Loan} {b : LoanBroker} (h : loan.withBroker b = .ok loan') :
    loan'.principalOutstanding = loan.principalOutstanding :=
  (congrArg RawLoan.principalOutstanding (Loan.withBroker_eq h) :)

/-- Accept keeps the principal. -/
private lemma Loan.accept_principal (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.principalOutstanding = loan.principalOutstanding := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact (congrArg RawLoan.principalOutstanding (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :)

/-- Impair and unimpair keep the principal. -/
private lemma Loan.manage_principal (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (hnd : action ≠ .default) (h : (loan.manage action v now).run = .ok (.ok r)) :
    r.loan'.principalOutstanding = loan.principalOutstanding := by
  cases action with
  | impair =>
    obtain ⟨-, -, -, -, hloan⟩ := Loan.manageImpair_ok_parts loan v now r h
    exact (congrArg RawLoan.principalOutstanding hloan :)
  | unimpair =>
    obtain ⟨-, -, -, hloan⟩ := Loan.manageUnimpair_ok_parts loan v r h
    exact (congrArg RawLoan.principalOutstanding hloan :)
  | default => exact absurd rfl hnd

/-- A transaction that neither pays nor defaults the loan at `i` keeps its PrincipalOutstanding. The slot
stays inside the list, and a loan in it afterwards had a loan in it before with the same principal. -/
private lemma LendingLedger.slot_other {l l' : LendingLedger} {tx : LendingTx} {i : Nat}
    (h : (l.apply tx).run = .ok (.ok l')) (hi : i < l.loans.length)
    (hnp : ∀ paymentType amount, tx ≠ .loanPay i paymentType amount) (hnd : tx ≠ .loanManage i .default) :
    i < l'.loans.length ∧ ∀ e', l'.loan? i = some e' →
      ∃ e, l.loan? i = some e ∧ e'.loan.principalOutstanding = e.loan.principalOutstanding := by
  have hsame : l'.loans = l.loans → i < l'.loans.length ∧ ∀ e', l'.loan? i = some e' →
      ∃ e, l.loan? i = some e ∧ e'.loan.principalOutstanding = e.loan.principalOutstanding := fun hl =>
    ⟨by rw [hl]; exact hi, fun e' he' => ⟨e', by unfold LendingLedger.loan? at he' ⊢; rw [← hl]; exact he', rfl⟩⟩
  by_cases hv : tx.isVault = true
  · exact hsame (LendingLedger.vault_ops_scope_proof l l' tx hv h).1
  by_cases hb : tx.isBroker = true
  · exact hsame (LendingLedger.broker_ops_scope_proof l l' tx hb h).1
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hlen : i < (l.commitLoan u).loans.length := lt_of_lt_of_le hi (storeSlot_length _ _ _)
    cases tx with
    | loanSet j principal rates fees pi pt gp sd twoStep ao =>
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨-, r, -, -, -, rfl⟩ := LendingLedger.applyLoanSet_inv l u j _ _ _ _ _ _ hu
      refine ⟨hlen, fun e' he' => ⟨e', ?_, rfl⟩⟩
      rw [LendingLedger.loan?_commitLoan] at he'
      simp only [LoanEffect.ofCreate, lt_irrefl, ↓reduceIte] at he'
      rwa [if_neg (by omega)] at he'
    | loanAccept j =>
      obtain ⟨e, broker, loan, r, he, -, hw, -, hacc, rfl⟩ := LendingLedger.applyLoan_accept_inv l u j hu
      refine ⟨hlen, fun e' he' => ?_⟩
      rw [LendingLedger.loan?_commit_ofLoan l he] at he'
      split at he'
      · rename_i hij
        subst hij
        obtain rfl := Option.some.inj he'
        exact ⟨e, he, by
          show r.loan'.principalOutstanding = e.loan.principalOutstanding
          rw [Loan.accept_principal loan _ r hacc, Loan.withBroker_principal hw]⟩
      · exact ⟨e', he', rfl⟩
    | loanDelete j =>
      obtain ⟨e, broker, loan, r, he, -, -, -, -, rfl⟩ := LendingLedger.applyLoan_delete_inv l u j hu
      refine ⟨hlen, fun e' he' => ?_⟩
      rw [LendingLedger.loan?_commitLoan] at he'
      simp only [LendingLedger.loan?_lt he, ↓reduceIte] at he'
      split at he'
      · cases he'
      · exact ⟨e', he', rfl⟩
    | loanManage j action =>
      obtain ⟨e, broker, loan, r, he, -, hw, -, hman, rfl⟩ := LendingLedger.applyLoan_manage_inv l u j action hu
      refine ⟨hlen, fun e' he' => ?_⟩
      rw [LendingLedger.loan?_commit_ofLoan l he] at he'
      split at he'
      · rename_i hij
        subst hij
        obtain rfl := Option.some.inj he'
        have had : action ≠ .default := fun hd => hnd (by rw [hd])
        exact ⟨e, he, by
          show r.loan'.principalOutstanding = e.loan.principalOutstanding
          rw [Loan.manage_principal loan action _ _ r had hman, Loan.withBroker_principal hw]⟩
      · exact ⟨e', he', rfl⟩
    | loanPay j pt amount =>
      obtain ⟨e, broker, loan, r, he, -, -, -, -, rfl⟩ := LendingLedger.applyLoan_pay_inv l u j pt amount hu
      have hij : i ≠ j := fun hij => hnp pt amount (by rw [hij])
      refine ⟨hlen, fun e' he' => ?_⟩
      rw [LendingLedger.loan?_commit_ofLoan l he, if_neg hij] at he'
      exact ⟨e', he', rfl⟩
    | _ => simp [LendingTx.isLoan] at hl
  · -- close and vaultDelete keep the loans
    have hc := (LendingLedger.apply_checked h).2
    cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
      not_false_eq_true, not_true_eq_false] at hv hb hl
    · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
      unfold_ter at hc
      walk_ok
      exact hsame rfl
    · simp only [LendingLedger.applyChecked] at hc
      cases hc
      exact hsame rfl

/-- A payment of the loan at `i` that keeps AssetsAvailable plus what it pays below `10^16` base units adds at least
the principal it pays to AssetsAvailable. -/
private lemma LendingLedger.slot_pay {l l' : LendingLedger} (hr : l.Reachable) {i : Nat}
    {paymentType : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (hfits : l.PaymentFits i paymentType amount) :
    i < l'.loans.length ∧ ∀ e', l'.loan? i = some e' → ∃ e, l.loan? i = some e ∧
      e.loan.principalOutstanding.toRat - e'.loan.principalOutstanding.toRat ≤
        l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat := by
  have hge := LendingLedger.pay_assetsTotal_le hr h
  obtain ⟨e, loan, r, he, hat, hw, hok, rfl, -⟩ := LendingLedger.loanPay_parts h
  obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault paymentType amount l.now r hok
  have hge := hge loan hat p hp (hfits loan p hat hp)
  change l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat at hge

  obtain ⟨hls, -⟩ := hr.loanAt_scale hat
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨paid, hpg, hp0, hpo, -, had⟩ := Loan.pay_principal loan l.vault paymentType amount l.now r
    (by rw [hls]; omega) hok
  rw [hls] at hpg
  obtain ⟨q, hq⟩ := hpg.nat hp0
  obtain ⟨d, hd, hdv⟩ := hr.deployed_units
  have hqd : q ≤ d := by
    obtain ⟨-, -, -, hpad, -⟩ := hr.loanAt_principal hat
    have h0 : (0 : ℚ) ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
    have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    have : (q : ℚ) * 10 ^ l.vault.baseExponent ≤ (d : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hq, ← hdv]; linarith
    exact_mod_cast le_of_mul_le_mul_right this hp10
  have hd' := Number.operator_add_toRat_of_grid _ _ _ d (-(q : ℤ)) l.vault.baseExponent
    l.vault.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpg.1) (by rw [hdv]; norm_cast)
    (by rw [Number.toRat_neg, hq]; push_cast; ring) (by omega) (by unfold minExponent maxExponent; omega) had
  have hdq : r.pool'.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - paid.toRat := by
    rw [hd', hdv, hq]; push_cast; ring

  refine ⟨lt_of_lt_of_le (LendingLedger.loan?_lt he) (storeSlot_length _ _ _), fun e' he' => ?_⟩
  rw [LendingLedger.loan?_commit_ofLoan l he, if_pos rfl] at he'
  obtain rfl := Option.some.inj he'
  refine ⟨e, he, ?_⟩
  show e.loan.principalOutstanding.toRat - r.loan'.principalOutstanding.toRat ≤
    r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat
  rw [← Loan.withBroker_principal hw]
  linarith

/-- Along the run, every loan in the slot has added back the principal it lost. -/
private lemma LendingLedger.PaysLoan.bound {i : Nat} {l₀ l : LendingLedger} {paid : ℚ} (hr : l₀.Reachable)
    {e₀ : LoanEntry} (he₀ : l₀.loan? i = some e₀)
    (hrun : l₀.PaysLoan i (fun l paymentType amount => l.PaymentFits i paymentType amount) l paid) :
    l.Reachable ∧ i < l.loans.length ∧ ∀ e, l.loan? i = some e →
      e₀.loan.principalOutstanding.toRat - e.loan.principalOutstanding.toRat ≤ paid := by
  induction hrun with
  | refl =>
    refine ⟨hr, LendingLedger.loan?_lt he₀, fun e he => ?_⟩
    rw [he₀] at he
    obtain rfl := Option.some.inj he
    simp
  | pay paymentType amount _ hfits hstep ih =>
    obtain ⟨hrl, hil, hb⟩ := ih
    obtain ⟨hil', hslot⟩ := LendingLedger.slot_pay hrl hstep hfits
    refine ⟨hrl.apply hstep, hil', fun e' he' => ?_⟩
    obtain ⟨e, he, hle⟩ := hslot e' he'
    have := hb e he
    linarith
  | other tx _ hnp hnd hstep ih =>
    obtain ⟨hrl, hil, hb⟩ := ih
    obtain ⟨hil', hslot⟩ := LendingLedger.slot_other hstep hil hnp hnd
    refine ⟨hrl.apply hstep, hil', fun e' he' => ?_⟩
    obtain ⟨e, he, hpo⟩ := hslot e' he'
    rw [hpo]
    exact hb e he

/-- Proof body of `Lending.Reachable.payoff_returns_principal`. -/
lemma LendingLedger.payoff_returns_principal_proof (l₀ : LendingLedger) (hr : l₀.Reachable) (i : Nat) (loan₀ : Loan)
    (hat : l₀.LoanAt i loan₀) (l : LendingLedger) (paid : ℚ)
    (hrun : l₀.PaysLoan i (fun l paymentType amount => l.PaymentFits i paymentType amount) l paid)
    (hoff : ∃ e, l.loan? i = some e ∧ e.loan.paymentRemaining = 0) :
    loan₀.principalOutstanding.toRat ≤ paid := by
  obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
  have hpo₀ : loan₀.principalOutstanding = e₀.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  obtain ⟨-, -, hb⟩ := LendingLedger.PaysLoan.bound hr he₀ hrun
  obtain ⟨e, he, hpr⟩ := hoff
  have hz : e.loan.principalOutstanding.toRat = 0 := (e.loan.exact.paid_zeroed hpr).2.1
  have := hb e he
  rw [hpo₀]
  linarith

end XRPL.Model.Lending
