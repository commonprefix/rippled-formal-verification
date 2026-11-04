import XRPL.Properties.Lending.Ledger.Common.AssetFlowDefs
import XRPL.Properties.Lending.Ledger.Common.CoverGridInv
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Loan.Common.LoanCount
import XRPL.Properties.Lending.Loan.Common.BrokerDebt

/-! # CoverAvailable stays in the Open zone, beside the fees payments pay into it

A cover deposit passes the Open-limit check, a withdrawal, a clawback and a default on a vault that is not
coarsened only take cover out, and no other transaction but a payment moves it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The CoverAvailable of broker `j`, zero for an empty slot. -/
def LendingLedger.brokerCover (l : LendingLedger) (j : Nat) : ℚ :=
  match l.broker? j with
  | some b => b.coverAvailable.toRat
  | none => 0

/-- The fees a transaction pays into broker `j`'s cover: what a payment adds to that CoverAvailable, and zero for
every other transaction. -/
def LendingLedger.coverFee (l : LendingLedger) (tx : LendingTx) (l' : LendingLedger) (j : Nat) : ℚ :=
  match tx with
  | .loanPay .. => max 0 (l'.brokerCover j - l.brokerCover j)
  | _ => 0

/-- The fees the transactions `txs`, applied in order from `l`, pay into broker `j`'s cover, up to the first one that
fails. -/
def LendingLedger.coverFees (l : LendingLedger) (j : Nat) : List LendingTx → ℚ
  | [] => 0
  | tx :: txs =>
    match (l.apply tx).run with
    | .ok (.ok l') => l.coverFee tx l' j + l'.coverFees j txs
    | _ => 0

lemma LendingLedger.coverFee_nonneg (l : LendingLedger) (tx : LendingTx) (l' : LendingLedger) (j : Nat) :
    0 ≤ l.coverFee tx l' j := by
  unfold LendingLedger.coverFee
  split
  · exact le_max_left _ _
  · exact le_refl _

lemma LendingLedger.coverFees_nonneg (l : LendingLedger) (j : Nat) (txs : List LendingTx) :
    0 ≤ l.coverFees j txs := by
  induction txs generalizing l with
  | nil => exact le_refl _
  | cons tx txs ih =>
    unfold LendingLedger.coverFees
    split
    · exact add_nonneg (l.coverFee_nonneg _ _ _) (ih _)
    · exact le_refl _

/-- A run's cover fees grow by each step's. -/
lemma LendingLedger.coverFees_snoc {start l l' : LendingLedger} {txs : List LendingTx} {tx : LendingTx} (j : Nat)
    (h : LendingLedger.Reaches start txs l) (hok : (l.apply tx).run = .ok (.ok l')) :
    start.coverFees j (txs ++ [tx]) = start.coverFees j txs + l.coverFee tx l' j := by
  induction txs generalizing start with
  | nil =>
    obtain rfl := h.nil_inv
    simp only [List.nil_append, LendingLedger.coverFees, hok]
    ring
  | cons t ts ih =>
    obtain ⟨l₁, h₁, hr₁⟩ := LendingLedger.Reaches.cons_inv h
    simp only [List.cons_append, LendingLedger.coverFees, h₁]
    rw [ih hr₁]
    ring

/-- A cover withdrawal that passed its preflight withdraws a canonical amount of the asset. -/
private lemma LendingTx.preflight_coverWithdraw_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault)
    (i : Nat) (amount : STAmount)
    (hpre : ((LendingTx.loanBrokerCoverWithdraw i amount).preflight l).isTesSuccess = true) :
    amount.CanonicalOrZero := by
  have hc : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp only [LendingTx.preflight, hne, Bool.false_eq_true, ↓reduceIte] at hpre
    exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)
  rw [Bool.and_eq_true] at hc
  have hnz : amount.mValue ≠ 0 := by
    have := hc.2
    simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    exact this.2
  exact Or.inl (isCanonicalAmount_canonical amount _ hasset.maxValue_le hc.1 hnz).1

/-- A broker transaction leaves a cover at most the larger of the old one and the Open limit. A deposit stays in
the Open zone, and the other broker transactions keep the cover or take some out. -/
private lemma LendingLedger.applyBroker_cover (l : LendingLedger) (hr : l.Reachable) (tx : LendingTx)
    (hpre : (tx.preflight l).isTesSuccess = true) (u : BrokerEffect) (h : (l.applyBroker tx).run = .ok (.ok u))
    (b' : LoanBroker) (hb' : u.broker = some b') :
    b'.coverAvailable.toRat ≤ max (l.brokerCover u.index) (9 * 10 ^ 15 * (10 : ℚ) ^ l.vault.baseExponent) := by
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hold : ∀ b, l.broker? u.index = some b → l.brokerCover u.index = b.coverAvailable.toRat := by
    intro b hb; unfold LendingLedger.brokerCover; rw [hb]
  cases tx with
  | loanBrokerCreate ctx =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hcz := congrArg RawLoanBroker.coverAvailable
      (RawLoanBroker.to_lawful_ok ‹RawLoanBroker.to_lawful _ = Except.ok _›).1
    simp only [LoanBroker.createRaw] at hcz
    rw [hcz, Number.toRat_zero]
    exact le_trans (by positivity) (le_max_right _ _)
  | loanBrokerUpdate i dm =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hb := ‹l.broker? i = some _›
    have hcz := congrArg RawLoanBroker.coverAvailable
      (RawLoanBroker.to_lawful_ok ‹RawLoanBroker.to_lawful _ = Except.ok _›).1
    simp only at hcz
    rw [hcz, hold _ hb]
    exact le_max_left _ _
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    rename_i _ broker hb _ _ t hcan _ ht _ _ res hdep
    have hok : ∀ t : TER, ¬ (!t.isTesSuccess) = true → t = .tesSUCCESS := fun t ht =>
      (TER.isTesSuccess_iff t).mp (by simpa using ht)
    rw [hok t ht] at hcan
    have hbnt := hr.scaleInv.brokers _ _ hb
    rw [hold _ hb]
    exact LoanBroker.coverDeposit_le _ l.vault a _ (hr.cover_onGrid hb)
      (fun hi => l.vault.baseExponent_bounds.2.2 (by rw [← hbnt]; exact hi)) hcan hdep
  | loanBrokerCoverWithdraw i a =>
    have hd := LendingTx.preflight_coverWithdraw_canonical l hasset i a hpre
    simp only [LendingLedger.applyBroker, LoanBroker.coverWithdraw] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hb := ‹l.broker? i = some _›
    have hcl : clampToSumExponent _ a.operator_neg _ = .ok _ := ‹_›
    obtain ⟨hcf, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hd.operator_neg
      l.vault.baseExponent_range.1 l.vault.baseExponent_range.2 hcl
    rw [hold _ hb]
    exact (LoanBroker.applyCoverTransaction_debit_le _ _ _ hcf hc0 ‹_›).trans (le_max_left _ _)
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverClawback, LoanBroker.roundedCoverClawback] at h
    unfold_ter at h
    walk_ok
    all_goals
      simp only [Option.some.injEq] at hb'
      subst hb'
      have hb := ‹l.broker? i = some _›
      have hbnt := hr.scaleInv.brokers _ _ hb
      have hof : STAmount.ofNumber _ _ .to_nearest = .ok _ := ‹_›
      have hcz := (STAmount.ofNumber_canonicalOrZero _ _ _ _ (by rw [hbnt]; exact hmax) hof).1
      have hcl : clampToSumExponent _ _ _ = .ok _ := ‹_›
      obtain ⟨hcf, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hcz.operator_neg
        l.vault.baseExponent_range.1 l.vault.baseExponent_range.2 hcl
      rw [hold _ hb]
      exact (LoanBroker.applyCoverTransaction_debit_le _ _ _ hcf hc0 ‹_›).trans (le_max_left _ _)
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- The broker a loan transaction other than a payment writes keeps at most its cover, on a vault that is not
coarsened: a default there pays the vault a cover of at least zero. -/
private lemma LendingLedger.applyLoan_cover (l : LendingLedger) (hr : l.Reachable) (hnc : l.NotCoarsened)
    (tx : LendingTx) (hpay : ∀ i pt amount, tx ≠ .loanPay i pt amount) (u : LoanEffect)
    (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    ∃ b, l.broker? u.brokerIndex = some b ∧ u.broker.coverAvailable.toRat ≤ b.coverAvailable.toRat := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    obtain ⟨_, _, _, -, hbr⟩ := Loan.create_ok_broker broker l.vault principal rates fees _ ao twoStep r hcr
    refine ⟨broker, hb, le_of_eq ?_⟩
    show r.loan'.broker.toRawLoanBroker.coverAvailable.toRat = _
    rw [hbr]
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, le_of_eq ?_⟩
    show r.loan'.broker.coverAvailable.toRat = _
    rw [Loan.accept_broker loan _ r hr', hlb]
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show r.loan'.broker.coverAvailable.toRat ≤ _
    cases action with
    | impair => rw [(Loan.manageImpair_debt loan l.vault l.now r hr').1, hlb]
    | unimpair => rw [(Loan.manageUnimpair_debt loan l.vault r hr').1, hlb]
    | default =>
      have hdef : ∃ r₀ : LoanWithAmounts Vault, (loan.manageDefault l.vault).run = .ok (.ok r₀) ∧
          r = r₀.toLoanWithPool := by
        simp only [Loan.manage] at hr'
        unfold_ter at hr'
        walk_ok
        exact ⟨_, ‹_›, rfl⟩
      obtain ⟨r₀, hok₀, rfl⟩ := hdef
      have hdc0 := LendingLedger.loanDefault_cover_nonneg l hr i loan ⟨e, broker, he, hb, hw⟩ r₀ hok₀ hnc
      obtain ⟨_, _, c, _, b', -, -, -, -, -, hcov, hbr, hloan, -⟩ := Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
      have hcb : r₀.loan'.broker.coverAvailable = c := by
        rw [show r₀.loan'.broker = r₀.loan'.toRawLoan.broker from rfl, hloan]
        show b'.toRawLoanBroker.coverAvailable = _
        rw [hbr]; rfl
      show r₀.loan'.broker.coverAvailable.toRat ≤ _
      rw [hcb, ← hlb]
      have hdn := Loan.defaultCover_isNormalized loan l.vault _ (Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
        |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1)
      exact Number.roundsToRepresentable_le _ _ (operator_sub_rounded_to_nearest _ _ _
        loan.broker.wf.coverAvailable_norm hdn hcov) _ loan.broker.wf.coverAvailable_norm (by linarith)
  | loanPay i paymentType amount => exact absurd rfl (hpay i paymentType amount)
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, le_of_eq ?_⟩
    show r.broker'.coverAvailable.toRat = _
    by_cases hp : loan.isPending = true
    · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan l.vault r hp hr'
      rw [LoanBroker.releaseLoan_cover _ _ _ hrel, hlb]
    · simp only [Loan.delete, Bool.not_eq_true] at hr' hp
      rw [hp] at hr'
      unfold_ter at hr'
      walk_ok
      rw [LoanBroker.releaseLoan_cover _ _ _ ‹Loan.deleteActive _ = Except.ok _›, hlb]
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A transaction keeps every broker's cover at most the larger of its old cover and the Open limit, plus what a
payment adds to it, on a reachable ledger that is not coarsened. -/
lemma LendingLedger.cover_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hnc : l.NotCoarsened) (j : Nat) :
    l'.brokerCover j ≤ max (l.brokerCover j) l.openLimit + l.coverFee tx l' j := by
  have hO : (0 : ℚ) ≤ l.openLimit := by unfold LendingLedger.openLimit; positivity
  have hO' : (0 : ℚ) ≤ max (l.brokerCover j) l.openLimit := le_trans hO (le_max_right _ _)
  by_cases hpay : ∃ i pt amount, tx = .loanPay i pt amount
  · obtain ⟨i, pt, amount, rfl⟩ := hpay
    show _ ≤ _ + max 0 (l'.brokerCover j - l.brokerCover j)
    have h1 := le_max_left (l.brokerCover j) l.openLimit
    have h2 := le_max_right 0 (l'.brokerCover j - l.brokerCover j)
    linarith
  push Not at hpay
  have hfee : l.coverFee tx l' j = 0 := by
    unfold LendingLedger.coverFee
    split
    · rename_i i pt amount; exact absurd rfl (hpay i pt amount)
    · rfl
  rw [hfee, add_zero]
  have hpre := (LendingLedger.apply_checked h).1
  have hsame : l'.brokers = l.brokers → l'.brokerCover j ≤ max (l.brokerCover j) l.openLimit := by
    intro hbr
    unfold LendingLedger.brokerCover LendingLedger.broker?
    rw [hbr]
    exact le_max_left _ _
  by_cases hvt : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hvt h
    apply hsame
    unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    unfold LendingLedger.brokerCover
    rw [LendingLedger.broker?_commitBroker]
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj]
      cases hub : u.broker with
      | none => exact hO'
      | some b' =>
        have hc := l.applyBroker_cover hr tx hpre u hu b' hub
        have hidx : l.brokerCover u.index = l.brokerCover j := by
          split at hj
          · rw [hj]
          · rename_i hge
            have h1 : l.broker? u.index = none := by
              unfold LendingLedger.broker?; rw [List.getElem?_eq_none (by omega)]; rfl
            have h2 : l.broker? j = none := by
              unfold LendingLedger.broker?; rw [List.getElem?_eq_none (by omega)]; rfl
            unfold LendingLedger.brokerCover; rw [h1, h2]
        rw [hidx] at hc
        exact hc
    · rw [if_neg hj]; exact le_max_left _ _
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    obtain ⟨b, hbk, hcu⟩ := l.applyLoan_cover hr hnc tx (fun i pt amount h' => hpay i pt amount h') u hu
    have hbc : (l.commitLoan u).brokerCover j =
        if j = u.brokerIndex then u.broker.coverAvailable.toRat else l.brokerCover j := by
      unfold LendingLedger.brokerCover
      rw [LendingLedger.broker?_commitLoan l u b hbk]
      split_ifs <;> rfl
    rw [hbc]
    split_ifs with hj
    · subst hj
      have hold : l.brokerCover u.brokerIndex = b.coverAvailable.toRat := by
        unfold LendingLedger.brokerCover; rw [hbk]
      rw [hold]
      exact hcu.trans (le_max_left _ _)
    · exact le_max_left _ _
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hsame rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hsame rfl

/-- Proof body of `Lending.Reachable.cover_within_open_zone`. -/
lemma LendingLedger.cover_within_open_zone_proof (genesis l : LendingLedger) (txs : List LendingTx) (x : ℚ)
    (hg : genesis.Genesis) (hrun : genesis.ReachableFromIn txs l x)
    (hnc : ∀ (pre : List LendingTx) (tx : LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre ++ [tx] <+: txs →
      genesis.ReachableFromIn pre l₁ x₁ → l₁.NotCoarsened)
    (j : Nat) (b : LoanBroker) (hb : l.broker? j = some b) :
    b.coverAvailable.toRat ≤ l.openLimit + genesis.coverFees j txs := by
  suffices h : l.brokerCover j ≤ l.openLimit + genesis.coverFees j txs by
    unfold LendingLedger.brokerCover at h; rw [hb] at h; exact h
  clear hb b
  induction hrun with
  | refl =>
    have h0 : genesis.brokerCover j = 0 := by
      unfold LendingLedger.brokerCover LendingLedger.broker?; rw [hg.no_brokers]; rfl
    rw [h0, show genesis.coverFees j [] = 0 from rfl, add_zero]
    unfold LendingLedger.openLimit; positivity
  | @step txs₀ l₀ l₁ x₀ tx hprev hok ih =>
    have ih' := ih (fun pre t l₂ x₂ hpre hr' => hnc pre t l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr')
    have hr₀ := hprev.reachable hg
    have hstep := LendingLedger.cover_step l₀ l₁ tx hr₀ hok (hnc txs₀ tx l₀ x₀ (List.prefix_refl _) hprev) j
    have hO : l₁.openLimit = l₀.openLimit := by
      unfold LendingLedger.openLimit; rw [LendingLedger.apply_baseExponent hok]
    rw [LendingLedger.coverFees_snoc j hprev.reaches hok, hO]
    have hF := genesis.coverFees_nonneg j txs₀
    have hO0 : (0 : ℚ) ≤ l₀.openLimit := by unfold LendingLedger.openLimit; positivity
    have hmax : max (l₀.brokerCover j) l₀.openLimit ≤ l₀.openLimit + genesis.coverFees j txs₀ :=
      max_le ih' (by linarith)
    linarith

end XRPL.Model.Lending
