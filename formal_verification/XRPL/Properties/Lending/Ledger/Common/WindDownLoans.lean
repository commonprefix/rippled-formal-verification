import XRPL.Properties.Lending.Ledger.Common.WindDownDefs
import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Lending.Ledger.Common.DefaultOrder
import XRPL.Properties.Lending.Ledger.Common.LoanClosable
import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs

/-! # Closing every loan of a vault in its redemption phase

Past RedemptionDate plus every grace period, each stored loan is deleted: a pending or closed loan at once, an
active loan after a default. None of these steps adds to AssetsAvailable + AssetsDeployed, so a vault that is not
coarsened stays so, and a broker's cover only shrinks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

open private LendingLedger.default_at_base from XRPL.Properties.Lending.Ledger.Common.DefaultOrder

/-- What the wind-down keeps while it closes loans: the hypotheses of `wind_down` on the current ledger, close time,
coarsening while a loan is open, and covers. -/
structure LendingLedger.LoanPhase (l : LendingLedger) (s : VaultSchedule) : Prop where
  reachable : l.Reachable
  notDeleted : l.vaultDeleted = false
  schedule : l.vault.schedule = some s
  past : s.redemptionDate < l.now
  grace : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
    s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat
  pending : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened
  active : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
    e.loan.paymentRemaining ≠ 0 → l.NotCoarsened
  cover : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
    b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount

/-- Emptying an occupied slot lowers the number of occupied slots. -/
lemma List.countP_set_none_lt {α : Type} (xs : List (Option α)) (i : Nat) (x : α) (h : xs[i]? = some (some x)) :
    (xs.set i none).countP (·.isSome) < xs.countP (·.isSome) := by
  have hi : i < xs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have hx : xs[i] = some x := by
    rw [List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  rw [List.countP_set hi, hx]
  have hpos : 0 < xs.countP (·.isSome) :=
    List.countP_pos_iff.mpr ⟨xs[i], List.getElem_mem hi, by rw [hx]; rfl⟩
  simp only [Option.isSome_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
  omega

/-- Past RedemptionDate plus the grace period, an active loan is past NextPaymentDueDate + GracePeriod as the
ledger adds the times. -/
private lemma LendingLedger.LoanPhase.late {l : LendingLedger} {s : VaultSchedule} (hP : l.LoanPhase s) {i : Nat}
    {e : LoanEntry} (he : l.loan? i = some e) (hrem : e.loan.paymentRemaining ≠ 0) :
    e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < l.now := by
  have hdue := l.due_before_redemption hP.reachable _ hP.schedule _ _ he hrem
  have hg := hP.grace i e he
  have hnow := l.now.toNat_lt_size
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  have hsize : UInt32.size = 4294967296 := rfl
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- A ledger whose vault is not coarsened stores a pending loan's principal next to AssetsAvailable exactly. -/
private lemma LendingLedger.Reachable.pending_fits {l : LendingLedger} (hr : l.Reachable) (hnc : l.NotCoarsened)
    {i : Nat} {e : LoanEntry} (he : l.loan? i = some e) :
    STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat) := by
  obtain ⟨na, hna⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨mp, hmp⟩ := hr.scaleInv.principal_grid he
  have hle := l.principalIf_le_sum (fun _ => true) i
  rw [he] at hle
  simp only [LoanEntry.principalIf, if_true] at hle
  have hAD : l.vault.assetsDeployed.toRat = l.principalSum (fun _ => true) := hr.debtInv.deployed
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hpo0 : 0 ≤ e.loan.principalOutstanding.toRat := e.loan.exact.principalOutstanding_nonneg
  unfold LendingLedger.NotCoarsened at hnc
  refine hr.representable _ ((na : ℤ) + mp) (by rw [hna, hmp]; push_cast; ring) (by linarith) ?_
  linarith


/-- A slot read from a list with one slot set. -/
lemma LendingLedger.loan?_of_set {l l' : LendingLedger} {i : Nat} {x : Option LoanEntry}
    (hi : i < l.loans.length) (h : l'.loans = l.loans.set i x) (j : Nat) :
    l'.loan? j = if j = i then x else l.loan? j := by
  unfold LendingLedger.loan?
  rw [h]
  split
  · subst_vars; rw [List.getElem?_set_self hi]; cases x <;> rfl
  · rw [List.getElem?_set_ne (Ne.symm ‹_›)]

/-- A broker slot read from a list with one slot set. -/
private lemma LendingLedger.broker?_of_set {l l' : LendingLedger} {k : Nat} {b' : LoanBroker}
    (h : l'.brokers = l.brokers.set k (some b')) (hk : k < l.brokers.length) (j : Nat) :
    l'.broker? j = if j = k then some b' else l.broker? j := by
  unfold LendingLedger.broker?
  rw [h]
  split
  · subst_vars; rw [List.getElem?_set_self hk]; rfl
  · rw [List.getElem?_set_ne (Ne.symm ‹_›)]

/-- What a LoanDelete writes. The loan's slot empties, its broker's slot holds the broker with the same cover,
and the vault changes only for a pending loan. -/
lemma LendingLedger.loanDelete_frame {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) :
    ∃ (e : LoanEntry) (b b' : LoanBroker), l.loan? i = some e ∧ l.broker? e.brokerIndex = some b ∧
      l'.loans = l.loans.set i none ∧ l'.brokers = l.brokers.set e.brokerIndex (some b') ∧
      b'.coverAvailable = b.coverAvailable ∧ l'.vaultDeleted = l.vaultDeleted ∧ l'.now = l.now ∧
      l'.shares = l.shares ∧ Vault.KeepsSettings l.vault l'.vault ∧
      (e.loan.isPending = false → l'.vault = l.vault) := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  have hs := l.applyLoan_keepsSettings _ u hu
  obtain ⟨e, b, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hlp : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
  have hrel : r.broker'.coverAvailable = b.coverAvailable ∧ (e.loan.isPending = false → r.pool' = l.vault) := by
    by_cases hp : loan.isPending = true
    · obtain ⟨p', raw, d, -, -, -, -, hb'⟩ := Loan.delete_pending_ok_inv loan l.vault r hp hr
      refine ⟨by rw [LoanBroker.releaseLoan_cover _ _ _ hb', hlb], fun hp' => ?_⟩
      rw [hlp] at hp; rw [hp] at hp'; cases hp'
    · have hp' : loan.isPending = false := by simpa using hp
      rw [Loan.delete_active_reduce loan l.vault hp'] at hr
      unfold Loan.deleteActive at hr
      cases hd : loan.broker.releaseLoan loan.broker.debtTotal with
      | error e => rw [hd] at hr; cases hr
      | ok b' =>
        rw [hd] at hr
        simp only [Except.ok.injEq] at hr
        subst hr
        exact ⟨by rw [LoanBroker.releaseLoan_cover _ _ _ hd, hlb], fun _ => rfl⟩
  refine ⟨e, b, r.broker', he, hb, ?_, rfl, hrel.1, rfl, rfl, rfl, hs, hrel.2⟩
  show storeSlot l.loans i none = _
  unfold storeSlot
  rw [if_pos (LendingLedger.loan?_lt he)]


/-- What a default writes on a vault that is not coarsened. The loan's slot holds the closed loan on the same
broker, the broker's cover shrinks, AssetsAvailable + AssetsDeployed shrinks, and the rest is kept. -/
private lemma LendingLedger.default_frame {l l' : LendingLedger} (hr : l.Reachable) (hnc : l.NotCoarsened) {i : Nat}
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) :
    ∃ (e e' : LoanEntry) (b b' : LoanBroker), l.loan? i = some e ∧ l.broker? e.brokerIndex = some b ∧
      l'.loans = l.loans.set i (some e') ∧ e'.brokerIndex = e.brokerIndex ∧ e'.loan.paymentRemaining = 0 ∧
      e'.loan.isPending = false ∧ l'.brokers = l.brokers.set e.brokerIndex (some b') ∧
      b'.coverAvailable.toRat ≤ b.coverAvailable.toRat ∧ l'.vaultDeleted = l.vaultDeleted ∧ l'.now = l.now ∧
      l'.shares = l.shares ∧ Vault.KeepsSettings l.vault l'.vault ∧
      l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat ≤
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  have hs := l.applyLoan_keepsSettings _ u hu
  obtain ⟨e, b, loan, r, he, hb, hw, hc, hok, rfl⟩ := l.applyLoan_manage_inv u i .default hu
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hpend : loan.isPending = false := by
    cases hp : loan.isPending
    · rfl
    · unfold Loan.canManage at hc; simp [hp] at hc
  obtain ⟨r₀, hok₀, hl', hp'⟩ : ∃ r₀ : LoanWithAmounts Vault, (loan.manageDefault l.vault).run = .ok (.ok r₀) ∧
      r.loan' = r₀.loan' ∧ r.pool' = r₀.pool' := by
    simp only [Loan.manage] at hok
    unfold_ter at hok
    walk_ok
    exact ⟨_, ‹_›, rfl, rfl⟩
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  obtain ⟨-, hdc0, hdcpo, haa', had', -⟩ := LendingLedger.default_at_base hr hat hok₀ hnc
  obtain ⟨_, _, c, _, b', -, hdc, -, -, -, hcov, hbr', hloan, -⟩ := Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
  have hpr := (Loan.manageDefault_closes_proof loan l.vault r₀ hok₀).2.2.2.1
  have hbr : r₀.loan'.broker = b' := by rw [show r₀.loan'.broker = r₀.loan'.toRawLoan.broker from rfl, hloan]; rfl
  have hc' : b'.coverAvailable = c := by
    rw [show b'.coverAvailable = b'.toRawLoanBroker.coverAvailable from rfl, hbr']; rfl
  have hdcn := Loan.defaultCover_isNormalized loan l.vault _ hdc
  have hcle : c.toRat ≤ b.coverAvailable.toRat := by
    rw [← hlb]
    exact Number.RoundsToRepresentable.le_of_le_normalized c _
      (operator_sub_rounded_to_nearest _ _ _ loan.broker.wf.coverAvailable_norm hdcn hcov) _
      loan.broker.wf.coverAvailable_norm (by linarith)
  refine ⟨e, { e with loan := r₀.loan' }, b, b', he, hb, ?_, rfl, hpr, ?_, ?_, by rw [hc']; exact hcle, rfl, rfl,
    rfl, hs, ?_⟩
  · show storeSlot l.loans i (some { e with loan := r.loan' }) = _
    unfold storeSlot
    rw [if_pos (LendingLedger.loan?_lt he), hl']
  · show r₀.loan'.toRawLoan.isPending = false
    rw [hloan]
    exact hpend
  · show l.brokers.set e.brokerIndex (some r.loan'.broker) = _
    rw [hl', hbr]
  · show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
    rw [hp', haa', had']
    linarith

/-- The cover bound of a broker list with one slot set to a broker with no more cover than before. -/
private lemma LendingLedger.cover_of_set {l l' : LendingLedger} {k : Nat} {b b' : LoanBroker}
    (hb : l.broker? k = some b) (h : l'.brokers = l.brokers.set k (some b'))
    (hle : b'.coverAvailable.toRat ≤ b.coverAvailable.toRat) :
    ∀ (j : Nat) (b₁ : LoanBroker), l'.broker? j = some b₁ →
      ∃ b₀, l.broker? j = some b₀ ∧ b₁.coverAvailable.toRat ≤ b₀.coverAvailable.toRat := by
  intro j b₁ hj
  rw [LendingLedger.broker?_of_set h (LendingLedger.broker?_lt hb)] at hj
  split at hj
  · subst_vars
    obtain rfl := Option.some.inj hj
    exact ⟨b, hb, hle⟩
  · exact ⟨b₁, hj, le_refl _⟩

/-- The wind-down keeps its hypotheses after a step that empties the slot of one loan, writes no more cover
and adds nothing to AssetsAvailable + AssetsDeployed. -/
private lemma LendingLedger.LoanPhase.of_frame {l l' : LendingLedger} {s : VaultSchedule} (hP : l.LoanPhase s)
    (hr' : l'.Reachable) (hnd : l'.vaultDeleted = l.vaultDeleted) (hset : Vault.KeepsSettings l.vault l'.vault)
    (hnow : l'.now = l.now) {i : Nat} (hi : i < l.loans.length) (hloans : l'.loans = l.loans.set i none)
    (hcov : ∀ (j : Nat) (b₁ : LoanBroker), l'.broker? j = some b₁ →
      ∃ b₀, l.broker? j = some b₀ ∧ b₁.coverAvailable.toRat ≤ b₀.coverAvailable.toRat)
    (htot : l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat ≤
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat) :
    l'.LoanPhase s := by
  have hbase : l'.vault.baseExponent = l.vault.baseExponent := by
    unfold Vault.baseExponent; rw [hset.numericType, hset.scale]
  have hold : ∀ (j : Nat) (e : LoanEntry), l'.loan? j = some e → l.loan? j = some e := by
    intro j e hj
    rw [LendingLedger.loan?_of_set hi hloans] at hj
    split at hj
    · cases hj
    · exact hj
  have hnc : l.NotCoarsened → l'.NotCoarsened := by
    unfold LendingLedger.NotCoarsened
    intro h
    rw [hbase]
    linarith
  refine ⟨hr', by rw [hnd]; exact hP.notDeleted, by rw [hset.schedule]; exact hP.schedule,
    by rw [hnow]; exact hP.past, fun j e hj => by rw [hnow]; exact hP.grace j e (hold j e hj),
    fun j e hj hp => hnc (hP.pending j e (hold j e hj) hp),
    fun j e hj hp hrem => hnc (hP.active j e (hold j e hj) hp hrem),
    fun j b₁ hj => ?_⟩
  obtain ⟨b₀, hb₀, hle⟩ := hcov j b₁ hj
  rw [hset.numericType]
  exact le_trans hle (hP.cover j b₀ hb₀)


/-- A LoanDelete adds nothing to AssetsAvailable + AssetsDeployed on a vault that is not coarsened. -/
private lemma LendingLedger.delete_total {l l' : LendingLedger} (hr : l.Reachable) (hnc : l.NotCoarsened) {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) :
    l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat ≤
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
  have htot := LendingLedger.flow_step l l' _ hr h hnc (fun ⟨_, _, _, h'⟩ => by cases h')
  have h0 : (l.flowOf (.loanDelete i)).net = 0 := AssetFlows.net_zero
  rw [h0, add_zero] at htot
  exact le_of_eq htot

/-- One loan of the wind-down closes. A pending or closed loan is deleted at once, an active loan is defaulted
and then deleted, and the wind-down keeps its hypotheses. -/
private lemma LendingLedger.LoanPhase.close_one {l : LendingLedger} {s : VaultSchedule} (hP : l.LoanPhase s)
    {i : Nat} {e : LoanEntry} (he : l.loan? i = some e) :
    ∃ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' ∧ l'.LoanPhase s ∧
      l'.loans = l.loans.set i none := by
  have hr := hP.reachable
  have hnd := hP.notDeleted
  have hi := LendingLedger.loan?_lt he
  by_cases hp : e.loan.isPending = true
  · -- a pending loan is deleted at once
    have hnc := hP.pending i e he hp
    obtain ⟨l', h⟩ := LendingLedger.pending_resolvable_proof l hr hr.holdsAsset.maxValue_le hnd i e he hp
      (hr.pending_fits hnc he)
    obtain ⟨e₀, b, b', he₀, hb, hloans, hbr, hcov, hnd', hnow, -, hset, -⟩ := LendingLedger.loanDelete_frame h
    rw [he] at he₀
    obtain rfl := Option.some.inj he₀
    exact ⟨[.loanDelete i], l', .single (show l.WholeWindDownTx (.loanDelete i) from trivial) h,
      hP.of_frame (hr.apply h) hnd' hset hnow hi hloans
        (LendingLedger.cover_of_set hb hbr (le_of_eq (by rw [hcov]))) (LendingLedger.delete_total hr hnc h), hloans⟩
  have hnp : e.loan.isPending = false := by simpa using hp
  by_cases hrem : e.loan.paymentRemaining = 0
  · -- a closed loan too
    obtain ⟨l', h⟩ := LendingLedger.closed_loan_deletable l hr hnd i e he hrem hnp
    obtain ⟨e₀, b, b', he₀, hb, hloans, hbr, hcov, hnd', hnow, -, hset, hvault⟩ := LendingLedger.loanDelete_frame h
    rw [he] at he₀
    obtain rfl := Option.some.inj he₀
    exact ⟨[.loanDelete i], l', .single (show l.WholeWindDownTx (.loanDelete i) from trivial) h,
      hP.of_frame (hr.apply h) hnd' hset hnow hi hloans
        (LendingLedger.cover_of_set hb hbr (le_of_eq (by rw [hcov]))) (by rw [hvault hnp]), hloans⟩
  -- an active loan is past its grace period: it is defaulted, then deleted as a closed loan
  have hnc := hP.active i e he hnp hrem
  have hd : e.loan.isDefault = false := by
    obtain ⟨s', hinv⟩ := hr.loansInv
    obtain ⟨t, -, hreach⟩ := hinv.reachable i e he
    cases hdf : e.loan.isDefault
    · rfl
    · exact absurd (hreach.default_paidOff hdf) hrem
  obtain ⟨l₁, h₁⟩ := LendingLedger.default_possible_proof l hr hnd hr.holdsAsset i e he hnp hd hrem (hP.late he hrem)
    hnc (hr.assetsAvailable_units hr.holdsAsset) hr.yield_lt (hr.interest_le_yield he hnp)
    (fun b hb => lt_of_le_of_lt (hP.cover _ b hb) (NumericType.maxAmount_lt _))
  obtain ⟨e₀, e', b, b', he₀, hb, hloans₁, hbi, hrem', hnp', hbr₁, hcov₁, hnd₁, hnow₁, -, hset₁, htot₁⟩ :=
    LendingLedger.default_frame hr hnc h₁
  rw [he] at he₀
  obtain rfl := Option.some.inj he₀
  have hr₁ := hr.apply h₁
  have he₁ : l₁.loan? i = some e' := by rw [LendingLedger.loan?_of_set hi hloans₁, if_pos rfl]
  obtain ⟨l₂, h₂⟩ := LendingLedger.closed_loan_deletable l₁ hr₁ (by rw [hnd₁]; exact hnd) i e' he₁ hrem' hnp'
  obtain ⟨e₂, b₂, b₂', he₂, hb₂, hloans₂, hbr₂, hcov₂, hnd₂, hnow₂, -, hset₂, hvault₂⟩ :=
    LendingLedger.loanDelete_frame h₂
  rw [he₁] at he₂
  obtain rfl := Option.some.inj he₂
  have hbb : b₂ = b' := by
    rw [LendingLedger.broker?_of_set hbr₁ (LendingLedger.broker?_lt hb), hbi, if_pos rfl] at hb₂
    exact (Option.some.inj hb₂).symm
  subst hbb
  have hl₂ : l₂.loans = l.loans.set i none := by rw [hloans₂, hloans₁, List.set_set]
  have hb₂l : l₂.brokers = l.brokers.set e.brokerIndex (some b₂') := by rw [hbr₂, hbr₁, hbi, List.set_set]
  refine ⟨[.loanManage i .default, .loanDelete i], l₂,
    (LendingLedger.WindsDownWhole.single (show l.WholeWindDownTx (.loanManage i .default) from trivial) h₁).trans
      (LendingLedger.WindsDownWhole.single (show l₁.WholeWindDownTx (.loanDelete i) from trivial) h₂),
    hP.of_frame (hr₁.apply h₂) (by rw [hnd₂, hnd₁]) (hset₁.trans hset₂) (by rw [hnow₂, hnow₁]) hi hl₂
      (LendingLedger.cover_of_set hb hb₂l (by rw [hcov₂]; exact hcov₁)) (by rw [hvault₂ hnp']; exact htot₁), hl₂⟩

/-- The wind-down closes every loan, keeping its hypotheses. -/
lemma LendingLedger.LoanPhase.close_all {s : VaultSchedule} :
    ∀ (n : Nat) (l : LendingLedger), l.LoanPhase s → l.loans.countP (·.isSome) = n →
      ∃ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' ∧ l'.LoanPhase s ∧
        ∀ i, l'.loan? i = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hP hn
    by_cases hex : ∃ i e, l.loan? i = some e
    · obtain ⟨i, e, he⟩ := hex
      obtain ⟨txs, l', hw, hP', hloans⟩ := hP.close_one he
      obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
      have hlt : l'.loans.countP (·.isSome) < n := by
        rw [hloans, ← hn]
        exact List.countP_set_none_lt _ i e (by rw [List.getElem?_eq_getElem hi, hei])
      obtain ⟨txs', l'', hw', hP'', hnone⟩ := ih _ hlt l' hP' rfl
      exact ⟨txs ++ txs', l'', hw.trans hw', hP'', hnone⟩
    · push Not at hex
      refine ⟨[], l, .refl, hP, fun i => ?_⟩
      cases h : l.loan? i with
      | none => rfl
      | some e => exact absurd h (hex i e)

end XRPL.Model.Lending
