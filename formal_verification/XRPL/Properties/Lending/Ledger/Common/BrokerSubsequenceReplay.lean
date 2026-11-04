import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceDefs
import XRPL.Properties.Lending.Ledger.Common.BrokerSteps
import XRPL.Properties.Lending.Ledger.Common.Exits

/-! # A broker transaction replayed on another ledger

A LoanBrokerSet update, a cover deposit, withdrawal or clawback, or a LoanBrokerDelete reads the broker, the vault's
asset and base exponent, and whether the vault exists. On a second ledger that holds the same broker under another
number, it succeeds the same way and gives the same broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The Open limit of a vault is `9·10^15` base units. -/
private lemma Vault.pool_openLimit_rep (v : Vault) :
    AssetPool.openLimit v = Number.from_rep 9 (15 + v.baseExponent) largeRange.min largeRange.max .to_nearest :=
  rfl

/-- The update checks read the vault only through its base exponent. -/
private lemma LoanBroker.canUpdate_vault (lb : LoanBroker) {v v' : Vault} (h : v'.baseExponent = v.baseExponent)
    (debtMaximum : Option Number) : lb.canUpdate v' debtMaximum = lb.canUpdate v debtMaximum := by
  simp only [LoanBroker.canUpdate, Vault.pool_baseExponent, h]

/-- The cover deposit reads the vault only through its base exponent. -/
private lemma LoanBroker.coverDeposit_vault (lb : LoanBroker) {v v' : Vault} (h : v'.baseExponent = v.baseExponent)
    (amount : STAmount) : lb.canCoverDeposit v' amount = lb.canCoverDeposit v amount ∧
      lb.coverDeposit v' amount = lb.coverDeposit v amount := by
  simp only [LoanBroker.canCoverDeposit, LoanBroker.coverDeposit, LoanBroker.roundedCoverAmount,
    LoanBroker.checkCoverOpenLimit, Vault.pool_baseExponent, Vault.pool_openLimit_rep, h, and_self]

/-- The cover withdrawal reads the vault only through its base exponent. -/
private lemma LoanBroker.coverWithdraw_vault (lb : LoanBroker) {v v' : Vault} (h : v'.baseExponent = v.baseExponent)
    (amount : STAmount) : lb.canCoverWithdraw v' amount = lb.canCoverWithdraw v amount ∧
      lb.coverWithdraw v' amount = lb.coverWithdraw v amount := by
  simp only [LoanBroker.canCoverWithdraw, LoanBroker.coverWithdraw, Vault.pool_baseExponent, h, and_self]

/-- The cover clawback reads the vault only through its base exponent. -/
private lemma LoanBroker.coverClawback_vault (lb : LoanBroker) {v v' : Vault} (h : v'.baseExponent = v.baseExponent)
    (amount : Option STAmount) : lb.canCoverClawback v' amount = lb.canCoverClawback v amount ∧
      lb.coverClawback v' amount = lb.coverClawback v amount := by
  simp only [LoanBroker.canCoverClawback, LoanBroker.coverClawback, LoanBroker.roundedCoverClawback,
    Vault.pool_baseExponent, h, and_self]

/-- The delete check never reads the vault: a broker without loans has no debt. -/
private lemma LoanBroker.canDelete_vault (lb : LoanBroker) (v v' : Vault) : lb.canDelete v' = lb.canDelete v := by
  unfold LoanBroker.canDelete
  by_cases h0 : lb.loanCount = 0
  · rw [h0, show lb.debtTotal = Number.zero from lb.valid.empty_broker h0]
    rfl
  · have hc : (lb.loanCount != 0) = true := by simpa using h0
    rw [if_pos hc, if_pos hc]

/-- A broker transaction on broker `k` of `l` runs the same on a ledger holding the same broker at `k'` with the
same base exponent, and writes the same broker at `k'`. -/
private lemma LendingLedger.applyBroker_transfer {l L : LendingLedger} {k k' : Nat} {b : LoanBroker}
    (hb : l.broker? k = some b) (hb' : L.broker? k' = some b) (hbe : L.vault.baseExponent = l.vault.baseExponent)
    {tx : LendingTx} (hk : l.txBroker? tx = some k) {u : BrokerEffect}
    (hu : (l.applyBroker tx).run = .ok (.ok u)) :
    u.index = k ∧ (L.applyBroker (tx.withBroker k')).run = .ok (.ok { u with index := k' }) := by
  cases tx
  case loanBrokerCreate =>
    simp only [LendingLedger.txBroker?, Option.some.injEq] at hk
    have := LendingLedger.broker?_lt hb
    omega
  all_goals first
    | (simp only [LendingLedger.applyBroker] at hu; cases hu)
    | skip
  all_goals
    simp only [LendingLedger.txBroker?, Option.some.injEq] at hk
    subst hk
    simp only [LendingLedger.applyBroker, LendingTx.withBroker, hb, hb', LoanBroker.canUpdate_vault b hbe,
      (LoanBroker.coverDeposit_vault b hbe _).1, (LoanBroker.coverDeposit_vault b hbe _).2,
      (LoanBroker.coverWithdraw_vault b hbe _).1, (LoanBroker.coverWithdraw_vault b hbe _).2,
      (LoanBroker.coverClawback_vault b hbe _).1, (LoanBroker.coverClawback_vault b hbe _).2,
      LoanBroker.canDelete_vault b l.vault L.vault] at hu ⊢
    unfold_ter at hu ⊢
    walk_ok
    refine ⟨rfl, ?_⟩
    split <;> simp_all

/-- The DebtMaximum a broker transaction leaves on a broker that had `debtMaximum`. Only an update sets it. -/
private def LendingTx.debtMaximumAfter (debtMaximum : Number) : LendingTx → Number
  | .loanBrokerUpdate _ dm => dm.getD debtMaximum
  | _ => debtMaximum

/-- A cover transaction changes only the cover. -/
private lemma LoanBroker.applyCoverTransaction_raw (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (r : LoanBrokerCoverResult) (h : lb.applyCoverTransaction d a = .ok r) :
    r.loanBroker'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := r.loanBroker'.coverAvailable } := by
  unfold LoanBroker.applyCoverTransaction at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  cases d <;>
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [(RawLoanBroker.to_lawful_ok hb).1]

/-- What a broker transaction on broker `k` writes at `k`: nothing for a LoanBrokerDelete, else the broker with the
DebtMaximum of an update or a new cover. -/
private lemma LendingLedger.applyBroker_shape {l : LendingLedger} {k : Nat} {b : LoanBroker}
    (hb : l.broker? k = some b) {tx : LendingTx} (hk : l.txBroker? tx = some k) {u : BrokerEffect}
    (hu : (l.applyBroker tx).run = .ok (.ok u)) :
    u.index = k ∧ ((tx = .loanBrokerDelete k ∧ u.broker = none) ∨ ((∀ i, tx ≠ .loanBrokerDelete i) ∧
      ∃ c, u.broker = some c ∧ c.toRawLoanBroker = { b.toRawLoanBroker with
        debtMaximum := tx.debtMaximumAfter b.debtMaximum, coverAvailable := c.coverAvailable })) := by
  cases tx
  case loanBrokerCreate =>
    simp only [LendingLedger.txBroker?, Option.some.injEq] at hk
    have := LendingLedger.broker?_lt hb
    omega
  all_goals first
    | (simp only [LendingLedger.applyBroker] at hu; cases hu)
    | skip
  all_goals
    simp only [LendingLedger.txBroker?, Option.some.injEq] at hk
    subst hk
    simp only [LendingLedger.applyBroker, LoanBroker.coverDeposit, LoanBroker.coverWithdraw,
      LoanBroker.coverClawback, hb] at hu
    unfold_ter at hu
    walk_ok
  all_goals first
    | exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | (refine ⟨rfl, Or.inr ⟨fun _ => nofun, _, rfl, ?_⟩⟩
       exact LoanBroker.applyCoverTransaction_raw _ _ _ _ ‹_›)
    | (refine ⟨rfl, Or.inr ⟨fun _ => nofun, _, rfl, ?_⟩⟩
       rw [(RawLoanBroker.to_lawful_ok ‹LoanBroker.update _ _ = _›).1]
       rfl)

/-- A transaction that succeeded wrote what its operation returned. -/
private lemma TerExcept.map_run_ok {ε β : Type} {x : TerExcept ε} {f : ε → β} {u : ε} (h : x.run = .ok (.ok u)) :
    (f <$> x).run = .ok (.ok (f u)) := by
  simp only [ExceptT.run, Functor.map, ExceptT.map, ExceptT.mk, bind, Except.bind] at h ⊢
  rw [h]
  rfl

/-- A broker transaction other than a create replays on a ledger that holds the same broker under another number,
with the same asset and base exponent and a vault that exists. Both write the same broker. -/
lemma LendingLedger.brokerTx_replay_same {l L lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}
    (hb : l.broker? k = some b) (hb' : L.broker? k' = some b')
    (hraw : b'.toRawLoanBroker = b.toRawLoanBroker) (hdel : L.vaultDeleted = false)
    (hnt : L.vault.numericType = l.vault.numericType) (hscale : L.vault.scale = l.vault.scale)
    (tx : LendingTx) (htx : tx.isBroker = true) (hk : l.txBroker? tx = some k)
    (hok : (l.apply tx).run = .ok (.ok lb)) :
    ∃ Lb, (L.apply (tx.withBroker k')).run = .ok (.ok Lb) ∧
      (lb.broker? k).map LoanBroker.toRawLoanBroker = (Lb.broker? k').map LoanBroker.toRawLoanBroker := by
  obtain rfl : b' = b := broker_eq_of_raw hraw
  have hbe : L.vault.baseExponent = l.vault.baseExponent := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent
    rw [hnt, hscale]
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker htx hok
  obtain ⟨hi, hu'⟩ := LendingLedger.applyBroker_transfer hb hb' hbe hk hu
  have hpreL : (tx.withBroker k').preflight L = .tesSUCCESS := by
    have h1 : (tx.withBroker k').preflight L = tx.preflight l := by
      cases tx <;> simp only [LendingTx.withBroker, LendingTx.preflight, hnt]
    rw [h1]
    exact (TER.isTesSuccess_iff _).mp (LendingLedger.apply_checked hok).1
  refine ⟨L.commitBroker { u with index := k' }, ?_, ?_⟩
  · rw [LendingLedger.apply_of_preflight hpreL]
    have hbL : (tx.withBroker k').isBroker = true := by
      cases tx <;> simp_all [LendingTx.withBroker, LendingTx.isBroker]
    revert hu' hbL
    generalize tx.withBroker k' = tx'
    intro hu' hbL
    cases tx' <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hbL <;>
    · simp only [LendingLedger.applyChecked, hdel, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
        ↓reduceIte]
      exact TerExcept.map_run_ok hu'
  · simp only [LendingLedger.broker?_commitBroker, hi, LendingLedger.broker?_lt hb, LendingLedger.broker?_lt hb',
      ↓reduceIte]

/-- A broker transaction other than a create that succeeds on two ledgers whose brokers differ only in the cover
leaves brokers that differ only in the cover, and equal covers stay equal. -/
lemma LendingLedger.brokerTx_result_same {l L lb Lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}
    (hb : l.broker? k = some b) (hb' : L.broker? k' = some b')
    (hraw : b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable })
    (hnt : L.vault.numericType = l.vault.numericType) (hscale : L.vault.scale = l.vault.scale)
    (tx : LendingTx) (htx : tx.isBroker = true) (hk : l.txBroker? tx = some k)
    (hok : (l.apply tx).run = .ok (.ok lb)) (hok' : (L.apply (tx.withBroker k')).run = .ok (.ok Lb)) :
    (lb.broker? k = none ∧ Lb.broker? k' = none) ∨ ∃ c c', lb.broker? k = some c ∧ Lb.broker? k' = some c' ∧
      c'.toRawLoanBroker = { c.toRawLoanBroker with coverAvailable := c'.coverAvailable } ∧
      (b'.coverAvailable.toRat = b.coverAvailable.toRat → c'.coverAvailable.toRat = c.coverAvailable.toRat) := by
  have hlt := LendingLedger.broker?_lt hb
  have hlt' := LendingLedger.broker?_lt hb'
  have hbL : (tx.withBroker k').isBroker = true := by
    cases tx <;> simp_all [LendingTx.withBroker, LendingTx.isBroker]
  have hk' : L.txBroker? (tx.withBroker k') = some k' := by
    cases tx <;> simp_all [LendingTx.isBroker, LendingTx.withBroker, LendingLedger.txBroker?]
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker htx hok
  obtain ⟨u', hu', rfl⟩ := LendingLedger.apply_broker hbL hok'
  obtain ⟨hi, hs⟩ := LendingLedger.applyBroker_shape hb hk hu
  obtain ⟨hi', hs'⟩ := LendingLedger.applyBroker_shape hb' hk' hu'
  simp only [LendingLedger.broker?_commitBroker, hi, hi', hlt, hlt', ↓reduceIte]
  rcases hs with ⟨rfl, hn⟩ | ⟨hnd, c, hc, hcraw⟩
  · rcases hs' with ⟨-, hn'⟩ | ⟨hnd', -⟩
    · exact Or.inl ⟨hn, hn'⟩
    · exact absurd rfl (hnd' k')
  rcases hs' with ⟨hd', -⟩ | ⟨-, c', hc', hcraw'⟩
  · exfalso
    cases tx <;> simp only [LendingTx.withBroker, reduceCtorEq] at hd'
    exact hnd _ rfl
  refine Or.inr ⟨c, c', hc, hc', ?_, fun hcov => ?_⟩
  · have hdm : b'.debtMaximum = b.debtMaximum := (congrArg RawLoanBroker.debtMaximum hraw :)
    have hafter : (tx.withBroker k').debtMaximumAfter b'.debtMaximum = tx.debtMaximumAfter b.debtMaximum := by
      rw [hdm]
      cases tx <;> rfl
    rw [hcraw', hafter, hraw, hcraw]
  · have hcv : b'.coverAvailable = b.coverAvailable :=
      Number.isNormalized.toRat_inj b'.wf.coverAvailable_norm b.wf.coverAvailable_norm hcov
    obtain rfl : b' = b := broker_eq_of_raw (by rw [hraw, hcv])
    have hbe : L.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent
      rw [hnt, hscale]
    have h2 := (LendingLedger.applyBroker_transfer hb hb' hbe hk hu).2
    rw [hu'] at h2
    simp only [Except.ok.injEq] at h2
    subst h2
    rw [hc] at hc'
    obtain rfl := Option.some.inj hc'
    rfl

end XRPL.Model.Lending
