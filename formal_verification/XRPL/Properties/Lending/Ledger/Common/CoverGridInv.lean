import XRPL.Properties.Lending.Ledger.Common.VaultGrid
import XRPL.Properties.Lending.LoanBroker.Common.CoverGrid
import XRPL.Properties.Lending.Loan.Common.Debt

/-! # CoverAvailable on the base grid

Every cover movement is clamped or floored onto a grid at or above the base, and a default's cover is a credit
to AssetsAvailable on the base grid, so on an IOU vault every broker keeps CoverAvailable whole base units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)


/-- A default takes a whole number of base units off CoverAvailable when AssetsAvailable is whole base units. -/
private lemma Loan.manageDefault_coverOnGrid (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hfr : loan.broker.numericType = .fractional) (hv : Number.OnGrid v.baseExponent v.assetsAvailable)
    (hc : Number.OnGrid v.baseExponent loan.broker.coverAvailable)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Number.OnGrid v.baseExponent r.loan'.broker.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨_, _, c, _, b, -, hdc, -, -, -, hcov, hbr, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  have hdcg : Number.OnGrid v.baseExponent r.amountToPool := by
    unfold Loan.defaultCover at hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨st, hst, hdc⟩ := bind_ok_peel _ _ _ hdc
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ st _ hv ⟨hb, v.baseExponent_bounds.2.1⟩
      (by rw [hfr]; intro h'; cases h') hst hdc
  have hcb : r.loan'.broker.coverAvailable = c := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]
    show b.toRawLoanBroker.coverAvailable = _
    rw [hbr]; rfl
  rw [hcb]
  exact Number.OnGrid.sub hc hdcg hsr hcov

/-- A payment keeps CoverAvailable whole base units: a fee that joins the cover is floored onto the grid of the
new cover. -/
private lemma Loan.pay_coverOnGrid (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hfr : loan.broker.numericType = .fractional)
    (hc : Number.OnGrid v.baseExponent loan.broker.coverAvailable)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loan'.broker.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, _, toBroker, cover', debtTotal', raw, broker', hsums, -, -, hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  -- the unimpair step keeps the asset and the scale, so it keeps the base exponent
  have hbe : p.pool.baseExponent = v.baseExponent := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
      obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
      rfl
    · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        obtain ⟨-, hnt1, hsc1⟩ := Vault.poolAdjust_sums v p.pool _ hadj1
        unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt1, hsc1]
  have hcb : r.loan'.broker.coverAvailable = cover' := by
    rw [show r.loan'.broker = broker' from (congrArg RawLoan.broker (RawLoan.to_lawful_ok hloan).1 :),
      show broker'.coverAvailable = broker'.toRawLoanBroker.coverAvailable from rfl,
      (RawLoanBroker.to_lawful_ok hbroker).1]
  rw [hcb]
  rcases hsums.fee with ⟨-, -, hcv⟩ | ⟨-, st, hst', hnum, hadd⟩
  · rw [hcv, hpb]; exact hc
  · rw [hpb, hbe] at hst'
    rw [hpb] at hadd
    exact Number.OnGrid.add hc (sumRoundAndSubtract_onGrid _ _ _ _ _ st _ hc ⟨hb, v.baseExponent_bounds.2.1⟩
      (by rw [hfr]; intro h'; cases h') hst' hnum) hsr hadd

/-- A cover withdrawal that passed its preflight withdraws an amount of the asset. -/
private lemma LendingTx.preflight_coverWithdraw (l : LendingLedger) (i : Nat) (amount : STAmount)
    (hfr : l.vault.numericType = .fractional)
    (hpre : ((LendingTx.loanBrokerCoverWithdraw i amount).preflight l).isTesSuccess = true) :
    amount.CanonicalOrZero := by
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hc
    simp only [Bool.and_eq_true, isCanonicalAmount, isPositiveAmount, hfr, NumericType.isIntegral,
      Bool.false_eq_true, if_false, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hty, hm⟩, -, hnz⟩ := hc
    rcases hm with hm | ⟨⟨⟨hlo, hhi⟩, helo⟩, hehi⟩
    · exact absurd hm hnz
    · refine Or.inl ⟨fun hi => ?_, fun _ => ⟨hty, hlo, hhi, helo, hehi⟩⟩
      exfalso
      unfold STAmount.integral at hi
      rw [hty] at hi
      cases hi
  · exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)

/-- The broker a broker transaction writes keeps its cover on the grid. A new broker has no cover, an
update keeps it, and a deposit, withdrawal or clawback moves it by whole base units. -/
private lemma LendingLedger.applyBroker_coverOnGrid (l : LendingLedger) (hscale : l.ScaleInv) (tx : LendingTx)
    (hpre : (tx.preflight l).isTesSuccess = true) (u : BrokerEffect) (h : (l.applyBroker tx).run = .ok (.ok u))
    (hfr : l.vault.numericType = .fractional) (b' : LoanBroker) (hb' : u.broker = some b')
    (hold : ∀ b, l.broker? u.index = some b → Number.OnGrid l.vault.baseExponent b.coverAvailable) :
    Number.OnGrid l.vault.baseExponent b'.coverAvailable := by
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
    rw [hcz]
    exact Number.OnGrid.zero _
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
    rw [hcz]
    exact hold _ hb
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hb := ‹l.broker? i = some _›
    have hbfr := (hscale.brokers _ _ hb).trans hfr
    exact LoanBroker.coverDeposit_onGrid _ l.vault a _ (fun h' => by rw [hbfr] at h'; cases h') (hold _ hb) ‹_›
  | loanBrokerCoverWithdraw i a =>
    have hd := LendingTx.preflight_coverWithdraw l i a hfr hpre
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hb := ‹l.broker? i = some _›
    exact LoanBroker.coverWithdraw_onGrid _ l.vault a _ hd (hold _ hb) ‹_›
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    have hb := ‹l.broker? i = some _›
    have hbfr := (hscale.brokers _ _ hb).trans hfr
    exact LoanBroker.coverClawback_onGrid _ l.vault a _ hbfr (hold _ hb) ‹_›
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- What every reachable ledger keeps about the brokers' cover: on an IOU vault every stored broker's
CoverAvailable is whole base units, beside the vault's own base grid. -/
structure LendingLedger.CoverGridInv (l : LendingLedger) : Prop where
  grid : l.GridInv
  cover : l.vault.numericType = .fractional → ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
    Number.OnGrid l.vault.baseExponent b.coverAvailable

/-- Releasing a loan keeps the cover. -/
lemma LoanBroker.releaseLoan_cover (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.coverAvailable = lb.coverAvailable := by
  unfold LoanBroker.releaseLoan at h
  exact (congrArg RawLoanBroker.coverAvailable (RawLoanBroker.to_lawful_ok h).1 :)

/-- The broker a loan transaction writes keeps its cover on the grid. -/
private lemma LendingLedger.CoverGridInv.loan_cover {l : LendingLedger} (hinv : l.CoverGridInv) {tx : LendingTx}
    {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) (hfr : l.vault.numericType = .fractional) :
    ∃ b, l.broker? u.brokerIndex = some b ∧ Number.OnGrid l.vault.baseExponent u.broker.coverAvailable := by
  have hscale := hinv.grid.scale
  have hcov := hinv.cover hfr
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    obtain ⟨_, _, _, -, hbr⟩ := Loan.create_ok_broker broker l.vault principal rates fees _ ao twoStep r hcr
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.loan'.broker.toRawLoanBroker.coverAvailable
    rw [hbr]
    exact hcov i broker hb
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.loan'.broker.coverAvailable
    rw [Loan.accept_broker loan _ r hr, hlb]
    exact hcov _ broker hb
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.loan'.broker.coverAvailable
    cases action with
    | impair => rw [(Loan.manageImpair_debt loan l.vault l.now r hr).1, hlb]; exact hcov _ broker hb
    | unimpair => rw [(Loan.manageUnimpair_debt loan l.vault r hr).1, hlb]; exact hcov _ broker hb
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      rename_i rd hd
      have hbfr : loan.broker.numericType = .fractional := by rw [hlb, hscale.brokers _ broker hb, hfr]
      exact Loan.manageDefault_coverOnGrid loan l.vault rd hbfr (hinv.grid.grid hfr).1
        (by rw [hlb]; exact hcov _ broker hb) hd
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    have hbfr : loan.broker.numericType = .fractional := by rw [hlb, hscale.brokers _ broker hb, hfr]
    exact ⟨broker, hb, Loan.pay_coverOnGrid loan l.vault paymentType amount l.now r hbfr
      (by rw [hlb]; exact hcov _ broker hb) hr⟩
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.broker'.coverAvailable
    by_cases hp : loan.isPending = true
    · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan l.vault r hp hr
      rw [LoanBroker.releaseLoan_cover _ _ _ hrel, hlb]; exact hcov _ broker hb
    · simp only [Loan.delete, Bool.not_eq_true] at hr hp
      rw [hp] at hr
      unfold_ter at hr
      walk_ok
      rw [LoanBroker.releaseLoan_cover _ _ _ ‹Loan.deleteActive _ = Except.ok _›, hlb]
      exact hcov _ broker hb
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.CoverGridInv.step {l l' : LendingLedger} (hinv : l.CoverGridInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.CoverGridInv := by
  have hpre := (LendingLedger.apply_checked h).1
  have hgrid := hinv.grid.step h
  refine ⟨hgrid, fun hfr' => ?_⟩
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).brokers = l.brokers ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    rw [hrest.2] at hfr' ⊢
    rw [hbe]
    intro j b hb
    have hb0 : l.broker? j = some b := by unfold LendingLedger.broker? at hb ⊢; rw [hrest.1] at hb; exact hb
    exact hinv.cover (hk.numericType ▸ hfr') j b hb0
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    intro j b' hb'
    rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj] at hb'
      exact l.applyBroker_coverOnGrid hinv.grid.scale tx hpre u hu hfr' b' hb' (fun b hb => hinv.cover hfr' _ b hb)
    · rw [if_neg hj] at hb'; exact hinv.cover hfr' j b' hb'
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    have hfr : l.vault.numericType = .fractional := hs.numericType ▸ hfr'
    obtain ⟨b, hb, hcu⟩ := hinv.loan_cover hu hfr
    intro j b' hb'
    show Number.OnGrid u.vault.baseExponent _
    rw [hs.baseExponent_eq]
    rw [LendingLedger.broker?_commitLoan l u b hb] at hb'
    split at hb'
    · cases hb'; exact hcu
    · exact hinv.cover hfr j b' hb'
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hinv.cover hfr'
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hinv.cover hfr'

/-- A genesis ledger has no brokers. -/
lemma LendingLedger.Genesis.coverGridInv {g : LendingLedger} (hg : g.Genesis) : g.CoverGridInv := by
  refine ⟨hg.gridInv, fun _ j b hb => ?_⟩
  unfold LendingLedger.broker? at hb; rw [hg.no_brokers] at hb; cases hb

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.coverGridInv {l : LendingLedger} (hr : l.Reachable) : l.CoverGridInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.coverGridInv) (fun _ _ _ hi ha => hi.step ha) hr

end XRPL.Model.Lending
