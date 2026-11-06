import XRPL.Properties.Lending.Ledger.Common.BaseGrid

/-! # CoverAvailable in whole units on an XRP or MPT vault

Every cover movement of an XRP or MPT broker is a whole number of units, so on such a vault every broker keeps
CoverAvailable whole units, as `CoverGridInv` shows for an IOU. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- On an XRP or MPT vault every stored broker's CoverAvailable is whole base units. -/
def LendingLedger.IntegralCover (l : LendingLedger) : Prop :=
  l.vault.numericType.isIntegral = true → ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
    Number.OnGrid l.vault.baseExponent b.coverAvailable

/-- A default takes a whole number of base units off CoverAvailable when AssetsAvailable is whole base units. -/
private lemma Loan.manageDefault_coverOnGrid' (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hint : loan.broker.numericType.isIntegral = true → v.baseExponent = 0)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable)
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
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ st _ hv ⟨hb, v.baseExponent_bounds.2.1⟩ hint hst hdc
  have hcb : r.loan'.broker.coverAvailable = c := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]
    show b.toRawLoanBroker.coverAvailable = _
    rw [hbr]; rfl
  rw [hcb]
  exact Number.OnGrid.sub hc hdcg hsr hcov

/-- A payment keeps CoverAvailable whole base units: a fee that joins the cover is floored onto the grid of the
new cover. -/
private lemma Loan.pay_coverOnGrid' (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hint : loan.broker.numericType.isIntegral = true → v.baseExponent = 0)
    (hc : Number.OnGrid v.baseExponent loan.broker.coverAvailable)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loan'.broker.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, _, toBroker, cover', debtTotal', raw, broker', hsums, -, -, hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v p.pool _ hu
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
      hint hst' hnum) hsr hadd

/-- A cover withdrawal of an XRP or MPT asset that passed its preflight withdraws an amount of the asset. -/
private lemma LendingTx.preflight_coverWithdraw' (l : LendingLedger) (i : Nat) (amount : STAmount)
    (hint : l.vault.numericType.isIntegral = true)
    (hmax : l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpre : ((LendingTx.loanBrokerCoverWithdraw i amount).preflight l).isTesSuccess = true) :
    amount.CanonicalOrZero := by
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hc
    simp only [Bool.and_eq_true, isCanonicalAmount, hint, if_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨hty, hoff, hval⟩, -⟩ := hc
    refine Or.inl ⟨fun _ => ⟨⟨by rw [hty]; exact hint, hoff, by rw [hty]; exact hval⟩, by rw [hty]; exact hmax⟩,
      fun hfr => ?_⟩
    exfalso
    unfold STAmount.integral at hfr
    rw [hty, hint] at hfr
    cases hfr
  · exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)

/-- The broker a broker transaction writes on an XRP or MPT vault keeps its cover in whole units. -/
private lemma LendingLedger.applyBroker_coverOnGrid' (l : LendingLedger) (hscale : l.ScaleInv) (tx : LendingTx)
    (hpre : (tx.preflight l).isTesSuccess = true) (u : BrokerEffect) (h : (l.applyBroker tx).run = .ok (.ok u))
    (hint : l.vault.numericType.isIntegral = true) (hmax : l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (b' : LoanBroker) (hb' : u.broker = some b')
    (hold : ∀ b, l.broker? u.index = some b → Number.OnGrid l.vault.baseExponent b.coverAvailable) :
    Number.OnGrid l.vault.baseExponent b'.coverAvailable := by
  have hb0 : l.vault.baseExponent = 0 := Vault.baseExponent_integral l.vault hint
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
    exact LoanBroker.coverDeposit_onGrid _ l.vault a _ (fun _ => hb0) (hold _ hb) ‹_›
  | loanBrokerCoverWithdraw i a =>
    have hd := LendingTx.preflight_coverWithdraw' l i a hint hmax hpre
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
    have hbnt := hscale.brokers _ _ hb
    exact LoanBroker.coverClawback_onGrid_integral _ l.vault a _ (by rw [hbnt]; exact hint) (by rw [hbnt]; exact hmax)
      (hold _ hb) ‹_›
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- The broker a loan transaction writes on an XRP or MPT vault keeps its cover in whole units. -/
private lemma LendingLedger.IntegralCover.loan_cover {l : LendingLedger} (hr : l.Reachable) (hinv : l.IntegralCover)
    {tx : LendingTx} {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u))
    (hint : l.vault.numericType.isIntegral = true) :
    ∃ b, l.broker? u.brokerIndex = some b ∧ Number.OnGrid l.vault.baseExponent u.broker.coverAvailable := by
  have hscale := hr.scaleInv
  have hcov := hinv hint
  have hb0 : l.vault.baseExponent = 0 := Vault.baseExponent_integral l.vault hint
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
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.loan'.broker.coverAvailable
    rw [Loan.accept_broker loan _ r hr', hlb]
    exact hcov _ broker hb
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.loan'.broker.coverAvailable
    cases action with
    | impair => rw [(Loan.manageImpair_debt loan l.vault l.now r hr').1, hlb]; exact hcov _ broker hb
    | unimpair => rw [(Loan.manageUnimpair_debt loan l.vault r hr').1, hlb]; exact hcov _ broker hb
    | default =>
      simp only [Loan.manage] at hr'
      unfold_ter at hr'
      walk_ok
      rename_i rd hd
      exact Loan.manageDefault_coverOnGrid' loan l.vault rd (fun _ => hb0)
        (hr.assetsAvailable_onGrid hr.holdsAsset.maxValue_le) (by rw [hlb]; exact hcov _ broker hb) hd
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    exact ⟨broker, hb, Loan.pay_coverOnGrid' loan l.vault paymentType amount l.now r (fun _ => hb0)
      (by rw [hlb]; exact hcov _ broker hb) hr'⟩
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨broker, hb, ?_⟩
    show Number.OnGrid _ r.broker'.coverAvailable
    by_cases hp : loan.isPending = true
    · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan l.vault r hp hr'
      rw [LoanBroker.releaseLoan_cover _ _ _ hrel, hlb]; exact hcov _ broker hb
    · simp only [Loan.delete, Bool.not_eq_true] at hr' hp
      rw [hp] at hr'
      unfold_ter at hr'
      walk_ok
      rw [LoanBroker.releaseLoan_cover _ _ _ ‹Loan.deleteActive _ = Except.ok _›, hlb]
      exact hcov _ broker hb
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction on a reachable ledger keeps the invariant. -/
private lemma LendingLedger.IntegralCover.step {l l' : LendingLedger} (hr : l.Reachable) (hinv : l.IntegralCover)
    {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) : l'.IntegralCover := by
  have hpre := (LendingLedger.apply_checked h).1
  have hmax := hr.holdsAsset.maxValue_le
  intro hint' j b' hb'
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).brokers = l.brokers ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    rw [hrest.2] at hint' ⊢
    rw [hbe]
    have hb0 : l.broker? j = some b' := by unfold LendingLedger.broker? at hb' ⊢; rw [hrest.1] at hb'; exact hb'
    exact hinv (hk.numericType ▸ hint') j b' hb0
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj] at hb'
      exact l.applyBroker_coverOnGrid' hr.scaleInv tx hpre u hu hint' (hmax hint') b' hb'
        (fun b hb => hinv hint' _ b hb)
    · rw [if_neg hj] at hb'; exact hinv hint' j b' hb'
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    have hint : l.vault.numericType.isIntegral = true := hs.numericType ▸ hint'
    obtain ⟨b, hb, hcu⟩ := hinv.loan_cover hr hu hint
    show Number.OnGrid u.vault.baseExponent _
    rw [hs.baseExponent_eq]
    rw [LendingLedger.broker?_commitLoan l u b hb] at hb'
    split at hb'
    · cases hb'; exact hcu
    · exact hinv hint j b' hb'
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hinv hint' j b' hb'
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hinv hint' j b' hb'

/-- On a reachable XRP or MPT vault every broker's CoverAvailable is whole units. -/
lemma LendingLedger.Reachable.integralCover {l : LendingLedger} (hr : l.Reachable) : l.IntegralCover :=
  (LendingLedger.Reachable.invariant (Inv := fun l => l.Reachable ∧ l.IntegralCover)
    (fun g hg => ⟨LendingLedger.Reachable.of_run hg (show g.run [] = .ok g from rfl), fun _ j b hb => by
      unfold LendingLedger.broker? at hb; rw [hg.no_brokers] at hb; cases hb⟩)
    (fun _ _ _ hi ha => ⟨hi.1.apply ha, hi.2.step hi.1 ha⟩) hr).2

/-- On a reachable ledger every broker's CoverAvailable is whole base units. -/
lemma LendingLedger.Reachable.cover_onGrid {l : LendingLedger} (hr : l.Reachable) {j : Nat} {b : LoanBroker}
    (hb : l.broker? j = some b) : Number.OnGrid l.vault.baseExponent b.coverAvailable := by
  cases hint : l.vault.numericType.isIntegral
  · exact hr.coverGridInv.cover (NumericType.eq_fractional_of_not_integral hint) j b hb
  · exact hr.integralCover hint j b hb

/-- On a reachable XRP or MPT vault the asset stores a broker's CoverAvailable exactly while it is within the
asset's maximum. -/
lemma LendingLedger.Reachable.cover_representable_integral {l : LendingLedger} (hr : l.Reachable)
    (hint : l.vault.numericType.isIntegral = true) {j : Nat} {b : LoanBroker} (hb : l.broker? j = some b)
    (hcap : b.coverAvailable.toRat ≤ l.vault.numericType.maxValue.toNat) :
    STAmount.Representable l.vault.numericType b.coverAvailable.toRat := by
  have h0 : 0 ≤ b.coverAvailable.toRat := b.exact.coverAvailable_nonneg
  obtain ⟨k, hk⟩ := (hr.integralCover hint j b hb).nat h0
  have hb0 : l.vault.baseExponent = 0 := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent NumericType.baseExponent
    simp [hint]
  rw [hb0, zpow_zero, mul_one] at hk
  have hrep := hr.holdsAsset.maxValue_le hint
  have hk' : k ≤ l.vault.numericType.maxValue.toNat := by
    rw [hk] at hcap
    exact_mod_cast hcap
  right
  rcases hr.holdsAsset with h | h | h
  · rw [h] at hint; cases hint
  all_goals
    rw [h] at hk' hrep ⊢
    refine ⟨by decide, k, hk', le_trans hk' (le_trans hrep (by decide)), hk⟩

/-- Proof body of `Lending.Reachable.base_grid`. -/
lemma LendingLedger.base_grid_all_proof (l : LendingLedger) (hr : l.Reachable) :
    Number.OnGrid l.vault.baseExponent l.vault.assetsAvailable ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsDeployed ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsReserved ∧
      Number.OnGrid l.vault.baseExponent l.vault.lossUnrealized ∧
      Number.OnGrid l.vault.baseExponent l.vault.yieldUnrealized ∧
      ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        Number.OnGrid l.vault.baseExponent b.debtTotal ∧ Number.OnGrid l.vault.baseExponent b.coverAvailable := by
  obtain ⟨hAA, hAD, hAR, hLU, hYU, hb⟩ := LendingLedger.base_grid_proof l hr hr.holdsAsset.maxValue_le
  exact ⟨hAA, hAD, hAR, hLU, hYU, fun j b hj => ⟨(hb j b hj).1, hr.cover_onGrid hj⟩⟩

end XRPL.Model.Lending
