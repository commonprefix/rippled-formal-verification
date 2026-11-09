import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Ledger.Common.SubscriptionInv
import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.AcceptExits

/-! # A LoanAccept that passes its checks succeeds

The accept adds the loan's interestDue to YieldUnrealized and takes its principal off AssetsReserved. On a
reachable ledger both stay far below `10^96`, AssetsReserved holds the principal, and both re-checks pass. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private LendingLedger.Reachable.loan_withBroker from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private cash_zero_sum Vault.assetsDeployed_lt_pow from XRPL.Properties.Lending.Loan.Common.ManageTotal
open private Vault.lossUnrealized_gt_false from XRPL.Properties.Lending.Loan.Common.AcceptExits
open private Loan.canAccept_open from XRPL.Properties.Lending.Loan.Common.YieldValue

/-- The accept checks read the loan only, never its broker. -/
private lemma Loan.canAccept_withBroker {loan loan' : Loan} {b : LoanBroker} (hw : loan.withBroker b = .ok loan')
    (v : Vault) (now : UInt32) : loan'.canAccept v now = loan.canAccept v now := by
  have hraw := Loan.withBroker_eq hw
  unfold Loan.canAccept
  rw [hraw]
  rfl

/-- An accept that passes its checks and succeeds on the stored loan writes its result. -/
private lemma LendingLedger.apply_accept_ok (l : LendingLedger) (hnd : l.vaultDeleted = false) (i : Nat)
    (e : LoanEntry) (b : LoanBroker) (loan : Loan) (r : LoanWithDisbursement Vault)
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    (hc : loan.canAccept l.vault l.now = .ok .tesSUCCESS) (hr : (loan.accept l.vault).run = .ok (.ok r)) :
    (l.apply (.loanAccept i)).run = .ok (.ok (l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool'))) := by
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  simp only [ExceptT.run] at hr
  simp only [hc, show TER.tesSUCCESS.isTesSuccess = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr]
  rfl

/-- An accept of a stored pending loan that passed its checks succeeds on a reachable ledger. -/
lemma LendingLedger.accept_total_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e)
    (hc : e.loan.canAccept l.vault l.now = .ok .tesSUCCESS) :
    ∃ l', (l.apply (.loanAccept i)).run = .ok (.ok l') := by
  obtain ⟨b, loan, hb, hw, hraw⟩ := LendingLedger.Reachable.loan_withBroker hr he
  have hc' : loan.canAccept l.vault l.now = .ok .tesSUCCESS := by rw [Loan.canAccept_withBroker hw]; exact hc
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hpend : loan.isPending = true := Loan.canAccept_pending loan l.vault l.now hc'
  have hep : e.loan.isPending = true := by
    rw [show e.loan.isPending = loan.isPending from (congrArg RawLoan.isPending hraw :).symm]; exact hpend
  obtain ⟨x, hx, ho⟩ := Loan.canAccept_open loan l.vault l.now hc'
  have hxn := (Loan.interestDue_onGrid loan x hx).1
  obtain ⟨t, -, hrl⟩ := hr.loanAt_reachable ⟨e, b, he, hb, hw⟩
  have hx0 : 0 ≤ x.toRat := by rw [Loan.interestDue_toExact loan x hx]; exact Loan.Reachable.interestDue_nonneg hrl
  have hYx := (Vault.exceedsOpenLimit_false_bound l.vault x hxn ho).2.1
  have hY0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ (l.vault.baseExponent - 1) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hp1' : (0 : ℚ) < 10 ^ (l.vault.baseExponent - 1) := zpow_pos (by norm_num) _
  have hlim : ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * 10 ^ (l.vault.baseExponent - 1) < 10 ^ 96 := by
    push_cast; nlinarith
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hPAR : loan.principalOutstanding.toRat ≤ l.vault.assetsReserved.toRat := by
    rw [hr.reservedInv.sum, hpo]
    have := LendingLedger.principalIf_le_sum l (·.isPending) i
    rw [he] at this
    simpa [LoanEntry.principalIf, hep] using this
  have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := l.vault.exact.assetsReserved_nonneg
  have hARD : l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsReserved_le
  have hAD := Vault.assetsDeployed_lt_pow l.vault
  obtain ⟨aa', hcash, haa0⟩ := cash_zero_sum l.vault (loan.acceptChange x) rfl
    (hr.storesAvailable hr.holdsAsset.maxValue_le)
  obtain ⟨ar', har⟩ := Number.operator_sub_ok_of_lt l.vault.assetsReserved loan.principalOutstanding .to_nearest
    l.vault.wf.assetsReserved_norm loan.wf.principalOutstanding_norm hAR0 (by linarith) hP0 (by linarith)
  obtain ⟨yu', hyu⟩ := Number.operator_add_ok_of_lt l.vault.yieldUnrealized x .to_nearest
    l.vault.wf.yieldUnrealized_norm hxn hY0 (by linarith) hx0 (by linarith)
  have har' : l.vault.assetsReserved.operator_add loan.principalOutstanding.operator_neg .to_nearest = .ok ar' := har
  have hnegn := Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm
  have harn := operator_add_isNormalized_to_nearest_sz _ _ _ l.vault.wf.assetsReserved_norm hnegn har'
  have har0 : 0 ≤ ar'.toRat :=
    operator_add_nonneg _ _ _ l.vault.wf.assetsReserved_norm hnegn har' (by rw [Number.toRat_neg]; linarith)
  have hyun := operator_add_isNormalized_to_nearest_sz _ _ _ l.vault.wf.yieldUnrealized_norm hxn hyu
  have hyu0 : 0 ≤ yu'.toRat := operator_add_nonneg _ _ _ l.vault.wf.yieldUnrealized_norm hxn hyu (by linarith)
  have hs : Vault.AdjustSums l.vault (loan.acceptChange x) aa' l.vault.assetsDeployed l.vault.lossUnrealized ar'
      yu' :=
    ⟨hcash, Number.operator_add_zero_right _ _, Number.operator_add_zero_right _ _, har', hyu⟩
  have hadj := Vault.adjustBalances_ok l.vault _ _ _ _ _ _ hs
    ⟨haa0, Number.signum_nonneg_of_toRat _ l.vault.wf.assetsDeployed_norm l.vault.exact.assetsDeployed_nonneg,
      Number.signum_nonneg_of_toRat _ l.vault.wf.lossUnrealized_norm l.vault.exact.lossUnrealized_nonneg,
      Number.signum_nonneg_of_toRat _ hyun hyu0, Number.signum_nonneg_of_toRat _ harn har0⟩
    (Vault.lossUnrealized_gt_false l.vault)
  obtain ⟨v', hv', -⟩ := Loan.accept_vault_lawful loan l.vault x _ hx hadj
  obtain ⟨loan', hl', -⟩ := Loan.accept_loan_lawful loan
  obtain ⟨a, ha, -⟩ := Loan.acceptAmount_ok loan
  have hacc := Loan.accept_success_proof loan l.vault x _ v' loan' a hx hadj hv' hl' ha
  exact ⟨_, LendingLedger.apply_accept_ok l hnd i e b loan _ he hb hw hc' hacc⟩

/-- Proof body of the accept line of `Lending.Reachable.loan_resolvable`. A pending loan exists only after the
subscription phase and starts before RedemptionDate, so before StartDate only the Open limit check is left. -/
lemma LendingLedger.accept_before_start_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) (hp : e.loan.isPending = true)
    (ht : l.now < e.loan.schedule.startDate)
    (hopen : ∀ x, e.loan.interestDue = .ok x → l.vault.exceedsOpenLimit x = .ok false) :
    ∃ l', (l.apply (.loanAccept i)).run = .ok (.ok l') := by
  refine LendingLedger.accept_total_proof l hr hnd i e he ?_
  obtain ⟨x, hx⟩ := Loan.interestDue_ok e.loan
  refine Loan.canAccept_success_proof e.loan l.vault l.now hp ht ?_ x hx (hopen x hx)
  cases hph : l.vault.phase l.now
  · exact Or.inl rfl
  · have := (LendingLedger.subscription_no_loans_proof l hr hph).1 i
    rw [he] at this
    cases this
  · exact Or.inr rfl
  · exfalso
    cases hs : l.vault.schedule with
    | none => simp [Vault.phase, hs] at hph
    | some s =>
      have hm := LendingLedger.loans_mature_proof l hr s hs i e he
      simp only [Vault.phase, hs] at hph
      split at hph <;> try cases hph
      split at hph <;> try cases hph
      rename_i hred
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hred
      have ht' : l.now.toNat < e.loan.schedule.startDate.toNat := ht
      have hred' : s.redemptionDate.toNat ≤ l.now.toNat := hred
      omega

end XRPL.Model.Lending
