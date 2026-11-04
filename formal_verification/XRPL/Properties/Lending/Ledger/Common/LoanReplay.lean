import XRPL.Properties.Lending.Ledger.Common.AcceptTotal
import XRPL.Properties.Lending.Ledger.Common.LoanClosable
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.RecheckPay
import XRPL.Properties.Lending.Loan.Common.TwinPay
import XRPL.Properties.Lending.Loan.Common.PaySettle

/-! # A loan transaction replayed on another reachable ledger

A transaction on a stored loan reads the close time, the vault settings, the loan, its broker's asset and
management fee rate, and the vault's balances. When a second reachable ledger keeps all but the balances, the
transaction that succeeded on the first succeeds on the second as well, while the vault is not coarsened and
a LoanAccept still fits the Open limit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.canAccept_withBroker from XRPL.Properties.Lending.Ledger.Common.AcceptTotal
open private Loan.canManage_withBroker LendingLedger.apply_manage_ok LendingLedger.Reachable.loan_withBroker
  LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private cash_zero_sum Vault.assetsDeployed_lt_pow from XRPL.Properties.Lending.Loan.Common.ManageTotal

/-- What a transaction on stored loan `j` reads, kept from `l` to `l'`: the close time, the vault settings, the
loan, and a broker of the same management fee rate. -/
structure LendingLedger.KeepsLoan (l l' : LendingLedger) (j : Nat) (e : LoanEntry) : Prop where
  now : l'.now = l.now
  deleted : l'.vaultDeleted = l.vaultDeleted
  settings : Vault.KeepsSettings l.vault l'.vault
  loan : l'.loan? j = some e
  broker : ∀ b, l.broker? e.brokerIndex = some b → ∃ b', l'.broker? e.brokerIndex = some b' ∧
    b'.managementFeeRate = b.managementFeeRate

/-- A loan transaction succeeds only while the vault exists. -/
lemma LendingLedger.apply_loan_live {l l' : LendingLedger} {tx : LendingTx} (hl : tx.isLoan = true)
    (h : (l.apply tx).run = .ok (.ok l')) : l.vaultDeleted = false := by
  have h := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isLoan, Bool.false_eq_true] at hl <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · cases h
    · simpa using ‹¬ l.vaultDeleted = true›

/-- The vault settings fix the phase. -/
private lemma Vault.KeepsSettings.phase {v v' : Vault} (h : Vault.KeepsSettings v v') (t : UInt32) :
    v'.phase t = v.phase t := by
  unfold XRPL.Model.SingleAssetVault.Vault.phase
  rw [h.schedule]

/-- The accept checks pass on another vault in the same phase whose Open limit still takes the interest. -/
private lemma Loan.canAccept_of_open (loan : Loan) (v v' : Vault) (now : UInt32)
    (h : loan.canAccept v now = .ok .tesSUCCESS) (hph : v'.phase now = v.phase now)
    (hopen : ∀ x, loan.interestDue = .ok x → v'.exceedsOpenLimit x = .ok false) :
    loan.canAccept v' now = .ok .tesSUCCESS := by
  unfold Loan.canAccept at h ⊢
  simp only [Vault.pool_phase, Vault.pool_exceedsOpenLimit, hph] at h ⊢
  obtain ⟨x, hx⟩ := Loan.interestDue_ok loan
  simp only [hx] at h ⊢
  revert h
  rcases v.exceedsOpenLimit x with err | _ | _ <;> split <;> (try split) <;> (try split) <;> simp_all

/-- A LoanAccept replays while the Open limit still takes the loan's interest. -/
lemma LendingLedger.accept_replay {l L lb : LendingLedger} (hR : L.Reachable) {j : Nat} {e : LoanEntry}
    (hk : l.KeepsLoan L j e) (he : l.loan? j = some e) (hb : (l.apply (.loanAccept j)).run = .ok (.ok lb))
    (hopen : ∀ x, e.loan.interestDue = .ok x → L.vault.exceedsOpenLimit x = .ok false) :
    ∃ L', (L.apply (.loanAccept j)).run = .ok (.ok L') := by
  have hnd := LendingLedger.apply_loan_live rfl hb
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, -, hw, hc, -, -⟩ := LendingLedger.applyLoan_accept_inv l u j hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hc' : e.loan.canAccept l.vault l.now = .ok .tesSUCCESS := by rw [← Loan.canAccept_withBroker hw]; exact hc
  refine LendingLedger.accept_total_proof L hR (by rw [hk.deleted]; exact hnd) j e hk.loan ?_
  rw [hk.now]
  exact Loan.canAccept_of_open e.loan l.vault L.vault l.now hc' (hk.settings.phase _) hopen

/-- AssetsAvailable plus the principal of a stored loan is an amount the asset holds while the vault is not
coarsened. -/
private lemma LendingLedger.Reachable.available_principal_fits {L : LendingLedger} (hR : L.Reachable) {j : Nat}
    {e : LoanEntry} (he : L.loan? j = some e)
    (htotal : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent) :
    STAmount.Representable L.vault.numericType
      (L.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat) := by
  obtain ⟨b, loan, hb, hw, hraw⟩ := LendingLedger.Reachable.loan_withBroker hR he
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  obtain ⟨p, -, hpv, hpAD, -⟩ := hR.loanAt_principal ⟨e, b, he, hb, hw⟩
  obtain ⟨a, hav⟩ := hR.assetsAvailable_units hR.holdsAsset
  rw [hpo] at hpv hpAD
  have hp10 : (0 : ℚ) < 10 ^ L.vault.baseExponent := zpow_pos (by norm_num) _
  have hap : a + p < 10 ^ 16 := by
    have : ((a + p : ℕ) : ℚ) * 10 ^ L.vault.baseExponent < 10 ^ 16 * 10 ^ L.vault.baseExponent := by
      push_cast; rw [add_mul, ← hav, ← hpv]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds L.vault
  obtain ⟨w, hw', hwv⟩ := Number.exists_normalized_int_mul_pow ((a + p : ℕ) : ℤ) L.vault.baseExponent
    ⟨by omega, by omega⟩ ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hwv' : w.toRat = ((a + p : ℕ) : ℚ) * 10 ^ L.vault.baseExponent := by rw [hwv]; norm_cast
  have hnr := hR.holdsAsset.isRounded_units w (a + p) hw' hap hwv'
  have := (STAmount.isRounded_eq_false_iff _ w hw' (by rw [hwv']; positivity)).mp hnr
  rwa [hwv', show ((a + p : ℕ) : ℚ) * 10 ^ L.vault.baseExponent =
    L.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat by rw [hav, hpv]; push_cast; ring] at this

/-- A LoanDelete replays while the vault is not coarsened. -/
lemma LendingLedger.delete_replay {l L lb : LendingLedger} (hR : L.Reachable) {j : Nat} {e : LoanEntry}
    (hk : l.KeepsLoan L j e) (he : l.loan? j = some e) (hb : (l.apply (.loanDelete j)).run = .ok (.ok lb))
    (htotal : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent) :
    ∃ L', (L.apply (.loanDelete j)).run = .ok (.ok L') := by
  have hndL : L.vaultDeleted = false := by rw [hk.deleted]; exact LendingLedger.apply_loan_live rfl hb
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, -, hw, hc, -, -⟩ := LendingLedger.applyLoan_delete_inv l u j hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hraw := Loan.withBroker_eq hw
  have hp : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
  have hpr : loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
  cases hpend : e.loan.isPending
  · -- a closed loan: the check passed, so no payment is left
    have hrem : e.loan.paymentRemaining = 0 := by
      unfold Loan.canDelete at hc
      rw [hp, hpend, hpr] at hc
      by_contra h0
      have : e.loan.paymentRemaining > 0 := by
        rw [GT.gt, UInt32.lt_iff_toNat_lt]
        have := UInt32.toNat_inj.not.mpr h0
        simp at this ⊢
        omega
      simp [this] at hc
    exact LendingLedger.closed_loan_deletable L hR hndL j e hk.loan hrem hpend
  · exact LendingLedger.pending_resolvable_proof L hR hR.holdsAsset.maxValue_le hndL j e hk.loan hpend
      (hR.available_principal_fits hk.loan htotal)

/-- What a default's checks need: an active loan with payments left, past its grace period. -/
private lemma Loan.canManage_default_facts (loan : Loan) (now : UInt32)
    (h : loan.canManage .default now = .tesSUCCESS) :
    loan.isPending = false ∧ loan.isDefault = false ∧ loan.paymentRemaining ≠ 0 ∧
      loan.nextPaymentDueDate + loan.schedule.gracePeriod < now := by
  unfold Loan.canManage at h
  by_cases h1 : loan.isPending = true
  · simp [h1] at h
  by_cases h2 : loan.isDefault = true
  · simp [h2] at h
  by_cases h3 : loan.paymentRemaining = 0
  · simp [h3] at h
  simp only [Bool.not_eq_true] at h1 h2
  refine ⟨h1, h2, h3, ?_⟩
  by_contra h4
  simp [h1, h2, h3, h4] at h

/-- An unimpair of the stored impaired loan succeeds on a reachable ledger. LossUnrealized holds the loan's
principal and gives it back. -/
lemma LendingLedger.Reachable.manageUnimpair_ok {L : LendingLedger} (hR : L.Reachable) {j : Nat} {loan : Loan}
    (hat : L.LoanAt j loan) (himp : loan.isImpaired = true) :
    ∃ r, (loan.manageUnimpair L.vault).run = .ok (.ok r) := by
  obtain ⟨e, he, -, hraw⟩ := hat.stored
  have himp' : e.loan.isImpaired = true := by
    rw [show loan.isImpaired = loan.toRawLoan.isImpaired from rfl, hraw] at himp; exact himp
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  set v := L.vault
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hPN := loan.wf.principalOutstanding_norm
  have hPLU : loan.principalOutstanding.toRat ≤ v.lossUnrealized.toRat := by
    rw [hpo, hR.lossInv.sum]
    have := LendingLedger.principalIf_le_sum L (·.isImpaired) j
    rw [he] at this
    simpa [LoanEntry.principalIf, himp'] using this
  have hLUAD : v.lossUnrealized.toRat ≤ v.assetsDeployed.toRat := v.exact.lossUnrealized_le
  have hLU0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  have hnegN := Number.operator_neg_isNormalized _ hPN
  obtain ⟨lu', hlu'⟩ := Number.operator_add_ok_of_abs v.lossUnrealized loan.principalOutstanding.operator_neg
    .to_nearest v.wf.lossUnrealized_norm hnegN
    (by rw [abs_of_nonneg hLU0]; linarith [Vault.assetsDeployed_lt_pow v])
    (by rw [Number.toRat_neg, abs_neg, abs_of_nonneg hP0]; linarith [Vault.assetsDeployed_lt_pow v])
  have hlu'v : lu'.toRat = v.lossUnrealized.toRat - loan.principalOutstanding.toRat := by
    obtain ⟨w, hw', hwv⟩ := hR.unimpair_fits hat
    have hwv' : w.toRat = v.lossUnrealized.toRat + loan.principalOutstanding.operator_neg.toRat := by
      rw [hwv, Number.toRat_neg]; ring
    rw [Number.operator_add_exact_of_fits v.wf.lossUnrealized_norm hnegN hlu' ⟨w, hw', hwv'⟩, Number.toRat_neg]
    ring
  have hlu'N := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm hnegN hlu'
  obtain ⟨aa', hcash, haa0⟩ := cash_zero_sum v { loss := loan.principalOutstanding.operator_neg } rfl
    hR.availableStored
  have hs : Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' v.assetsDeployed lu'
      v.assetsReserved v.yieldUnrealized :=
    ⟨hcash, Number.operator_add_zero_right _ _, hlu', Number.operator_add_zero_right _ _,
      Number.operator_add_zero_right _ _⟩
  have hle : lu'.operator_gt v.assetsDeployed = false := by
    unfold Number.operator_gt
    exact (operator_lt_eq_false_iff _ _ v.wf.assetsDeployed_norm hlu'N).mpr (by rw [hlu'v]; linarith)
  have hadj := Vault.adjustBalances_ok v _ _ _ _ _ _ hs
    ⟨haa0, Number.signum_nonneg_of_toRat _ v.wf.assetsDeployed_norm v.exact.assetsDeployed_nonneg,
      Number.signum_nonneg_of_toRat _ hlu'N (by rw [hlu'v]; linarith),
      Number.signum_nonneg_of_toRat _ v.wf.yieldUnrealized_norm v.exact.yieldUnrealized_nonneg,
      Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm v.exact.assetsReserved_nonneg⟩ hle
  obtain ⟨v', loan', hok, -, -⟩ := Loan.manageUnimpair_success_proof loan v _ hadj
  exact ⟨_, hok⟩

/-- An unimpair of a stored impaired loan that passes its checks succeeds on a reachable ledger. -/
private lemma LendingLedger.unimpair_total (L : LendingLedger) (hR : L.Reachable) (hnd : L.vaultDeleted = false)
    (j : Nat) (e : LoanEntry) (he : L.loan? j = some e) (hc : e.loan.canManage .unimpair L.now = .tesSUCCESS) :
    ∃ L', (L.apply (.loanManage j .unimpair)).run = .ok (.ok L') := by
  obtain ⟨b, loan, hb, hw, -⟩ := LendingLedger.Reachable.loan_withBroker hR he
  have hc' : loan.canManage .unimpair L.now = .tesSUCCESS := by rw [Loan.canManage_withBroker hw]; exact hc
  obtain ⟨r, hok⟩ := hR.manageUnimpair_ok ⟨e, b, he, hb, hw⟩ (Loan.canManage_unimpair_impaired loan L.now hc')
  exact ⟨_, LendingLedger.apply_manage_ok L hnd j e b loan .unimpair r he hb hw hc' hok⟩

/-- A LoanManage replays while the vault is not coarsened. A default also needs a cover the broker holds. -/
lemma LendingLedger.manage_replay {l L lb : LendingLedger} (hR : L.Reachable) {j : Nat} {e : LoanEntry}
    (hk : l.KeepsLoan L j e) (he : l.loan? j = some e) (action : LoanManageAction)
    (hb : (l.apply (.loanManage j action)).run = .ok (.ok lb))
    (htotal : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent)
    (hca : ∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) :
    ∃ L', (L.apply (.loanManage j action)).run = .ok (.ok L') := by
  have hndL : L.vaultDeleted = false := by rw [hk.deleted]; exact LendingLedger.apply_loan_live rfl hb
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, -, hw, hc, hok, -⟩ := LendingLedger.applyLoan_manage_inv l u j action hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hc' : e.loan.canManage action L.now = .tesSUCCESS := by
    rw [hk.now, ← Loan.canManage_withBroker hw]; exact hc
  have hraw := Loan.withBroker_eq hw
  cases action with
  | impair =>
    have hlate : e.loan.nextPaymentDueDate < L.now := by
      rw [hk.now]
      by_contra hl
      have hnd : loan.nextPaymentDueDate = e.loan.nextPaymentDueDate := (congrArg RawLoan.nextPaymentDueDate hraw :)
      have hlf : loan.isPaymentLate l.now = false := by
        unfold Loan.isPaymentLate; rw [hnd]; exact decide_eq_false hl
      simp only [Loan.manage, Loan.manageImpair, hlf] at hok
      unfold_ter at hok
      simp at hok
    exact LendingLedger.impair_total_proof L hR hndL hR.holdsAsset.maxValue_le j e hk.loan hc' hlate
  | unimpair => exact LendingLedger.unimpair_total L hR hndL j e hk.loan hc'
  | default =>
    obtain ⟨hp, hd, hrem, hlate⟩ := Loan.canManage_default_facts e.loan L.now hc'
    exact LendingLedger.default_possible_proof L hR hndL hR.holdsAsset j e hk.loan hp hd hrem hlate htotal
      (hR.assetsAvailable_units hR.holdsAsset) hR.yield_lt (hR.interest_le_yield hk.loan hp) hca

end XRPL.Model.Lending
