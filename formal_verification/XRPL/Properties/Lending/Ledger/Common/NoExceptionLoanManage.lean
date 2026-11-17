import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanManageSteps
import XRPL.Properties.Lending.Ledger.Common.RecheckLoan
import XRPL.Properties.Lending.Ledger.Common.XrpTotal

/-! # LoanAccept, LoanDelete and LoanManage return a result code

On a reachable ledger each of the three transactions ends in a result code, never in a model error (a C++
exception). LoanAccept, impair and unimpair need nothing more. A pending LoanDelete and a default add an amount to
AssetsAvailable, and the sum must stay within the asset's largest amount. On XRP the total the vault stored keeps
it so. On an MPT or an IOU C++ keeps it so through the balance of the vault account, which the model does not run. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)
open NoExceptionLoanManage

/-- A LoanAccept on a reachable ledger returns a result code, never a model error. -/
lemma LendingLedger.loanAccept_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) :
    ∃ r, (l.apply (.loanAccept i)).run = .ok r := by
  cases hrun : (l.apply (.loanAccept i)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    have hyu := yield_lt_pow hr
    have hne : e ≠ .notLawful := fun he => LendingLedger.loanAccept_ne_notLawful l hr i (he ▸ hrun)
    have h := applyLoan_error rfl hrun
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    · exact hne (loan_to_lawful_error ‹_›)
    · exact canAccept_ne_error _ _ _ hyu _ ‹_›
    · exact hne (accept_error _ _ (Headroom.of_nonneg_lt l.vault.wf.yieldUnrealized_norm
        l.vault.exact.yieldUnrealized_nonneg hyu) hr.totalStored ‹_›)

/-- A LoanDelete on a reachable ledger returns a result code, never a model error, while on an MPT or an IOU
AssetsAvailable plus the principal of a pending loan is at most the asset's largest amount. -/
lemma LendingLedger.loanDelete_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    -- a pending loan on an MPT or an IOU: C++ holds AssetsAvailable and the reserved principal in the vault
    -- account, so their sum is an amount of the asset. The model runs no balances
    (hroom : l.vault.numericType ≠ NumericType.native → ∀ e, l.loan? i = some e → e.loan.isPending = true →
      l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.loanDelete i)).run = .ok r := by
  cases hrun : (l.apply (.loanDelete i)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    have hyu := yield_lt_pow hr
    have hne : e ≠ .notLawful := fun he => LendingLedger.loanDelete_ne_notLawful l hr i (he ▸ hrun)
    have h := applyLoan_error rfl hrun
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    · exact hne (loan_to_lawful_error ‹_›)
    rename_i e' he _ b hb _ _ loan hw _ _ _ hd
    have hat : l.LoanAt i loan := ⟨e', b, he, hb, hw⟩
    have hraw := Loan.withBroker_eq hw
    have hpo : loan.principalOutstanding = e'.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hpend : loan.isPending = e'.loan.isPending := (congrArg RawLoan.isPending hraw :)
    obtain ⟨-, -, -, hpad, -⟩ := hr.loanAt_principal hat
    have hroomL : loan.isPending = true →
        l.vault.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤ l.vault.numericType.maxAmount := by
      intro hp
      by_cases hx : l.vault.numericType = NumericType.native
      · -- XRP: the principal is part of AssetsDeployed, and the vault stored the total as an XRP amount
        have htot := hr.total_le_native hx
        have hma : l.vault.numericType.maxAmount = (l.vault.numericType.maxValue.toNat : ℚ) := by
          unfold NumericType.maxAmount
          rw [if_pos (by rw [hx]; rfl)]
        rw [hma]
        linarith
      · rw [hpo]; exact hroom hx e' he (by rw [← hpend]; exact hp)
    refine hne (delete_error loan l.vault hr.holdsAsset
      (Headroom.of_nonneg_lt l.vault.wf.yieldUnrealized_norm l.vault.exact.yieldUnrealized_nonneg hyu)
      hr.totalStored (hr.loanAt_scale hat).2 hpad (fun _ => deployed_lt_pow hr)
      (by rw [show loan.broker = b from (congrArg RawLoan.broker hraw :)]
          exact hr.loanCountInv.loanCount_ne_zero he hb)
      (debt_headroom hr hat) (fun hp => (hr.deletePending_fits hat hp).1)
      hroomL hd)

/-- A LoanManage on a reachable ledger returns a result code, never a model error. A default needs the cover, and
off XRP AssetsAvailable plus the cover paid, within the asset's largest amount, and an IOU vault on the base grid. -/
lemma LendingLedger.loanManage_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (action : LoanManageAction)
    -- default: C++ holds CoverAvailable and AssetsAvailable as balances of the asset, so each is an amount of the
    -- asset and their sum is within its supply. The model runs no balances. On XRP the stored total bounds the sum
    (hcover : action = .default → ∀ e b, l.loan? i = some e → l.broker? e.brokerIndex = some b →
      b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount ∧
      (l.vault.numericType ≠ NumericType.native →
        l.vault.assetsAvailable.toRat + min e.loan.principalOutstanding.toRat b.coverAvailable.toRat ≤
          l.vault.numericType.maxAmount))
    -- default on an IOU: the vault holds less than `10^16` base units, so the cover lands on the base grid
    (hiou : action = .default → l.vault.numericType = .fractional →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ r, (l.apply (.loanManage i action)).run = .ok r := by
  cases hrun : (l.apply (.loanManage i action)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    have hyu := yield_lt_pow hr
    have hyuH := Headroom.of_nonneg_lt l.vault.wf.yieldUnrealized_norm l.vault.exact.yieldUnrealized_nonneg hyu
    have hne : e ≠ .notLawful := fun he => LendingLedger.loanManage_ne_notLawful l hr i action (he ▸ hrun)
    have h := applyLoan_error rfl hrun
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    · exact hne (loan_to_lawful_error ‹_›)
    · exact canManage_ne_error _ _ _ _ ‹_›
    rename_i _ e' he _ b hb _ _ loan hw _ _ _ ter hct _ hc _ hm
    refine hne (manage_error loan action l.vault l.now hyuH hr.totalStored (fun hact hdef => ?_) hm)

    -- a default: the loan read at `i`, its broker and the vault on the ledger
    have hat : l.LoanAt i loan := ⟨e', b, he, hb, hw⟩
    have hraw := Loan.withBroker_eq hw
    have hpo : loan.principalOutstanding = e'.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
    obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
    obtain ⟨p, hp16, hpv, hpad, -⟩ := hr.loanAt_principal hat
    obtain ⟨hca, hroomN⟩ := hcover hact e' b he hb
    have hroom : l.vault.assetsAvailable.toRat + min e'.loan.principalOutstanding.toRat b.coverAvailable.toRat ≤
        l.vault.numericType.maxAmount := by
      by_cases hx : l.vault.numericType = NumericType.native
      · -- XRP: the cover paid is at most the principal, a part of AssetsDeployed
        have htot := hr.total_le_native hx
        have hma : l.vault.numericType.maxAmount = (l.vault.numericType.maxValue.toNat : ℚ) := by
          unfold NumericType.maxAmount
          rw [if_pos (by rw [hx]; rfl)]
        have hmin : min e'.loan.principalOutstanding.toRat b.coverAvailable.toRat ≤
            l.vault.assetsDeployed.toRat := le_trans (min_le_left _ _) (by rw [← hpo]; exact hpad)
        rw [hma]
        linarith
      · exact hroomN hx
    have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
    have hp : loan.principalOutstanding.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
      rw [hpv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp16) hp10.le
    have hdtad : loan.broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
      rw [hlb, hr.debtInv.debt _ b hb, hr.debtInv.deployed]
      exact l.brokerPrincipal_le _
    have hcaH : Headroom loan.broker.coverAvailable := by
      rw [hlb]
      exact Headroom.of_nonneg_lt b.wf.coverAvailable_norm b.exact.coverAvailable_nonneg
        (lt_of_le_of_lt hca (NumericType.maxAmount_lt _))
    have hfacts : CoverFacts loan l.vault := CoverFacts.of_ok (defaultCover_facts loan l.vault hr.holdsAsset hnt hls
      (hr.loanAt_debt_units hat) hp (fun hfr => ⟨hr.assetsAvailable_units hr.holdsAsset,
        by linarith [hiou hact hfr], by linarith [hiou hact hfr]⟩))
    exact manageDefault_error loan l.vault hr.holdsAsset hyuH hr.totalStored hls hpad
      (fun _ => deployed_lt_pow hr) (debt_headroom hr hat) hcaH hfacts
      (by rw [hpo, hlb]; exact hroom) hdef

end XRPL.Model.Lending
