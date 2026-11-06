import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Ledger.Common.ScaleInv
import XRPL.Properties.Lending.Ledger.Common.ShareInv
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Ledger.Common.WrapLoan

/-! # Where a transaction could wrap around

A transaction runs its preflight, the ledger lookups and the commit without any fixed-width operation, so it wraps
only through the vault, broker or loan operation it runs. The preflight passes only normalized Numbers and amounts
of the vault's asset, and a reachable ledger holds XRP, an MPT or an IOU with normalized shares, so none of the
operations wraps while no broker has `2^32 − 1` loans. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A transaction that wraps passed its preflight, and its checks and operation wrapped. -/
private lemma LendingLedger.apply_wrap {l : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .error .wrap) :
    tx.preflight l = .tesSUCCESS ∧ (l.applyChecked tx).run = .error .wrap :=
  LendingLedger.apply_error h

lemma Loan.withBroker_ne_wrap (loan : Loan) (b : LoanBroker) : loan.withBroker b ≠ .error .wrap :=
  RawLoan.to_lawful_ne_wrap _

/-- XRP, an MPT and an IOU have a largest value below `2^63`. -/
lemma Vault.HoldsAsset.maxValue_lt {v : Vault} (h : Vault.HoldsAsset v) : v.numericType.maxValue.toNat < 2 ^ 63 := by
  rcases h with h | h | h <;> rw [h] <;> decide

/-- An amount the preflight accepts as canonical for a type whose largest value is below `2^63` has a magnitude
below `2^63`. -/
lemma isCanonicalAmount_mValue_lt {s : STAmount} {nt : NumericType} (hc : isCanonicalAmount s nt = true)
    (hnt : nt.maxValue.toNat < 2 ^ 63) : s.mValue.toNat < 2 ^ 63 := by
  unfold isCanonicalAmount at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨-, hc⟩ := hc
  split at hc
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    omega
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with h | ⟨⟨⟨_, h⟩, _⟩, _⟩
    · rw [h]; decide
    · omega

/-- A vault transaction that passed its preflight never wraps on a reachable ledger. -/
lemma LendingLedger.applyVault_ne_wrap (l : LendingLedger) (hr : l.Reachable) (tx : LendingTx)
    (hpre : tx.preflight l = .tesSUCCESS) : (l.applyVault tx).run ≠ .error .wrap := by
  have hnt := hr.holdsAsset.maxValue_lt
  have hs := hr.sharesNormalized.sharesOf
  intro h
  cases tx with
  | vaultDeposit i amount isDonation =>
    have ha := isCanonicalAmount_mValue_lt (s := amount) (by simp [LendingTx.preflight] at hpre; tauto) hnt
    have hi := hs i
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | vaultWithdraw i amount =>
    have hi := hs i
    cases amount with
    | vaultAssets a =>
      have ha := isCanonicalAmount_mValue_lt (s := a) (by simp [LendingTx.preflight] at hpre; tauto) hnt
      simp only [LendingLedger.applyVault] at h
      unfold_ter at h
      walk_ok
      all_goals wrap_leaf
    | vaultShares a =>
      have ha := isCanonicalAmount_mValue_lt (s := a) (by simp [LendingTx.preflight] at hpre; tauto)
        NumericType.int64_maxValue_lt
      simp only [LendingLedger.applyVault] at h
      unfold_ter at h
      walk_ok
      all_goals wrap_leaf
  | vaultClawback i assets =>
    have ha := isCanonicalAmount_mValue_lt (s := assets)
      (by simp only [LendingTx.preflight] at hpre; split_ifs at hpre; simp_all) hnt
    have hi := hs i
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | vaultBurnShares i amount =>
    have hi := hs i
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | vaultSet am bd ud =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | _ => simp only [LendingLedger.applyVault] at h; unfold_ter at h; cases h

/-- A broker transaction that passed its preflight never wraps on a reachable ledger. -/
lemma LendingLedger.applyBroker_ne_wrap (l : LendingLedger) (hr : l.Reachable) (tx : LendingTx)
    (hpre : tx.preflight l = .tesSUCCESS) : (l.applyBroker tx).run ≠ .error .wrap := by
  have hnt := hr.holdsAsset.maxValue_lt
  have hbnt : ∀ {i : Nat} {b : LoanBroker}, l.broker? i = some b → b.numericType.maxValue.toNat < 2 ^ 63 :=
    fun hb => by rw [hr.scaleInv.brokers _ _ hb]; exact hnt
  intro h
  cases tx with
  | loanBrokerCoverDeposit i amount =>
    have ha := isCanonicalAmount_mValue_lt (s := amount) (by simp [LendingTx.preflight] at hpre; tauto) hnt
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | loanBrokerCoverWithdraw i amount =>
    have ha := isCanonicalAmount_mValue_lt (s := amount) (by simp [LendingTx.preflight] at hpre; tauto) hnt
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | loanBrokerCoverClawback i amount =>
    have ha : ∀ a ∈ amount, a.Fits := by
      intro a rfl
      exact STAmount.Fits.of_lt (isCanonicalAmount_mValue_lt (s := a)
        (by simp [LendingTx.preflight] at hpre; tauto) hnt)
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact LoanBroker.canCoverClawback_ne_wrap _ _ _ (hbnt ‹_›) ha ‹_›
      | exact LoanBroker.coverClawback_ne_wrap _ _ _ (hbnt ‹_›) ha ‹_›
  | _ =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf

/-- A LoanSet never wraps when its broker has a successor LoanCount. The preflight asks for a payment, and the
schedule check passes only for a first due date within the ledger clock. -/
lemma LendingLedger.applyLoanSet_ne_wrap (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (twoStep ao : Bool) (hpr : schedule.paymentTotal ≠ 0)
    (hint : 0 < schedule.paymentInterval) (hp : principal.isNormalized)
    (hcount : ∀ b, l.broker? i = some b → b.loanCount.toNat + 1 < 2 ^ 32) :
    (l.applyLoanSet i principal rates fees schedule twoStep ao).run ≠ .error .wrap := by
  intro h
  unfold LendingLedger.applyLoanSet at h
  split at h
  · rename_i e he
    have : e = .wrap := by simpa [ExceptT.run, ExceptT.mk] using h
    subst this
    exact schedule.checkTimeAvailability_ne_wrap he
  rename_i t ht
  split at h
  · cases h
  rename_i hts
  have hfits : schedule.Fits := by
    have hn : 0 < schedule.paymentTotal := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_zero]
      exact Nat.pos_of_ne_zero (fun h0 => hpr (UInt32.toNat_inj.mp (by rw [h0, UInt32.toNat_zero])))
    have hok : t = .tesSUCCESS := (TER.isTesSuccess_iff t).mp (by simpa using hts)
    exact (schedule.checkTimeAvailability_success_iff hn hint).mp (by rw [ht, hok])
  split at h
  · cases h
  rename_i b hb
  unfold LendingLedger.loanSetChecked at h
  dsimp only at h
  split at h
  · rename_i e he
    cases h
    exact Loan.canCreate_ne_wrap _ _ _ _ _ _ _ he
  split at h
  · cases h
  exact Loan.create_ne_wrap _ _ _ _ _ _ _ _ hpr (hcount b hb) hfits.firstDue_lt hp (TerExcept.map_error h)

/-- A LoanSet that passed its preflight has a payment, a payment interval above zero and a normalized principal. -/
private lemma LendingTx.preflight_loanSet_schedule (l : LendingLedger) (i : Nat) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (pi pt gp : Option UInt32) (sd : UInt32) (twoStep ao : Bool)
    (h : (LendingTx.loanSet i principal rates fees pi pt gp sd twoStep ao).preflight l = .tesSUCCESS) :
    0 < pt.getD defaultPaymentTotal ∧ minPaymentInterval ≤ pi.getD defaultPaymentInterval ∧
      principal.isNormalized := by
  refine ⟨?_, ?_, ?_⟩ <;> by_contra hne <;> simp [LendingTx.preflight, isPositiveInput, hne] at h

/-- A loan transaction on a reachable ledger never wraps while no broker has `2^32 − 1` loans. -/
lemma LendingLedger.applyLoan_ne_wrap (l : LendingLedger) (hr : l.Reachable) (tx : LendingTx)
    (hpre : tx.preflight l = .tesSUCCESS)
    (hcount : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount.toNat + 1 < 2 ^ 32) :
    (l.applyLoan tx).run ≠ .error .wrap := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpt, hpi, hp⟩ :=
      LendingTx.preflight_loanSet_schedule l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan]
    refine LendingLedger.applyLoanSet_ne_wrap l i principal rates fees _ twoStep ao ?_ ?_ hp (hcount i)
    · show pt.getD defaultPaymentTotal ≠ 0
      intro h0; rw [h0] at hpt; exact absurd hpt (by decide)
    · show 0 < pi.getD defaultPaymentInterval
      have h60 : minPaymentInterval.toNat = 60 := rfl
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_zero]
      rw [UInt32.le_iff_toNat_le, h60] at hpi
      omega
  | loanAccept i =>
    intro h
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.withBroker_ne_wrap _ _ ‹_›
      | exact Loan.canAccept_ne_wrap _ _ _ ‹_›
      | exact Loan.accept_ne_wrap _ _ ‹_›
  | loanDelete i =>
    intro h
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.withBroker_ne_wrap _ _ ‹_›
      | skip
    rename_i _ e he _ b hb _ _ loan hw _ _ _ hdel
    have hlb : loan.broker = b := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    exact Loan.delete_ne_wrap _ _ (by rw [hlb]; exact hr.loanCountInv.loanCount_ne_zero he hb) hdel
  | loanManage i action =>
    intro h
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.withBroker_ne_wrap _ _ ‹_›
      | exact Loan.canManage_ne_wrap _ _ _ ‹_›
      | exact Loan.manage_ne_wrap _ _ _ _ ‹_›
  | loanPay i pt amount =>
    intro h
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.withBroker_ne_wrap _ _ ‹_›
      | exact Loan.pay_ne_wrap _ _ _ _ _ ‹_›
  | _ => intro h; simp only [LendingLedger.applyLoan] at h; unfold_ter at h; cases h

/-- A transaction on a reachable ledger never wraps while no broker has `2^32 − 1` loans. -/
lemma LendingLedger.apply_ne_wrap (l : LendingLedger) (hr : l.Reachable) (tx : LendingTx)
    (hcount : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount.toNat + 1 < 2 ^ 32) :
    (l.apply tx).run ≠ .error .wrap := by
  intro ha
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_wrap ha
  cases htx : tx <;> subst htx
  case close t =>
    simp only [LendingLedger.applyChecked] at ha
    cases ha
  case vaultDelete =>
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at ha
    unfold_ter at ha
    walk_ok'
    all_goals exact SingleAssetVault.Vault.canVaultDelete_ne_wrap _ ‹_›
  all_goals simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte] at ha
  all_goals split at ha
  all_goals try (cases ha)
  all_goals first
    | exact l.applyVault_ne_wrap hr _ hpre (TerExcept.map_error ha)
    | exact l.applyBroker_ne_wrap hr _ hpre (TerExcept.map_error ha)
    | exact l.applyLoan_ne_wrap hr _ hpre hcount (TerExcept.map_error ha)

end XRPL.Model.Lending
