import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Loan.Common.Impaired

/-! # Proof bodies for the vault-phase theorems -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- The invariant's schedule is the vault's schedule. -/
private lemma LendingLedger.LoansInv.schedule_eq {l : LendingLedger} {s s' : VaultSchedule} (hinv : l.LoansInv s')
    (hs : l.vault.schedule = some s) : s' = s := by
  rw [hinv.schedule] at hs; exact Option.some.inj hs

/-- Proof body of `Lending.Reachable.loans_mature`. -/
lemma LendingLedger.loans_mature_proof (l : LendingLedger) (hr : l.Reachable) (s : VaultSchedule)
    (hs : l.vault.schedule = some s) (j : Nat) (e : LoanEntry) (he : l.loan? j = some e) :
    e.loan.schedule.startDate.toNat + e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat +
      loanRedemptionBuffer ≤ s.redemptionDate.toNat := by
  obtain ⟨s', hinv⟩ := hr.loansInv
  rw [← hinv.schedule_eq hs]
  exact hinv.mature j e he

/-- A stored loan with payments left is due before RedemptionDate. -/
lemma LendingLedger.due_before_redemption (l : LendingLedger) (hr : l.Reachable) (s : VaultSchedule)
    (hs : l.vault.schedule = some s) (j : Nat) (e : LoanEntry) (he : l.loan? j = some e)
    (hp : e.loan.paymentRemaining ≠ 0) :
    e.loan.nextPaymentDueDate.toNat + loanRedemptionBuffer ≤ s.redemptionDate.toNat := by
  obtain ⟨s', hinv⟩ := hr.loansInv
  have hm := hinv.mature j e he
  rw [hinv.schedule_eq hs] at hm
  obtain ⟨t, -, hre⟩ := hinv.reachable j e he
  have hdue := Loan.Reachable.dueDate_proof e.loan t hre hp
  have hle : e.loan.paymentRemaining.toNat ≤ e.loan.schedule.paymentTotal.toNat :=
    UInt32.le_iff_toNat_le.mp (Loan.Reachable.paymentRemaining_le e.loan t hre)
  have hP1 : 1 ≤ e.loan.paymentRemaining.toNat := by
    have : e.loan.paymentRemaining.toNat ≠ 0 := fun h0 => hp (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  have hmul : (e.loan.schedule.paymentTotal.toNat - e.loan.paymentRemaining.toNat + 1) *
      e.loan.schedule.paymentInterval.toNat ≤
      e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The redemption phase starts at RedemptionDate. -/
private lemma Vault.redemption_after (v : Vault) (t : UInt32) (s : VaultSchedule) (hs : v.schedule = some s)
    (hred : v.phase t = .redemption) : s.redemptionDate.toNat ≤ t.toNat := by
  unfold XRPL.Model.SingleAssetVault.Vault.phase at hred
  rw [hs] at hred
  dsimp only at hred
  split at hred
  · cases hred
  · split at hred
    · cases hred
    · rename_i h
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at h
      exact UInt32.le_iff_toNat_le.mp h

/-- Proof body of the late-payment line of `Lending.Reachable.redemption_loans_late`. -/
lemma LendingLedger.redemption_loans_late_proof (l : LendingLedger) (hr : l.Reachable)
    (hred : l.vault.phase l.now = .redemption) (j : Nat) (e : LoanEntry) (he : l.loan? j = some e)
    (hp : e.loan.paymentRemaining ≠ 0) : e.loan.isPaymentLate l.now = true := by
  obtain ⟨s, hinv⟩ := hr.loansInv
  have hdue := l.due_before_redemption hr s hinv.schedule j e he hp
  have hafter := Vault.redemption_after l.vault l.now s hinv.schedule hred
  unfold Loan.isPaymentLate
  simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
  unfold loanRedemptionBuffer at hdue
  omega

/-- Proof body of the GracePeriod line of `Lending.Reachable.redemption_loans_late`. -/
lemma LendingLedger.redemption_defaultable_proof (l : LendingLedger) (hr : l.Reachable) (s : VaultSchedule)
    (hs : l.vault.schedule = some s) (j : Nat) (e : LoanEntry) (he : l.loan? j = some e)
    (hp : e.loan.paymentRemaining ≠ 0)
    (ht : s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat) :
    e.loan.nextPaymentDueDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat := by
  have hdue := l.due_before_redemption hr s hs j e he hp
  unfold loanRedemptionBuffer at hdue
  omega

/-- Proof body of `Lending.Reachable.impaired_late`. -/
lemma LendingLedger.impaired_late_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat) (e : LoanEntry)
    (he : l.loan? j = some e) (hi : e.loan.isImpaired = true) (hp : e.loan.paymentRemaining ≠ 0) :
    e.loan.isPaymentLate l.now = true := by
  obtain ⟨s, hinv⟩ := hr.loansInv
  obtain ⟨t, hle, hre⟩ := hinv.reachable j e he
  have h := Loan.Reachable.impaired_late_proof e.loan t hre hi hp
  unfold Loan.isPaymentLate at h ⊢
  simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt] at h ⊢
  rw [UInt32.le_iff_toNat_le] at hle
  omega

end XRPL.Model.Lending
