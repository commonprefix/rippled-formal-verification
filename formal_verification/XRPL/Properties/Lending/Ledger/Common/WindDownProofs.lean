import XRPL.Properties.Lending.Ledger.Common.ClosedLoans
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.SumFacts
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.PayDefs

/-! # Loans lock the vault, and a vault without loans settles

A stored loan that owes principal keeps AssetsDeployed above zero, so no withdrawal or clawback can take
every share. Once no broker has a loan, nothing is lent out, lost or reserved. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultAmounts WithdrawAmount computeWithdraw)

/-- A stored loan that owes principal keeps AssetsDeployed above zero. -/
private lemma LendingLedger.Reachable.deployed_ne_zero {l : LendingLedger} (hr : l.Reachable) {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) (hpo : e.loan.principalOutstanding ≠ Number.zero) :
    l.vault.assetsDeployed.operator_ne Number.zero = true := by
  have hpos : 0 < e.loan.principalOutstanding.toRat := by
    have h0 : 0 ≤ e.loan.principalOutstanding.toRat := e.loan.exact.principalOutstanding_nonneg
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd ((Number.toRat_eq_zero_iff_eq_zero e.loan.wf.principalOutstanding_norm).mp h.symm) hpo
  have hle := l.principalIf_le_sum (fun _ => true) j
  rw [he] at hle
  simp only [LoanEntry.principalIf, if_true] at hle
  have had : 0 < l.vault.assetsDeployed.toRat := by rw [hr.debtInv.deployed]; linarith
  cases hne : l.vault.assetsDeployed.operator_ne Number.zero
  · rw [Number.operator_ne_false_iff_eq'] at hne
    rw [hne, Number.toRat_zero] at had
    exact absurd had (lt_irrefl 0)
  · rfl

/-- Proof body of the VaultWithdraw exit of `Lending.vault_exits`. -/
lemma LendingLedger.loans_lock_withdraw_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat) (e : LoanEntry)
    (he : l.loan? j = some e) (hpo : e.loan.principalOutstanding ≠ Number.zero) (h : Nat) (amount : WithdrawAmount)
    (hpre : (LendingTx.vaultWithdraw h amount).preflight l = .tesSUCCESS) (hnd : l.vaultDeleted = false)
    (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts) (sharesTotalAmount : STAmount)
    (hsoon : (l.vault.earlyExitFeeRate.isNone && l.vault.phase l.now == .investment) = false)
    (hcomp : (computeWithdraw l.vault amount (l.isSoleShareholder h)).run = .ok (.ok amounts))
    (hst : STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : amounts.shares.operator_eq sharesTotalAmount = true) :
    (l.apply (.vaultWithdraw h amount)).run = .ok (.error .tecHAS_OBLIGATIONS) :=
  l.vaultWithdraw_has_obligations h amount hpre hnd hpos amounts sharesTotalAmount hsoon hcomp hst hfinal
    (hr.deployed_ne_zero he hpo)

/-- Proof body of the VaultClawback exit of `Lending.vault_exits`. -/
lemma LendingLedger.loans_lock_clawback_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat) (e : LoanEntry)
    (he : l.loan? j = some e) (hpo : e.loan.principalOutstanding ≠ Number.zero) (h : Nat) (assets : STAmount)
    (hpre : (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS) (hnd : l.vaultDeleted = false)
    (hnn : 0 ≤ assets.toRat) (holderShares shares recovered sharesTotalAmount : STAmount)
    (hheld : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok holderShares)
    (hpr : l.vault.ClawbackPriced assets holderShares (l.isSoleShareholder h) shares recovered)
    (hst : STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : shares.operator_eq sharesTotalAmount = true) :
    (l.apply (.vaultClawback h assets)).run = .ok (.error .tecHAS_OBLIGATIONS) :=
  l.vaultClawback_has_obligations h assets hpre hnd hnn holderShares shares recovered sharesTotalAmount hheld hpr hst
    hfinal (hr.deployed_ne_zero he hpo)

/-- Brokers without loans -> no stored loan. -/
private lemma LendingLedger.Reachable.no_loans_of_counts {l : LendingLedger} (hr : l.Reachable)
    (h0 : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount = 0) :
    ∀ (j : Nat) (e : LoanEntry), l.loan? j ≠ some e := by
  intro j e he
  have hpos := LendingLedger.loansOf_pos he
  have hinv := hr.loanCountInv
  cases hb : l.broker? e.brokerIndex with
  | none => have := hinv.orphans _ hb; omega
  | some b =>
    have hc := hinv.counted _ b hb
    rw [h0 _ b hb] at hc
    simp at hc
    omega

/-- Proof body of `Lending.Reachable.lifecycle_settles`. -/
lemma LendingLedger.lifecycle_settles_proof (l : LendingLedger) (hr : l.Reachable)
    (h0 : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount = 0) :
    l.vault.assetsTotal = .ok l.vault.assetsAvailable ∧ l.vault.assetsDeployed = Number.zero ∧
      l.vault.lossUnrealized = Number.zero ∧ l.vault.assetsReserved = Number.zero ∧
      l.vault.yieldUnrealized = Number.zero := by
  have hnone := hr.no_loans_of_counts h0
  have hz : ∀ p : Loan → Bool, l.principalSum p = 0 := fun p =>
    l.principalSum_eq_zero p fun j e he => absurd he (hnone j e)
  have had : l.vault.assetsDeployed = Number.zero :=
    (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.assetsDeployed_norm).mp (by rw [hr.debtInv.deployed, hz])
  refine ⟨?_, had, ?_, ?_, ?_⟩
  · unfold RawVault.assetsTotal
    rw [show l.vault.toRawVault.assetsDeployed = l.vault.assetsDeployed from rfl, had,
      Number.operator_add_zero_right]
  · exact (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.lossUnrealized_norm).mp
      (by rw [LendingLedger.loss_impaired_proof l hr, hz])
  · exact (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.assetsReserved_norm).mp
      (by rw [LendingLedger.reserved_pending_proof l hr, hz])
  · exact (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.yieldUnrealized_norm).mp
      (by rw [LendingLedger.yield_scheduled_proof l hr, l.interestSum_eq_zero _ fun j e he => absurd he (hnone j e)])

end XRPL.Model.Lending
