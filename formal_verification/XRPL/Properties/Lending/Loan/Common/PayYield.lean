import XRPL.Properties.Lending.Loan.Common.PayReachable
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # YieldUnrealized after a payment on a reachable ledger

A payment adds the change in the loan's interestDue to YieldUnrealized. What the loan owes the vault does not rise,
so the new YieldUnrealized stays below AssetsDeployed + YieldUnrealized before it, inside the Open limit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.pay_yieldDelta from XRPL.Properties.Lending.Loan.Common.PayReachable

/-- A payment on a reachable ledger leaves YieldUnrealized below `10^16` base units. The change it adds is at
most the loan's PrincipalOutstanding, which AssetsDeployed holds. -/
lemma LendingLedger.Reachable.pay_yield_lt {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {pt : LoanPaymentType} {amount : Number} {r : LoanWithAmounts Vault}
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r)) :
    r.pool'.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
  obtain ⟨yd, hydn, hy, k, hydv, hk1, -, hyde⟩ := Loan.pay_yieldDelta loan amount pt r l hr i hat hok
  obtain ⟨t, -, hrl⟩ := hr.loanAt_reachable hat
  have hi0 := Loan.Reachable.interestDue_nonneg hrl
  have hls := (hr.loanAt_scale hat).1
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  -- what the loan owes the vault does not rise, and AssetsDeployed holds its principal
  have howe := Loan.pay_owed_le loan l.vault pt amount l.now r (by rw [hls]; omega)
    (fun _ => by rw [hls]; exact hbhi) hi0 hok
  obtain ⟨-, -, -, hPAD, -⟩ := hr.loanAt_principal hat
  have hP0' : 0 ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
  have hbound := hr.deployed_yield_le
  unfold LendingLedger.openLimit at hbound
  -- YieldUnrealized plus the change stays inside the Open limit, so the sum is exact
  obtain ⟨hYn, ky, hky⟩ := hr.yieldGridInv.grid
  have hky0 : 0 ≤ ky := by
    have h0 : (0 : ℚ) ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
    rw [hky] at h0
    exact_mod_cast nonneg_of_mul_nonneg_left h0 hp
  have hle : ((ky + k : ℤ) : ℚ) * 10 ^ l.vault.baseExponent ≤ 9 * 10 ^ 15 * 10 ^ l.vault.baseExponent := by
    push_cast
    rw [add_mul, ← hky, ← hydv, hyde]
    linarith
  have hlt : ky + k < 2 ^ 63 := by
    have : ((ky + k : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast at hle ⊢; nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have hv := Number.operator_add_toRat_of_grid _ _ _ ky k l.vault.baseExponent hYn hydn hky hydv
    (by constructor <;> omega) hsb hy
  rw [hv]
  push_cast at hle ⊢
  nlinarith

end XRPL.Model.Lending
