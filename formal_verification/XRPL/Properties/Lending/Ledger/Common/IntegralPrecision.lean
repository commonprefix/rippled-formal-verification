import XRPL.Properties.Lending.Ledger.Common.VaultPrecision
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # associateAsset on the vault, its brokers and its loans

YieldUnrealized is whole base units within the Open limit, and a loan's outstanding amounts are whole base units
below the asset's mantissa bound, so the asset stores them exactly. On an XRP or MPT vault every amount
associateAsset rounds, CoverAvailable included, is a whole number within the asset's maximum, so the rounding
changes nothing. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Whole base units, fewer than the asset's mantissa bound, are a value the asset stores exactly. -/
private lemma Vault.isRounded_false_of_atExponent (v : Vault) (hv : Vault.HoldsAsset v) (x : Number)
    (hn : x.isNormalized) (hnn : 0 ≤ x.toRat)
    (h : Number.AtExponent x.toRat v.baseExponent v.numericType.mantissaBound) :
    STAmount.isRounded v.numericType x = false := by
  rw [STAmount.isRounded_eq_false_iff _ _ hn hnn]
  obtain ⟨m, hm, hx⟩ := h
  obtain ⟨hlo, hhi, hint⟩ := v.baseExponent_bounds
  cases hnt : v.numericType with
  | fractional =>
    rw [hnt] at hm
    rw [hx]
    exact STAmount.representable_fractional_of_units m _ hm (by omega) (by omega)
  | integral mv mo ms msh =>
    have hb0 : v.baseExponent = 0 := hint (by rw [hnt]; rfl)
    rw [hb0, zpow_zero, mul_one] at hx
    rw [hnt] at hm
    simp only [NumericType.mantissaBound] at hm
    have hmo : 0 ≤ mo := by
      rcases hv with h | h | h <;> rw [hnt] at h
      · cases h
      · simp only [NumericType.native] at h; rw [(NumericType.integral.inj h).2.1]; decide
      · simp only [NumericType.int64] at h; rw [(NumericType.integral.inj h).2.1]; decide
    have hrep : maxRep.toNat = 9223372036854775807 := by decide
    rcases Nat.eq_zero_or_pos m with rfl | _
    · exact Or.inl (by rw [hx]; simp)
    · exact Or.inr ⟨hmo, m, by omega, by norm_num; omega, hx⟩

/-- On a reachable ledger the asset stores YieldUnrealized exactly: whole base units within the Open limit. -/
lemma LendingLedger.Reachable.yield_isRounded_false {l : LendingLedger} (hr : l.Reachable) :
    STAmount.isRounded l.vault.numericType l.vault.yieldUnrealized = false := by
  have hg := (LendingLedger.base_grid_proof l hr hr.holdsAsset.maxValue_le).2.2.2.2.1
  have h0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
  have hAD : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hle := hr.deployed_yield_le
  unfold LendingLedger.openLimit at hle
  obtain ⟨k, hk, hx⟩ := Number.OnGrid.units_le _ _ hg h0 (by linarith)
  have hmb : 9 * 10 ^ 15 < l.vault.numericType.mantissaBound := by
    rcases hr.holdsAsset with h | h | h <;> rw [h] <;> decide
  exact Vault.isRounded_false_of_atExponent l.vault hr.holdsAsset _ l.vault.wf.yieldUnrealized_norm h0
    ⟨k, lt_of_le_of_lt hk hmb, hx⟩

/-- On a reachable ledger the asset stores every stored loan's PrincipalOutstanding, TotalValueOutstanding and
ManagementFeeOutstanding exactly: each is whole base units below the asset's mantissa bound. -/
lemma LendingLedger.Reachable.loan_isRounded_false {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {e : LoanEntry} (he : l.loan? j = some e) :
    STAmount.isRounded l.vault.numericType e.loan.principalOutstanding = false ∧
      STAmount.isRounded l.vault.numericType e.loan.totalValueOutstanding = false ∧
      STAmount.isRounded l.vault.numericType e.loan.managementFeeOutstanding = false := by
  have hs := hr.scaleInv.loanScale j e he
  have hnt := hr.scaleInv.loanBroker j e he
  have key : ∀ x : Number, x.isNormalized → 0 ≤ x.toRat →
      Number.AtExponent x.toRat e.loan.loanScale e.loan.broker.numericType.mantissaBound →
      STAmount.isRounded l.vault.numericType x = false := fun x hn h0 h => by
    rw [hs, hnt] at h
    exact Vault.isRounded_false_of_atExponent l.vault hr.holdsAsset x hn h0 h
  exact ⟨key _ e.loan.wf.principalOutstanding_norm e.loan.exact.principalOutstanding_nonneg
      e.loan.grid.principalOutstanding_atExponent,
    key _ e.loan.wf.totalValueOutstanding_norm e.loan.exact.totalValueOutstanding_nonneg
      e.loan.grid.totalValueOutstanding_atExponent,
    key _ e.loan.wf.managementFeeOutstanding_norm e.loan.exact.managementFeeOutstanding_nonneg
      e.loan.grid.managementFeeOutstanding_atExponent⟩

/-- Proof body of `Lending.Reachable.associateAsset_noop`. -/
lemma LendingLedger.associateAsset_exact_proof (l : LendingLedger) (hr : l.Reachable) :
    STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsDeployed = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsReserved = false ∧
      STAmount.isRounded l.vault.numericType l.vault.lossUnrealized = false ∧
      STAmount.isRounded l.vault.numericType l.vault.yieldUnrealized = false ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        STAmount.isRounded l.vault.numericType b.debtTotal = false) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        STAmount.isRounded l.vault.numericType e.loan.principalOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.totalValueOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.managementFeeOutstanding = false) ∧
      ∀ m ∈ l.vault.assetsMaximum, STAmount.isRounded l.vault.numericType m = false := by
  obtain ⟨hAA, hAD, hAR, hLU, hDT, hAM⟩ := LendingLedger.associateAsset_noop_proof l hr hr.holdsAsset.maxValue_le
  exact ⟨hAA, hAD, hAR, hLU, hr.yield_isRounded_false, hDT, fun _ _ he => hr.loan_isRounded_false he, hAM⟩

/-- Proof body of `Lending.Reachable.associateAsset_integral`. -/
lemma LendingLedger.associateAsset_integral_proof (l : LendingLedger) (hr : l.Reachable)
    (hint : l.vault.numericType.isIntegral = true)
    (hcap : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      b.coverAvailable.toRat ≤ l.vault.numericType.maxValue.toNat) :
    (STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsDeployed = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsReserved = false ∧
      STAmount.isRounded l.vault.numericType l.vault.lossUnrealized = false ∧
      STAmount.isRounded l.vault.numericType l.vault.yieldUnrealized = false ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        STAmount.isRounded l.vault.numericType b.debtTotal = false) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        STAmount.isRounded l.vault.numericType e.loan.principalOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.totalValueOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.managementFeeOutstanding = false) ∧
      ∀ m ∈ l.vault.assetsMaximum, STAmount.isRounded l.vault.numericType m = false) ∧
    ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      STAmount.isRounded l.vault.numericType b.coverAvailable = false := by
  refine ⟨LendingLedger.associateAsset_exact_proof l hr, fun j b hb => ?_⟩
  rw [STAmount.isRounded_eq_false_iff _ _ b.wf.coverAvailable_norm b.exact.coverAvailable_nonneg]
  exact hr.cover_representable_integral hint hb (hcap j b hb)

end XRPL.Model.Lending
