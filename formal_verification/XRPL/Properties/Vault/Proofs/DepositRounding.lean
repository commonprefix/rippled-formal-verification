import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Vault.Proofs.OpenZone
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # `Vault.deposit` entry rounding and donation -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open DepRnd

lemma Vault.roundedDepositAmount_integral_proof (v : Vault) (amountDeposit : STAmount) (assetsTotal : Number)
    (hint : amountDeposit.integral = true) (hpos : 0 < amountDeposit.toRat)
    (hat : v.assetsTotal = .ok assetsTotal) :
    (v.roundedDepositAmount amountDeposit).run = .ok (.ok amountDeposit) := by
  have hneg : amountDeposit.negative = false := STAmount.mIsNegative_false_of_pos amountDeposit hpos
  have hcl := clampToSumExponent_integral assetsTotal amountDeposit v.baseExponent hint
  rw [hneg, if_neg (by decide)] at hcl
  have hz : amountDeposit.isZero = false := by
    have hmv : amountDeposit.mValue ≠ 0 := fun h0 => by
      rw [(STAmount.toRat_eq_zero_iff amountDeposit).mpr h0] at hpos; exact lt_irrefl _ hpos
    simpa [STAmount.isZero] using hmv
  rw [roundedDepositAmount_ok v amountDeposit amountDeposit assetsTotal hat hcl, hz]
  rfl

lemma Vault.deposit_donation_proof (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    r.assets = roundedAmount ∧ r.shares = STAmount.zero .int64 := by
  obtain ⟨ra, amounts, -, hra, hcd, -, -, -, hassets, hshares⟩ :=
    Vault.deposit_ok_reduces v amountDeposit true t hpos r hok
  rw [hrounded, Except.ok.injEq, Except.ok.injEq] at hra
  rw [← hra] at hcd
  obtain ⟨assetsTotal, hsh0, hat, hcl₂, hfnp⟩ := computeDeposit_donation_reduces v roundedAmount amounts hcd
  obtain ⟨assetsTotal', hat', hcl₁, -⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  refine ⟨?_, by rw [hshares, hsh0]⟩
  rw [hassets]
  obtain ⟨hAn, hAD⟩ := Vault.assetsTotal_ge_deployed v assetsTotal hat
  have hA0 : 0 ≤ assetsTotal.toRat := le_trans v.exact.assetsDeployed_nonneg hAD
  by_cases hint : amountDeposit.integral = true
  · -- integral amounts pass through both clamps
    have h1 := clampToSumExponent_integral_nonneg assetsTotal amountDeposit roundedAmount v.baseExponent hint
      hpos.le hcl₁
    rw [h1] at hcl₂ ⊢
    exact clampToSumExponent_integral_nonneg assetsTotal amountDeposit amounts.assets v.baseExponent hint
      hpos.le hcl₂
  -- a fractional charge that survives the zero check is nonzero
  have hfr : amountDeposit.integral = false := by simpa using hint
  have hc'0 : amounts.assets.mValue ≠ 0 := by
    intro h0
    obtain ⟨-, hcnt, -⟩ := clampToSumExponent_canonicalOrZero assetsTotal roundedAmount amounts.assets
      v.baseExponent
      (Or.inl (DepRnd.Vault.roundedDepositAmount_canonical_pos v amountDeposit roundedAmount hcanon hrounded).1)
      v.baseExponent_range.1 v.baseExponent_range.2 hcl₂
    obtain ⟨-, hrnt, -⟩ := clampToSumExponent_canonicalOrZero assetsTotal amountDeposit roundedAmount v.baseExponent
      (Or.inl hcanon) v.baseExponent_range.1 v.baseExponent_range.2 hcl₁
    have hnt : amounts.assets.mNumericType = .fractional := by
      rw [hcnt, hrnt, (hcanon.2 hfr).is_fractional]
    rw [STAmount.isFractionalNonPositive_zero _ hnt h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  exact clampToSumExponent_twice assetsTotal amountDeposit roundedAmount amounts.assets v.baseExponent hAn hA0
    hcanon hpos (by have := v.baseExponent_range.1; omega) v.baseExponent_range.2 hcl₁ hcl₂ hc'0

lemma Vault.roundedDepositAmount_bounds_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hpos : 0 < amountDeposit.toRat)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false := by
  obtain ⟨assetsTotal, -, hcl, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  refine ⟨?_, hnz⟩
  have hmv : roundedAmount.mValue ≠ 0 := (STAmount.isZero_eq_false_iff _).mp hnz
  by_cases hint : amountDeposit.integral = true
  · -- the clamp hands an integral amount straight back, which sits on its own grid
    have heq := clampToSumExponent_integral_nonneg assetsTotal amountDeposit roundedAmount v.baseExponent hint
      hpos.le hcl
    subst heq
    exact ⟨roundedAmount.exponent, STAmount.self_grid roundedAmount,
      STAmount.ulp_le_abs_toRat roundedAmount hmv⟩
  have hfr : amountDeposit.integral = false := by simpa using hint
  have hc := hcanon hfr
  obtain ⟨-, e, -, -, -, hval⟩ := clampToSumExponent_frac_floor assetsTotal amountDeposit roundedAmount
    v.baseExponent ⟨hc.is_fractional, Or.inl hc⟩ v.baseExponent_range.1 v.baseExponent_range.2 hmv hcl
  rw [abs_of_pos hpos] at hval
  refine ⟨e, hval, ?_⟩
  -- a nonzero floor keeps at least one grid step
  have hpow : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hk1 : 1 ≤ ⌊amountDeposit.toRat / 10 ^ e⌋ := by
    have hnn : 0 ≤ ⌊amountDeposit.toRat / 10 ^ e⌋ := Int.floor_nonneg.mpr (div_pos hpos hpow).le
    have hne : ⌊amountDeposit.toRat / 10 ^ e⌋ ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, zero_mul] at hval
      exact STAmount.toRat_ne_zero roundedAmount hmv hval
    omega
  have hk1q : (1 : ℚ) ≤ (⌊amountDeposit.toRat / 10 ^ e⌋ : ℚ) := by exact_mod_cast hk1
  rw [hval, abs_of_nonneg (by positivity)]
  nlinarith

end XRPL.Model.SingleAssetVault
