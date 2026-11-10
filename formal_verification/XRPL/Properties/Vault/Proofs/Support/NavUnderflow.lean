import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # The net asset value never flushes to zero

On a lawful vault the total and the loss it subtracts are far above the smallest Number, so the `to_nearest`
subtraction returns zero only when the exact difference is zero. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A nonzero nonnegative amount an asset stores exactly is at least `10^-81`, the smallest IOU amount. -/
private lemma STAmount.ge_of_isRounded_false (nt : NumericType) (x : Number) (hx : x.isNormalized)
    (hnn : 0 ≤ x.toRat) (hne : x.toRat ≠ 0) (hr : STAmount.isRounded nt x = false) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ x.toRat := by
  rcases (STAmount.isRounded_eq_false_iff nt x hx hnn).mp hr with hz | hr
  · exact absurd hz hne
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, -, -, hk⟩ := hr
    rw [hk] at hne ⊢
    have hk1 : (1 : ℚ) ≤ k := by
      have hk0 : k ≠ 0 := by rintro rfl; exact hne (by simp)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    have h1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := by norm_num
    linarith
  | fractional =>
    obtain ⟨m, e, hmlo, -, helo, -, hval⟩ := hr
    rw [hval]
    have hm : (10 : ℚ) ^ (15 : ℕ) ≤ m := by exact_mod_cast hmlo
    have he : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) helo
    calc (10 : ℚ) ^ (-81 : ℤ) = 10 ^ (15 : ℕ) * 10 ^ (-96 : ℤ) := by norm_num
      _ ≤ m * 10 ^ e := mul_le_mul hm he (by positivity) (by positivity)

/-- A nonzero normalized Number is below `10^19` units of its exponent. -/
private lemma Number.toRat_lt_exponent (x : Number) (hx : x.isNormalized) (hm : x.mantissa_ ≠ 0) :
    x.toRat < (10 : ℚ) ^ (19 : ℕ) * 10 ^ x.exponent_ := by
  rcases hx with hz | ⟨_, hmax, _, _, _⟩
  · exact absurd (by rw [hz]; rfl) hm
  have hle : x.mantissa_.toNat ≤ largeRange.max.toNat := UInt64.le_iff_toNat_le.mp hmax
  rw [largeRange_max_val] at hle
  have hlt : (x.mantissa_.toNat : ℚ) < 10 ^ (19 : ℕ) := by
    exact_mod_cast (show x.mantissa_.toNat < 10 ^ 19 by omega)
  calc x.toRat ≤ |x.toRat| := le_abs_self _
    _ = x.mantissa_.toNat * 10 ^ x.exponent_ := abs_toRat_eq x
    _ < _ := mul_lt_mul_of_pos_right hlt (zpow_pos (by norm_num) _)

/-- Two nonnegative Numbers with exponents at least `E` differ by a whole multiple of `10^E`, so a nonzero
difference is at least `10^E`. -/
private lemma Number.sub_ge_of_exponent_ge (x y : Number) (E : ℤ) (hxn : x.negative_ = false)
    (hyn : y.negative_ = false) (hxe : E ≤ x.exponent_) (hye : E ≤ y.exponent_)
    (hne : x.toRat - y.toRat ≠ 0) : (10 : ℚ) ^ E ≤ |x.toRat - y.toRat| := by
  have hgrid : ∀ n : Number, n.negative_ = false → E ≤ n.exponent_ →
      n.toRat = ((n.mantissa_.toNat * 10 ^ (n.exponent_ - E).toNat : ℕ) : ℚ) * 10 ^ E := by
    intro n hn he
    rw [Number.toRat_of_nonneg n hn]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
      Int.toNat_of_nonneg (by omega : 0 ≤ n.exponent_ - E), sub_add_cancel]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, x.toRat = (a : ℚ) * 10 ^ E := ⟨_, hgrid x hxn hxe⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, y.toRat = (b : ℚ) * 10 ^ E := ⟨_, hgrid y hyn hye⟩
  have hd : x.toRat - y.toRat = (((a : ℤ) - b : ℤ) : ℚ) * 10 ^ E := by
    rw [ha, hb]; push_cast; ring
  have hk : (a : ℤ) - b ≠ 0 := by
    intro h; apply hne; rw [hd, h]; simp
  have h1 : (1 : ℚ) ≤ |(((a : ℤ) - b : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hpow : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) E
  rw [hd, abs_mul, abs_of_pos hpow]
  nlinarith

/-- On a lawful vault, subtracting from the total a nonnegative amount at most the deployed assets gives zero only
when the exact difference is zero. -/
lemma Vault.assetsTotal_sub_zero_exact (v : Vault) (total y nav : Number)
    (hat : v.assetsTotal = .ok total) (hy : y.isNormalized) (hy_nn : 0 ≤ y.toRat)
    (hy_le : y.toRat ≤ v.assetsDeployed.toRat)
    (hok : total.operator_sub y .to_nearest = .ok nav) (h0 : nav.mantissa_ = 0) :
    total.toRat - y.toRat = 0 := by
  obtain ⟨htn, hge⟩ := v.assetsTotal_ge_deployed total hat
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  by_contra hd
  -- subtracting zero returns the total, so a zero `y` leaves a zero total
  have hym : y.mantissa_ ≠ 0 := by
    intro hym
    rw [Number.eq_zero_of_mantissa_zero y hy hym, Number.operator_sub_zero, Except.ok.injEq] at hok
    subst hok
    apply hd
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0, Number.toRat_eq_zero_of_mantissa_zero _ hym, sub_zero]
  have hy0 : 0 < y.toRat :=
    lt_of_le_of_ne hy_nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero y hym))
  have hpos : 0 < total.toRat - y.toRat := lt_of_le_of_ne (by linarith) (Ne.symm hd)
  have htm : total.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hpos; linarith
  have htneg := Number.negative_false_of_nonneg total htn (by linarith)
  have hyneg := Number.negative_false_of_nonneg y hy hy_nn
  -- the model flushed a nonzero difference, so it is below the underflow bound
  have hsmall := operator_add_underflow_truth_small total y.operator_neg nav .to_nearest htn
    (Number.operator_neg_isNormalized y hy) htm (by simp [Number.operator_neg, hym])
    (by simp [Number.operator_neg, hym, htneg, hyneg])
    (fun h => hd (by rw [sub_eq_add_neg_toRat]; exact add_truth_zero_of_eq_neg _ _ h)) hok h0
  rw [← sub_eq_add_neg_toRat, abs_of_pos hpos] at hsmall
  have hU : (10 : ℚ) ^ (18 : ℕ) * 10 ^ minExponent = 10 ^ (minExponent + 18) := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm]; norm_num
  rw [hU] at hsmall
  -- AssetsDeployed fits an STAmount, so it and the total are at least 10^-81
  have hAD : (10 : ℚ) ^ (-81 : ℤ) ≤ v.assetsDeployed.toRat :=
    STAmount.ge_of_isRounded_false _ _ v.wf.assetsDeployed_norm hAD0 (by linarith)
      v.valid.assetsDeployed_representable
  have hte : minExponent + 18 ≤ total.exponent_ := by
    have hlt := Number.toRat_lt_exponent total htn htm
    rw [show (10 : ℚ) ^ (19 : ℕ) * 10 ^ total.exponent_ = 10 ^ (total.exponent_ + 19) by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm]; norm_num] at hlt
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp (by linarith : (10 : ℚ) ^ (-81 : ℤ) <
      10 ^ (total.exponent_ + 19))
    unfold minExponent; omega
  by_cases hye : minExponent + 18 ≤ y.exponent_
  · -- both on the grid of 10^(minExponent + 18), so a nonzero difference is at least one step
    have := Number.sub_ge_of_exponent_ge total y _ htneg hyneg hte hye hd
    rw [abs_of_pos hpos] at this
    linarith
  · -- y is below 10^-82, so the difference stays above 10^-82
    have hylt := Number.toRat_lt_exponent y hy hym
    have hpe : (10 : ℚ) ^ y.exponent_ ≤ 10 ^ (-101 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent at hye; omega)
    have hyb : y.toRat < 10 ^ (-82 : ℤ) := by
      have h82 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-101 : ℤ) = 10 ^ (-82 : ℤ) := by norm_num
      nlinarith
    have hUb : (10 : ℚ) ^ (minExponent + 18) ≤ 10 ^ (-82 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; omega)
    have h81 : (10 : ℚ) ^ (-82 : ℤ) + 10 ^ (-82 : ℤ) ≤ 10 ^ (-81 : ℤ) := by norm_num
    linarith

end XRPL.Model.SingleAssetVault
