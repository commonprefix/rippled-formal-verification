import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Reduce

/-! # Pricing and clamp facts for the withdraw proofs -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

lemma zero_mOffset (nt : NumericType) (hint : nt.isIntegral = true) :
    (STAmount.zero nt).mOffset = 0 := by
  cases nt with
  | fractional => exact absurd hint (by decide)
  | integral => rfl

/-- On an integral vault the priced payout is an offset-`0` record within `maxRep`. -/
lemma price_integral_shape (v : Vault) (sh p : STAmount) (w : Bool)
    (hint : v.numericType.isIntegral = true)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    p.mNumericType = v.numericType ∧ p.mOffset = 0 ∧ p.mValue.toNat ≤ maxRep.toNat := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact ⟨STAmount.zero_mNumericType _, zero_mOffset _ hint, by rw [STAmount.zero_mValue]; exact Nat.zero_le _⟩
    | exact STAmount.ofNumber_integral_facts _ _ _ _ hint ‹_›

/-- On an integral amount the clamp returns the negated amount's magnitude:
the record fields other than the sign are unchanged. -/
lemma clamp_integral (x : Number) (a b : STAmount) (hint : a.integral = true)
    (hok : clampToSumExponent x a.operator_neg = .ok b) :
    b.mNumericType = a.mNumericType ∧ b.mOffset = a.mOffset ∧ b.mValue = a.mValue ∧
      (b.mValue = 0 ∨ b.mIsNegative = false) := by
  have hint' : a.operator_neg.integral = true := by
    unfold STAmount.operator_neg; split <;> exact hint
  simp only [clampToSumExponent, hint', if_true, pure, Except.pure] at hok
  have hb := (Except.ok.inj hok).symm
  subst hb
  unfold STAmount.operator_neg STAmount.negative
  by_cases h0 : a.mValue = 0
  · simp [h0]
  · simp [h0]
    cases a.mIsNegative <;> simp

/-- An integer above a nonnegative normalized `x` clears it by `10 ^ (-40)`. -/
lemma int_gap (x : Number) (hx : x.isNormalized) (hxnn : 0 ≤ x.toRat) (k : ℚ)
    (hk : k.den = 1) (hlt : x.toRat < k) : x.toRat + (10 : ℚ) ^ (-40 : ℤ) ≤ k := by
  have hp : (10 : ℚ) ^ (-40 : ℤ) ≤ 1 / 2 := by norm_num
  have hk1 : 1 ≤ k := by
    have := rat_one_le_sub_of_lt k 0 hk rfl (lt_of_le_of_lt hxnn hlt); linarith
  by_cases hsmall : x.toRat < 1 / 2
  · generalize (10 : ℚ) ^ (-40 : ℤ) = g at hp ⊢; linarith
  push_neg at hsmall
  have hm : x.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero x h] at hsmall; norm_num at hsmall
  have hneg := Number.negative_false_of_normalized_nonneg x hx hxnn
  have hval := Number.toRat_of_nonneg x hneg
  obtain ⟨hMlo, hMhi⟩ := hx.mantissaBounds_nat hm
  set M := x.mantissa_.toNat with hM
  set e := x.exponent_ with he
  by_cases he0 : 0 ≤ e
  · have hden : x.toRat.den = 1 := by
      rw [hval, show e = ((e.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg he0).symm, zpow_natCast]
      exact_mod_cast Rat.den_natCast (M * 10 ^ e.toNat)
    have := rat_one_le_sub_of_lt k x.toRat hk hden hlt
    generalize (10 : ℚ) ^ (-40 : ℤ) = g at hp ⊢; linarith
  push_neg at he0
  set n := (-e).toNat with hn
  have hen : e = -(n : ℤ) := by rw [hn, Int.toNat_of_nonneg (by omega)]; ring
  have hpow : (10 : ℚ) ^ e = 1 / 10 ^ n := by rw [hen, zpow_neg, zpow_natCast]; ring
  have h10 : (0 : ℚ) < 10 ^ n := by positivity
  -- the exponent is at least `-20`, since `x ≥ 1/2` and `M < 10 ^ 19`
  have hn20 : n ≤ 20 := by
    by_contra hc
    push_neg at hc
    have h1 : (10 : ℚ) ^ 21 ≤ 10 ^ n := pow_le_pow_right₀ (by norm_num) hc
    have h2 : (M : ℚ) < 10 ^ 19 := by exact_mod_cast hMhi
    rw [hval, hpow] at hsmall
    rw [mul_one_div, le_div_iff₀ h10] at hsmall
    nlinarith
  -- grid step: `x + 10 ^ e ≤ k`
  have hkq : k = (k.num : ℚ) := (rat_eq_num_cast_of_den_one k hk).symm
  have hlt' : (M : ℚ) < (k.num : ℚ) * 10 ^ n := by
    rw [hval, hpow, hkq, mul_one_div, div_lt_iff₀ h10] at hlt; exact hlt
  have hint : (M : ℤ) < k.num * 10 ^ n := by exact_mod_cast hlt'
  have hstep : ((M : ℚ) + 1) ≤ (k.num : ℚ) * 10 ^ n := by
    have : (M : ℤ) + 1 ≤ k.num * 10 ^ n := hint
    exact_mod_cast this
  have hg : (10 : ℚ) ^ (-40 : ℤ) ≤ 1 / 10 ^ n := by
    rw [zpow_neg, one_div]
    apply inv_anti₀ h10
    calc (10 : ℚ) ^ n ≤ 10 ^ 40 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (10 : ℚ) ^ (40 : ℤ) := by norm_num
  rw [hval, hpow, hkq]
  have : (M : ℚ) * (1 / 10 ^ n) + 1 / 10 ^ n ≤ (k.num : ℚ) := by
    rw [show (M : ℚ) * (1 / 10 ^ n) + 1 / 10 ^ n = (M + 1) / 10 ^ n by ring,
      div_le_iff₀ h10]; linarith
  linarith

/-- A nonnegative rounded difference `x - k` with integer `k` forces `k ≤ x`. -/
lemma le_of_sub_nonneg (x y r : Number) (hx : x.isNormalized) (hxnn : 0 ≤ x.toRat)
    (hy : y.isNormalized) (hyd : y.toRat.den = 1)
    (hok : x.operator_sub y .to_nearest = .ok r) (hr : 0 ≤ r.toRat) :
    y.toRat ≤ x.toRat := by
  by_contra hlt
  push_neg at hlt
  have hgap := int_gap x hx hxnn y.toRat hyd hlt
  obtain ⟨w, hw, -, -, hwv, -⟩ := exists_normalized_of_int_mul_pow 1 (-40) le_rfl (by norm_num)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hle := operator_sub_le_of_le_normalized x y r w.operator_neg hx hy hok
    (Number.operator_neg_isNormalized w hw) (by rw [Number.toRat_neg, hwv]; push_cast; linarith)
  rw [Number.toRat_neg, hwv] at hle
  have : (0 : ℚ) < 10 ^ (-40 : ℤ) := by positivity
  push_cast at hle
  linarith

end XRPL.Model.SingleAssetVault.WdAcc
