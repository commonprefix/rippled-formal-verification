import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # The gap between the largest Number and the next one

The largest Number is `Number.top`. The next value up, `Number.top_plus_ten`, does not fit. An exact result between
them should round to one of the two, and the rounding mode decides which. Add, subtract and divide check for overflow
before they round (FV_M1_19), so they return a result exactly below `Number.top_plus_one`, in every mode. The lemmas
here say for which exact results that agrees with the rule of each mode. -/

namespace XRPL.Model.Protocol

/-- The largest Number, `(2^63 + 2) * 10^32768`: the mantissa `maxRepUp` at `maxExponent`. -/
def Number.top : ℚ := 9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ)

/-- `Number.top` with its mantissa plus one, `(2^63 + 3) * 10^32768`. From this size on add, subtract and divide fail
in every mode, because they check for overflow before they round (FV_M1_19). -/
def Number.top_plus_one : ℚ := 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ)

/-- `Number.top` with its mantissa plus five, `(2^63 + 7) * 10^32768`: halfway to the next value. -/
def Number.top_plus_five : ℚ := 9223372036854775815 * (10 : ℚ) ^ (maxExponent : ℤ)

/-- `Number.top` with its mantissa plus ten, `(2^63 + 12) * 10^32768`: the next value. It does not fit in a Number. -/
def Number.top_plus_ten : ℚ := 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ)

lemma ten_zpow_maxExponent_pos : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _

/-- The four values in order. -/
lemma Number.topGap_order :
    0 < Number.top ∧ Number.top < Number.top_plus_one ∧
      Number.top_plus_one < Number.top_plus_five ∧ Number.top_plus_five < Number.top_plus_ten := by
  have hp := ten_zpow_maxExponent_pos
  unfold Number.top Number.top_plus_one Number.top_plus_five Number.top_plus_ten
  generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Where the early check agrees with the rule of each mode

Each lemma is an "exactly when". So the range on its right side is the widest one a theorem can assume. -/

lemma topGap_to_nearest_agree_iff {v : ℚ} :
    (|v| < Number.top_plus_one ↔ |v| < Number.top_plus_five) ↔
      (|v| < Number.top_plus_one ∨ Number.top_plus_five ≤ |v|) := by
  obtain ⟨-, -, hRM, -⟩ := Number.topGap_order
  constructor
  · intro h
    by_cases hv : |v| < Number.top_plus_one
    · exact Or.inl hv
    · exact Or.inr (not_lt.mp fun hlt => hv (h.mpr hlt))
  · rintro (h | h)
    · exact ⟨fun _ => by linarith, fun _ => h⟩
    · exact ⟨fun h' => by linarith, fun h' => by linarith⟩

lemma topGap_towards_zero_agree_iff {v : ℚ} :
    (|v| < Number.top_plus_one ↔ |v| < Number.top_plus_ten) ↔
      (|v| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |v|) := by
  obtain ⟨-, -, hRM, hMN⟩ := Number.topGap_order
  constructor
  · intro h
    by_cases hv : |v| < Number.top_plus_one
    · exact Or.inl hv
    · exact Or.inr (not_lt.mp fun hlt => hv (h.mpr hlt))
  · rintro (h | h)
    · exact ⟨fun _ => by linarith, fun _ => h⟩
    · exact ⟨fun h' => by linarith, fun h' => by linarith⟩

lemma topGap_downward_agree_iff {v : ℚ} :
    (|v| < Number.top_plus_one ↔ -Number.top ≤ v ∧ v < Number.top_plus_ten) ↔
      ((v ≤ -Number.top_plus_one ∨ -Number.top ≤ v) ∧
        (v < Number.top_plus_one ∨ Number.top_plus_ten ≤ v)) := by
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  rw [abs_lt]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases h1 : -Number.top ≤ v
      · exact Or.inr h1
      · exact Or.inl (not_lt.mp fun h2 => h1 (h.mp ⟨h2, by linarith⟩).1)
    · by_cases h2 : v < Number.top_plus_one
      · exact Or.inl h2
      · exact Or.inr (not_lt.mp fun h3 => h2 (h.mpr ⟨by linarith, h3⟩).2)
  · rintro ⟨h1, h2⟩
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨?_, by linarith⟩
      rcases h1 with h1 | h1
      · linarith
      · exact h1
    · rintro ⟨ha, hb⟩
      refine ⟨by linarith, ?_⟩
      rcases h2 with h2 | h2
      · exact h2
      · linarith

lemma topGap_upward_agree_iff {v : ℚ} :
    (|v| < Number.top_plus_one ↔ -Number.top_plus_ten < v ∧ v ≤ Number.top) ↔
      ((v ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < v) ∧
        (v ≤ Number.top ∨ Number.top_plus_one ≤ v)) := by
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  rw [abs_lt]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases h1 : -Number.top_plus_one < v
      · exact Or.inr h1
      · exact Or.inl (not_lt.mp fun h2 => h1 (h.mpr ⟨h2, by linarith⟩).1)
    · by_cases h2 : v ≤ Number.top
      · exact Or.inl h2
      · exact Or.inr (not_lt.mp fun h3 => h2 (h.mp ⟨by linarith, h3⟩).2)
  · rintro ⟨h1, h2⟩
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨by linarith, ?_⟩
      rcases h2 with h2 | h2
      · exact h2
      · linarith
    · rintro ⟨ha, hb⟩
      refine ⟨?_, by linarith⟩
      rcases h1 with h1 | h1
      · linarith
      · exact h1

/-! ## The overflow rule of each mode against the early check

In `to_nearest` and `towards_zero` the overflow rule of the mode always implies the early check. In `downward` and
`upward` it does so exactly on the range on the right side. -/

lemma topGap_overflow_to_nearest {v : ℚ} (h : Number.top_plus_five ≤ |v|) : Number.top_plus_one ≤ |v| := by
  obtain ⟨-, -, hRM, -⟩ := Number.topGap_order
  linarith

lemma topGap_overflow_towards_zero {v : ℚ} (h : Number.top_plus_ten ≤ |v|) : Number.top_plus_one ≤ |v| := by
  obtain ⟨-, -, hRM, hMN⟩ := Number.topGap_order
  linarith

lemma topGap_overflow_downward_iff {v : ℚ} :
    (v < -Number.top ∨ Number.top_plus_ten ≤ v → Number.top_plus_one ≤ |v|) ↔
      (v ≤ -Number.top_plus_one ∨ -Number.top ≤ v) := by
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  constructor
  · intro h
    by_cases h1 : -Number.top ≤ v
    · exact Or.inr h1
    · have h2 := h (Or.inl (not_le.mp h1))
      rw [abs_of_neg (by linarith)] at h2
      exact Or.inl (by linarith)
  · rintro (h1 | h1) (h | h)
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

lemma topGap_overflow_upward_iff {v : ℚ} :
    (v ≤ -Number.top_plus_ten ∨ Number.top < v → Number.top_plus_one ≤ |v|) ↔
      (v ≤ Number.top ∨ Number.top_plus_one ≤ v) := by
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  constructor
  · intro h
    by_cases h1 : v ≤ Number.top
    · exact Or.inl h1
    · have h2 := h (Or.inr (not_le.mp h1))
      rw [abs_of_pos (by linarith)] at h2
      exact Or.inr h2
  · rintro (h1 | h1) (h | h)
    · rw [abs_of_neg (by linarith)]; linarith
    · linarith
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-! ## Operands with an exact result in the gap

These are the operands of the FV_M1_19 C++ test. "mid" results are from `Number.top_plus_one` to below
`Number.top_plus_five`, "low" results are between `Number.top` and `Number.top_plus_one`. -/

lemma Number.toRat_mk_nonneg (m : UInt64) (e : Int) (n : ℕ) (hm : m.toNat = n) :
    (⟨false, m, e⟩ : Number).toRat = (n : ℚ) * (10 : ℚ) ^ e := by
  rw [← hm]; exact Number.toRat_of_nonneg _ rfl

lemma Number.toRat_mk_neg (m : UInt64) (e : Int) (n : ℕ) (hm : m.toNat = n) :
    (⟨true, m, e⟩ : Number).toRat = -((n : ℚ) * (10 : ℚ) ^ e) := by
  rw [← hm]; exact Number.toRat_of_neg _ rfl

lemma Number.add_topGap_mid_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top_plus_one ≤ x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_five := by
  refine ⟨⟨false, 9223372036854775810, maxExponent⟩, ⟨false, 3000000000000000000, maxExponent - 18⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_nonneg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_nonneg _ _ 3000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.add_topGap_mid_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_five < x.toRat + y.toRat ∧ x.toRat + y.toRat ≤ -Number.top_plus_one := by
  refine ⟨⟨true, 9223372036854775810, maxExponent⟩, ⟨true, 3000000000000000000, maxExponent - 18⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_neg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_neg _ _ 3000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.add_topGap_low_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_one := by
  refine ⟨⟨false, 9223372036854775810, maxExponent⟩, ⟨false, 4000000000000000000, maxExponent - 19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_nonneg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_nonneg _ _ 4000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.add_topGap_low_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_one < x.toRat + y.toRat ∧ x.toRat + y.toRat < -Number.top := by
  refine ⟨⟨true, 9223372036854775810, maxExponent⟩, ⟨true, 4000000000000000000, maxExponent - 19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_neg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_neg _ _ 4000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.sub_topGap_mid_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top_plus_one ≤ x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_five := by
  refine ⟨⟨false, 9223372036854775810, maxExponent⟩, ⟨true, 3000000000000000000, maxExponent - 18⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_nonneg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_neg _ _ 3000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.sub_topGap_mid_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_five < x.toRat - y.toRat ∧ x.toRat - y.toRat ≤ -Number.top_plus_one := by
  refine ⟨⟨true, 9223372036854775810, maxExponent⟩, ⟨false, 3000000000000000000, maxExponent - 18⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_neg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_nonneg _ _ 3000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.sub_topGap_low_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_one := by
  refine ⟨⟨false, 9223372036854775810, maxExponent⟩, ⟨true, 4000000000000000000, maxExponent - 19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_nonneg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_neg _ _ 4000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.sub_topGap_low_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_one < x.toRat - y.toRat ∧ x.toRat - y.toRat < -Number.top := by
  refine ⟨⟨true, 9223372036854775810, maxExponent⟩, ⟨false, 4000000000000000000, maxExponent - 19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_neg _ _ 9223372036854775810 rfl,
      Number.toRat_mk_nonneg _ _ 4000000000000000000 rfl, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.div_topGap_mid_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top_plus_one ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_five := by
  refine ⟨⟨false, 8507059173023461590, maxExponent⟩, ⟨false, 9223372036854775807, -19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_nonneg _ _ 8507059173023461590 rfl,
      Number.toRat_mk_nonneg _ _ 9223372036854775807 rfl]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.div_topGap_mid_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_five < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ -Number.top_plus_one := by
  refine ⟨⟨true, 8507059173023461590, maxExponent⟩, ⟨false, 9223372036854775807, -19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top_plus_one Number.top_plus_five
    rw [Number.toRat_mk_neg _ _ 8507059173023461590 rfl,
      Number.toRat_mk_nonneg _ _ 9223372036854775807 rfl]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.div_topGap_low_pos :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_one := by
  refine ⟨⟨false, 8507059173023461588, maxExponent⟩, ⟨false, 9223372036854775807, -19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_nonneg _ _ 8507059173023461588 rfl,
      Number.toRat_mk_nonneg _ _ 9223372036854775807 rfl]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

lemma Number.div_topGap_low_neg :
    ∃ x y : Number, x.isNormalized ∧ y.isNormalized ∧ x.mantissa_ ≠ 0 ∧ y.mantissa_ ≠ 0 ∧
      -Number.top_plus_one < x.toRat / y.toRat ∧ x.toRat / y.toRat < -Number.top := by
  refine ⟨⟨true, 8507059173023461588, maxExponent⟩, ⟨false, 9223372036854775807, -19⟩,
    ?_, ?_, by decide, by decide, ?_⟩
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · right; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Number.top Number.top_plus_one
    rw [Number.toRat_mk_neg _ _ 8507059173023461588 rfl,
      Number.toRat_mk_nonneg _ _ 9223372036854775807 rfl]
    have hp := ten_zpow_maxExponent_pos
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = p at hp ⊢
    norm_num
    constructor <;> linarith

end XRPL.Model.Protocol
