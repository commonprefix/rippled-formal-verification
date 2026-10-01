import Mathlib.Tactic

/-! # Round-trip arithmetic on an integral asset

`J = A₁·s/(S + s)` is the redeemed shares' worth on the updated total `A₁ = T + c + e`;
it sits `w·(I − c) + (1 − w)·e` above the charge `c`, `w = S/(S + s)`. The charge and the
payout are integers within `0.552` of their quotients `Y ≈ I` and `X ≈ J` (half a unit
from `9.3·10¹⁷` on), so a gain or loss of two units needs `c > 8·10¹⁷`, and beyond that
the excess over one unit is at most `η·(I + J)`, `η` the product's relative error. -/

namespace XRPL.Model.SingleAssetVault.RtT

lemma int_step (S s T I c e J : ℚ) (hS : 0 < S) (hs : 0 < s) (hTI : T * s = S * I)
    (hJ : J * (S + s) = (T + c + e) * s) :
    ∃ w : ℚ, 0 < w ∧ w < 1 ∧ J - c = w * (I - c) + (1 - w) * e := by
  have hSs : 0 < S + s := by linarith
  refine ⟨S / (S + s), div_pos hS hSs, (div_lt_one hSs).mpr (by linarith), ?_⟩
  have h1 : (J - c) * (S + s) = S * (I - c) + s * e := by linear_combination hJ + hTI
  have h2 : (S / (S + s) * (I - c) + (1 - S / (S + s)) * e) * (S + s) = S * (I - c) + s * e := by
    field_simp; ring
  exact mul_right_cancel₀ (ne_of_gt hSs) (h1.trans h2.symm)

lemma int_le_of_lt (z : ℚ) (n : ℤ) (hz : ∃ k : ℤ, z = k) (h : z < n + 1) : z ≤ n := by
  obtain ⟨k, rfl⟩ := hz
  have : k < n + 1 := by exact_mod_cast h
  exact_mod_cast (show k ≤ n by omega)

/-- A convex combination of two values is at most any common bound. -/
lemma comb_le (w x y B : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hx : x ≤ B) (hy : y ≤ B) :
    w * x + (1 - w) * y ≤ B := by
  have h1 : w * x ≤ w * B := mul_le_mul_of_nonneg_left hx hw0
  have h2 : (1 - w) * y ≤ (1 - w) * B := mul_le_mul_of_nonneg_left hy (by linarith)
  linarith

lemma comb_ge (w x y B : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hx : B ≤ x) (hy : B ≤ y) :
    B ≤ w * x + (1 - w) * y := by
  have h1 : w * B ≤ w * x := mul_le_mul_of_nonneg_left hx hw0
  have h2 : (1 - w) * B ≤ (1 - w) * y := mul_le_mul_of_nonneg_left hy (by linarith)
  linarith

/-- Below `8·10¹⁷` the excess stays under two units. -/
lemma int_small (I c J η a d : ℚ) (hη0 : 0 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hI0 : 0 ≤ I) (hc8 : c ≤ 8 * 10 ^ 17) (hIc : I - c ≤ I * η + 69 / 125)
    (hJ : J - c ≤ 1) (hJ' : J ≤ max I (c + 1)) (ha : a ≤ 69 / 125) (hd : d ≤ J * η) :
    a + d + (J - c) < 2 := by
  have h1 : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hI8 : I ≤ 8 * 10 ^ 17 + 1 := by linarith
  have hJ8 : J ≤ 8 * 10 ^ 17 + 1 := le_trans hJ' (max_le hI8 (by linarith))
  have hJ0 : 0 ≤ J ∨ J < 0 := le_or_gt 0 J
  have h2 : J * η ≤ (8 * 10 ^ 17 + 1) * (54211 / 10 ^ 23) := by
    rcases hJ0 with hJ0 | hJ0
    · calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
        _ ≤ (8 * 10 ^ 17 + 1) * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_right hJ8 (by norm_num)
    · have : J * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hJ0.le hη0
      linarith
  linarith

/-- Up to `10²⁰/121` the excess stays under two units once the quotients sit on the `0.1`
grid. -/
lemma int_tight (I c J η a d : ℚ) (hη0 : 0 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hI0 : 0 ≤ I) (hc8 : c ≤ 10 ^ 20 / 121) (hIc : I * (1 - η) ≤ c + 11 / 20)
    (hJ : J - c ≤ 1) (hJ' : J ≤ max I (c + 1)) (ha : a ≤ 11 / 20) (hd : d ≤ J * η) :
    a + d + (J - c) < 2 := by
  have h1 : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hI8 : I ≤ 10 ^ 20 / 121 + 1 := by nlinarith
  have hJ8 : J ≤ 10 ^ 20 / 121 + 1 := le_trans hJ' (max_le hI8 (by linarith))
  have h2 : J * η ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) := by
    rcases le_or_gt 0 J with hJ0 | hJ0
    · calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
        _ ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_right hJ8 (by norm_num)
    · have : J * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hJ0.le hη0
      have : (0 : ℚ) ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) := by norm_num
      linarith
  have h3 : (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23 : ℚ) < 9 / 20 := by norm_num
  linarith

/-- Up to `9.3·10¹⁷` the excess stays under three units. -/
lemma int_mid (I c J η a d : ℚ) (hη0 : 0 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hI0 : 0 ≤ I) (hI93 : I * (1 - η) ≤ 93 * 10 ^ 16 + 1) (hc93 : c ≤ 93 * 10 ^ 16 + 1)
    (hJ : J - c ≤ I * η + 1) (hJ' : J ≤ max I (c + 1)) (ha : a ≤ 69 / 125)
    (hd : d ≤ J * η) :
    a + d + (J - c) < 3 := by
  have h1 : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hIb : I ≤ 93 * 10 ^ 16 + 2 := by nlinarith
  have hJb : J ≤ 93 * 10 ^ 16 + 2 := le_trans hJ' (max_le hIb (by linarith))
  have hIη : I * η ≤ (93 * 10 ^ 16 + 2) * (54211 / 10 ^ 23) :=
    le_trans h1 (mul_le_mul_of_nonneg_right hIb (by norm_num))
  have h2 : J * η ≤ (93 * 10 ^ 16 + 2) * (54211 / 10 ^ 23) := by
    rcases le_or_gt 0 J with hJ0 | hJ0
    · calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
        _ ≤ (93 * 10 ^ 16 + 2) * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_right hJb (by norm_num)
    · have : J * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hJ0.le hη0
      linarith
  linarith

/-- From `9.3·10¹⁷` on the excess over one unit is at most `η·(I + J) ≤ c/(8·10¹⁷)`. -/
lemma int_big (I c J η : ℚ) (hη0 : 0 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hI0 : 0 ≤ I) (hc9 : 9 * 10 ^ 17 ≤ c) (hIc : I - c ≤ I * η + 1 / 2)
    (hJ : J ≤ max I (c + I * η + 1 / 2)) :
    I * η + J * η ≤ c * (121 / 10 ^ 20) := by
  have h1 : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hIb : I ≤ c * (1 + 2 / 10 ^ 18) + 1 := by nlinarith
  have hIη : I * η ≤ (c * (1 + 2 / 10 ^ 18) + 1) * (54211 / 10 ^ 23) :=
    le_trans h1 (mul_le_mul_of_nonneg_right hIb (by norm_num))
  have hJb : J ≤ c * (1 + 2 / 10 ^ 18) + 1 := by
    refine le_trans hJ (max_le hIb ?_)
    nlinarith
  have hJ0 : 0 ≤ J ∨ J < 0 := le_or_gt 0 J
  have h2 : J * η ≤ (c * (1 + 2 / 10 ^ 18) + 1) * (54211 / 10 ^ 23) := by
    rcases hJ0 with hJ0 | hJ0
    · calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
        _ ≤ _ := mul_le_mul_of_nonneg_right hJb (by norm_num)
    · have : J * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hJ0.le hη0
      have : (0 : ℚ) ≤ (c * (1 + 2 / 10 ^ 18) + 1) * (54211 / 10 ^ 23) := by positivity
      linarith
  nlinarith

lemma int_gap (x : ℚ) (hx : ∃ k : ℤ, x = k) (h : x < 2) : x ≤ 1 := by
  have := int_le_of_lt x 1 hx (by push_cast; linarith)
  exact_mod_cast this

lemma int_gap3 (x : ℚ) (hx : ∃ k : ℤ, x = k) (h : x < 3) : x ≤ 2 := by
  have := int_le_of_lt x 2 hx (by push_cast; linarith)
  exact_mod_cast this

lemma int_sub (a b : ℚ) (ha : ∃ k : ℤ, a = k) (hb : ∃ k : ℤ, b = k) : ∃ k : ℤ, a - b = k := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x - y, by push_cast; ring⟩

/-- `Iη ≥ 1/2` once the quotient is past `9.3·10¹⁷`. -/
lemma half_le_Iη (I Y η : ℚ) (hηlo : 5421 / 10 ^ 22 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hI0 : 0 ≤ I) (hY : Y - I ≤ I * η) (hY93 : 93 * 10 ^ 16 ≤ Y) : 1 / 2 ≤ I * η := by
  have h1 : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hI : 93 * 10 ^ 16 - 1 ≤ I := by nlinarith
  have := mul_le_mul hI hηlo (by norm_num) hI0
  nlinarith

set_option maxHeartbeats 2000000 in
-- the gain and the loss, each a three-way split on the charge's magnitude
lemma int_core (T S s I c q Y J X e η : ℚ)
    (hηlo : 5421 / 10 ^ 22 ≤ η) (hη : η ≤ 54211 / 10 ^ 23)
    (hS : 0 < S) (hs : 0 < s) (hTI : T * s = S * I)
    (hJ : J * (S + s) = (T + c + e) * s)
    (hY : |Y - I| ≤ I * η) (hI0 : 0 ≤ I) (hc0 : 0 ≤ c)
    (hc1 : Y < 9223372036854775807 → |c - Y| ≤ 69 / 125)
    (hc2 : 925 * 10 ^ 15 ≤ Y → Y < 9223372036854775807 → |c - Y| ≤ 1 / 2)
    (hc3 : 9223372036854775807 ≤ Y → c = 9223372036854775807)
    (hc4 : 93 * 10 ^ 15 ≤ Y → Y < 922 * 10 ^ 15 → |c - Y| ≤ 11 / 20)
    (hX : |X - J| ≤ J * η) (hJ0 : 0 ≤ J)
    (hq1 : X < 9223372036854775807 → |q - X| ≤ 69 / 125)
    (hq2 : 925 * 10 ^ 15 ≤ X → X < 9223372036854775807 → |q - X| ≤ 1 / 2)
    (hq3 : 9223372036854775807 ≤ X → q = 9223372036854775807)
    (hq4 : 93 * 10 ^ 15 ≤ X → X < 922 * 10 ^ 15 → |q - X| ≤ 11 / 20)
    (hcM : c ≤ 9223372036854775807) (hqM : q ≤ 9223372036854775807)
    (heu : e ≤ 1) (hel : -3 ≤ e) (hel1 : -1 ≤ e ∨ 9223372036854775807 - 10 ^ 18 < c)
    (hcz : ∃ z : ℤ, c = z) (hqz : ∃ z : ℤ, q = z) :
    q - c ≤ c * (121 / 10 ^ 20) + 1 ∧ c - q ≤ c * (121 / 10 ^ 20) + 1 := by
  obtain ⟨w, hw0, hw1, hJc⟩ := int_step S s T I c e J hS hs hTI hJ
  have hη0 : 0 ≤ η := le_trans (by norm_num) hηlo
  have hYb := abs_le.mp hY
  have hXb := abs_le.mp hX
  have hκ : (0 : ℚ) ≤ c * (121 / 10 ^ 20) := by positivity
  have hIη : I * η ≤ I * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hI0
  have hqc := int_sub q c hqz hcz
  have hcq := int_sub c q hcz hqz
  have hJmax : ∀ B, I ≤ B → c + e ≤ B → J ≤ B := fun B h1 h2 => by
    have := comb_le w I (c + e) B hw0.le hw1.le h1 h2; linarith
  have hJmin : ∀ B, B ≤ I → B ≤ c + e → B ≤ J := fun B h1 h2 => by
    have := comb_ge w I (c + e) B hw0.le hw1.le h1 h2; linarith
  constructor
  · ------------------------------------------------------------------ gain
    rcases le_or_gt 9223372036854775807 Y with hYM | hYM
    · have := hc3 hYM; linarith
    have hcY := abs_le.mp (hc1 hYM)
    have hqX : q - X ≤ 69 / 125 := by
      rcases le_or_gt 9223372036854775807 X with hXM | hXM
      · have := hq3 hXM; linarith
      · exact (abs_le.mp (hq1 hXM)).2
    have hIc : I - c ≤ I * η + 69 / 125 := by linarith
    have hJc' : ∀ B, I - c ≤ B → e ≤ B → J - c ≤ B := fun B h1 h2 => by
      have := comb_le w (I - c) e B hw0.le hw1.le h1 h2; linarith
    rcases le_or_gt c (8 * 10 ^ 17) with hc8 | hc8
    · have h := int_small I c J η (q - X) (X - J) hη0 hη hI0 hc8 hIc
        (hJc' 1 (by nlinarith) heu) (hJmax _ (le_max_left _ _) (by
          have : c + e ≤ c + 1 := by linarith
          exact le_trans this (le_max_right _ _))) hqX (by linarith)
      have := int_gap (q - c) hqc (by linarith)
      linarith
    rcases le_or_gt c (10 ^ 20 / 121) with hc9 | hc9
    · -- the quotients sit on the `0.1` grid
      have hcY4 := abs_le.mp (hc4 (by linarith) (by linarith))
      have hI1 : I * (1 - η) ≤ c + 11 / 20 := by linarith
      have hIb : I ≤ 10 ^ 20 / 121 + 1 := by nlinarith
      have hIη' : I * η ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) :=
        le_trans hIη (mul_le_mul_of_nonneg_right hIb (by norm_num))
      have hIη2 : I * η ≤ 9 / 20 := le_trans hIη' (by norm_num)
      have hJ1 := hJc' 1 (by linarith) heu
      have hJm : J ≤ max I (c + 1) := hJmax _ (le_max_left _ _) (le_trans (by linarith) (le_max_right _ _))
      by_cases hX93 : 93 * 10 ^ 15 ≤ X
      · have hJb : J ≤ 10 ^ 20 / 121 + 1 := le_trans hJm (max_le hIb (by linarith))
        have hXb' : X < 922 * 10 ^ 15 := by
          have : J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
          nlinarith
        have hqX4 := (abs_le.mp (hq4 hX93 hXb')).2
        have h := int_tight I c J η (q - X) (X - J) hη0 hη hI0 hc9 hI1 hJ1 hJm hqX4 (by linarith)
        have := int_gap (q - c) hqc (by linarith)
        linarith
      · have := int_gap (q - c) hqc (by push Not at hX93; linarith)
        linarith
    rcases lt_or_ge Y (93 * 10 ^ 16) with hY93 | hY93
    · have h := int_mid I c J η (q - X) (X - J) hη0 hη hI0 (by linarith) (by linarith)
        (hJc' _ (by linarith) (by nlinarith)) (hJmax _ (le_max_left _ _) (by
          have : c + e ≤ c + 1 := by linarith
          exact le_trans this (le_max_right _ _))) hqX (by linarith)
      have := int_gap3 (q - c) hqc (by linarith)
      have : (1 : ℚ) ≤ c * (121 / 10 ^ 20) := by
        linarith
      linarith
    · have hcY2 := abs_le.mp (hc2 (by linarith) hYM)
      by_contra hgt
      push Not at hgt
      have hq2c : 2 ≤ q - c := by
        by_contra hlt; push Not at hlt
        have := int_gap (q - c) hqc hlt; linarith
      have hqX2 : q - X ≤ 1 / 2 := by
        rcases le_or_gt 9223372036854775807 X with hXM | hXM
        · have := hq3 hXM; linarith
        · exact (abs_le.mp (hq2 (by linarith) hXM)).2
      have hIc2 : I - c ≤ I * η + 1 / 2 := by linarith
      have hh := half_le_Iη I Y η hηlo hη hI0 hYb.2 hY93
      have hJ1 := hJc' (I * η + 1 / 2) hIc2 (by linarith)
      have hfin := int_big I c J η hη0 hη hI0 (by linarith) hIc2
        (hJmax _ (le_max_left _ _) (by
          have : c + e ≤ c + I * η + 1 / 2 := by linarith
          exact le_trans this (le_max_right _ _)))
      linarith
  · ------------------------------------------------------------------ loss
    rcases le_or_gt 9223372036854775807 X with hXM | hXM
    · have := hq3 hXM; linarith
    have hqX := abs_le.mp (hq1 hXM)
    have hcY : c - Y ≤ 69 / 125 := by
      rcases le_or_gt 9223372036854775807 Y with hYM | hYM
      · have := hc3 hYM; linarith
      · exact (abs_le.mp (hc1 hYM)).2
    have hcI : c - I ≤ I * η + 69 / 125 := by linarith
    have hJc' : ∀ B, c - I ≤ B → -e ≤ B → c - J ≤ B := fun B h1 h2 => by
      have := comb_le w (c - I) (-e) B hw0.le hw1.le h1 h2; linarith
    have hIlo : Y - 69 / 125 - I * η ≤ I := by linarith
    have hYc : Y < 9223372036854775807 → Y ≤ c + 69 / 125 := fun h => by
      have := (abs_le.mp (hc1 h)).1; linarith
    rcases le_or_gt c (8 * 10 ^ 17) with hc8 | hc8
    · have he1 : -1 ≤ e := hel1.resolve_right (by push Not; linarith)
      have hYM : Y < 9223372036854775807 := by
        by_contra h; push Not at h; have := hc3 h; linarith
      have hIY : I * (1 - η) ≤ 8 * 10 ^ 17 + 69 / 125 := by have := hYc hYM; linarith
      have hI8 : I ≤ 8 * 10 ^ 17 + 1 := by nlinarith
      have hIη' : I * η ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_right hI8 (show (0 : ℚ) ≤ 54211 / 10 ^ 23 by norm_num)
        linarith
      have hcJ := hJc' 1 (by linarith) (by linarith)
      have hJb : J ≤ 8 * 10 ^ 17 + 1 := hJmax _ hI8 (by linarith)
      have hJη : J * η ≤ (8 * 10 ^ 17 + 1) * (54211 / 10 ^ 23) := by
        calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
          _ ≤ _ := mul_le_mul_of_nonneg_right hJb (by norm_num)
      have := int_gap (c - q) hcq (by norm_num at hJη ⊢; linarith)
      linarith
    rcases le_or_gt c (10 ^ 20 / 121) with hc9 | hc9
    · have he1 : -1 ≤ e := hel1.resolve_right (by push Not; linarith)
      have hYM : Y < 9223372036854775807 := by
        by_contra h; push Not at h; have := hc3 h; linarith
      have hYl : 93 * 10 ^ 15 ≤ Y := by have := (abs_le.mp (hc1 hYM)).2; linarith
      have hYu : Y < 922 * 10 ^ 15 := by have := hYc hYM; linarith
      have hcY4 := abs_le.mp (hc4 hYl hYu)
      have hI1 : I * (1 - η) ≤ c + 11 / 20 := by linarith
      have hIb : I ≤ 10 ^ 20 / 121 + 1 := by nlinarith
      have hIη' : I * η ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) :=
        le_trans hIη (mul_le_mul_of_nonneg_right hIb (by norm_num))
      have hIη2 : I * η ≤ 9 / 20 := le_trans hIη' (by norm_num)
      have hcJ := hJc' 1 (by linarith) (by linarith)
      have hJb : J ≤ 10 ^ 20 / 121 + 1 := hJmax _ hIb (by linarith)
      have hJlo : 8 * 10 ^ 17 - 2 ≤ J := hJmin _ (by nlinarith) (by linarith)
      have hJη : J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
      have hX93 : 93 * 10 ^ 15 ≤ X := by nlinarith
      have hXb' : X < 922 * 10 ^ 15 := by nlinarith
      have hqX4 := (abs_le.mp (hq4 hX93 hXb')).1
      have h2 : J * (54211 / 10 ^ 23) ≤ (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23) :=
        mul_le_mul_of_nonneg_right hJb (by norm_num)
      have h3 : (10 ^ 20 / 121 + 1) * (54211 / 10 ^ 23 : ℚ) < 9 / 20 := by norm_num
      have := int_gap (c - q) hcq (by linarith)
      linarith
    have hYM : Y < 9223372036854775807 ∨ 9223372036854775807 ≤ Y := lt_or_ge _ _
    rcases lt_or_ge Y (93 * 10 ^ 16) with hY93 | hY93
    · have hYM' : Y < 9223372036854775807 := by linarith
      have hcb := abs_le.mp (hc1 hYM')
      have he1 : -1 ≤ e := hel1.resolve_right (by push Not; linarith)
      have hIb : I * (1 - η) ≤ 93 * 10 ^ 16 + 1 := by linarith
      have hIb' : I ≤ 93 * 10 ^ 16 + 2 := by nlinarith
      have hIη' : I * η ≤ (93 * 10 ^ 16 + 2) * (54211 / 10 ^ 23) :=
        le_trans hIη (mul_le_mul_of_nonneg_right hIb' (by norm_num))
      have hcJ := hJc' (I * η + 1) (by linarith) (by linarith)
      have hJb : J ≤ 93 * 10 ^ 16 + 2 := hJmax _ hIb' (by linarith)
      have hJη : J * η ≤ (93 * 10 ^ 16 + 2) * (54211 / 10 ^ 23) := by
        calc J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
          _ ≤ _ := mul_le_mul_of_nonneg_right hJb (by norm_num)
      have := int_gap3 (c - q) hcq (by linarith)
      have : (1 : ℚ) ≤ c * (121 / 10 ^ 20) := by
        linarith
      linarith
    · rcases le_or_gt 9223372036854775807 Y with hYM | hYM
      · -- the charge is `maxRep`, so the payout's quotient is within ten units of it
        have hcM' := hc3 hYM
        have hIM : 9223372036854775807 - 51 / 10 ≤ I := by
          have : Y ≤ I + I * (54211 / 10 ^ 23) := by linarith
          nlinarith
        have hJM : 9223372036854775807 - 51 / 10 ≤ J := hJmin _ hIM (by linarith)
        have hJup : J ≤ 9223372036854775807 + 6 := by
          by_contra h; push Not at h
          have : J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
          nlinarith
        have hXM' : 9223372036854775807 - 1012 / 100 ≤ X := by
          have h1 : J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
          have h2 : J * (54211 / 10 ^ 23) ≤ (9223372036854775807 + 6) * (54211 / 10 ^ 23) :=
            mul_le_mul_of_nonneg_right hJup (by norm_num)
          have h3 : (9223372036854775807 + 6) * (54211 / 10 ^ 23 : ℚ) ≤ 501 / 100 := by norm_num
          linarith
        have : (11 : ℚ) ≤ c * (121 / 10 ^ 20) := by
          linarith
        linarith
      by_contra hgt
      push Not at hgt
      have hq2c : 2 ≤ c - q := by
        by_contra hlt; push Not at hlt
        have := int_gap (c - q) hcq hlt; linarith
      have hcY2 := abs_le.mp (hc2 (by linarith) hYM)
      have hcl : 93 * 10 ^ 16 - 1 ≤ c := by linarith
      have hh := half_le_Iη I Y η hηlo hη hI0 hYb.2 hY93
      have hI93 : 93 * 10 ^ 16 - 1 ≤ I := by nlinarith
      have hJ9 : 93 * 10 ^ 16 - 4 ≤ J := hJmin _ (by linarith) (by linarith)
      have hX925 : 925 * 10 ^ 15 ≤ X := by
        have : J * η ≤ J * (54211 / 10 ^ 23) := mul_le_mul_of_nonneg_left hη hJ0
        nlinarith
      have hqX2' := (abs_le.mp (hq2 hX925 hXM)).1
      have hqX2 : X - q ≤ 1 / 2 := by linarith
      have hcI2 : c - I ≤ I * η + 1 / 2 := by linarith
      have hIc2 : I - c ≤ I * η + 1 / 2 := by linarith
      have hme : -e ≤ I * η + 1 / 2 := by
        rcases hel1 with h | h
        · linarith
        · have hIbig : 9223372036854775807 - 10 ^ 18 - 5 ≤ I := by nlinarith
          have := mul_le_mul hIbig hηlo (by norm_num) hI0
          have : (3 : ℚ) ≤ (9223372036854775807 - 10 ^ 18 - 5) * (5421 / 10 ^ 22) := by norm_num
          linarith
      have hJ1 := hJc' (I * η + 1 / 2) hcI2 hme
      have hc9 : (9 * 10 ^ 17 : ℚ) ≤ c := by linarith
      have hce : c + e ≤ max I (c + I * η + 1 / 2) :=
        le_trans (show c + e ≤ c + I * η + 1 / 2 by linarith) (le_max_right _ _)
      have hJm : J ≤ max I (c + I * η + 1 / 2) := hJmax _ (le_max_left _ _) hce
      have hfin := int_big I c J η hη0 hη hI0 hc9 hIc2 hJm
      linarith

end XRPL.Model.SingleAssetVault.RtT
