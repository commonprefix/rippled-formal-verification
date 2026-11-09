import XRPL.Properties.Lending.Loan.Common.SetMonotone
import XRPL.Properties.Lending.Loan.Common.Grid
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # The values a new loan computes

A rounding that never jumps over a point of the `10^s` grid is `GridFaithful`. Every step of the loan
value computation is, so the stored values sit on the LoanScale grid next to the exact ones. -/

namespace XRPL.Model.Protocol

/-- `y` rounds `x` without jumping over a nonnegative point of the `10^s` grid: a grid point at or below
`x` stays at or below `y`, a grid point at or above `x` stays at or above `y`. -/
structure GridFaithful (s : ℤ) (x y : ℚ) : Prop where
  lower : ∀ z : ℕ, (z : ℚ) * 10 ^ s ≤ x → (z : ℚ) * 10 ^ s ≤ y
  upper : ∀ z : ℕ, x ≤ (z : ℚ) * 10 ^ s → y ≤ (z : ℚ) * 10 ^ s

/-- A value is faithful to itself. -/
lemma GridFaithful.refl (s : ℤ) (x : ℚ) : GridFaithful s x x :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- Two faithful roundings in a row are faithful. -/
lemma GridFaithful.trans {s : ℤ} {x y w : ℚ} (h₁ : GridFaithful s x y) (h₂ : GridFaithful s y w) :
    GridFaithful s x w :=
  ⟨fun z h => h₂.lower z (h₁.lower z h), fun z h => h₂.upper z (h₁.upper z h)⟩

/-- A point of the `10^s` grid is a point of every finer grid `10^s'`. -/
lemma grid_point_fine (z : ℕ) (s s' : ℤ) (hle : s' ≤ s) :
    (z : ℚ) * 10 ^ s = ((z * 10 ^ (s - s').toNat : ℕ) : ℚ) * 10 ^ s' := by
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  congr 2
  omega

/-- A rounding faithful on a fine grid is faithful on every coarser grid. -/
lemma GridFaithful.coarsen {s' s : ℤ} {x y : ℚ} (h : GridFaithful s' x y) (hle : s' ≤ s) :
    GridFaithful s x y :=
  ⟨fun z hz => by rw [grid_point_fine z s s' hle] at hz ⊢; exact h.lower _ hz,
   fun z hz => by rw [grid_point_fine z s s' hle] at hz ⊢; exact h.upper _ hz⟩

/-- A value between the floor and the ceiling on the grid rounds faithfully. -/
private lemma GridFaithful.of_floor_ceil {s : ℤ} {x y : ℚ}
    (hlo : (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ y) (hhi : y ≤ (⌈x / 10 ^ s⌉ : ℚ) * 10 ^ s) :
    GridFaithful s x y := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  constructor
  · intro z hz
    have : ((z : ℤ) : ℚ) ≤ ⌊x / 10 ^ s⌋ := by
      have h1 : (z : ℤ) ≤ ⌊x / 10 ^ s⌋ := Int.le_floor.mpr (by rw [le_div_iff₀ hp]; exact_mod_cast hz)
      exact_mod_cast h1
    calc (z : ℚ) * 10 ^ s ≤ (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hp.le
      _ ≤ y := hlo
  · intro z hz
    have : (⌈x / 10 ^ s⌉ : ℚ) ≤ ((z : ℤ) : ℚ) := by
      have h1 : ⌈x / 10 ^ s⌉ ≤ (z : ℤ) := Int.ceil_le.mpr (by rw [div_le_iff₀ hp]; exact_mod_cast hz)
      exact_mod_cast h1
    calc y ≤ (⌈x / 10 ^ s⌉ : ℚ) * 10 ^ s := hhi
      _ ≤ (z : ℚ) * 10 ^ s := by exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hp.le

/-- On the grid and faithful to `x`: at least the floor of `x`. -/
lemma GridFaithful.floor_le {s : ℤ} {x y : ℚ} (h : GridFaithful s x y) (hx : 0 ≤ x) :
    (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ y := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hf0 : 0 ≤ ⌊x / 10 ^ s⌋ := Int.floor_nonneg.mpr (div_nonneg hx hp.le)
  have := h.lower ⌊x / 10 ^ s⌋.toNat (by
    rw [show ((⌊x / 10 ^ s⌋.toNat : ℕ) : ℚ) = (⌊x / 10 ^ s⌋ : ℚ) by exact_mod_cast Int.toNat_of_nonneg hf0]
    have := Int.floor_le (x / 10 ^ s)
    rwa [le_div_iff₀ hp] at this)
  rwa [show ((⌊x / 10 ^ s⌋.toNat : ℕ) : ℚ) = (⌊x / 10 ^ s⌋ : ℚ) by
    exact_mod_cast Int.toNat_of_nonneg hf0] at this

/-- Faithful to `x`: at most the ceiling of `x`. -/
lemma GridFaithful.le_ceil {s : ℤ} {x y : ℚ} (h : GridFaithful s x y) (hx : 0 ≤ x) :
    y ≤ (⌈x / 10 ^ s⌉ : ℚ) * 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hc0 : 0 ≤ ⌈x / 10 ^ s⌉ := Int.ceil_nonneg (div_nonneg hx hp.le)
  have := h.upper ⌈x / 10 ^ s⌉.toNat (by
    rw [show ((⌈x / 10 ^ s⌉.toNat : ℕ) : ℚ) = (⌈x / 10 ^ s⌉ : ℚ) by exact_mod_cast Int.toNat_of_nonneg hc0]
    have := Int.le_ceil (x / 10 ^ s)
    rwa [div_le_iff₀ hp] at this)
  rwa [show ((⌈x / 10 ^ s⌉.toNat : ℕ) : ℚ) = (⌈x / 10 ^ s⌉ : ℚ) by
    exact_mod_cast Int.toNat_of_nonneg hc0] at this

/-- Rounding down onto a grid never raises a value. -/
private lemma floor_grid_le (x : ℚ) (s : ℤ) : (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ x := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have h := Int.floor_le (x / 10 ^ s)
  rwa [le_div_iff₀ hp] at h

/-- A grid point at or above `x` and at most the ceiling of `x` is that ceiling. -/
private lemma ceil_grid_eq_of_grid {s : ℤ} {x : ℚ} (k : ℕ) (hge : x ≤ (k : ℚ) * 10 ^ s)
    (hle : (k : ℚ) * 10 ^ s ≤ (⌈x / 10 ^ s⌉ : ℚ) * 10 ^ s) :
    (k : ℚ) * 10 ^ s = (⌈x / 10 ^ s⌉ : ℚ) * 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have h1 : ⌈x / 10 ^ s⌉ ≤ (k : ℤ) := Int.ceil_le.mpr (by rw [div_le_iff₀ hp]; exact_mod_cast hge)
  have h1' : (⌈x / 10 ^ s⌉ : ℚ) ≤ (k : ℚ) := by exact_mod_cast h1
  exact le_antisymm hle (mul_le_mul_of_nonneg_right h1' hp.le)

/-- A `Number` rounding of a nonnegative value below `2^63 - 1` grid units is faithful on the grid. -/
private lemma Number.RoundsToRepresentable.gridFaithful {r : Number} {t : ℚ} {mode : rounding_mode}
    (hR : r.RoundsToRepresentable t mode)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (s : ℤ)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (ht : t ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) * 10 ^ s) :
    GridFaithful s t r.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hrep : ∀ z : ℕ, z < 2 ^ 63 → ∃ w : Number, w.isNormalized ∧ w.toRat = (z : ℚ) * 10 ^ s := by
    intro z hz
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (z : ℤ) s ⟨by omega, by omega⟩ hs
    exact ⟨w, hw, by rw [hwv]; push_cast; rfl⟩
  constructor
  · intro z hz
    have hzlt : z < 2 ^ 63 := by
      by_contra hc
      push Not at hc
      have h1 : ((2 ^ 63 - 1 : ℕ) : ℚ) < (z : ℚ) := by
        have : 2 ^ 63 - 1 < z := by omega
        exact_mod_cast this
      have := mul_lt_mul_of_pos_right h1 hp
      linarith
    obtain ⟨w, hw, hwv⟩ := hrep z hzlt
    rw [← hwv] at hz ⊢
    exact hR.ge_of_le hmode w hw hz
  · intro z hz
    by_cases hzlt : z < 2 ^ 63
    · obtain ⟨w, hw, hwv⟩ := hrep z hzlt
      rw [← hwv] at hz ⊢
      exact hR.le_of_ge hmode w hw hz
    · obtain ⟨w, hw, hwv⟩ := hrep (2 ^ 63 - 1) (by norm_num)
      have h1 : r.toRat ≤ w.toRat := hR.le_of_ge hmode w hw (by rw [hwv]; exact ht)
      rw [hwv] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hp.le)
      have : 2 ^ 63 - 1 ≤ z := by omega
      exact_mod_cast this

/-! ## The `STAmount` steps -/

open private STAmount.repack_exact from XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid

/-- The floor of a quotient of naturals is their natural quotient. -/
private lemma floor_natCast_div (M d : ℕ) : ⌊(M : ℚ) / d⌋ = ((M / d : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff, Int.cast_natCast]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hq : (M : ℚ) = d * ((M / d : ℕ) : ℚ) + ((M % d : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod M d).symm
  have hr : ((M % d : ℕ) : ℚ) < d := by exact_mod_cast Nat.mod_lt M hd
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℚ) ≤ ((M % d : ℕ) : ℚ) := by positivity
  constructor
  · rw [le_div_iff₀ hdq]; nlinarith
  · rw [div_lt_iff₀ hdq]; nlinarith

/-- A grid value within half a step of `t` lies between the floor and the ceiling of `t`. -/
private lemma floor_ceil_of_within_half {g : ℤ} {t y : ℚ} (k : ℤ) (hy : y = (k : ℚ) * 10 ^ g)
    (hd : |y - t| ≤ (1 / 2 : ℚ) * 10 ^ g) :
    (⌊t / 10 ^ g⌋ : ℚ) * 10 ^ g ≤ y ∧ y ≤ (⌈t / 10 ^ g⌉ : ℚ) * 10 ^ g := by
  have hp : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  set u := t / 10 ^ g with hu
  have ht : t = u * 10 ^ g := by rw [hu]; field_simp
  have hku : |(k : ℚ) - u| ≤ 1 / 2 := by
    have h1 : |y - t| = |(k : ℚ) - u| * 10 ^ g := by
      rw [hy, ht, ← sub_mul, abs_mul, abs_of_pos hp]
    rw [h1] at hd
    exact le_of_mul_le_mul_right (by linarith) hp
  rw [abs_le] at hku
  constructor
  · rw [hy]
    refine mul_le_mul_of_nonneg_right ?_ hp.le
    have : ⌊u⌋ ≤ k := by
      by_contra hc
      push Not at hc
      have h2 : (k : ℚ) ≤ (⌊u⌋ : ℚ) - 1 := by exact_mod_cast (by omega : k ≤ ⌊u⌋ - 1)
      linarith [Int.floor_le u]
    exact_mod_cast this
  · rw [hy]
    refine mul_le_mul_of_nonneg_right ?_ hp.le
    have : k ≤ ⌈u⌉ := by
      by_contra hc
      push Not at hc
      have h2 : (⌈u⌉ : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast (by omega : ⌈u⌉ + 1 ≤ k)
      linarith [Int.le_ceil u]
    exact_mod_cast this

/-- A nonzero canonical IOU amount is a whole number of steps of every grid at or below its exponent. -/
private lemma STAmount.toRat_grid_of_le (a : STAmount) (h0 : 0 ≤ a.toRat) (g : ℤ) (hg : g ≤ a.exponent) :
    a.toRat = ((a.mValue.toNat * 10 ^ (a.exponent - g).toNat : ℕ) : ℚ) * 10 ^ g := by
  have habs := STAmount.abs_toRat a
  rw [abs_of_nonneg h0] at habs
  rw [habs]
  exact grid_point_fine a.mValue.toNat a.mOffset g hg

/-- A downward fractional `ofNumber` rounds down onto the 16-digit grid of its source. A nonzero
result is the floor of a nonnegative source at scale `10 ^ (exponent + 3)`, at that exponent. -/
private lemma STAmount.ofNumber_iou_downward_floor_value (n : Number) (result : STAmount) (hn : n.isNormalized)
    (hn0 : n.mantissa_ ≠ 0) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n .downward = .ok result) (hresult : result.mValue ≠ 0) :
    result.toRat = (⌊n.toRat / 10 ^ (n.exponent_ + 3)⌋ : ℚ) * 10 ^ (n.exponent_ + 3) ∧
      result.exponent = n.exponent_ + 3 := by
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  have hneg := Number.negative_false_of_nonneg n hn h0
  have hexp := STAmount.ofNumber_iou_success_exp_range n .downward result hb.1 hb.2 hemin hok hresult
  obtain ⟨mant, exp, hnr, hval, hrexp, -⟩ := STAmount.ofNumber_iou_snap_pos .fractional n .downward result
    rfl hneg hb.1 hb.2 hemin hexp hok hresult
  obtain ⟨hfloor, hE⟩ := normalizeToRange_16_floor_pos n mant exp .downward (Or.inl rfl) hneg hb.1 hb.2
    (by omega) hexp hnr
  have hnv : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := Number.toRat_of_nonneg n hneg
  have hdiv : n.toRat / 10 ^ (n.exponent_ + 3) = ((n.mantissa_.toNat : ℕ) : ℚ) / ((1000 : ℕ) : ℚ) := by
    rw [hnv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    field_simp
    norm_num
  refine ⟨?_, by rw [hrexp, hE]⟩
  rw [hval, hfloor, hdiv, floor_natCast_div, Int.cast_natCast]

/-- The `ofNumber` step is faithful. A nonzero fractional result of a nonnegative source is canonical,
at an exponent at least three above the source, and never jumps over a point of that finer grid. -/
lemma STAmount.ofNumber_frac_stage (x : Number) (mode : rounding_mode) (st : STAmount)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hok : STAmount.ofNumber .fractional x mode = .ok st) (hst : st.mValue ≠ 0) :
    st.IOUCanonical ∧ x.exponent_ + 3 ≤ st.exponent ∧ GridFaithful (x.exponent_ + 3) x.toRat st.toRat ∧
      (mode = .upward → x.toRat ≤ st.toRat) ∧ (mode = .downward → st.toRat ≤ x.toRat) := by
  have hm0 : x.mantissa_ ≠ 0 := by
    intro h
    rw [Number.eq_zero_of_mantissa_zero x hx h, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hok
    exact hst (by rw [← hok])
  have hb := mantissaBounds_nat_of (hx.mantissaBounds hm0)
  have hemin := Number.exponent_ge_min x hx hm0
  have hneg := Number.negative_false_of_nonneg x hx h0
  have hexp := STAmount.ofNumber_iou_success_exp_range x mode st hb.1 hb.2 hemin hok hst
  have hty := STAmount.ofNumber_mNumericType _ _ _ st hok
  have hc : st.IOUCanonical :=
    (STAmount.ofNumber_exactCanonical .fractional x mode st hx h0 hok hst).iouCanonical
      (by unfold STAmount.integral; rw [hty]; rfl)
  have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hok
  have hp : (0 : ℚ) < 10 ^ (x.exponent_ + 3) := zpow_pos (by norm_num) _
  rcases hmode with rfl | rfl | rfl
  · obtain ⟨hhalf, hle⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional x st rfl hb.1 hb.2 hemin hexp hok hst
    have hgrid := STAmount.toRat_grid_of_le st hst0 (x.exponent_ + 3) hle
    obtain ⟨hlo, hhi⟩ :=
      floor_ceil_of_within_half ((st.mValue.toNat * 10 ^ (st.exponent - (x.exponent_ + 3)).toNat : ℕ) : ℤ)
        (by rw [hgrid, Int.cast_natCast]) hhalf
    exact ⟨hc, hle, GridFaithful.of_floor_ceil hlo hhi, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · have hR := STAmount.ofNumber_iou_upward_ceil x st hx hm0 h0 hok hst
    have hR' : st.toRat = (⌈x.toRat / 10 ^ (x.exponent_ + 3)⌉ : ℚ) * 10 ^ (x.exponent_ + 3) := hR
    obtain ⟨mant, exp, hnr, -, hrexp, -⟩ := STAmount.ofNumber_iou_snap_pos .fractional x .upward st
      rfl hneg hb.1 hb.2 hemin hexp hok hst
    obtain ⟨-, hE⟩ := normalizeToRange_16_ceil_pos x mant exp hneg hb.1 hb.2 (by omega) hexp hnr
    refine ⟨hc, by rw [hrexp]; exact hE, GridFaithful.of_floor_ceil ?_ (le_of_eq hR'), fun _ => ?_,
      fun h => absurd h (by decide)⟩
    · rw [hR']
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le_ceil _) hp.le
    · rw [hR']; exact le_ceil_grid _ _
  · obtain ⟨hR, hE⟩ := STAmount.ofNumber_iou_downward_floor_value x st hx hm0 h0 hok hst
    refine ⟨hc, le_of_eq hE.symm, GridFaithful.of_floor_ceil (le_of_eq hR.symm) ?_, fun h => absurd h (by decide),
      fun _ => by rw [hR]; exact floor_grid_le _ _⟩
    rw [hR]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le_ceil _) hp.le

/-- A fractional `ofNumber` that gives zero came from zero or from a source below `10^-81`. -/
private lemma STAmount.ofNumber_frac_zero_small (x : Number) (mode : rounding_mode) (st : STAmount)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hok : STAmount.ofNumber .fractional x mode = .ok st) (hst : st.mValue = 0) :
    x.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
  by_cases hm0 : x.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero x hm0]; positivity
  have hb := mantissaBounds_nat_of (hx.mantissaBounds hm0)
  have hexp : x.exponent_ < -99 := by
    by_contra hc
    push Not at hc
    exact STAmount.ofNumber_iou_ne_zero_of_exponent x mode st hx hm0 hc hok hst
  rw [Number.toRat_of_nonneg x (Number.negative_false_of_nonneg x hx h0)]
  have hm : (x.mantissa_.toNat : ℚ) < 10 ^ (19 : ℕ) := by exact_mod_cast hb.2
  have hpe : (10 : ℚ) ^ x.exponent_ ≤ 10 ^ (-100 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  calc (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ < 10 ^ (19 : ℕ) * 10 ^ x.exponent_ :=
        mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
    _ ≤ 10 ^ (19 : ℕ) * 10 ^ (-100 : ℤ) := mul_le_mul_of_nonneg_left hpe (by positivity)
    _ = (10 : ℚ) ^ (-81 : ℤ) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num

/-- Zero is faithful to a nonnegative value below one step of the grid. -/
private lemma GridFaithful.zero_of_lt {s : ℤ} {x : ℚ} (h0 : 0 ≤ x) (hlt : x < 10 ^ s) : GridFaithful s x 0 := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  constructor
  · intro z hz
    have hz0 : z = 0 := by
      by_contra hc
      have : (1 : ℚ) ≤ z := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
      nlinarith
    rw [hz0]; simp
  · intro z _
    positivity

/-- Rounding a positive IOU amount onto a coarser grid `10^s`, with `s` at least `-81`, gives a whole
number `k` of grid units, zero or a canonical amount, with `k` the floor or ceiling the mode asks for. -/
lemma STAmount.roundToExponent_nonneg_units (value result : STAmount) (s : ℤ) (mode : rounding_mode)
    (hc : value.IOUCanonical) (hneg : value.mIsNegative = false) (hev : value.mOffset < s)
    (hs : -81 ≤ s) (hs_hi : s ≤ 80) (hok : STAmount.roundToExponent value s mode = .ok result) :
    ∃ k : ℕ, result.toRat = (k : ℚ) * 10 ^ s ∧ result.mNumericType = .fractional ∧
      (result.mValue = 0 ∨ result.IOUCanonical) ∧
      (mode = .to_nearest → (k : ℤ) = ⌊value.toRat / 10 ^ s⌋ ∨ (k : ℤ) = ⌈value.toRat / 10 ^ s⌉) ∧
      (mode = .downward → (k : ℤ) = ⌊value.toRat / 10 ^ s⌋) ∧
      (mode = .upward → (k : ℤ) = ⌈value.toRat / 10 ^ s⌉) := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0
    have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo
    omega
  have hval_nn : 0 ≤ value.toRat := by rw [STAmount.toRat_of_nonneg value hneg]; positivity
  have h_abs : |value.toRat| = value.toRat := abs_of_nonneg hval_nn
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true),
      if_neg (by
        show ¬ value.isZero = true
        unfold STAmount.isZero
        rw [beq_eq_false_iff_ne.mpr h_mv_ne]
        exact Bool.false_ne_true),
      if_neg (show ¬ value.exponent ≥ s from not_le.mpr hev)] at hok
  rw [show STAmount.checked value.mNumericType kMinValue s value.negative mode
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ from by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative mode (by omega) hs_hi] at hok
  simp only [] at hok
  set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
  obtain ⟨sum, h_sum_ok, h_sub_ok⟩ : ∃ sum,
      STAmount.operator_add value refA mode = .ok sum ∧
      STAmount.operator_sub sum refA mode = .ok result := by
    match h1 : STAmount.operator_add value refA mode with
    | .error e => rw [h1] at hok; exact absurd hok (by intro h; cases h)
    | .ok sum =>
      rw [h1] at hok
      exact ⟨sum, rfl, hok⟩
  obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, h_tn, -, h_dn, h_up⟩ :=
    STAmount.roundToExponent_sum_spec value s mode hc hev (by omega) hs_hi sum h_sum_ok
  -- subtracting the reference back is exact, the result is `k` units of `10^s`
  have hres : result.toRat = (k : ℚ) * 10 ^ s ∧ result.mNumericType = .fractional ∧
      (result.mValue = 0 ∨ result.IOUCanonical) := by
    unfold STAmount.operator_sub at h_sub_ok
    have h_negRef : refA.operator_neg = ⟨value.mNumericType, kMinValue, s, !value.mIsNegative⟩ := by
      rw [STAmount.operator_neg_of_ne refA (by show kMinValue ≠ 0; decide)]
    rw [h_negRef] at h_sub_ok
    set negRef : STAmount := ⟨value.mNumericType, kMinValue, s, !value.mIsNegative⟩ with hnegRef_def
    have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
    have hc_sum : sum.IOUCanonical :=
      { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
        mant_lo := by omega
        mant_hi := by omega
        exp_lo := by rw [h_sum_off]; omega
        exp_hi := by rw [h_sum_off]; exact hs_hi }
    have hc_negRef : negRef.IOUCanonical :=
      { is_fractional := by rw [hnegRef_def]; exact hc.is_fractional
        mant_lo := by show 10 ^ 15 ≤ kMinValue.toNat; omega
        mant_hi := by show kMinValue.toNat < 10 ^ 16; omega
        exp_lo := by show (-96 : ℤ) ≤ s; omega
        exp_hi := hs_hi }
    rw [STAmount.operator_add_iou_unfold sum negRef mode hc_sum hc_negRef] at h_sub_ok
    set s1n : Number := ⟨sum.mIsNegative, sum.mValue * 10 * 10 * 10, sum.mOffset - 3⟩ with hs1n_def
    set s2n : Number := ⟨negRef.mIsNegative, negRef.mValue * 10 * 10 * 10, negRef.mOffset - 3⟩ with hs2n_def
    obtain ⟨n₂, h_add₂, hok₃⟩ : ∃ n₂, Number.operator_add s1n s2n mode = .ok n₂ ∧
        (match IOUAmount.ofNumber n₂ mode with
         | .error e => (Except.error e : Except Error STAmount)
         | .ok sumI => STAmount.ofIOUAmount sumI mode) = .ok result := by
      match h1 : Number.operator_add s1n s2n mode with
      | .error e => rw [h1] at h_sub_ok; exact absurd h_sub_ok (by intro h; cases h)
      | .ok n₂ =>
        rw [h1] at h_sub_ok
        exact ⟨n₂, rfl, h_sub_ok⟩
    obtain ⟨sumI₂, h_of₂, h_pack₂⟩ : ∃ sumI₂, IOUAmount.ofNumber n₂ mode = .ok sumI₂ ∧
        STAmount.ofIOUAmount sumI₂ mode = .ok result := by
      match h1 : IOUAmount.ofNumber n₂ mode with
      | .error e => rw [h1] at hok₃; exact absurd hok₃ (by intro h; cases h)
      | .ok sumI₂ =>
        rw [h1] at hok₃
        exact ⟨sumI₂, rfl, hok₃⟩
    have hs1_norm : s1n.isNormalized :=
      lift_isNormalized sum.mIsNegative sum.mValue sum.mOffset hc_sum.mant_lo hc_sum.mant_hi
        (by have := hc_sum.exp_lo; unfold minExponent; omega)
        (by have := hc_sum.exp_hi; unfold maxExponent; omega)
    have hs2_norm : s2n.isNormalized :=
      lift_isNormalized negRef.mIsNegative negRef.mValue negRef.mOffset hc_negRef.mant_lo hc_negRef.mant_hi
        (by have := hc_negRef.exp_lo; unfold minExponent; omega)
        (by have := hc_negRef.exp_hi; unfold maxExponent; omega)
    have hs1_val : s1n.toRat = sum.toRat := lift_toRat sum hc_sum.mant_hi
    have hs2_val : s2n.toRat = negRef.toRat := lift_toRat negRef hc_negRef.mant_hi
    have hs1_mant : s1n.mantissa_ ≠ 0 := by
      intro h0
      have h1 : s1n.mantissa_.toNat = 0 := by rw [h0]; rfl
      have hM : (sum.mValue * 10 * 10 * 10).toNat = sum.mValue.toNat * 1000 :=
        m_mul_thousand_no_overflow hc_sum.mant_hi
      have h2 : s1n.mantissa_.toNat = sum.mValue.toNat * 1000 := hM
      have := hc_sum.mant_lo
      omega
    have hs2_mant : s2n.mantissa_ ≠ 0 := by
      intro h0
      have h1 : s2n.mantissa_.toNat = 0 := by rw [h0]; rfl
      have h2 : s2n.mantissa_.toNat = 10 ^ 18 := by
        show (kMinValue * 10 * 10 * 10).toNat = 10 ^ 18
        decide
      omega
    have h_diff : s1n.negative_ ≠ s2n.negative_ := by
      show sum.mIsNegative ≠ !value.mIsNegative
      rw [h_sum_neg, hneg]
      decide
    have h_sum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
      rw [STAmount.toRat_of_nonneg sum (by rw [h_sum_neg, hneg]), h_sum_off, h_sum_mv]
    have h_negRef_val : negRef.toRat = -((10 ^ 15 : ℚ) * 10 ^ s) := by
      rw [STAmount.toRat_of_neg negRef (by show (!value.mIsNegative) = true; rw [hneg]; rfl)]
      show -((kMinValue.toNat : ℚ) * 10 ^ s) = _
      rw [h_kMin_toNat]; push_cast; ring
    have hτ : s1n.toRat + s2n.toRat = (k : ℚ) * 10 ^ s := by
      rw [hs1_val, hs2_val, h_sum_val, h_negRef_val]; push_cast; ring
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · -- `k = 0` cancels exactly to the canonical zero
      subst hk0
      have h_n₂_val : n₂.toRat = 0 := by
        have h := operator_add_exact_diff_sign s1n s2n n₂ mode hs1_norm hs2_norm hs1_mant hs2_mant h_diff
          Number.zero (Or.inl rfl) (by rw [Number.toRat_zero, hτ]; push_cast; ring) h_add₂
        rw [h, hτ]; push_cast; ring
      have h_n₂_mant : n₂.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp h_n₂_val
      rw [IOUAmount.ofNumber_zero_mantissa n₂ mode h_n₂_mant] at h_of₂
      have h_sumI₂ : sumI₂ = IOUAmount.zero := Except.ok.inj h_of₂.symm
      rw [h_sumI₂, STAmount.ofIOU_zero mode] at h_pack₂
      have h_result : result = ⟨.fractional, 0, -100, false⟩ := Except.ok.inj h_pack₂.symm
      subst h_result
      exact ⟨by rw [STAmount.toRat_eq_zero_of_mValue_zero _ rfl]; push_cast; ring, rfl, Or.inl rfl⟩
    · -- `k ≥ 1` gives a grid point the asset stores exactly
      obtain ⟨w, hw_norm, hw_neg, hw_mant, hw_val, hw_mod, hw_lo, hw_hi⟩ :=
        exists_normalized_of_int_mul_pow k s hk_pos (by omega)
          (by unfold minExponent; omega) (by unfold maxExponent; omega)
      have hn₂_val : n₂.toRat = w.toRat := by
        rw [operator_add_exact_diff_sign s1n s2n n₂ mode hs1_norm hs2_norm hs1_mant hs2_mant h_diff
          w hw_norm (by rw [hw_val, hτ]) h_add₂, hτ, hw_val]
      have hτ_ne : s1n.toRat + s2n.toRat ≠ 0 := by
        rw [hτ]
        have : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk_pos
        positivity
      have h_n₂_mant : n₂.mantissa_ ≠ 0 := by
        intro h0
        apply hτ_ne
        rw [hτ, ← hw_val, ← hn₂_val]
        exact Number.toRat_eq_zero_iff.mpr h0
      have h_not_zero₂ : ¬ s1n.operator_eq s2n.operator_neg := fun h => hτ_ne (add_truth_zero_of_eq_neg s1n s2n h)
      have hn₂ : n₂ = w :=
        (operator_add_result_isNormalized s1n s2n n₂ mode hs1_norm hs2_norm hs1_mant hs2_mant h_diff
          h_not_zero₂ h_add₂ h_n₂_mant).toRat_inj hw_norm hn₂_val
      subst hn₂
      obtain ⟨hof, hpack, hr_c, hr_val⟩ :=
        STAmount.repack_exact n₂ mode hw_norm hw_neg hw_mant hw_mod (by omega) (by omega)
      rw [hof, Except.ok.injEq] at h_of₂
      subst h_of₂
      rw [hpack, Except.ok.injEq] at h_pack₂
      subst h_pack₂
      exact ⟨by rw [hr_val, hw_val], hr_c.is_fractional, Or.inr hr_c⟩
  refine ⟨k, hres.1, hres.2.1, hres.2.2, fun h => by rw [← h_abs]; exact h_tn h,
    fun h => by have := h_dn h; rw [hneg, if_neg Bool.false_ne_true, h_abs] at this; exact this,
    fun h => by have := h_up h; rw [hneg, if_neg Bool.false_ne_true, h_abs] at this; exact this⟩

/-- Rounding to a fractional amount at a scale is faithful. When the `ofNumber` step lands at or
below the scale, the result is a whole number of steps of `10^s` and never jumps over a grid point. -/
lemma STAmount.roundToNumericType_frac_grid (x T : Number) (mode : rounding_mode) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hs : -81 ≤ s ∧ s ≤ 80)
    (hexp : ∀ st, STAmount.ofNumber .fractional x mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ s)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) :
    GridFaithful s x.toRat T.toRat ∧ (∃ k : ℕ, T.toRat = (k : ℚ) * 10 ^ s) ∧
      (mode = .upward → (T.toRat ≠ 0 ∨ (10 : ℚ) ^ (-81 : ℤ) ≤ x.toRat) → x.toRat ≤ T.toRat) ∧
      (mode = .downward → T.toRat ≤ x.toRat) := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x mode with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
    rw [if_neg (by rw [hint]; decide)] at hok
    cases hr : STAmount.roundToExponent st s mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      by_cases hst : st.mValue = 0
      · -- a zero amount stays zero
        have hsmall := STAmount.ofNumber_frac_zero_small x mode st hx h0 hof hst
        have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode
          (Or.inr (Or.inl (by unfold STAmount.isZero; simp [hst]))) hr
        subst hrst
        rw [STAmount.toNumber_zero_fractional r mode hint hst, Except.ok.injEq] at hok
        subst hok
        rw [Number.toRat_zero]
        refine ⟨GridFaithful.zero_of_lt h0 (hsmall.trans_le (zpow_le_zpow_right₀ (by norm_num) hs.1)),
          ⟨0, by simp⟩, fun _ h => h.elim (fun h => absurd rfl h) (fun h => absurd h (not_le.mpr hsmall)),
          fun _ => h0⟩
      · obtain ⟨hc, hle, hgf, hup, hdown⟩ := STAmount.ofNumber_frac_stage x mode st hx h0 hmode hof hst
        have hneg := Number.negative_false_of_nonneg x hx h0
        have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hof
        have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hst
        have hes : st.exponent ≤ s := hexp st hof hst
        have hgf' := hgf.coarsen (le_trans hle hes)
        by_cases heq : s ≤ st.exponent
        · -- already at the scale
          have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode (Or.inr (Or.inr heq)) hr
          subst hrst
          obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hc
          rw [hsn, Except.ok.injEq] at hok
          subst hok
          rw [hv]
          have hes' : r.exponent = s := le_antisymm hes heq
          refine ⟨hgf', ⟨r.mValue.toNat, ?_⟩, fun hm _ => hup hm, hdown⟩
          rw [STAmount.toRat_of_nonneg r hsneg]
          exact congrArg _ (congrArg _ hes')
        · -- the reference sum rounds it onto the scale
          push Not at heq
          obtain ⟨k, hrk, hrty, hrc, htn, hdn, hupk⟩ :=
            STAmount.roundToExponent_nonneg_units st r s mode hc hsneg heq hs.1 hs.2 hr
          have hT : T.toRat = r.toRat := by
            rcases hrc with hr0 | hrc
            · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
              rw [STAmount.toNumber_zero_fractional r mode hrint hr0, Except.ok.injEq] at hok
              rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hr0]
            · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrc
              rw [hsn, Except.ok.injEq] at hok
              rw [← hok, hv]
          have hfc : (⌊st.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ r.toRat ∧
              r.toRat ≤ (⌈st.toRat / 10 ^ s⌉ : ℚ) * 10 ^ s := by
            have hfl : (⌊st.toRat / 10 ^ s⌋ : ℚ) ≤ ⌈st.toRat / 10 ^ s⌉ := by
              exact_mod_cast Int.floor_le_ceil _
            rw [hrk]
            rcases hmode with rfl | rfl | rfl
            · rcases htn rfl with h | h
              · rw [show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, h]
                exact ⟨le_refl _, mul_le_mul_of_nonneg_right hfl hp.le⟩
              · rw [show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, h]
                exact ⟨mul_le_mul_of_nonneg_right hfl hp.le, le_refl _⟩
            · rw [show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, hupk rfl]
              exact ⟨mul_le_mul_of_nonneg_right hfl hp.le, le_refl _⟩
            · rw [show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, hdn rfl]
              exact ⟨le_refl _, mul_le_mul_of_nonneg_right hfl hp.le⟩
          refine ⟨hgf'.trans (by rw [hT]; exact GridFaithful.of_floor_ceil hfc.1 hfc.2), ⟨k, by rw [hT, hrk]⟩,
            fun hm _ => ?_, fun hm => ?_⟩
          · subst hm
            rw [hT, hrk, show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, hupk rfl]
            exact (hup rfl).trans (le_ceil_grid _ _)
          · subst hm
            rw [hT, hrk, show ((k : ℚ)) = ((k : ℤ) : ℚ) by push_cast; rfl, hdn rfl]
            exact (floor_grid_le _ _).trans (hdown rfl)

/-- Rounding to an integral amount is faithful on the whole numbers. The scale is ignored. -/
lemma STAmount.roundToNumericType_int_grid (nt : NumericType) (hnt : nt.isIntegral = true) (x T : Number)
    (mode : rounding_mode) (s : Option ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hok : STAmount.roundToNumericType nt x mode s = .ok T) :
    GridFaithful 0 x.toRat T.toRat ∧ (∃ k : ℕ, T.toRat = (k : ℚ)) ∧ (mode = .upward → x.toRat ≤ T.toRat) ∧
      (mode = .downward → T.toRat ≤ x.toRat) := by
  have hneg := Number.negative_false_of_nonneg x hx h0
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x mode with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hint : st.integral = true := by unfold STAmount.integral; rw [hty]; exact hnt
    have hT : st.toNumber mode = .ok T := by
      cases s with
      | none => exact hok
      | some s => simp only [hint, if_true] at hok; exact hok
    obtain ⟨iv, hrep, hval⟩ := STAmount.ofNumber_integral_toRat nt x mode st hnt hneg hof
    obtain ⟨hiv0, -⟩ := Number.to_rep_nonneg_range x mode iv hneg hrep
    have hic := (STAmount.ofNumber_integral_canonical nt x mode st hnt hof).1
    have hsz : st.mValue.toNat ≤ 2 ^ 63 - 1 := by
      by_cases hz : st.mValue = 0
      · rw [hz]; decide
      · exact ((STAmount.ofNumber_exactCanonical nt x mode st hx h0 hof hz).integralCanonical hint).2
    obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st mode hic hsz
    rw [hsn, Except.ok.injEq] at hT
    subst hT
    have hTv : sn.toRat = ((iv.toInt.toNat : ℕ) : ℚ) := by
      rw [hv, hval]; exact_mod_cast (Int.toNat_of_nonneg hiv0).symm
    have hy1 : sn.toRat = ((iv.toInt.toNat : ℤ) : ℚ) * 10 ^ (0 : ℤ) := by
      rw [hTv, zpow_zero, mul_one, Int.cast_natCast]
    have hfloor : (⌊x.toRat / 10 ^ (0 : ℤ)⌋ : ℚ) * 10 ^ (0 : ℤ) ≤ (⌈x.toRat / 10 ^ (0 : ℤ)⌉ : ℚ) * 10 ^ (0 : ℤ) := by
      simp only [zpow_zero, div_one, mul_one]; exact_mod_cast Int.floor_le_ceil _
    refine ⟨?_, ⟨_, hTv⟩, fun hm => ?_, fun hm => ?_⟩
    · rcases hmode with rfl | rfl | rfl
      · have hd := Number.to_rep_to_nearest_within_half x iv hx hneg hrep
        rw [← hval, ← hv] at hd
        obtain ⟨hlo, hhi⟩ := floor_ceil_of_within_half _ hy1 (by rw [zpow_zero, mul_one]; exact hd)
        exact GridFaithful.of_floor_ceil hlo hhi
      · obtain ⟨h1, h2⟩ := Number.to_rep_upward_ceil x iv hx hneg hrep
        have hc : (⌈x.toRat / 10 ^ (0 : ℤ)⌉ : ℚ) * 10 ^ (0 : ℤ) = sn.toRat := by
          rw [hv, hval]
          simp only [zpow_zero, div_one, mul_one]
          have : ⌈x.toRat⌉ = iv.toInt := by rw [Int.ceil_eq_iff]; constructor <;> linarith
          rw [this]
        exact GridFaithful.of_floor_ceil (hc ▸ hfloor) (le_of_eq hc.symm)
      · obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor x iv hx hneg hrep
        have hc : (⌊x.toRat / 10 ^ (0 : ℤ)⌋ : ℚ) * 10 ^ (0 : ℤ) = sn.toRat := by
          rw [hv, hval]
          simp only [zpow_zero, div_one, mul_one]
          have : ⌊x.toRat⌋ = iv.toInt := by rw [Int.floor_eq_iff]; constructor <;> linarith
          rw [this]
        exact GridFaithful.of_floor_ceil (le_of_eq hc) (hc ▸ hfloor)
    · subst hm
      rw [hv, hval]
      exact (Number.to_rep_upward_ceil x iv hx hneg hrep).1
    · subst hm
      rw [hv, hval]
      exact (Number.to_rep_downward_floor x iv hx hneg hrep).1

/-- A normalized `Number` has a positive sign exactly when its value is positive. -/
lemma Number.signum_pos_iff_toRat {n : Number} (hn : n.isNormalized) : 0 < n.signum ↔ 0 < n.toRat := by
  rw [signum_eq n hn]
  split_ifs with h1 h2
  · exact iff_of_true (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

/-- A normalized `Number` has a nonnegative sign exactly when its value is nonnegative. -/
lemma Number.signum_nonneg_iff_toRat {n : Number} (hn : n.isNormalized) : 0 ≤ n.signum ↔ 0 ≤ n.toRat := by
  rw [signum_eq n hn]
  split_ifs with h1 h2
  · exact iff_of_true (by decide) h1.le
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_true le_rfl (by linarith)

/-- A normalized `Number` whose sign is not negative is at least zero. -/
lemma Number.toRat_nonneg_of_not_signum_neg (n : Number) (hn : n.isNormalized) (h : ¬ n.signum < 0) :
    0 ≤ n.toRat :=
  (Number.signum_nonneg_iff_toRat hn).mp (by omega)

/-- A `UInt32` keeps its value through `UInt64` and `Int64`. -/
private lemma UInt32.toUInt64_toInt64_toInt (n : UInt32) : n.toInt64.toInt = (n.toNat : ℤ) :=
  UInt32.toInt_toInt64 n

/-- An `Int64` other than the smallest converts to a `Number` of the same value. -/
lemma Number.ofInt64_toRat_of_ne (m : Int64) (hm : m ≠ Int64.minValue) :
    (Number.ofInt64 m).toRat = (m.toInt : ℚ) := by
  obtain ⟨w, hw, hv, -⟩ := Number.from_rep_exact m 0 .to_nearest hm (by unfold minExponent; norm_num)
    (by unfold maxExponent; norm_num)
  unfold Number.ofInt64
  rw [hw]
  show w.toRat = _
  rw [hv, zpow_zero, mul_one]

/-- A count converts to a `Number` of the same value. -/
lemma Number.ofInt64_count (n : UInt32) : (Number.ofInt64 n.toInt64).toRat = (n.toNat : ℚ) := by
  have hne : n.toInt64 ≠ Int64.minValue := by
    intro h
    have h1 := congrArg Int64.toInt h
    rw [UInt32.toUInt64_toInt64_toInt, show Int64.minValue.toInt = -2 ^ 63 from by decide] at h1
    omega
  rw [Number.ofInt64_toRat_of_ne _ hne, UInt32.toUInt64_toInt64_toInt]
  push_cast; rfl

/-- A 16-digit IOU amount has one exponent for its value. -/
private lemma STAmount.exponent_eq_of_toRat (a : STAmount) (hc : a.IOUCanonical) (h0 : 0 ≤ a.toRat) (m : ℕ) (e : ℤ)
    (hm : 10 ^ 15 ≤ m ∧ m < 10 ^ 16) (hv : a.toRat = (m : ℚ) * 10 ^ e) : a.exponent = e := by
  have habs := STAmount.abs_toRat a
  rw [abs_of_nonneg h0] at habs
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hlo := hc.mant_lo
  have hhi := hc.mant_hi
  rcases lt_trichotomy a.mOffset e with hlt | heq | hgt
  · -- a lower exponent would need a mantissa ten times larger
    have h1 := grid_point_fine m e a.mOffset hlt.le
    rw [hv, h1] at habs
    have hpa : (0 : ℚ) < 10 ^ a.mOffset := zpow_pos (by norm_num) _
    have h2 : (m * 10 ^ (e - a.mOffset).toNat : ℕ) = a.mValue.toNat := by
      exact_mod_cast (mul_right_cancel₀ hpa.ne' habs.symm).symm
    have h3 : 10 ≤ 10 ^ (e - a.mOffset).toNat := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (e - a.mOffset).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : m * 10 ≤ a.mValue.toNat := by rw [← h2]; exact Nat.mul_le_mul_left m h3
    omega
  · exact heq
  · have h1 := grid_point_fine a.mValue.toNat a.mOffset e hgt.le
    rw [hv, h1] at habs
    have h2 : (a.mValue.toNat * 10 ^ (a.mOffset - e).toNat : ℕ) = m := by
      exact_mod_cast (mul_right_cancel₀ hp.ne' habs).symm
    have h3 : 10 ≤ 10 ^ (a.mOffset - e).toNat := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (a.mOffset - e).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : a.mValue.toNat * 10 ≤ m := by rw [← h2]; exact Nat.mul_le_mul_left _ h3
    omega

/-- An amount the asset stores exactly converts to itself. A fractional source `m·10^e` with a
16-digit `m` converts, rounding to nearest, up or down, to a canonical amount of the same value at exponent `e`. -/
private lemma STAmount.ofNumber_frac_of_representable (x : Number) (mode : rounding_mode) (st : STAmount) (m : ℕ)
    (e : ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hm : 10 ^ 15 ≤ m ∧ m < 10 ^ 16) (he : -96 ≤ e) (hv : x.toRat = (m : ℚ) * 10 ^ e)
    (hof : STAmount.ofNumber .fractional x mode = .ok st) :
    st.mValue ≠ 0 ∧ st.IOUCanonical ∧ st.toRat = x.toRat ∧ st.exponent = e := by
  have hmin : (10 : ℚ) ^ (-81 : ℤ) ≤ x.toRat := by
    rw [hv]
    calc (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * 10 ^ (-96 : ℤ) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
      _ ≤ (m : ℚ) * 10 ^ e := mul_le_mul (by exact_mod_cast hm.1) (zpow_le_zpow_right₀ (by norm_num) he)
          (by positivity) (by positivity)
  have hst0 : st.mValue ≠ 0 := fun h => absurd (STAmount.ofNumber_frac_zero_small x mode st hx h0 hof h)
    (not_lt.mpr hmin)
  have hz : x.toRat ≠ 0 := fun h => by rw [h] at hmin; exact absurd hmin (not_le.mpr (by positivity))
  have hm0 : x.mantissa_ ≠ 0 := fun h => hz (Number.toRat_eq_zero_of_mantissa_zero x h)
  have hneg := Number.negative_false_of_nonneg x hx h0
  have hxe : x.exponent_ + 3 ≤ e := by
    by_contra hc
    push Not at hc
    have hb := hx.mantissaBounds_nat hm0
    have hxv := Number.toRat_of_nonneg x hneg
    have h1 : (10 : ℚ) ^ (16 : ℕ) * 10 ^ e ≤ x.toRat := by
      rw [hxv]
      calc (10 : ℚ) ^ (16 : ℕ) * 10 ^ e = 10 ^ (18 : ℕ) * 10 ^ (e - 2) := by
            rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; field_simp
        _ ≤ (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ := by
            apply mul_le_mul (by exact_mod_cast hb.1) (zpow_le_zpow_right₀ (by norm_num) (by omega))
              (by positivity) (by positivity)
    have h2 : x.toRat < (10 : ℚ) ^ (16 : ℕ) * 10 ^ e := by
      rw [hv]; exact mul_lt_mul_of_pos_right (by exact_mod_cast hm.2) (zpow_pos (by norm_num) _)
    linarith
  have hxg := grid_point_fine m e (x.exponent_ + 3) hxe
  obtain ⟨hc, -, hgf, -, -⟩ := STAmount.ofNumber_frac_stage x mode st hx h0 hmode hof hst0
  have hlo := hgf.lower _ (by rw [← hxg, ← hv])
  have hhi := hgf.upper _ (by rw [← hxg, ← hv])
  rw [← hxg, ← hv] at hlo hhi
  have hstx : st.toRat = x.toRat := le_antisymm hhi hlo
  exact ⟨hst0, hc, hstx, STAmount.exponent_eq_of_toRat st hc (hstx ▸ h0) m e hm (by rw [hstx, hv])⟩

/-- An amount the precision check finds exact at scale `s` is on that grid. The value is one an
STAmount stores exactly, so its directed roundings at `s` bracket it, and the check finds them equal. -/
lemma isRounded_grid (nt : NumericType) (x : Number) (s : ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hst : STAmount.isRounded nt x = false) (hs : -81 ≤ s ∧ s ≤ 80) (hint : nt.isIntegral = true → s = 0)
    (hchk : isRounded x s nt = .ok true) : ∃ j : ℕ, x.toRat = (j : ℚ) * 10 ^ s := by
  by_cases hz : x.toRat = 0
  · exact ⟨0, by rw [hz]; simp⟩
  have hrep := ((STAmount.isRounded_eq_false_iff nt x hx h0).mp hst).resolve_left hz
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hrep
    obtain ⟨-, k, -, -, hk⟩ := hrep
    rw [hint (by rw [hnt]; rfl)]
    exact ⟨k, by rw [hk, zpow_zero, mul_one]⟩
  | fractional =>
    rw [hnt] at hrep hchk
    obtain ⟨m, e, hmlo, hmhi, helo, hehi, hv⟩ := hrep
    by_cases hes : s ≤ e
    · exact ⟨m * 10 ^ (e - s).toNat, by rw [hv]; exact grid_point_fine m e s hes⟩
    push Not at hes
    have hexp : ∀ mode, (mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) →
        ∀ st, STAmount.ofNumber .fractional x mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ s := by
      intro mode hmode st hof _
      rw [(STAmount.ofNumber_frac_of_representable x mode st m e hx h0 hmode ⟨hmlo, hmhi⟩ helo hv hof).2.2.2]
      exact hes.le
    unfold isRounded at hchk
    obtain ⟨down, hdown, hchk⟩ := bind_ok_peel _ _ _ hchk
    obtain ⟨up, hup, hchk⟩ := bind_ok_peel _ _ _ hchk
    have heq : down.operator_eq up = true := by
      simp only [pure, Except.pure, Except.ok.injEq] at hchk; exact hchk
    have hdu := (Number.operator_eq_iff_eq _ _).mp heq
    obtain ⟨-, ⟨k, hk⟩, -, hdle⟩ := STAmount.roundToNumericType_frac_grid x down .downward s hx h0
      (Or.inr (Or.inr rfl)) hs (hexp _ (Or.inr (Or.inr rfl))) hdown
    obtain ⟨-, -, hupge, -⟩ := STAmount.roundToNumericType_frac_grid x up .upward s hx h0
      (Or.inr (Or.inl rfl)) hs (hexp _ (Or.inr (Or.inl rfl))) hup
    have hmin : (10 : ℚ) ^ (-81 : ℤ) ≤ x.toRat := by
      rw [hv]
      calc (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * 10 ^ (-96 : ℤ) := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
        _ ≤ (m : ℚ) * 10 ^ e := mul_le_mul (by exact_mod_cast hmlo) (zpow_le_zpow_right₀ (by norm_num) helo)
            (by positivity) (by positivity)
    have h1 := hdle rfl
    have h2 := hupge rfl (Or.inr hmin)
    rw [← hdu] at h2
    exact ⟨k, by rw [← hk]; exact le_antisymm h2 h1⟩

/-- An amount already on the grid stays put. When the `ofNumber` step gives a nonzero amount on
the `10^s` grid, at or below the scale, rounding at the scale keeps its value. -/
lemma STAmount.roundToNumericType_frac_of_grid (x T : Number) (mode : rounding_mode) (s : ℤ) (st : STAmount)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hs : -81 ≤ s ∧ s ≤ 80) (hof : STAmount.ofNumber .fractional x mode = .ok st) (hst : st.mValue ≠ 0)
    (hc : st.IOUCanonical) (h0 : 0 ≤ st.toRat) (hes : st.exponent ≤ s) (j : ℕ)
    (hj : st.toRat = (j : ℚ) * 10 ^ s)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) : T.toRat = st.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hdiv : st.toRat / 10 ^ s = (j : ℚ) := by rw [hj]; field_simp
  unfold STAmount.roundToNumericType at hok
  rw [hof] at hok
  simp only at hok
  have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
  have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
  rw [if_neg (by rw [hint]; decide)] at hok
  have hsneg := STAmount.mIsNegative_false_of_nonneg st h0 hst
  cases hr : STAmount.roundToExponent st s mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok r =>
    rw [hr] at hok
    simp only at hok
    by_cases heq : s ≤ st.exponent
    · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode (Or.inr (Or.inr heq)) hr
      subst hrst
      obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hc
      rw [hsn, Except.ok.injEq] at hok
      rw [← hok, hv]
    · push Not at heq
      obtain ⟨k, hrk, hrty, hrc, htn, hdn, hupk⟩ :=
        STAmount.roundToExponent_nonneg_units st r s mode hc hsneg heq hs.1 hs.2 hr
      -- the floor and the ceiling of a grid point are the point
      have hkj : (k : ℤ) = j := by
        have hf : ⌊st.toRat / 10 ^ s⌋ = j := by rw [hdiv]; exact Int.floor_natCast j
        have hcl : ⌈st.toRat / 10 ^ s⌉ = j := by rw [hdiv]; exact Int.ceil_natCast j
        rcases hmode with rfl | rfl | rfl
        · rcases htn rfl with h | h <;> omega
        · rw [hupk rfl, hcl]
        · rw [hdn rfl, hf]
      have hT : T.toRat = r.toRat := by
        rcases hrc with hr0 | hrc
        · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
          rw [STAmount.toNumber_zero_fractional r mode hrint hr0, Except.ok.injEq] at hok
          rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hr0]
        · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrc
          rw [hsn, Except.ok.injEq] at hok
          rw [← hok, hv]
      rw [hT, hrk, hj]
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ) * 10 ^ s) hkj

/-- A zero `ofNumber` amount stays zero at every scale. -/
lemma STAmount.roundToNumericType_frac_of_zero (x T : Number) (mode : rounding_mode) (s : ℤ) (st : STAmount)
    (hof : STAmount.ofNumber .fractional x mode = .ok st) (hst : st.mValue = 0)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) : T.toRat = 0 := by
  unfold STAmount.roundToNumericType at hok
  rw [hof] at hok
  simp only at hok
  have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
  have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
  rw [if_neg (by rw [hint]; decide), STAmount.roundToExponent_eq_self st s mode
    (Or.inr (Or.inl (by unfold STAmount.isZero; simp [hst])))] at hok
  simp only at hok
  rw [STAmount.toNumber_zero_fractional st mode hint hst, Except.ok.injEq] at hok
  rw [← hok, Number.toRat_zero]

/-- An amount the asset stores exactly, on the grid, rounds to itself at the scale. -/
lemma STAmount.roundToNumericType_representable_grid (nt : NumericType) (x T : Number) (mode : rounding_mode)
    (s : ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hs : -81 ≤ s ∧ s ≤ 80)
    (hint : nt.isIntegral = true → s = 0) (hst : STAmount.isRounded nt x = false) (j : ℕ)
    (hj : x.toRat = (j : ℚ) * 10 ^ s) (hj16 : nt = .fractional → j < 10 ^ 16)
    (hok : STAmount.roundToNumericType nt x mode (some s) = .ok T) : T.toRat = x.toRat := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    have hs0 := hint (by rw [hnt]; rfl)
    rw [hs0, zpow_zero, mul_one] at hj
    obtain ⟨hgf, -⟩ := STAmount.roundToNumericType_int_grid _ rfl x T mode _ hx h0 hmode hok
    have h1 := hgf.lower j (by rw [hj, zpow_zero, mul_one])
    have h2 := hgf.upper j (by rw [hj, zpow_zero, mul_one])
    rw [zpow_zero, mul_one] at h1 h2
    rw [hj]; linarith
  | fractional =>
    rw [hnt] at hok hst
    by_cases hz : x.toRat = 0
    · have hx0 : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp hz
      have hof := STAmount.ofNumber_fractional_zero mode
      rw [← hx0] at hof
      rw [STAmount.roundToNumericType_frac_of_zero x T mode s _ hof rfl hok, hz]
    obtain ⟨m, e, hmlo, hmhi, helo, -, hv⟩ :=
      ((STAmount.isRounded_eq_false_iff .fractional x hx h0).mp hst).resolve_left hz
    cases hof : STAmount.ofNumber .fractional x mode with
    | error err =>
      unfold STAmount.roundToNumericType at hok; rw [hof] at hok; exact absurd hok (by simp)
    | ok st =>
      obtain ⟨hst0, hc, hstx, hste⟩ :=
        STAmount.ofNumber_frac_of_representable x mode st m e hx h0 hmode ⟨hmlo, hmhi⟩ helo hv hof
      -- the 16-digit exponent is at most the scale, as the value has fewer than `10^16` steps
      have hes : e ≤ s := by
        by_contra hc'
        push Not at hc'
        have h1 := grid_point_fine m e s hc'.le
        rw [hv, h1] at hj
        have h2 : (m * 10 ^ (e - s).toNat : ℕ) = j := by
          exact_mod_cast mul_right_cancel₀ (zpow_pos (by norm_num : (0 : ℚ) < 10) s).ne' hj
        have h3 : 10 ≤ 10 ^ (e - s).toNat := by
          calc 10 = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ (e - s).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : m * 10 ≤ j := by rw [← h2]; exact Nat.mul_le_mul_left m h3
        have := hj16 hnt
        omega
      rw [STAmount.roundToNumericType_frac_of_grid x T mode s st hmode hs hof hst0 hc (hstx ▸ h0) (hste ▸ hes) j
        (by rw [hstx, hj]) hok, hstx]

/-- A rounding of zero is zero. -/
lemma Number.RoundsToRepresentable.toRat_of_zero {r : Number} {mode : rounding_mode}
    (hR : r.RoundsToRepresentable 0 mode) (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) :
    r.toRat = 0 := by
  have h1 := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero])
  have h2 := hR.le_of_ge hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero])
  rw [Number.toRat_zero] at h1 h2
  linarith

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The rounding mode of the loan value: upward with interest, to nearest without. -/
abbrev valueMode (rate : Number) : rounding_mode :=
  if rate.operator_eq Number.zero then .to_nearest else .upward

/-- What the loan properties computed. The periodic payment, the total value `PP × n` rounded at
LoanScale, the principal rounded at LoanScale, and the management fee on the interest between them. -/
lemma computeLoanProperties_inv (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (props : LoanProperties)
    (h : computeLoanProperties principal ir interval n mgmt nt minScale = .ok props) :
    ∃ rate amount amountSt ti,
      loanPeriodicRate ir interval = .ok rate ∧
      loanPeriodicPayment principal rate n = .ok props.periodicPayment ∧
      props.periodicPayment.operator_mul (Number.ofInt64 n.toInt64) (valueMode rate) = .ok amount ∧
      STAmount.ofNumber nt amount (valueMode rate) = .ok amountSt ∧
      props.loanScale = max minScale amountSt.exponent ∧
      STAmount.roundToNumericType nt amount (valueMode rate) (some props.loanScale) =
        .ok props.totalValueOutstanding ∧
      STAmount.roundToNumericType nt principal .to_nearest (some props.loanScale) =
        .ok props.principalOutstanding ∧
      props.totalValueOutstanding.operator_sub props.principalOutstanding .to_nearest = .ok ti ∧
      computeManagementFee nt ti mgmt props.loanScale = .ok props.managementFeeOutstanding := by
  unfold computeLoanProperties at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  obtain ⟨amount, hamount, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨amountSt, hst, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tvo, htvo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨rp, hrp, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨ti, hti, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨mfo, hmfo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rate, amount, amountSt, ti, hrate, hpp, hamount, hst, rfl, htvo, hrp, hti, hmfo⟩

/-- Guards that pass. The interest has the sign InterestRate asks for, the first payment pays some
principal, and the fee, the total value and the payment pass the sanity check. -/
lemma LoanProperties.checkGuards_ok_inv (props : LoanProperties) (principal : Number) (ir : TenthBips32)
    (n : UInt32) (nt : NumericType)
    (h : props.checkGuards principal ir n nt = .ok .tesSUCCESS) :
    ∃ ti, props.totalValueOutstanding.operator_sub principal .to_nearest = .ok ti ∧
      (ir ≠ 0 → 0 < ti.signum) ∧ (ir = 0 → ti.signum ≤ 0) ∧ 0 < props.firstPaymentPrincipal.signum ∧
      0 ≤ props.managementFeeOutstanding.signum ∧ 0 < props.totalValueOutstanding.signum ∧
      0 < props.periodicPayment.signum := by
  unfold LoanProperties.checkGuards at h
  cases hg : props.amortizationGuards principal (ir != 0) n nt with
  | error e => rw [hg] at h; exact absurd h (by simp [bind, Except.bind])
  | ok g =>
    rw [hg] at h
    simp only [bind, Except.bind] at h
    by_cases hgs : g.isTesSuccess = true
    · simp only [hgs, Bool.not_true, Bool.false_eq_true, if_false] at h
      have hg' : g = .tesSUCCESS := (TER.isTesSuccess_iff g).mp hgs
      subst hg'
      simp only [pure, Except.pure] at h
      split at h
      · exact absurd h (by decide)
      · rename_i hsan
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hsan
        unfold LoanProperties.amortizationGuards at hg
        cases hti : props.totalValueOutstanding.operator_sub principal .to_nearest with
        | error e => rw [hti] at hg; exact absurd hg (by simp [bind, Except.bind])
        | ok ti =>
          rw [hti] at hg
          simp only [bind, Except.bind, pure, Except.pure] at hg
          split at hg
          · exact absurd hg (by decide)
          rename_i h1
          split at hg
          · exact absurd hg (by decide)
          rename_i h2
          split at hg
          · exact absurd hg (by decide)
          rename_i h3
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and, not_le, Bool.not_eq_true',
            bne_eq_false_iff_eq, gt_iff_lt, not_lt] at h1 h2
          refine ⟨ti, rfl, fun hir => h1 hir, fun hir => h2 hir, by omega, hsan.1.1, by omega, by omega⟩
    · simp only [Bool.not_eq_true] at hgs
      simp only [hgs, Bool.not_false, if_true, pure, Except.pure, Except.ok.injEq] at h
      rw [h] at hgs; exact absurd hgs (by decide)

/-- The base exponent of a vault is between `-10` and `0`. -/
lemma Vault.baseExponent_scale_range (v : Vault) :
    (-10 : Int) ≤ v.baseExponent ∧ v.baseExponent ≤ 0 := by
  have hs : v.scale.toNat ≤ 10 := by
    have := v.wf.scale_le
    rw [UInt8.le_iff_toNat_le] at this
    simpa [XRPL.Model.SingleAssetVault.vaultMaximumIOUScale] using this
  unfold XRPL.Model.SingleAssetVault.Vault.baseExponent NumericType.baseExponent
  split <;> omega

/-- A nonzero InterestRate over a nonzero PaymentInterval gives a positive periodic rate. Every step of the rate
rounds a positive value to nearest, well above the smallest `Number`. -/
private lemma loanPeriodicRate_pos (ir : TenthBips32) (interval : UInt32) (rate : Number) (hir : ir ≠ 0)
    (hint : interval ≠ 0) (h : loanPeriodicRate ir interval = .ok rate) : 0 < rate.toRat := by
  have heq : loanPeriodicRate ir interval =
      ((Number.ofInt64 interval.toInt64).operator_mul ir.toNumber .to_nearest >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨p, hp, ht⟩ := bind_ok_peel _ _ _ ht
  have hI := Number.ofInt64_isNormalized interval.toInt64
  have hB := Number.ofInt64_isNormalized ir.toInt64
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toInt64
  have hY := Number.ofInt64_isNormalized (31536000 : Int64)
  have hIv := Number.ofInt64_count interval
  have hBv : (Number.ofInt64 ir.toInt64).toRat = (ir.toNat : ℚ) := Number.ofInt64_count ir
  have hUv : (Number.ofInt64 kTenthBipsPerUnity.toInt64).toRat = 100000 := by
    rw [Number.ofInt64_count]; rfl
  have hYv : (Number.ofInt64 31536000).toRat = 31536000 := by
    rw [Number.ofInt64_toRat_of_ne _ (by decide)]; rfl
  have hpN := Number.operator_mul_isNormalized _ _ p _ hI hB hp
  have htN := Number.operator_div_isNormalized _ _ t _ hpN hU ht
  have hR1 := operator_mul_rounded_to_nearest _ _ p hI hB hp
  have hR2 := operator_div_rounded_to_nearest _ _ t hpN hU ht
  have hR3 := operator_div_rounded_to_nearest _ _ rate htN hY h
  have hi1 : (1 : ℚ) ≤ interval.toNat := by
    have : 0 < interval.toNat := by
      rcases Nat.eq_zero_or_pos interval.toNat with h0 | h0
      · exact absurd (UInt32.toNat_inj.mp (by rw [h0]; rfl)) hint
      · exact h0
    exact_mod_cast this
  have hb1 : (1 : ℚ) ≤ ir.toNat := by
    have : 0 < ir.toNat := by
      rcases Nat.eq_zero_or_pos ir.toNat with h0 | h0
      · exact absurd (UInt32.toNat_inj.mp (by rw [h0]; rfl)) hir
      · exact h0
    exact_mod_cast this
  have hw : ∀ e : ℕ, e ≤ 20 → ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (-(e : ℤ)) := by
    intro e he
    obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (-(e : ℤ)) (by norm_num)
      (by unfold minExponent maxExponent; omega)
    exact ⟨w, hwn, by rw [hwv]; simp⟩
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  obtain ⟨w0, hw0, hw0v⟩ := hw 0 (by norm_num)
  have hp1 : 1 ≤ p.toRat := by
    have := hR1.ge_of_le hmode w0 hw0 (by rw [hw0v, hIv, hBv]; simp; nlinarith)
    rwa [hw0v, show (-((0 : ℕ) : ℤ)) = 0 from rfl, zpow_zero] at this
  obtain ⟨w5, hw5, hw5v⟩ := hw 5 (by norm_num)
  have ht5 : (10 : ℚ) ^ (-((5 : ℕ) : ℤ)) ≤ t.toRat := by
    have := hR2.ge_of_le hmode w5 hw5 (by
      rw [hw5v, hUv]
      calc (10 : ℚ) ^ (-((5 : ℕ) : ℤ)) = 1 / 100000 := by norm_num
        _ ≤ p.toRat / 100000 := by gcongr)
    rwa [hw5v] at this
  obtain ⟨w13, hw13, hw13v⟩ := hw 13 (by norm_num)
  have := hR3.ge_of_le hmode w13 hw13 (by
    rw [hw13v, hYv]
    calc (10 : ℚ) ^ (-((13 : ℕ) : ℤ)) ≤ (10 : ℚ) ^ (-((5 : ℕ) : ℤ)) / 31536000 := by norm_num
      _ ≤ t.toRat / 31536000 := by gcongr)
  rw [hw13v] at this
  exact lt_of_lt_of_le (by positivity) this

/-- A successful create stores the loan built from its computed properties, on the broker with
the new DebtTotal and LoanCount. -/
lemma Loan.create_loan_eq (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ props loanState debtTotal' broker',
      Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal' ∧
      r.loan'.toRawLoan = RawLoan.build principal props rates fees schedule broker' allowsOverpayment pending
        (schedule.startDate + schedule.paymentInterval) ∧
      broker'.toRawLoanBroker =
        { broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 } := by
  obtain ⟨props, loanState, debtTotal', _, broker', hchecks, -, -, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  exact ⟨props, loanState, debtTotal', broker', hchecks, (RawLoan.to_lawful_ok hloan).1,
    (RawLoanBroker.to_lawful_ok hbroker).1⟩

/-- The total value at LoanScale. With interest every step rounds up, so it is `PP × n` rounded up
onto the LoanScale grid. -/
private lemma Loan.create_value_ceil (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hrate : rates.interestRate ≠ 0) :
    r.loan'.toExact.totalValueOutstanding =
      (⌈r.loan'.toExact.periodicPayment * r.loan'.toExact.paymentTotal.toNat / 10 ^ r.loan'.loanScale⌉ : ℚ) *
        10 ^ r.loan'.loanScale := by
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst, hls, htvo, -, -, -⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hSC : r.loan'.schedule = schedule := by
    show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  -- with interest the periodic rate is positive, so every step rounds up
  have hrate0 : 0 < rate.toRat := loanPeriodicRate_pos _ _ rate hrate (by
    intro h0
    have := hex.paymentInterval_min
    simp only [RawLoan.toExact] at this
    rw [hSC, h0] at this
    exact absurd this (by decide)) hrt
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrt
  have hmode : valueMode rate = .upward := by
    unfold valueMode
    rw [if_neg]
    intro heq
    rw [(operator_eq_iff rate Number.zero hrN Number.zero_isNormalized).mp heq, Number.toRat_zero] at hrate0
    exact lt_irrefl _ hrate0
  rw [hmode] at hamt hst htvo
  have hppN : props.periodicPayment.isNormalized := hPP ▸ hwf.periodicPayment_norm
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  have hpp0 : 0 < props.periodicPayment.toRat := by
    have := hex.periodicPayment_pos; simp only [RawLoan.toExact] at this; rwa [hPP] at this
  obtain ⟨-, -, -, -, -, -, htv0, -⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  have htv0' : 0 < props.totalValueOutstanding.toRat := (Number.signum_pos_iff_toRat htvN).mp htv0
  have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toInt64
  have hNv := Number.ofInt64_count schedule.paymentTotal
  have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
  have hamt0 : amount.mantissa_ ≠ 0 := by
    intro h0
    rw [Number.eq_zero_of_mantissa_zero amount hamtN h0, STAmount.roundToNumericType_zero,
      Except.ok.injEq] at htvo
    rw [← htvo, Number.toRat_zero] at htv0'
    exact lt_irrefl _ htv0'
  have hR := operator_mul_rounded_upward _ _ amount hppN hN hamt hamt0
  set t := props.periodicPayment.toRat * (Number.ofInt64 schedule.paymentTotal.toInt64).toRat with ht
  have ht0 : 0 ≤ t := by rw [ht, hNv]; positivity
  have hta : t ≤ amount.toRat := by obtain ⟨n', hn', hv⟩ := hR; rw [hv]; exact Number.le_upper _ _ hn'
  -- the scale is the LoanScale, between `-10` and `80`
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  have hbase := Vault.baseExponent_scale_range v
  have hls_lo : -10 ≤ props.loanScale := by rw [hls]; exact le_trans hbase.1 (le_max_left _ _)
  have hls_hi : props.loanScale ≤ 80 := by have := hrange.2; unfold cMaxOffset at this; exact this
  have hstep : GridFaithful props.loanScale amount.toRat props.totalValueOutstanding.toRat ∧
      (∃ k : ℕ, props.totalValueOutstanding.toRat = (k : ℚ) * 10 ^ props.loanScale) ∧
      amount.toRat ≤ props.totalValueOutstanding.toRat := by
    cases hnt : broker.numericType with
    | fractional =>
      rw [hnt] at htvo hst
      obtain ⟨hgf, hk, hup, -⟩ := STAmount.roundToNumericType_frac_grid amount _ .upward props.loanScale hamtN
        (le_trans ht0 hta) (Or.inr (Or.inl rfl)) ⟨by omega, hls_hi⟩
        (fun st hst' _ => by
          rw [hst, Except.ok.injEq] at hst'
          rw [← hst', hls]; exact le_max_right _ _) htvo
      exact ⟨hgf, hk, hup rfl (Or.inl (ne_of_gt htv0'))⟩
    | integral mv mo ms msh =>
      rw [hnt] at htvo hst
      have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
      obtain ⟨hgf, ⟨k, hk⟩, hup, -⟩ := STAmount.roundToNumericType_int_grid _ hint amount _ .upward _ hamtN
        (le_trans ht0 hta) (Or.inr (Or.inl rfl)) htvo
      have hoff := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint hst).1.offset_zero
      have hls0 : props.loanScale = 0 := by
        rw [hls]; unfold STAmount.exponent; rw [hoff]; exact max_eq_right hbase.2
      rw [hls0]
      exact ⟨hgf, ⟨k, by rw [hk, zpow_zero, mul_one]⟩, hup rfl⟩
  obtain ⟨hgf, ⟨k, hk⟩, hat⟩ := hstep
  have hbound : t ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) * 10 ^ props.loanScale := by
    obtain ⟨m, hm, hmv⟩ := hexg.totalValueOutstanding_atExponent
    simp only [RawLoan.toExact] at hm hmv
    rw [hTV, hLS] at hmv
    have hm' : m ≤ 2 ^ 63 - 1 := by
      have := NumericType.mantissaBound_le r.loan'.broker.numericType; omega
    calc t ≤ props.totalValueOutstanding.toRat := hta.trans hat
      _ = (m : ℚ) * 10 ^ props.loanScale := hmv
      _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) * 10 ^ props.loanScale :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm') (zpow_pos (by norm_num) _).le
  have hgf0 := hR.gridFaithful (Or.inr (Or.inl rfl)) props.loanScale
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩ hbound
  have hgft := hgf0.trans hgf
  have hceil := ceil_grid_eq_of_grid (x := t) k (by rw [← hk]; exact hta.trans hat)
    (by rw [← hk]; exact hgft.le_ceil ht0)
  show r.loan'.totalValueOutstanding.toRat =
    (⌈r.loan'.periodicPayment.toRat * (r.loan'.schedule.paymentTotal.toNat : ℚ) / 10 ^ r.loan'.loanScale⌉ : ℚ) *
      10 ^ r.loan'.loanScale
  rw [hTV, hPP, hLS, hSC, ← hNv, ← ht, hk, hceil]

/-- The LoanScale is never below the base scale, and an integral amount has LoanScale `0`. -/
lemma computeLoanProperties_loanScale (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (props : LoanProperties)
    (h : computeLoanProperties principal ir interval n mgmt nt minScale = .ok props) (hmin : minScale ≤ 0) :
    minScale ≤ props.loanScale ∧ (nt.isIntegral = true → props.loanScale = 0) := by
  obtain ⟨rate, amount, amountSt, ti, -, -, -, hst, hls, -⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ h
  refine ⟨by rw [hls]; exact le_max_left _ _, fun hint => ?_⟩
  have hoff := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint hst).1.offset_zero
  rw [hls]; unfold STAmount.exponent; rw [hoff]; exact max_eq_right hmin

/-- The LoanScale of a new loan is between `-10` and `80`, and `0` for an integral amount. -/
lemma Loan.create_loanScale_range (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal')
    (hhi : props.loanScale ≤ cMaxOffset) :
    -10 ≤ props.loanScale ∧ props.loanScale ≤ 80 ∧ (broker.numericType.isIntegral = true → props.loanScale = 0) := by
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨h1, h2⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2
  exact ⟨le_trans hbase.1 h1, hhi, h2⟩

/-- Proof body of the upper bound part of `Lending.create_value`. -/
lemma Loan.create_value_upper_bound_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hrate : rates.interestRate ≠ 0) :
    r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.periodicPayment * r.loan'.toExact.paymentTotal.toNat <
      10 ^ r.loan'.toExact.loanScale := by
  rw [Loan.create_value_ceil broker v principal rates fees schedule allowsOverpayment pending r hok hrate]
  show _ - _ < (10 : ℚ) ^ r.loan'.loanScale
  have hp : (0 : ℚ) < 10 ^ r.loan'.loanScale := zpow_pos (by norm_num) _
  set x := r.loan'.toExact.periodicPayment * (r.loan'.toExact.paymentTotal.toNat : ℚ)
  have h1 := Int.ceil_lt_add_one (x / 10 ^ r.loan'.loanScale)
  have h2 : (⌈x / 10 ^ r.loan'.loanScale⌉ : ℚ) * 10 ^ r.loan'.loanScale <
      (x / 10 ^ r.loan'.loanScale + 1) * 10 ^ r.loan'.loanScale := mul_lt_mul_of_pos_right h1 hp
  rw [add_mul, div_mul_cancel₀ _ hp.ne', one_mul] at h2
  linarith

/-- Proof body of the lower bound part of `Lending.create_value`. -/
lemma Loan.create_value_lower_bound_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hrate : rates.interestRate ≠ 0) :
    r.loan'.toExact.periodicPayment * r.loan'.toExact.paymentTotal.toNat - r.loan'.toExact.totalValueOutstanding ≤
      0 := by
  rw [Loan.create_value_ceil broker v principal rates fees schedule allowsOverpayment pending r hok hrate]
  linarith [le_ceil_grid (r.loan'.toExact.periodicPayment * (r.loan'.toExact.paymentTotal.toNat : ℚ))
    r.loan'.loanScale]

/-- Proof body of the PrincipalRequested part of `Lending.create_value`. -/
lemma Loan.create_covers_principal_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault) (hp : principal.isNormalized)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hrate : rates.interestRate ≠ 0) :
    principal.toRat < r.loan'.toExact.periodicPayment * r.loan'.toExact.paymentTotal.toNat := by
  have hceil := Loan.create_value_ceil broker v principal rates fees schedule allowsOverpayment pending r hok hrate
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ r.loan'.wf.totalValueOutstanding_norm
  set x := r.loan'.toExact.periodicPayment * (r.loan'.toExact.paymentTotal.toNat : ℚ) with hx
  have hx0 : 0 < x := by
    have h1 := hex.periodicPayment_pos
    have h2 : (0 : ℚ) < (r.loan'.toExact.paymentTotal.toNat : ℚ) := by
      have := hex.paymentTotal_pos
      have : 0 < r.loan'.toExact.paymentTotal.toNat := by
        rw [UInt32.lt_iff_toNat_lt] at this; simpa using this
      exact_mod_cast this
    positivity
  -- with interest the guard asks for a total value above PrincipalRequested
  obtain ⟨ti, hsub, hpos, -⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hp hsub
  have hgt : principal.toRat < props.totalValueOutstanding.toRat := by
    by_contra hc
    push Not at hc
    have hR := operator_sub_rounded_to_nearest _ _ ti htvN hp hsub
    have := Number.roundsToRepresentable_nonpos ti _ hR (by linarith)
    have := (Number.signum_pos_iff_toRat htiN).mp (hpos hrate)
    linarith
  by_cases hP : principal.toRat ≤ 0
  · linarith
  push Not at hP
  -- PrincipalRequested is on the LoanScale grid
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hP.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
  by_contra hc
  push Not at hc
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  have h1 : ⌈x / 10 ^ props.loanScale⌉ ≤ (j : ℤ) :=
    Int.ceil_le.mpr (by rw [div_le_iff₀ hp10]; exact_mod_cast (hj ▸ hc))
  have h2 : (⌈x / 10 ^ props.loanScale⌉ : ℚ) * 10 ^ props.loanScale ≤ principal.toRat := by
    rw [hj]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hp10.le
  have h3 : props.totalValueOutstanding.toRat = (⌈x / 10 ^ props.loanScale⌉ : ℚ) * 10 ^ props.loanScale := by
    have := hceil
    simp only [RawLoan.toExact] at this
    rw [hTV, hLS] at this
    exact this
  linarith

/-- With InterestRate `0` the periodic rate is zero. -/
private lemma loanPeriodicRate_zero (interval : UInt32) (rate : Number) (h : loanPeriodicRate 0 interval = .ok rate) :
    rate = Number.zero := by
  have heq : loanPeriodicRate 0 interval =
      ((Number.ofInt64 interval.toInt64).operator_mul (0 : TenthBips32).toNumber .to_nearest >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨p, hp, ht⟩ := bind_ok_peel _ _ _ ht
  have hI := Number.ofInt64_isNormalized interval.toInt64
  have hB := Number.ofInt64_isNormalized (0 : TenthBips32).toInt64
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toInt64
  have hY := Number.ofInt64_isNormalized (31536000 : Int64)
  have hBv : (Number.ofInt64 (0 : TenthBips32).toInt64).toRat = 0 := by
    rw [Number.ofInt64_count]; rfl
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  have hpN := Number.operator_mul_isNormalized _ _ p _ hI hB hp
  have htN := Number.operator_div_isNormalized _ _ t _ hpN hU ht
  have hrN := Number.operator_div_isNormalized _ _ rate _ htN hY h
  have hp0 : p.toRat = 0 := by
    have hR := operator_mul_rounded_to_nearest _ _ p hI hB hp
    rw [hBv, mul_zero] at hR
    exact hR.toRat_of_zero hmode
  have ht0 : t.toRat = 0 := by
    have hR := operator_div_rounded_to_nearest _ _ t hpN hU ht
    rw [hp0, zero_div] at hR
    exact hR.toRat_of_zero hmode
  have hR := operator_div_rounded_to_nearest _ _ rate htN hY h
  rw [ht0, zero_div] at hR
  exact (Number.toRat_eq_zero_iff_eq_zero hrN).mp (hR.toRat_of_zero hmode)

/-- With a zero periodic rate the payment is PrincipalRequested over the count. -/
private lemma loanPeriodicPayment_zero_rate (principal : Number) (n : UInt32) (pp : Number)
    (hp : principal.isNormalized) (hp0 : principal.toRat ≠ 0) (hn : n ≠ 0)
    (h : loanPeriodicPayment principal Number.zero n = .ok pp) :
    principal.operator_div (Number.ofInt64 n.toInt64) .to_nearest = .ok pp := by
  have hpe : principal.operator_eq Number.zero = false := by
    cases hq : principal.operator_eq Number.zero
    · rfl
    · exact absurd ((operator_eq_iff _ _ hp Number.zero_isNormalized).mp hq) (by rw [Number.toRat_zero]; exact hp0)
  have hne : (n == 0) = false := by simpa using hn
  unfold loanPeriodicPayment at h
  simp only [hpe, hne, Bool.or_false, Bool.false_eq_true, if_false] at h
  exact h

/-- With InterestRate `0` the total value is PrincipalRequested. `PP × n` lands within half a 16-digit
step of PrincipalRequested, a LoanScale grid point, and an integral amount below `10^17` rounds back to it. -/
lemma computeLoanProperties_zero_rate_value (principal : Number) (interval n : UInt32) (mgmt : TenthBips16)
    (nt : NumericType) (minScale : Int) (props : LoanProperties) (hp : principal.isNormalized)
    (hmin : -10 ≤ minScale ∧ minScale ≤ 0) (hn : 0 < n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : principal.toRat = (j : ℚ) * 10 ^ props.loanScale) (hint : nt.isIntegral = true → j < 10 ^ 17)
    (h : computeLoanProperties principal 0 interval n mgmt nt minScale = .ok props) :
    props.totalValueOutstanding.toRat = principal.toRat ∧ 0 < props.periodicPayment.toRat := by
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, -, -, -⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ h
  obtain ⟨hlsmin, hls0⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ h hmin.2
  have hr0 := loanPeriodicRate_zero _ rate hrt
  have hmode : valueMode rate = .to_nearest := by rw [hr0]; rfl
  rw [hmode] at hamt hst' htvo
  rw [hr0] at hpp
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  have hP0 : 0 < principal.toRat := by
    rw [hj]; exact mul_pos (by exact_mod_cast hj1) hp10
  have hPmin : (10 : ℚ) ^ (-10 : ℤ) ≤ principal.toRat := by
    rw [hj]
    calc (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ props.loanScale := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 * 10 ^ props.loanScale := by ring
      _ ≤ (j : ℚ) * 10 ^ props.loanScale := mul_le_mul_of_nonneg_right (by exact_mod_cast hj1) hp10.le
  have hn' : n ≠ 0 := by intro h0; rw [h0] at hn; exact absurd hn (by decide)
  have hdiv := loanPeriodicPayment_zero_rate _ _ _ hp hP0.ne' hn' hpp
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hn0 : (0 : ℚ) < n.toNat := by
    rw [UInt32.lt_iff_toNat_lt] at hn; exact_mod_cast hn
  have hn32 : (n.toNat : ℚ) < 10 ^ (10 : ℕ) := by
    have := n.toNat_lt; have : n.toNat < 10 ^ 10 := by omega
    exact_mod_cast this
  have hmode' : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  have hw : ∀ e : ℕ, e ≤ 30 → ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (-(e : ℤ)) := by
    intro e he
    obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (-(e : ℤ)) (by norm_num)
      (by unfold minExponent maxExponent; omega)
    exact ⟨w, hwn, by rw [hwv]; simp⟩
  -- the payment is positive, at least `10^-20`
  have hppN := Number.operator_div_isNormalized _ _ _ _ hp hN hdiv
  have hR1 := operator_div_rounded_to_nearest _ _ _ hp hN hdiv
  obtain ⟨w20, hw20, hw20v⟩ := hw 20 (by norm_num)
  have hpp20 : (10 : ℚ) ^ (-((20 : ℕ) : ℤ)) ≤ props.periodicPayment.toRat := by
    have := hR1.ge_of_le hmode' w20 hw20 (by
      rw [hw20v, hNv, le_div_iff₀ hn0]
      calc (10 : ℚ) ^ (-((20 : ℕ) : ℤ)) * n.toNat ≤ 10 ^ (-((20 : ℕ) : ℤ)) * 10 ^ (10 : ℕ) :=
            mul_le_mul_of_nonneg_left hn32.le (by positivity)
        _ = 10 ^ (-10 : ℤ) := by norm_num
        _ ≤ principal.toRat := hPmin)
    rwa [hw20v] at this
  have hpp0 : 0 < props.periodicPayment.toRat := lt_of_lt_of_le (by positivity) hpp20
  refine ⟨?_, hpp0⟩
  have hpp_ne : props.periodicPayment.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hpp0; exact lt_irrefl _ hpp0
  -- the two roundings of `P / n × n` move it by less than `2·10^-18` of itself
  have hW1 := operator_div_rounds_to_nearest _ _ _ hp hN hdiv hpp_ne
  simp only [RoundsWithin] at hW1
  change |props.periodicPayment.toRat - principal.toRat / _| ≤ _ at hW1
  rw [hNv] at hW1
  set nq : ℚ := (n.toNat : ℚ)
  set P := principal.toRat
  set pp := props.periodicPayment.toRat
  have hq0 : 0 < P / nq := div_pos hP0 hn0
  rw [abs_of_pos hq0] at hW1
  have hε1 : (6 : ℚ) / (2 ^ 63 - 3) ≤ 7 / 10 ^ 19 := by norm_num
  have hε2 : (5 : ℚ) / (2 ^ 63 + 7) ≤ 6 / 10 ^ 19 := by norm_num
  have hppn : |pp * nq - P| ≤ P * (7 / 10 ^ 19) := by
    have h1 : pp * nq - P = (pp - P / nq) * nq := by field_simp
    rw [h1, abs_mul, abs_of_pos hn0]
    calc |pp - P / nq| * nq ≤ (P / nq * (6 / (2 ^ 63 - 3))) * nq := mul_le_mul_of_nonneg_right hW1 hn0.le
      _ = P * (6 / (2 ^ 63 - 3)) := by field_simp
      _ ≤ P * (7 / 10 ^ 19) := mul_le_mul_of_nonneg_left hε1 hP0.le
  -- `amount` is at least `10^-11`, so nonzero with an exponent above `-99`
  have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
  have hRa := operator_mul_rounded_to_nearest _ _ amount hppN hN hamt
  obtain ⟨w11, hw11, hw11v⟩ := hw 11 (by norm_num)
  have hamt11 : (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ amount.toRat := by
    have := hRa.ge_of_le hmode' w11 hw11 (by
      rw [hw11v, hNv]
      change _ ≤ pp * nq
      have := (abs_le.mp hppn).1
      have h2 : (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ P * (1 - 7 / 10 ^ 19) := by
        calc (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ 10 ^ (-10 : ℤ) * (1 - 7 / 10 ^ 19) := by norm_num
          _ ≤ P * (1 - 7 / 10 ^ 19) := mul_le_mul_of_nonneg_right hPmin (by norm_num)
      calc (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ P * (1 - 7 / 10 ^ 19) := h2
        _ = P - P * (7 / 10 ^ 19) := by ring
        _ ≤ pp * nq := by linarith [this])
    rwa [hw11v] at this
  have hamt0 : 0 ≤ amount.toRat := le_trans (by positivity) hamt11
  have hm0 : amount.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hamt11
    exact absurd hamt11 (not_le.mpr (by positivity))
  have hW2 := operator_mul_rounds_to_nearest _ _ _ hppN hN hamt hm0
  simp only [RoundsWithin] at hW2
  change |amount.toRat - props.periodicPayment.toRat * _| ≤ _ at hW2
  rw [hNv, abs_of_pos (mul_pos hpp0 hn0)] at hW2
  have hppn2 : pp * nq ≤ 2 * P := by have := (abs_le.mp hppn).2; nlinarith
  have hdist : |amount.toRat - P| ≤ P * (2 / 10 ^ 18) := by
    calc |amount.toRat - P| ≤ |amount.toRat - pp * nq| + |pp * nq - P| := abs_sub_le _ _ _
      _ ≤ pp * nq * (6 / 10 ^ 19) + P * (7 / 10 ^ 19) := by
        gcongr
        exact hW2.trans (mul_le_mul_of_nonneg_left hε2 (by positivity))
      _ ≤ P * (2 / 10 ^ 18) := by nlinarith
  have hb := hamtN.mantissaBounds_nat hm0
  have hemin := Number.exponent_ge_min amount hamtN hm0
  set E := amount.exponent_
  have hamtv : amount.toRat = (amount.mantissa_.toNat : ℚ) * 10 ^ E :=
    Number.toRat_of_nonneg amount (Number.negative_false_of_nonneg amount hamtN hamt0)
  have hpE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  have hamt_lt : amount.toRat < 10 ^ (19 : ℕ) * 10 ^ E := by
    rw [hamtv]; exact mul_lt_mul_of_pos_right (by exact_mod_cast hb.2) hpE
  have hE99 : (-99 : ℤ) ≤ E := by
    by_contra hc
    push Not at hc
    have h1 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ E ≤ 10 ^ (19 : ℕ) * 10 ^ (-100 : ℤ) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by positivity)
    have h2 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-100 : ℤ) < 10 ^ (-((11 : ℕ) : ℤ)) := by norm_num
    linarith
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hst' htvo
    have hint' : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    have hls00 := hls0 (by rw [hnt]; rfl)
    have hj17 := hint (by rw [hnt]; rfl)
    rw [hls00, zpow_zero, mul_one] at hj
    -- the whole-number conversion lands on PrincipalRequested
    have hhalf := STAmount.ofNumber_integral_within_half _ amount amountSt hint' hamtN
      (Number.negative_false_of_nonneg amount hamtN hamt0) hst'
    obtain ⟨iv, hrep, hivv⟩ := STAmount.ofNumber_integral_toRat _ amount _ amountSt hint'
      (Number.negative_false_of_nonneg amount hamtN hamt0) hst'
    have hclose : |amountSt.toRat - P| < 1 := by
      have hP17 : P < 10 ^ (17 : ℕ) := by rw [hj]; exact_mod_cast hj17
      calc |amountSt.toRat - P| ≤ |amountSt.toRat - amount.toRat| + |amount.toRat - P| := abs_sub_le _ _ _
        _ ≤ 1 / 2 + P * (2 / 10 ^ 18) := add_le_add hhalf hdist
        _ < 1 := by nlinarith
    have hstP : amountSt.toRat = P := by
      rw [hivv] at hclose ⊢
      rw [hj] at hclose ⊢
      rw [abs_lt] at hclose
      have h1 : iv.toInt - j < 1 := by exact_mod_cast (by linarith [hclose.2] : (iv.toInt : ℚ) - j < 1)
      have h2 : -1 < iv.toInt - j := by exact_mod_cast (by linarith [hclose.1] : (-1 : ℚ) < iv.toInt - j)
      have : iv.toInt = j := by omega
      rw [this]; push_cast; ring
    unfold STAmount.roundToNumericType at htvo
    rw [hst'] at htvo
    have hty := STAmount.ofNumber_mNumericType _ _ _ amountSt hst'
    have hsint : amountSt.integral = true := by unfold STAmount.integral; rw [hty]; rfl
    simp only [hsint, if_true] at htvo
    have hic := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint' hst').1
    have hsz : amountSt.mValue.toNat ≤ 2 ^ 63 - 1 := by
      by_cases hz : amountSt.mValue = 0
      · rw [hz]; decide
      · exact ((STAmount.ofNumber_exactCanonical _ amount _ amountSt hamtN hamt0 hst' hz).integralCanonical
          hsint).2
    obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact amountSt _ hic hsz
    rw [hsn, Except.ok.injEq] at htvo
    rw [← htvo, hv, hstP]
  | fractional =>
    rw [hnt] at hst' htvo
    have hst0 := STAmount.ofNumber_iou_ne_zero_of_exponent amount _ amountSt hamtN hm0 hE99 hst'
    obtain ⟨hc, hle3, -, -, -⟩ := STAmount.ofNumber_frac_stage amount _ amountSt hamtN hamt0 hmode' hst' hst0
    have hexpr := STAmount.ofNumber_iou_success_exp_range amount _ amountSt hb.1 hb.2 hemin hst' hst0
    obtain ⟨hhalf, -⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional amount amountSt rfl hb.1 hb.2 hemin
      hexpr hst' hst0
    have hls80 : props.loanScale ≤ 80 := by rw [hls]; exact max_le (by omega) hc.exp_hi
    -- so `amount` is within half a 16-digit step of a grid point: the conversion lands on PrincipalRequested
    have hP_lt : P < 2 * (10 ^ (19 : ℕ) * 10 ^ E) := by
      have := (abs_le.mp hdist).1; nlinarith
    have hE3 : (10 : ℚ) ^ (E + 3) = 1000 * 10 ^ E := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    have hclose : |amountSt.toRat - P| < 10 ^ (E + 3) := by
      calc |amountSt.toRat - P| ≤ |amountSt.toRat - amount.toRat| + |amount.toRat - P| := abs_sub_le _ _ _
        _ ≤ (1 / 2 : ℚ) * 10 ^ (E + 3) + P * (2 / 10 ^ 18) := add_le_add hhalf hdist
        _ < 10 ^ (E + 3) := by rw [hE3]; nlinarith
    have hstnn : 0 ≤ amountSt.toRat := STAmount.ofNumber_nonneg _ _ _ _ hamtN
      (Number.negative_false_of_nonneg amount hamtN hamt0) hst'
    have hes : amountSt.exponent ≤ props.loanScale := by rw [hls]; exact le_max_right _ _
    have hgA := STAmount.toRat_grid_of_le amountSt hstnn (E + 3) hle3
    have hgP := grid_point_fine j props.loanScale (E + 3) (le_trans hle3 hes)
    set A := amountSt.mValue.toNat * 10 ^ (amountSt.exponent - (E + 3)).toNat
    set J := j * 10 ^ (props.loanScale - (E + 3)).toNat
    have hAJ : A = J := by
      rw [hgA, hj, hgP, ← sub_mul, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 10) (E + 3))] at hclose
      have h1 : |(A : ℚ) - J| < 1 :=
        (mul_lt_iff_lt_one_left (zpow_pos (by norm_num : (0 : ℚ) < 10) (E + 3))).mp hclose
      rw [abs_lt] at h1
      have h2 : (A : ℤ) - J < 1 := by exact_mod_cast h1.2
      have h3 : -1 < (A : ℤ) - J := by exact_mod_cast h1.1
      omega
    have hstP : amountSt.toRat = (j : ℚ) * 10 ^ props.loanScale := by rw [hgA, hAJ, ← hgP]
    rw [STAmount.roundToNumericType_frac_of_grid amount _ _ _ amountSt hmode' ⟨by omega, hls80⟩ hst' hst0 hc hstnn
      hes j hstP htvo, hstP, ← hj]

/-- Proof body of the zero InterestRate line of `Lending.create_value`. -/
lemma Loan.create_zero_rate_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault) (hp : principal.isNormalized)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hrate : rates.interestRate = 0) :
    r.loan'.toExact.totalValueOutstanding = principal.toRat := by
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, -, -, -, hrt, hpp, -, -, -, -, hpo, -, -⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  -- InterestRate `0` gives the periodic rate `0`, so the payment is the principal over the count
  rw [hrate] at hrt
  have hr0 := loanPeriodicRate_zero _ rate hrt
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  have hpp0 : 0 < props.periodicPayment.toRat := by
    have := hex.periodicPayment_pos; simp only [RawLoan.toExact] at this; rwa [hPP] at this
  have hppne : props.periodicPayment ≠ Number.zero := fun h => by
    rw [h, Number.toRat_zero] at hpp0; exact lt_irrefl _ hpp0
  have hdiv : principal.operator_div (Number.ofInt64 schedule.paymentTotal.toInt64) .to_nearest =
      .ok props.periodicPayment := by
    rcases loanPeriodicPayment_cases _ _ _ _ hpp hppne with ⟨-, hd⟩ | ⟨hz, -⟩
    · exact hd
    · rw [hr0] at hz; exact absurd hz (by decide)
  have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toInt64
  have hNv := Number.ofInt64_count schedule.paymentTotal
  have hn0 : (0 : ℚ) < schedule.paymentTotal.toNat := by
    have h := hex.paymentTotal_pos
    simp only [RawLoan.toExact] at h
    have hsc : r.loan'.schedule = schedule := by show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
    rw [hsc, UInt32.lt_iff_toNat_lt] at h
    exact_mod_cast h
  have hP0 : 0 < principal.toRat := by
    have hR := operator_div_rounded_to_nearest _ _ _ hp hN hdiv
    have := Number.pos_of_roundsToRepresentable _ _ hR hpp0
    rw [hNv] at this
    exact (div_pos_iff_of_pos_right hn0).mp this
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hP0.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
  show r.loan'.totalValueOutstanding.toRat = principal.toRat
  rw [hTV]
  obtain ⟨ti', hsub, -, hle0, -, -, -, -⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  cases hnt : broker.numericType with
  | integral mv mo ms msh =>
    have hint' : broker.numericType.isIntegral = true := by rw [hnt]; rfl
    have hls0 := hint hint'
    rw [hls0, zpow_zero, mul_one] at hj
    rw [hnt] at hpo
    obtain ⟨hgf, -⟩ := STAmount.roundToNumericType_int_grid _ rfl principal _ .to_nearest _ hp hP0.le
      (Or.inl rfl) hpo
    have hpo1 := hgf.lower j (by rw [hj, zpow_zero, mul_one])
    have hpo2 := hgf.upper j (by rw [hj, zpow_zero, mul_one])
    rw [zpow_zero, mul_one] at hpo1 hpo2
    have hpoP : props.principalOutstanding.toRat = principal.toRat := by rw [hj]; linarith
    -- the loan invariant keeps the interest at or above zero for an integral amount
    have htol := hex.interest_nonneg
    have hmf0 := hex.managementFeeOutstanding_nonneg
    simp only [RawLoan.Exact.interestDue, RawLoan.toExact] at htol hmf0
    rw [hTV, hPO, hMF, hpoP] at htol
    rw [hMF] at hmf0
    -- the zero-rate guard keeps the total value at or below PrincipalRequested
    have hle : props.totalValueOutstanding.toRat ≤ principal.toRat := by
      by_contra hc
      push Not at hc
      obtain ⟨a, -, ha⟩ := hexg.totalValueOutstanding_atExponent
      simp only [RawLoan.toExact] at ha
      rw [hTV, hLS, hls0, zpow_zero, mul_one] at ha
      have h1 : (j : ℚ) + 1 ≤ a := by
        have : j < a := by exact_mod_cast (show (j : ℚ) < a by rw [← ha, ← hj]; exact hc)
        exact_mod_cast this
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 0 (by norm_num)
        (by unfold minExponent maxExponent; norm_num)
      have hR := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
      have hge := hR.ge_of_le (Or.inl rfl) w hw (by rw [hwv, ha, hj]; push_cast; linarith)
      have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti' htvN hp hsub
      have := (Number.signum_pos_iff_toRat htiN).mpr (by rw [hwv] at hge; push_cast at hge; linarith)
      exact absurd (hle0 hrate) (not_le.mpr this)
    linarith
  | fractional =>
    -- the 16-digit conversion of `PP × n` lands on PrincipalRequested
    have hprops := hchecks.properties_ok
    rw [hrate] at hprops
    have hsc : r.loan'.schedule = schedule := by show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
    have hn : 0 < schedule.paymentTotal := by
      have h := hex.paymentTotal_pos
      simp only [RawLoan.toExact] at h
      rwa [hsc] at h
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hj; simp at hj; linarith
      · exact h0
    have hbase := Vault.baseExponent_scale_range v
    exact (computeLoanProperties_zero_rate_value principal _ _ _ _ _ props hp ⟨hbase.1, hbase.2⟩ hn j hj1 hj
      (fun h => by rw [hnt] at h; exact absurd h (by decide)) hprops).1

/-- The management fee rate of a broker is at most 10%. -/
lemma LoanBroker.managementFeeRate_le (b : LoanBroker) : b.managementFeeRate.toNat ≤ 10000 := by
  have h := b.valid.managementFeeRate_cap
  rw [UInt16.le_iff_toNat_le] at h
  exact h

/-- The management fee on `K` LoanScale units of interest at a rate of at most 10% is whole units from the floor of
`K × rate / 10^5` to its ceiling, and for `K` below `10^16` at most `10^-3` units above the share. -/
lemma computeManagementFee_bounds (nt : NumericType) (ti mfo : Number) (K : ℕ) (mgmt : TenthBips16) (ls : ℤ)
    (htiN : ti.isNormalized) (hK : ti.toRat = (K : ℚ) * 10 ^ ls) (hKlt : K < 2 ^ 63)
    (hR : mgmt.toNat ≤ 10000) (hls : -10 ≤ ls ∧ ls ≤ 80) (hint : nt.isIntegral = true → ls = 0)
    (hfr : nt = .fractional → K < 10 ^ 16) (h : computeManagementFee nt ti mgmt ls = .ok mfo) :
    ((K * mgmt.toNat / 100000 : ℕ) : ℚ) * 10 ^ ls ≤ mfo.toRat ∧
      mfo.toRat ≤ (((K * mgmt.toNat + 99999) / 100000 : ℕ) : ℚ) * 10 ^ ls ∧
      (K < 10 ^ 16 → mfo.toRat ≤ (((K * mgmt.toNat + 99) / 100 : ℕ) : ℚ) * 10 ^ (ls - 3)) ∧
      ∃ m : ℕ, mfo.toRat = (m : ℚ) * 10 ^ ls := by
  set R := mgmt.toNat with hRdef
  have hp10 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _
  have hs : minExponent + 18 ≤ ls ∧ ls ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hs5 : minExponent + 18 ≤ ls + 5 ∧ ls + 5 ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hs2 : minExponent + 18 ≤ ls + 2 ∧ ls + 2 ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hs3 : minExponent + 18 ≤ ls - 3 ∧ ls - 3 ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  -- the fee is the floor at LoanScale of `(I × rate) / 10^5`, each step to nearest
  have heq : computeManagementFee nt ti mgmt ls =
      (ti.operator_mul mgmt.toTenthBips32.toNumber .to_nearest >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun raw => STAmount.roundToNumericType nt raw .downward (some ls)) := rfl
  rw [heq] at h
  obtain ⟨raw, hraw, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨y, hy, hraw⟩ := bind_ok_peel _ _ _ hraw
  have hRB := Number.ofInt64_isNormalized mgmt.toTenthBips32.toInt64
  have hRBv : (Number.ofInt64 mgmt.toTenthBips32.toInt64).toRat = (R : ℚ) := by
    rw [Number.ofInt64_count]
    show ((mgmt.toUInt32.toNat : ℕ) : ℚ) = _
    rw [UInt16.toNat_toUInt32]
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toInt64
  have hUv : (Number.ofInt64 kTenthBipsPerUnity.toInt64).toRat = 100000 := by
    rw [Number.ofInt64_count]; rfl
  have hyN := Number.operator_mul_isNormalized _ _ y _ htiN hRB hy
  have hrawN := Number.operator_div_isNormalized _ _ raw _ hyN hU hraw
  have hR1 := operator_mul_rounded_to_nearest _ _ y htiN hRB hy
  have hR2 := operator_div_rounded_to_nearest _ _ raw hyN hU hraw
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  have hpow5 : (10 : ℚ) ^ (ls + 5) = 100000 * 10 ^ ls := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  set F := K * R / 100000 with hF
  set C := (K * R + 99999) / 100000 with hC
  have hFle : F * 100000 ≤ K * R := Nat.div_mul_le_self _ _
  have hCge : K * R ≤ C * 100000 := by omega
  have hKR : K * R ≤ K * 10000 := Nat.mul_le_mul_left K hR
  have hFlt : F < 2 ^ 63 := by omega
  have hClt : C < 2 ^ 63 := by omega
  obtain ⟨w1, hw1, hw1v⟩ := Number.exists_normalized_int_mul_pow (F : ℤ) (ls + 5) ⟨by omega, by omega⟩ hs5
  obtain ⟨w2, hw2, hw2v⟩ := Number.exists_normalized_int_mul_pow (C : ℤ) (ls + 5) ⟨by omega, by omega⟩ hs5
  obtain ⟨w3, hw3, hw3v⟩ := Number.exists_normalized_int_mul_pow (F : ℤ) ls ⟨by omega, by omega⟩ hs
  obtain ⟨w4, hw4, hw4v⟩ := Number.exists_normalized_int_mul_pow (C : ℤ) ls ⟨by omega, by omega⟩ hs
  have hFq : (F : ℚ) * 100000 ≤ (K : ℚ) * R := by exact_mod_cast hFle
  have hCq : (K : ℚ) * R ≤ (C : ℚ) * 100000 := by exact_mod_cast hCge
  have hy_lo : (F : ℚ) * 10 ^ (ls + 5) ≤ y.toRat := by
    have := hR1.ge_of_le hmode w1 hw1 (by
      rw [hw1v, hK, hRBv, hpow5]; push_cast; nlinarith)
    rw [hw1v] at this; push_cast at this; exact this
  have hy_hi : y.toRat ≤ (C : ℚ) * 10 ^ (ls + 5) := by
    have := hR1.le_of_ge hmode w2 hw2 (by
      rw [hw2v, hK, hRBv, hpow5]; push_cast; nlinarith)
    rw [hw2v] at this; push_cast at this; exact this
  have hraw_lo : (F : ℚ) * 10 ^ ls ≤ raw.toRat := by
    have := hR2.ge_of_le hmode w3 hw3 (by
      rw [hw3v, hUv, le_div_iff₀ (by norm_num : (0 : ℚ) < 100000)]; push_cast; rw [hpow5] at hy_lo; linarith)
    rw [hw3v] at this; push_cast at this; exact this
  have hraw_hi : raw.toRat ≤ (C : ℚ) * 10 ^ ls := by
    have := hR2.le_of_ge hmode w4 hw4 (by
      rw [hw4v, hUv, div_le_iff₀ (by norm_num : (0 : ℚ) < 100000)]; push_cast; rw [hpow5] at hy_hi; linarith)
    rw [hw4v] at this; push_cast at this; exact this
  have hraw0 : 0 ≤ raw.toRat := le_trans (by positivity) hraw_lo
  have hraw_hi' : K < 10 ^ 16 → raw.toRat ≤ (((K * R + 99) / 100 : ℕ) : ℚ) * 10 ^ (ls - 3) := by
    intro hK16
    set D := (K * R + 99) / 100 with hD
    have hDge : K * R ≤ D * 100 := by omega
    have hDlt : D < 2 ^ 63 := by
      have : K * R ≤ (10 ^ 16 - 1) * 10000 := Nat.mul_le_mul (by omega) hR
      omega
    have hpow2 : (10 : ℚ) ^ (ls + 2) = 100 * 10 ^ ls := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    have hpow3 : (10 : ℚ) ^ (ls + 2) = 100000 * 10 ^ (ls - 3) := by
      rw [show ls + 2 = (ls - 3) + 5 by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    obtain ⟨w5, hw5, hw5v⟩ := Number.exists_normalized_int_mul_pow (D : ℤ) (ls + 2) ⟨by omega, by omega⟩ hs2
    obtain ⟨w6, hw6, hw6v⟩ := Number.exists_normalized_int_mul_pow (D : ℤ) (ls - 3) ⟨by omega, by omega⟩ hs3
    have hDq : (K : ℚ) * R ≤ (D : ℚ) * 100 := by exact_mod_cast hDge
    have hy5 : y.toRat ≤ (D : ℚ) * 10 ^ (ls + 2) := by
      have := hR1.le_of_ge hmode w5 hw5 (by rw [hw5v, hK, hRBv, hpow2]; push_cast; nlinarith)
      rw [hw5v] at this; push_cast at this; exact this
    have := hR2.le_of_ge hmode w6 hw6 (by
      rw [hw6v, hUv, div_le_iff₀ (by norm_num : (0 : ℚ) < 100000)]; push_cast; rw [hpow3] at hy5; linarith)
    rw [hw6v] at this; push_cast at this; exact this
  -- the downward rounding at LoanScale lands on the grid, between the floor and `raw`
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at h
    have hls0 := hint (by rw [hnt]; rfl)
    obtain ⟨hgf, ⟨m, hm⟩, -, hdown⟩ := STAmount.roundToNumericType_int_grid _ rfl raw _ .downward _ hrawN hraw0
      (Or.inr (Or.inr rfl)) h
    rw [hls0] at hraw_lo hraw_hi' ⊢
    rw [hls0] at hraw_hi
    refine ⟨hgf.lower F hraw_lo, (hdown rfl).trans hraw_hi, fun hK16 => (hdown rfl).trans (hraw_hi' hK16), m,
      by rw [hm, zpow_zero, mul_one]⟩
  | fractional =>
    rw [hnt] at h
    -- the 16-digit fee is at most `10^15` LoanScale units, so its exponent is at most LoanScale
    have hC15 : C ≤ 10 ^ 15 := by
      have hK16 := hfr hnt
      have : K * R ≤ (10 ^ 16 - 1) * 10000 := Nat.mul_le_mul (by omega) hR
      omega
    have hexp : ∀ st, STAmount.ofNumber .fractional raw .downward = .ok st → st.mValue ≠ 0 →
        st.exponent ≤ ls := by
      intro st hst hst0
      obtain ⟨hc, -, -, -, hdown⟩ := STAmount.ofNumber_frac_stage raw _ st hrawN hraw0 (Or.inr (Or.inr rfl))
        hst hst0
      have hsle := hdown rfl
      have hst0' : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hrawN
        (Number.negative_false_of_nonneg raw hrawN hraw0) hst
      have habs := STAmount.abs_toRat st
      rw [abs_of_nonneg hst0'] at habs
      by_contra hc'
      push Not at hc'
      have h1 : (10 : ℚ) ^ (15 : ℕ) * 10 ^ (ls + 1) ≤ st.toRat := by
        rw [habs]
        exact mul_le_mul (by exact_mod_cast hc.mant_lo) (zpow_le_zpow_right₀ (by norm_num) hc')
          (by positivity) (by positivity)
      have h2 : (C : ℚ) * 10 ^ ls ≤ (10 : ℚ) ^ (15 : ℕ) * 10 ^ ls :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hC15) hp10.le
      have h3 : (10 : ℚ) ^ (15 : ℕ) * 10 ^ (ls + 1) = 10 * ((10 : ℚ) ^ (15 : ℕ) * 10 ^ ls) := by
        rw [zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
      rw [h3] at h1
      have h5 : (0 : ℚ) < (10 : ℚ) ^ (15 : ℕ) * 10 ^ ls := by positivity
      linarith [h1.trans (hsle.trans (hraw_hi.trans h2))]
    obtain ⟨hgf, hm, -, hdown⟩ := STAmount.roundToNumericType_frac_grid raw _ .downward ls hrawN hraw0
      (Or.inr (Or.inr rfl)) ⟨by omega, hls.2⟩ hexp h
    exact ⟨hgf.lower F hraw_lo, (hdown rfl).trans hraw_hi, fun hK16 => (hdown rfl).trans (hraw_hi' hK16), hm⟩

/-- Proof body of `create_managementFee_lower_bound`. -/
lemma Loan.create_managementFee_lower_bound_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.principalOutstanding) -
      r.loan'.toExact.managementFeeOutstanding < 10 ^ r.loan'.toExact.loanScale := by
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, amount, amountSt, ti, -, -, -, -, -, -, -, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hFR : r.loan'.broker.managementFeeRate = broker.managementFeeRate := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.managementFeeRate = _; rw [hl]
    show broker'.toRawLoanBroker.managementFeeRate = _; rw [hb]
  show (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat) -
      r.loan'.managementFeeOutstanding.toRat < 10 ^ r.loan'.loanScale
  rw [hFR, hTV, hPO, hMF, hLS]
  set R := broker.managementFeeRate.toNat with hR
  have hR10 : R ≤ 10000 := broker.managementFeeRate_le
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  have hpoN : props.principalOutstanding.isNormalized := hPO ▸ hwf.principalOutstanding_norm
  have hmf0 : 0 ≤ props.managementFeeOutstanding.toRat := by
    have := hex.managementFeeOutstanding_nonneg; simp only [RawLoan.toExact] at this; rwa [hMF] at this
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  obtain ⟨a, ha, hav⟩ := hexg.totalValueOutstanding_atExponent
  obtain ⟨b, hbd, hbv⟩ := hexg.principalOutstanding_atExponent
  simp only [RawLoan.toExact] at ha hav hbd hbv
  rw [hTV, hLS] at hav
  rw [hPO, hLS] at hbv
  have hbound := NumericType.mantissaBound_le r.loan'.broker.numericType
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  have hs : minExponent + 18 ≤ props.loanScale ∧ props.loanScale ≤ maxExponent - 1 := by
    have h1 := hrange.1; have h2 := hrange.2
    unfold cMinOffset at h1; unfold cMaxOffset at h2; unfold minExponent maxExponent; omega
  have hti_v := Number.operator_sub_toRat_of_grid _ _ ti a b props.loanScale htvN hpoN
    (by rw [hav]; norm_cast) (by rw [hbv]; norm_cast) (by omega) hs hti
  rw [hav, hbv]
  have hgap : (0 : ℚ) < 10 ^ props.loanScale := by positivity
  by_cases hab : a ≤ b
  · -- no interest: the fee share is not positive
    have h1 : ((a : ℚ) * 10 ^ props.loanScale - (b : ℚ) * 10 ^ props.loanScale) ≤ 0 := by
      have : (a : ℚ) ≤ b := by exact_mod_cast hab
      nlinarith
    have h2 : (R : ℚ) / 100000 * ((a : ℚ) * 10 ^ props.loanScale - (b : ℚ) * 10 ^ props.loanScale) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    linarith
  push Not at hab
  set K := a - b with hK
  have hKv : ti.toRat = (K : ℚ) * 10 ^ props.loanScale := by
    rw [hti_v, hK]; push_cast [Nat.cast_sub hab.le]; ring
  have hIv : (a : ℚ) * 10 ^ props.loanScale - (b : ℚ) * 10 ^ props.loanScale =
      (K : ℚ) * 10 ^ props.loanScale := by
    rw [hK]; push_cast [Nat.cast_sub hab.le]; ring
  rw [hIv]
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  obtain ⟨hmf_lo, -, -, -⟩ := computeManagementFee_bounds broker.numericType ti _ K broker.managementFeeRate
    props.loanScale (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) hKv (by omega) hR10
    ⟨hlo, hhi⟩ hint (fun hnt => by rw [hNT, hnt] at ha; show a - b < 10 ^ 16; exact lt_of_le_of_lt (Nat.sub_le a b) ha)
    hmfo
  -- the share minus its floor is at most `99999` of `10^5` parts of a unit
  set F := K * R / 100000 with hF
  have hmod : K * R ≤ F * 100000 + 99999 := by
    have := Nat.div_add_mod (K * R) 100000
    have := Nat.mod_lt (K * R) (show 100000 > 0 by norm_num)
    omega
  have hmodq : (K : ℚ) * R ≤ (F : ℚ) * 100000 + 99999 := by exact_mod_cast hmod
  have h1 : (R : ℚ) / 100000 * ((K : ℚ) * 10 ^ props.loanScale) ≤
      ((F : ℚ) + 99999 / 100000) * 10 ^ props.loanScale := by
    have : (R : ℚ) / 100000 * ((K : ℚ) * 10 ^ props.loanScale) =
        ((K : ℚ) * R / 100000) * 10 ^ props.loanScale := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ hp10.le
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 100000)]
    linarith
  have h2 : ((F : ℚ) + 99999 / 100000) * 10 ^ props.loanScale =
      (F : ℚ) * 10 ^ props.loanScale + 99999 / 100000 * 10 ^ props.loanScale := by ring
  linarith

end XRPL.Model.Lending
