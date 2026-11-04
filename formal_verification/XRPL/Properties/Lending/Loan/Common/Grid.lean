import XRPL.Properties.Lending.Loan.Common.ManageRoundToExponent
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero

/-! # Amounts on a grid

`Number.OnGrid s x` says `x` is a whole number of `10^s` units. Sums, differences, minima, maxima and roundings at
`s` stay on the grid, and an amount of at least `10^18` units is always on it. -/

namespace XRPL.Model.Protocol

/-- A `Number` rounding to nearest, upward or downward never jumps over a value it can represent. -/
lemma Number.RoundsToRepresentable.ge_of_le {r : Number} {t : ℚ} {mode : rounding_mode}
    (hR : r.RoundsToRepresentable t mode)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (w : Number) (hw : w.isNormalized) (hwt : w.toRat ≤ t) : w.toRat ≤ r.toRat := by
  rcases hmode with rfl | rfl | rfl
  · rcases hR with ⟨n, hn, hr⟩ | ⟨n, hn, hr⟩
    · rw [hr]; exact Number.lower_tight t n hn w hw hwt
    · rw [hr]; exact hwt.trans (Number.le_upper t n hn)
  · obtain ⟨n, hn, hr⟩ := hR
    rw [hr]; exact hwt.trans (Number.le_upper t n hn)
  · obtain ⟨n, hn, hr⟩ := hR
    rw [hr]; exact Number.lower_tight t n hn w hw hwt

/-- The other side: never above a representable value at or above the truth. -/
lemma Number.RoundsToRepresentable.le_of_ge {r : Number} {t : ℚ} {mode : rounding_mode}
    (hR : r.RoundsToRepresentable t mode)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (w : Number) (hw : w.isNormalized) (hwt : t ≤ w.toRat) : r.toRat ≤ w.toRat := by
  rcases hmode with rfl | rfl | rfl
  · rcases hR with ⟨n, hn, hr⟩ | ⟨n, hn, hr⟩
    · rw [hr]; exact (Number.lower_le t n hn).trans hwt
    · rw [hr]; exact Number.upper_tight t n hn w hw hwt
  · obtain ⟨n, hn, hr⟩ := hR
    rw [hr]; exact Number.upper_tight t n hn w hw hwt
  · obtain ⟨n, hn, hr⟩ := hR
    rw [hr]; exact (Number.lower_le t n hn).trans hwt

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- `x` is a normalized whole number of `10^s` units. -/
def Number.OnGrid (s : Int) (x : Number) : Prop :=
  x.isNormalized ∧ ∃ k : ℤ, x.toRat = (k : ℚ) * 10 ^ s

lemma Number.OnGrid.zero (s : Int) : Number.OnGrid s Number.zero :=
  ⟨Number.zero_isNormalized, 0, by rw [Number.toRat_zero]; simp⟩

/-- An amount of at least `10^18` units is on the grid: its 19-digit mantissa sits at an exponent of at least
`s`. -/
lemma Number.OnGrid.of_large {s : Int} {x : Number} (hx : x.isNormalized)
    (h : (10 : ℚ) ^ (18 : ℕ) * 10 ^ s ≤ |x.toRat|) : Number.OnGrid s x := by
  refine ⟨hx, ?_⟩
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have habs := abs_toRat_eq x
  rcases hx with hz | ⟨-, hmax, -, -, -⟩
  · subst hz
    rw [Number.toRat_zero, abs_zero] at h
    have : (0 : ℚ) < (10 : ℚ) ^ (18 : ℕ) * 10 ^ s := by positivity
    linarith
  · -- the mantissa is below `10^19`, so the exponent is at least `s`
    have hm : (x.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by
      have h1 : x.mantissa_.toNat ≤ largeRange.max.toNat := UInt64.le_iff_toNat_le.mp hmax
      rw [largeRange_max_val] at h1
      have : x.mantissa_.toNat < 10 ^ 19 := by omega
      exact_mod_cast this
    have he : s ≤ x.exponent_ := by
      by_contra hlt
      push Not at hlt
      have h1 : (10 : ℚ) ^ x.exponent_ ≤ (10 : ℚ) ^ (s - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (s - 1) * 10 = 10 ^ s := by
        rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
      have hpe : (0 : ℚ) < (10 : ℚ) ^ x.exponent_ := zpow_pos (by norm_num) _
      have h3 : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ < (10 : ℚ) ^ (19 : ℕ) * 10 ^ (s - 1) :=
        lt_of_lt_of_le (mul_lt_mul_of_pos_right hm hpe) (mul_le_mul_of_nonneg_left h1 (by positivity))
      have h4 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ (s - 1) = (10 : ℚ) ^ (18 : ℕ) * 10 ^ s := by
        rw [← h2]; ring
      rw [habs] at h
      linarith
    have hsplit : (10 : ℚ) ^ x.exponent_ = (10 : ℚ) ^ (x.exponent_ - s).toNat * 10 ^ s := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
        sub_add_cancel]
    cases hneg : x.negative_
    · refine ⟨(x.mantissa_.toNat * 10 ^ (x.exponent_ - s).toNat : ℕ), ?_⟩
      rw [Number.toRat_of_nonneg x hneg, hsplit]; push_cast; ring
    · refine ⟨-(x.mantissa_.toNat * 10 ^ (x.exponent_ - s).toNat : ℕ), ?_⟩
      rw [Number.toRat_of_neg x hneg, hsplit]; push_cast; ring

/-- A rounding of a value at least `10^18` units away from zero is at least that far. -/
private lemma Number.RoundsToRepresentable.large {r : Number} {t : ℚ} (s : Int)
    (hR : r.RoundsToRepresentable t .to_nearest) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (ht : (10 : ℚ) ^ (18 : ℕ) * 10 ^ s ≤ |t|) : (10 : ℚ) ^ (18 : ℕ) * 10 ^ s ≤ |r.toRat| := by
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 18) s (by constructor <;> norm_num) hs
  obtain ⟨w', hw', hwv'⟩ := Number.exists_normalized_int_mul_pow (-10 ^ 18) s (by constructor <;> norm_num) hs
  push_cast at hwv hwv'
  rcases le_abs'.mp ht with hneg | hpos
  · have := hR.le_of_ge (Or.inl rfl) w' hw' (by rw [hwv']; linarith)
    rw [hwv'] at this
    rw [abs_of_nonpos (by have : (0 : ℚ) < (10 : ℚ) ^ (18 : ℕ) * 10 ^ s := by positivity
                          linarith)]
    linarith
  · have := hR.ge_of_le (Or.inl rfl) w hw (by rw [hwv]; linarith)
    rw [hwv] at this
    rw [abs_of_nonneg (by have : (0 : ℚ) < (10 : ℚ) ^ (18 : ℕ) * 10 ^ s := by positivity
                          linarith)]
    linarith

/-- A rounding of a whole number of units is on the grid: exact below `2^63` units, too large otherwise. -/
private lemma Number.OnGrid.of_rounds {r : Number} {s : Int} {k : ℤ} (hr : r.isNormalized)
    (hR : r.RoundsToRepresentable ((k : ℚ) * 10 ^ s) .to_nearest) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) :
    Number.OnGrid s r := by
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  by_cases hk : -2 ^ 63 < k ∧ k < 2 ^ 63
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow k s hk hs
    exact ⟨hr, k, Number.roundsToRepresentable_eq r _ hR w hw hwv⟩
  · apply Number.OnGrid.of_large hr
    apply Number.RoundsToRepresentable.large s hR hs
    rw [abs_mul, abs_of_pos hp]
    apply mul_le_mul_of_nonneg_right _ hp.le
    have : (10 : ℤ) ^ 18 ≤ |k| := by
      rw [not_and_or] at hk
      rcases hk with h | h <;> [rw [abs_of_neg (by omega)]; rw [abs_of_nonneg (by omega)]] <;> omega
    exact_mod_cast this

lemma Number.OnGrid.add {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hok : x.operator_add y .to_nearest = .ok d) :
    Number.OnGrid s d := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb⟩ := hy
  have hR := operator_add_rounded_to_nearest x y d hxn hyn hok
  rw [ha, hb, ← add_mul, show (a : ℚ) + b = ((a + b : ℤ) : ℚ) by push_cast; ring] at hR
  exact Number.OnGrid.of_rounds (operator_add_isNormalized_to_nearest_sz x y d hxn hyn hok) hR hs

lemma Number.OnGrid.sub {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hok : x.operator_sub y .to_nearest = .ok d) :
    Number.OnGrid s d := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb⟩ := hy
  have hR := operator_sub_rounded_to_nearest x y d hxn hyn hok
  rw [ha, hb, ← sub_mul, show (a : ℚ) - b = ((a - b : ℤ) : ℚ) by push_cast; ring] at hR
  exact Number.OnGrid.of_rounds (operator_sub_isNormalized_to_nearest_sz x y d hxn hyn hok) hR hs

lemma Number.OnGrid.neg {s : Int} {x : Number} (hx : Number.OnGrid s x) : Number.OnGrid s x.operator_neg := by
  obtain ⟨hxn, a, ha⟩ := hx
  exact ⟨Number.operator_neg_isNormalized x hxn, -a, by rw [Number.toRat_neg, ha]; push_cast; ring⟩

lemma Number.OnGrid.min {s : Int} {x y : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y) :
    Number.OnGrid s (Number.min x y) := by
  unfold Number.min; split <;> assumption

lemma Number.OnGrid.max {s : Int} {x y : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y) :
    Number.OnGrid s (Number.max x y) := by
  unfold Number.max; split <;> assumption

lemma Number.OnGrid.clamp {s : Int} {x lo hi : Number} (hx : Number.OnGrid s x) (hlo : Number.OnGrid s lo)
    (hhi : Number.OnGrid s hi) : Number.OnGrid s (Number.clamp x lo hi) := by
  unfold Number.clamp; split
  · exact hlo
  · split <;> assumption

/-- An integral `ofNumber` amount holds at most `2^63 - 1` units: its magnitude went through `to_rep`. -/
private lemma STAmount.ofNumber_integral_small (nt : NumericType) (x : Number) (mode : rounding_mode)
    (st : STAmount) (hi : nt.isIntegral = true) (hof : STAmount.ofNumber nt x mode = .ok st) :
    st.mValue.toNat ≤ 2 ^ 63 - 1 := by
  obtain ⟨hc, -⟩ := STAmount.ofNumber_integral_canonical nt x mode st hi hof
  unfold STAmount.ofNumber at hof
  rw [if_pos hi] at hof
  have hwneg : (if decide (x.signum < 0) = true then x.operator_neg else x).negative_ = false := by
    rw [Number.signum_neg_decide]
    cases hn : x.negative_
    · simp [hn]
    · simp only [if_true]
      unfold Number.operator_neg
      split
      · rfl
      · simp [hn]
  cases hrep : (if decide (x.signum < 0) = true then x.operator_neg else x).to_rep mode with
  | error e => rw [hrep] at hof; cases hof
  | ok iv =>
    rw [hrep] at hof
    simp only at hof
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range _ mode iv hwneg hrep
    have hval := toUInt64_toNat_le_maxRep iv hnn hle
    have hexact := STAmount.canonicalize_integral_toRat
      (STAmount.unchecked nt iv.toUInt64 0 (decide (x.signum < 0))) st mode hi rfl hval hof
    rw [STAmount.IntegralCanonical.toRat_eq_signedDrops st hc, STAmount.toRat_of_offset_zero _ rfl] at hexact
    have habs : st.mValue.toNat = iv.toUInt64.toNat := by
      have := congrArg (fun q : ℚ => |q|) hexact
      simp only [STAmount.signedDrops, STAmount.unchecked] at this
      split at this <;> split at this <;>
        simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Nat.cast_inj] at this <;> exact_mod_cast this
    rw [habs]
    rw [maxRep_val] at hval
    omega

/-- The `Number` of an integral `ofNumber` amount is an integer. -/
private lemma STAmount.toNumber_integral_int (nt : NumericType) (x : Number) (mode : rounding_mode) (st : STAmount)
    (T : Number) (hi : nt.isIntegral = true) (hof : STAmount.ofNumber nt x mode = .ok st)
    (h : st.toNumber mode = .ok T) : ∃ k : ℤ, T.toRat = k := by
  obtain ⟨hc, -⟩ := STAmount.ofNumber_integral_canonical nt x mode st hi hof
  obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st mode hc
    (STAmount.ofNumber_integral_small nt x mode st hi hof)
  rw [hsn, Except.ok.injEq] at h
  subst h
  exact ⟨st.signedDrops, by rw [hv, STAmount.IntegralCanonical.toRat_eq_signedDrops st hc]⟩

/-- A rounding at the grid's exponent is on the grid, for an amount of either sign. An integral amount
needs an exponent of at most zero. -/
lemma STAmount.roundToNumericType_onGrid (nt : NumericType) (x T : Number) (mode : rounding_mode) (s : Int)
    (hs : -81 ≤ s ∧ s ≤ 80) (hint : nt.isIntegral = true → s ≤ 0)
    (h : STAmount.roundToNumericType nt x mode (some s) = .ok T) : Number.OnGrid s T := by
  have hTn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h
  refine ⟨hTn, ?_⟩
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber nt x mode with
  | error e => rw [hof] at h; cases h
  | ok st =>
    rw [hof] at h
    simp only at h
    by_cases hi : nt.isIntegral = true
    · -- an integral amount converts to an integer, a whole number of units at `s ≤ 0`
      obtain ⟨hc, hnt⟩ := STAmount.ofNumber_integral_canonical nt x mode st hi hof
      have hsti : st.integral = true := hc.is_integral
      rw [if_pos hsti] at h
      obtain ⟨k, hk⟩ := STAmount.toNumber_integral_int nt x mode st T hi hof h
      have hs0 := hint hi
      refine ⟨k * 10 ^ (-s).toNat, ?_⟩
      rw [hk]
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
        neg_add_cancel, zpow_zero, mul_one]
    · have hnt : nt = .fractional := by
        cases nt with
        | integral _ _ _ _ => exact absurd rfl hi
        | fractional => rfl
      subst hnt
      have hfc := STAmount.ofNumber_fractional_fczr x mode st hof
      have hsti : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
      rw [if_neg (by rw [hsti]; decide)] at h
      cases hr : STAmount.roundToExponent st s mode with
      | error e => rw [hr] at h; cases h
      | ok r =>
        rw [hr] at h
        simp only at h
        have hrc := STAmount.roundToExponent_fczr st r s mode hfc hr
        have hrint : r.integral = false := by unfold STAmount.integral; rw [hrc.1]; rfl
        rcases hrc.2 with hrcan | hr0
        · -- the rounded amount converts exactly, and it is a grid point
          obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrcan
          rw [hsn, Except.ok.injEq] at h
          subst h
          rcases hfc.2 with hstc | hst0
          · have hR := STAmount.roundToExponent_rounded_of_scale st r s mode hstc hs.1 hs.2 hr
            unfold RoundsToRepresentableAt at hR
            rw [hv]
            cases mode with
            | to_nearest =>
              rcases hR with h1 | h1
              · exact ⟨_, h1⟩
              · exact ⟨_, h1⟩
            | upward => exact ⟨_, hR⟩
            | downward => exact ⟨_, hR⟩
            | towards_zero => dsimp only at hR; exact ⟨_, hR⟩
          · -- a zero amount rounds to itself
            have hz : st.isZero = true := by unfold STAmount.isZero; simp [hst0]
            rw [STAmount.roundToExponent_eq_self st s mode (Or.inr (Or.inl hz)), Except.ok.injEq] at hr
            subst hr
            exact absurd hst0 (by have := hrcan.mant_lo; intro h0; rw [h0] at this; simp at this)
        · rw [STAmount.toNumber_zero_fractional r mode hrint hr0, Except.ok.injEq] at h
          subst h
          exact ⟨0, by rw [Number.toRat_zero]; simp⟩

/-- A sum of two grid points within `2^63` units is exact. -/
lemma Number.add_exact_of_grid {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hlo : -(2 ^ 63 * (10 : ℚ) ^ s) < x.toRat + y.toRat) (hhi : x.toRat + y.toRat < 2 ^ 63 * (10 : ℚ) ^ s)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hok : x.operator_add y .to_nearest = .ok d) :
    d.toRat = x.toRat + y.toRat := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, c, hc⟩ := hy
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have hsum : x.toRat + y.toRat = ((a + c : ℤ) : ℚ) * 10 ^ s := by rw [ha, hc]; push_cast; ring
  have h1 : -2 ^ 63 < a + c := by
    have : ((-2 ^ 63 : ℤ) : ℚ) * 10 ^ s < ((a + c : ℤ) : ℚ) * 10 ^ s := by rw [← hsum]; push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have h2 : a + c < 2 ^ 63 := by
    have : ((a + c : ℤ) : ℚ) * 10 ^ s < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ s := by rw [← hsum]; push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  rw [Number.operator_add_toRat_of_grid x y d a c s hxn hyn ha hc ⟨h1, h2⟩ hs hok, hsum]

/-- A sum of two grid amounts below `2^63` units is exact, with the bound on its absolute value. -/
lemma Number.OnGrid.add_toRat {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hb : |x.toRat + y.toRat| < 2 ^ 63 * 10 ^ s)
    (h : x.operator_add y .to_nearest = .ok d) : d.toRat = x.toRat + y.toRat :=
  Number.add_exact_of_grid hx hy (abs_lt.mp hb).1 (abs_lt.mp hb).2 hs h

/-- A difference of two grid amounts below `2^63` units is exact. -/
lemma Number.OnGrid.sub_toRat {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hb : |x.toRat - y.toRat| < 2 ^ 63 * 10 ^ s)
    (h : x.operator_sub y .to_nearest = .ok d) : d.toRat = x.toRat - y.toRat := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb'⟩ := hy
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have e : x.toRat - y.toRat = ((a - b : ℤ) : ℚ) * 10 ^ s := by rw [ha, hb']; push_cast; ring
  have hab : |((a - b : ℤ) : ℚ)| < 2 ^ 63 := by
    rw [e, abs_mul, abs_of_pos hp] at hb
    exact lt_of_mul_lt_mul_right hb hp.le
  have hab' : |a - b| < 2 ^ 63 := by exact_mod_cast hab
  rw [Number.operator_sub_toRat_of_grid x y d a b s hxn hyn ha hb' (abs_lt.mp hab') hs h, ← e]

/-- A grid amount of at least zero is a whole number of units. -/
lemma Number.OnGrid.units {s : Int} {x : Number} (hx : Number.OnGrid s x) (h0 : 0 ≤ x.toRat) :
    ∃ n : ℕ, x.toRat = (n : ℚ) * 10 ^ s := by
  obtain ⟨-, k, hk⟩ := hx
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by rw [hk] at h0; exact_mod_cast nonneg_of_mul_nonneg_left h0 hp
  exact ⟨k.toNat, by rw [hk, show ((k.toNat : ℕ) : ℚ) = (k : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk0]⟩

/-- `10^(16 + b)` is `10^16` base units of `10^b`. -/
lemma open_line_eq (b : Int) : (10 : ℚ) ^ (16 + b) = 10 ^ 16 * 10 ^ b := by
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num

end XRPL.Model.Lending
