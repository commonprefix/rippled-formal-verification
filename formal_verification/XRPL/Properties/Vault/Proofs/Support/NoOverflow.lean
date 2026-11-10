import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Common.Checked
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.Common.TenthBipsTotality
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Vault.Proofs.Support.NormalizeFacts
import XRPL.Properties.Vault.Proofs.Support.IOUTotality
import XRPL.Properties.Vault.Proofs.Support.VaultBalances

/-! # Operations that never overflow

Only a product or a sum whose exponent leaves the `Number` range, an integer conversion past `int64` and an IOU
amount past the IOU ceiling raise `Error.overflow`. Normalizing, truncating and dividing never do. -/

namespace XRPL.Model.Protocol

/-- Split every `match` and `if` of a `_ ≠ .error .overflow` goal and close each branch with the lemmas for the
calls it makes. -/
macro "split_ne_overflow" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (repeat' (first | split | extract_lets)
             all_goals (try (intro hc; cases hc))
             all_goals first
               | (simp only [$args,*, ne_eq, not_false_eq_true]; done)
               | (simp only [$args,*] at *; done)
               | simp_all [$args,*]))

lemma _root_.UInt64.toInt64Checked_ne_overflow (a : UInt64) : a.toInt64Checked ≠ .error .overflow :=
  fun h => nomatch UInt64.toInt64Checked_eq_error h

lemma _root_.Int64.toUInt64Checked_ne_overflow (a : Int64) : a.toUInt64Checked ≠ .error .overflow :=
  fun h => nomatch Int64.toUInt64Checked_eq_error h

lemma _root_.Int64.negChecked_ne_overflow (a : Int64) : a.negChecked ≠ .error .overflow :=
  fun h => nomatch Int64.negChecked_eq_error h

lemma Guard.doRoundUp_ne_overflow (g : Guard) (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : internalrep) (mode : rounding_mode) (location : Error)
    (hloc : location ≠ .overflow) :
    g.doRoundUp negative mantissa exponent minMantissa maxMantissa mode location ≠ .error .overflow := by
  refine (Guard.doRoundUp_refines _ _ _ _ _ _ _ _).ne_error ?_ (by decide)
  unfold Guard.doRoundUpSpec
  have key : ∀ (c : Prop) [Decidable c] (r : RoundResult),
      (if c then (.error location : Except Error RoundResult) else .ok r) ≠ .error .overflow := by
    intro c _ r; split <;> simp [hloc]
  exact key _ _

lemma doNormalize_scaleDown_ne_overflow (maxMantissa m : UInt64) (e : Int) (g : Guard) :
    doNormalize_scaleDown maxMantissa m e g ≠ .error .overflow := by
  fun_induction doNormalize_scaleDown maxMantissa m e g <;> simp_all

lemma doNormalize_scaleDown128_ne_overflow (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard) :
    doNormalize_scaleDown128 maxMantissa m e g ≠ .error .overflow := by
  rw [doNormalize_scaleDown128_eq_spec]
  fun_induction doNormalize_scaleDown128Spec maxMantissa m e g <;> simp_all

lemma doNormalize_capAtMaxRep_ne_overflow (m : UInt64) (e : Int) (g : Guard) :
    doNormalize_capAtMaxRep m e g ≠ .error .overflow := by
  unfold doNormalize_capAtMaxRep
  split
  · split <;> simp
  · simp

lemma doNormalize_ne_overflow (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) :
    doNormalize negative mantissa exponent minMantissa maxMantissa mode ≠ .error .overflow := by
  refine (doNormalize_refines _ _ _ _ _ _).ne_error ?_ (by decide)
  unfold doNormalizeSpec
  split
  · simp
  dsimp only
  split_ne_overflow [doNormalize_scaleDown_ne_overflow, doNormalize_capAtMaxRep_ne_overflow,
    Guard.doRoundUp_ne_overflow]

lemma doNormalize128_ne_overflow (negative : Bool) (mantissa : UInt128) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) (stickyTail : Bool) :
    doNormalize128 negative mantissa exponent minMantissa maxMantissa mode stickyTail ≠ .error .overflow := by
  rw [doNormalize128_eq_spec]
  unfold doNormalize128Spec
  split
  · simp
  dsimp only
  split_ne_overflow [← doNormalize_scaleDown128_eq_spec, doNormalize_scaleDown128_ne_overflow,
    doNormalize_capAtMaxRep_ne_overflow, Guard.doRoundUp_ne_overflow]

lemma Number.normalize_ne_overflow (n : Number) (minMant maxMant : UInt64) (mode : rounding_mode) :
    n.normalize minMant maxMant mode ≠ .error .overflow :=
  doNormalize_ne_overflow _ _ _ _ _ _

lemma Number.normalizeToRange_ne_overflow (n : Number) (minMant maxMant : UInt64) (mode : rounding_mode) :
    n.normalizeToRange minMant maxMant mode ≠ .error .overflow := by
  unfold Number.normalizeToRange
  split
  · rename_i e he
    intro h; cases h; exact doNormalize_ne_overflow _ _ _ _ _ _ he
  · exact bind_ne_error (UInt64.toInt64Checked_ne_overflow _) fun _ =>
      bind_ne_error (ite_ne_error (Int64.negChecked_ne_overflow _) nofun) fun _ => nofun

lemma Number.normalized_ne_overflow (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMant maxMant : UInt64) (mode : rounding_mode) :
    Number.normalized negative mantissa exponent minMant maxMant mode ≠ .error .overflow :=
  Number.normalize_ne_overflow _ _ _ _

lemma Number.from_rep_ne_overflow (mantissa : Int64) (exponent : Int) (minMant maxMant : UInt64)
    (mode : rounding_mode) :
    Number.from_rep mantissa exponent minMant maxMant mode ≠ .error .overflow :=
  Number.normalized_ne_overflow _ _ _ _ _ _

lemma Number.truncate_ne_overflow (n : Number) : n.truncate ≠ .error .overflow := by
  unfold Number.truncate
  split_ne_overflow [Number.normalized_ne_overflow]

lemma Number.operator_div_ne_overflow (x y : Number) (mode : rounding_mode) :
    x.operator_div y mode ≠ .error .overflow := by
  unfold Number.operator_div
  split
  · simp
  split
  · exact nofun
  intro h
  rcases hq : divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_ with e | ⟨zm, ze, d⟩
  · rw [hq, err_bind] at h; cases h; exact nomatch divQuotient128_eq_error hq
  · rw [hq, ok_bind] at h; exact doNormalize128_ne_overflow _ _ _ _ _ _ _ h


lemma Number.to_rep_exponent_zero_ok (n : Number) (mode : rounding_mode) (hexp : n.exponent = 0) :
    ∃ r, n.to_rep mode = .ok r := by
  rw [Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  simp only
  by_cases hz : (n.mantissa == 0) = true
  · exact ⟨0, by rw [if_pos hz]⟩
  rw [if_neg hz, if_neg (show ¬ n.exponent < 0 by omega), if_pos (show n.exponent ≥ 0 by omega)]
  have hgrow : ∀ d, growSpec d n.exponent = .ok d := fun d => by rw [growSpec, if_neg (by omega)]
  rw [hgrow]
  have hg : (if n.negative_ = true then Guard.new.set_negative else Guard.new).round mode = -2 := by
    split <;> exact clean_guard_round _ rfl rfl mode
  simp only [hg]
  exact ⟨_, by rw [if_neg (by simp)]⟩


lemma STAmount.checked_integral_ne_overflow (nt : NumericType) (hnt : nt.isIntegral = true) (v : UInt64) (neg : Bool)
    (mode : rounding_mode) (hv : v.toNat ≤ maxRep.toNat) :
    STAmount.checked nt v 0 neg mode ≠ .error .overflow := by
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_pos (show (STAmount.unchecked nt v 0 neg).integral = true from hnt)]
  split
  · simp
  split
  · simp
  have hexp : (Number.unchecked neg v 0).exponent = 0 := by
    unfold Number.exponent Number.unchecked
    rw [if_neg (show ¬ v > maxRep from by rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; omega)]
  obtain ⟨r, hr⟩ := Number.to_rep_exponent_zero_ok _ mode hexp
  simp only [STAmount.unchecked, IntAmount.ofNumber, hr]
  split <;> simp

lemma IOUAmount.ofMantissaExp_ne_overflow (m : Int64) (e : Int) (mode : rounding_mode) (hm : m ≠ Int64.minValue)
    (he : m ≠ 0 → minExponent + 18 ≤ e ∧ e ≤ 76) :
    IOUAmount.ofMantissaExp m e mode ≠ .error .overflow := by
  unfold IOUAmount.ofMantissaExp IOUAmount.normalize
  by_cases h0 : (m == 0) = true
  · rw [if_pos h0]; simp
  rw [if_neg h0]
  have hm0 : m ≠ 0 := by simpa using h0
  obtain ⟨he_lo, he_hi⟩ := he hm0
  obtain ⟨v, hv, hvval, hvn⟩ := Number.from_rep_exact m e mode hm he_lo (by unfold maxExponent at *; omega)
  simp only [hv]
  have hmi : m.toInt ≠ 0 := fun h => hm0 (Int64.toInt_inj.mp (by rw [h]; rfl))
  have hmlt : |(m.toInt : ℚ)| < 10 ^ 19 := by
    have h1 := Int64.le_toInt m
    have h2 := Int64.toInt_le m
    rw [abs_lt]; constructor
    · have : (-(2 : ℤ) ^ 63) ≤ m.toInt := by simpa using h1
      have : (-(10 : ℤ) ^ 19) < m.toInt := by omega
      exact_mod_cast this
    · have : m.toInt ≤ 2 ^ 63 - 1 := by simpa using h2
      have : m.toInt < (10 : ℤ) ^ 19 := by omega
      exact_mod_cast this
  have hmge : (1 : ℚ) ≤ |(m.toInt : ℚ)| := by
    have : (1 : ℤ) ≤ |m.toInt| := Int.one_le_abs hmi
    exact_mod_cast this
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hvabs : |v.toRat| = |(m.toInt : ℚ)| * 10 ^ e := by rw [hvval, abs_mul, abs_of_pos hp]
  have hv0 : v.mantissa_ ≠ 0 := by
    intro h0; rw [Number.toRat_eq_zero_of_mantissa_zero v h0, abs_zero] at hvabs; nlinarith
  have hvhi : v.exponent_ < e + 1 := by
    apply Number.exponent_lt_of_abs_lt v hvn hv0
    rw [hvabs, show e + 1 + 18 = 19 + e by ring, zpow_add₀ (by norm_num)]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hmlt) hp
  have hvlo : e - 19 < v.exponent_ := by
    apply Number.exponent_gt_of_abs_ge v hvn hv0
    rw [hvabs, show e - 19 + 19 = e by ring]
    nlinarith
  obtain ⟨hb_lo, hb_hi⟩ := hvn.mantissaBounds_nat hv0
  unfold IOUAmount.fromNumber
  cases hnr : v.normalizeToRange cMinValue cMaxValue mode with
  | error err =>
    simp only
    intro h; cases h; exact Number.normalizeToRange_ne_overflow _ _ _ _ hnr
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    have hr := normalizeToRange_16_exp_range v mode mant exp hb_lo hb_hi (by omega)
      (by unfold maxExponent at *; omega) hnr
    simp only
    rw [if_neg (by unfold cMaxOffset; omega)]
    split <;> simp


lemma STAmount.checked_fractional_ne_overflow (M : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hM : M.toNat < 2 ^ 63) (he : M ≠ 0 → minExponent + 18 ≤ e ∧ e ≤ 76) :
    STAmount.checked .fractional M e neg mode ≠ .error .overflow := by
  set s := STAmount.unchecked .fractional M e neg with hs
  have hint : ¬ s.integral = true := by simp [hs, STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have hsM : s.mValue.toNat < 2 ^ 63 := hM
  rw [STAmount.checked, ← hs]
  unfold STAmount.canonicalize
  rw [if_neg hint, STAmount.iou_of_lt mode hint hsM]
  have hsd := STAmount.signedDrops_toInt64_toInt_of_lt s hsM
  have hmin : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    rw [h] at hsd
    have : Int64.minValue.toInt = -2 ^ 63 := by decide
    rw [this] at hsd
    unfold STAmount.signedDrops at hsd
    split at hsd <;> omega
  have hne := IOUAmount.ofMantissaExp_ne_overflow _ s.mOffset mode hmin (fun h0 => by
    apply he
    intro hM0
    apply h0
    have : s.signedDrops = 0 := by unfold STAmount.signedDrops; simp [hs, STAmount.unchecked, hM0]
    apply Int64.toInt_inj.mp
    rw [hsd, this]; rfl)
  split
  · rename_i err herr
    intro h; cases h; exact hne herr
  · simp

/-- The magnitude `STAmount.ofNumber` converts is normalized, not negative, and has the value's size and exponent. -/
lemma Number.working_facts (n : Number) (hn : n.isNormalized) :
    (if n.negative_ = true then n.operator_neg else n).isNormalized ∧
      (if n.negative_ = true then n.operator_neg else n).negative_ = false ∧
      (if n.negative_ = true then n.operator_neg else n).toRat = |n.toRat| ∧
      (if n.negative_ = true then n.operator_neg else n).mantissa_ = n.mantissa_ ∧
      (n.mantissa_ ≠ 0 → (if n.negative_ = true then n.operator_neg else n).exponent_ = n.exponent_) := by
  by_cases h0 : n.mantissa_ = 0
  · have hz := Number.eq_zero_of_mantissa_zero n hn h0
    subst hz
    rw [if_neg (by decide)]
    exact ⟨hn, rfl, by rw [Number.toRat_zero, abs_zero], rfl, fun h => absurd h0 h⟩
  by_cases hneg : n.negative_ = true
  · simp only [hneg, if_true]
    refine ⟨Number.operator_neg_isNormalized n hn, ?_, ?_, Number.operator_neg_mantissa_of_ne n h0, fun _ => ?_⟩
    · rw [Number.operator_neg_negative_of_ne n h0, hneg]; rfl
    · rw [Number.toRat_neg, abs_of_neg]
      exact lt_of_le_of_ne (by
        have := Number.toRat_nonneg_of_nonnegative n.operator_neg (by
          rw [Number.operator_neg_negative_of_ne n h0, hneg]; rfl)
        rw [Number.toRat_neg] at this; linarith) (Number.toRat_ne_zero_of_mantissa_ne_zero n h0)
    · unfold Number.operator_neg; rw [if_neg (by simpa using h0)]
  · rw [if_neg hneg]
    have hnf : n.negative_ = false := by simpa using hneg
    exact ⟨hn, hnf, (abs_of_nonneg (Number.toRat_nonneg_of_nonnegative n hnf)).symm, rfl, fun _ => rfl⟩


/-- A normalized value below `10^200` in size has its exponent below `182`, or is zero. -/
lemma Number.exponent_le_of_size (n : Number) (hn : n.isNormalized) (h : |n.toRat| < 10 ^ (200 : ℤ)) :
    n.exponent_ + 22 ≤ maxExponent := by
  by_cases h0 : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn h0]
    show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  · have := Number.exponent_lt_of_abs_lt n hn h0 182 (by norm_num at h ⊢; exact h)
    unfold maxExponent; omega

/-- A normalized nonzero value below `10^200` in size has its exponent below `182`. -/
lemma Number.exponent_lt_of_size (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0)
    (h : |n.toRat| < 10 ^ (200 : ℤ)) : n.exponent_ < 182 :=
  Number.exponent_lt_of_abs_lt n hn h0 182 (by norm_num at h ⊢; exact h)

/-- A normalized nonzero value at least `10^-200` in size has its exponent above `-219`. -/
lemma Number.exponent_ge_of_size (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0)
    (h : (10 : ℚ) ^ (-200 : ℤ) ≤ |n.toRat|) : -219 < n.exponent_ :=
  Number.exponent_gt_of_abs_ge n hn h0 (-219) (by norm_num at h ⊢; exact h)

lemma Number.operator_add_ok_of_size (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ (200 : ℤ)) (hyl : |y.toRat| < 10 ^ (200 : ℤ)) :
    ∃ r, x.operator_add y mode = .ok r :=
  Number.operator_add_ok_of_exp x y mode hx hy (Number.exponent_le_of_size x hx hxl)
    (Number.exponent_le_of_size y hy hyl)

lemma Number.operator_sub_ok_of_size (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ (200 : ℤ)) (hyl : |y.toRat| < 10 ^ (200 : ℤ)) :
    ∃ r, x.operator_sub y mode = .ok r :=
  Number.operator_sub_ok_of_exp x y mode hx hy (Number.exponent_le_of_size x hx hxl)
    (Number.exponent_le_of_size y hy hyl)

lemma Number.operator_mul_ok_of_size (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ (200 : ℤ)) (hyl : |y.toRat| < 10 ^ (200 : ℤ))
    (hxs : x.mantissa_ ≠ 0 → (10 : ℚ) ^ (-200 : ℤ) ≤ |x.toRat|)
    (hys : y.mantissa_ ≠ 0 → (10 : ℚ) ^ (-200 : ℤ) ≤ |y.toRat|) :
    ∃ r, x.operator_mul y mode = .ok r := by
  by_cases hx0 : x.mantissa_ = 0
  · refine ⟨x, ?_⟩
    have hz := Number.eq_zero_of_mantissa_zero x hx hx0
    unfold Number.operator_mul
    rw [if_pos (by rw [hz]; rfl)]
    rfl
  by_cases hy0 : y.mantissa_ = 0
  · refine ⟨y, ?_⟩
    have hz := Number.eq_zero_of_mantissa_zero y hy hy0
    unfold Number.operator_mul
    rw [Number.operator_eq_zero_false_of_mantissa_ne x hx0, if_neg Bool.false_ne_true, if_pos (by rw [hz]; rfl)]
    rfl
  have h1 := Number.exponent_lt_of_size x hx hx0 hxl
  have h2 := Number.exponent_lt_of_size y hy hy0 hyl
  have h3 := Number.exponent_ge_of_size x hx hx0 (hxs hx0)
  have h4 := Number.exponent_ge_of_size y hy hy0 (hys hy0)
  exact Number.operator_mul_ok_of_normalized x y mode hx hy hx0 hy0 (by unfold minExponent; omega)
    (by unfold maxExponent at *; omega)

lemma STAmount.checked_iou16_ne_overflow (mant : UInt64) (exp : Int) (neg : Bool) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16) (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ 80) :
    STAmount.checked .fractional mant exp neg mode ≠ .error .overflow := by
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  have h_int : ¬ (STAmount.unchecked .fractional mant exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_sd : (STAmount.unchecked .fractional mant exp neg).signedDrops.toInt64
      = if neg then -mant.toInt64 else mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat < 10 ^ 16 from h_hi),
        signed_mantissa_toInt neg mant h_fit]
    show (STAmount.unchecked .fractional mant exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [STAmount.signedDrops_toInt64Checked _ (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat
      < 2 ^ 63 from h_fit), ok_bind, h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo (by unfold maxExponent; omega)
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by unfold cMaxOffset; omega)]
  split
  · rename_i heq
    split at heq <;> cases heq
  · simp

/-- Converting a value below `9·10^18` in size never overflows. -/
lemma STAmount.ofNumber_ne_overflow (nt : NumericType) (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hlt : |n.toRat| < 9 * 10 ^ 18) :
    STAmount.ofNumber nt n mode ≠ .error .overflow := by
  obtain ⟨hwn, hwneg, hwv, hwm, hwe⟩ := Number.working_facts n hn
  unfold STAmount.ofNumber
  simp only [Number.signum_neg_decide]
  split
  · rename_i hint
    obtain ⟨r, hr, hr0, hrle, -⟩ := STAmount.ofNumber_integral_reduce nt _ mode hint hwn hwneg
      (by rw [hwv]; linarith)
    rw [hr]
    simp only [bind, Except.bind]
    rw [Int64.toUInt64Checked_eq_ok.mpr ⟨Int64.le_iff_toInt_le.mpr (by simpa using hr0), rfl⟩]
    exact STAmount.checked_integral_ne_overflow nt hint _ _ mode hrle
  · rename_i hint
    cases nt with
    | integral => exact absurd rfl hint
    | fractional =>
      cases hnr : (if n.negative_ = true then n.operator_neg else n).normalizeToRange kMinValue kMaxValue mode with
      | error err =>
        simp only
        intro h; cases h; exact Number.normalizeToRange_ne_overflow _ _ _ _ hnr
      | ok me =>
        obtain ⟨mant, exp⟩ := me
        simp only [bind, Except.bind]
        cases hu : mant.toUInt64Checked with
        | error err => intro h; cases h; exact Int64.toUInt64Checked_ne_overflow _ hu
        | ok val =>
          obtain ⟨hm0, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hu
          have hm0' : 0 ≤ mant.toInt := Int64.le_iff_toInt_le.mp hm0
          have hval : (mant.toUInt64.toNat : ℤ) = mant.toInt := toUInt64_toNat_of_nonneg mant hm0'
          by_cases hw0 : n.mantissa_ = 0
          · -- a zero value normalizes to a zero mantissa
            have hz : (if n.negative_ = true then n.operator_neg else n) = Number.zero :=
              Number.eq_zero_of_mantissa_zero _ hwn (by rw [hwm]; exact hw0)
            have hzr : Number.zero.normalizeToRange kMinValue kMaxValue mode = .ok (0, -2147483648) := by
              cases mode <;> rfl
            rw [hz, hzr] at hnr
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hnr)
            exact STAmount.checked_fractional_ne_overflow _ _ _ mode (by decide) (fun h => absurd rfl h)
          have hw0' : (if n.negative_ = true then n.operator_neg else n).mantissa_ ≠ 0 := by rw [hwm]; exact hw0
          obtain ⟨hlo, hhi⟩ := hwn.mantissaBounds_nat hw0'
          have hwlt := Number.exponent_lt_of_abs_lt _ hwn hw0' 1 (by
            rw [abs_of_nonneg (by rw [hwv]; exact abs_nonneg _), hwv]; norm_num; linarith)
          have hwge := Number.exponent_ge_min _ hwn hw0'
          have hr := normalizeToRange_16_exp_range _ mode mant exp hlo hhi (by omega)
            (by unfold maxExponent; omega) hnr
          have hmr := normalizeToRange_16_mantissa_range _ mode mant exp hlo hhi (by omega)
            (by unfold maxExponent; omega) hnr
          have hcmin : cMinValue.toNat = 10 ^ 15 := by decide
          have hcmax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
          rw [hcmin, hcmax] at hmr
          exact STAmount.checked_iou16_ne_overflow _ exp _ mode (by omega) (by omega) (by omega) (by omega)


/-- A to-nearest result of a value at most `10^18` in size is at most `10^18` in size: `±10^18` are representable. -/
lemma Number.abs_le_of_rounded (r : Number) (q : ℚ) (h : r.RoundsToRepresentable q .to_nearest)
    (hq : |q| ≤ 10 ^ 18) : |r.toRat| ≤ 10 ^ 18 := by
  have hBn : (⟨false, 1000000000000000000, 0⟩ : Number).isNormalized := by decide
  have hBn' : (⟨true, 1000000000000000000, 0⟩ : Number).isNormalized := by decide
  have hBv : (⟨false, 1000000000000000000, 0⟩ : Number).toRat = 10 ^ 18 := by
    rw [Number.toRat_of_nonneg _ rfl]
    have h : (1000000000000000000 : UInt64).toNat = 10 ^ 18 := by decide
    simp only [zpow_zero, mul_one, h]
    norm_num
  have hBv' : (⟨true, 1000000000000000000, 0⟩ : Number).toRat = -10 ^ 18 := by
    have := Number.toRat_neg ⟨false, 1000000000000000000, 0⟩
    rw [hBv] at this
    rw [← this]; rfl
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  rcases h with ⟨n, hl, hr⟩ | ⟨n, hu, hr⟩
  · have h1 := Number.lower_le q n hl
    have h2 := Number.lower_tight q n hl _ hBn' (by rw [hBv']; linarith)
    rw [hBv'] at h2
    rw [hr, abs_le]; constructor <;> linarith
  · have h1 := Number.le_upper q n hu
    have h2 := Number.upper_tight q n hu _ hBn (by rw [hBv]; linarith)
    rw [hBv] at h2
    rw [hr, abs_le]; constructor <;> linarith

/-- A to-nearest product is at most `1 + 10⁻¹⁸` times the exact product in size. -/
lemma Number.mul_abs_le (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_mul y .to_nearest = .ok r) : |r.toRat| ≤ |x.toRat * y.toRat| * (1 + 1 / 10 ^ 18) := by
  by_cases h0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r h0, abs_zero]; positivity
  have h := operator_mul_rounds_to_nearest x y r hx hy hok h0
  unfold RoundsWithin at h
  have h1 := abs_sub_abs_le_abs_sub r.toRat (x.toRat * y.toRat)
  have h2 : |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7)) ≤ |x.toRat * y.toRat| * (1 / 10 ^ 18) :=
    mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
  change |r.toRat - x.toRat * y.toRat| ≤ _ at h
  nlinarith

/-- A to-nearest quotient is at most `1 + 10⁻¹⁸` times the exact quotient in size. -/
lemma Number.div_abs_le (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_div y .to_nearest = .ok r) : |r.toRat| ≤ |x.toRat / y.toRat| * (1 + 1 / 10 ^ 18) := by
  by_cases h0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r h0, abs_zero]; positivity
  have h := operator_div_rounds_to_nearest x y r hx hy hok h0
  unfold RoundsWithin at h
  have h1 := abs_sub_abs_le_abs_sub r.toRat (x.toRat / y.toRat)
  have h2 : |x.toRat / y.toRat| * (6 / (2 ^ 63 - 3)) ≤ |x.toRat / y.toRat| * (1 / 10 ^ 18) :=
    mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
  change |r.toRat - x.toRat / y.toRat| ≤ _ at h
  nlinarith

lemma STAmount.operator_lt_ne_overflow (lhs rhs : STAmount) : lhs.operator_lt rhs ≠ .error .overflow := by
  unfold STAmount.operator_lt
  split <;> simp

lemma STAmount.isFractionalNonPositive_ne_overflow (a : STAmount) : a.isFractionalNonPositive ≠ .error .overflow := by
  unfold STAmount.isFractionalNonPositive STAmount.operator_le
  split
  · simp
  · have := STAmount.operator_lt_ne_overflow (STAmount.zero a.numericType) a
    split <;> simp_all


/-- A fractional record canonicalized to zero carries the zero offset `-100`. -/
lemma STAmount.canonicalize_fractional_zero_offset (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hok : s.canonicalize mode = .ok result) (hz : result.mValue = 0) :
    result.mOffset = -100 := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  cases hone : s.iou mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only at hok
    have heq := Except.ok.inj hok
    have hres : result.mOffset = i.exponent_ := by rw [← heq]
    have hval : result.mValue = i.mantissa_.magnitude := by rw [← heq]
    rw [hres]
    unfold STAmount.iou at hone
    rw [if_neg hint] at hone
    obtain ⟨m, -, hone⟩ := bind_ok_peel _ _ _ hone
    have hi0 : i.mantissa_ = 0 := by
      rw [hval] at hz
      have h1 := Int64.toNat_magnitude i.mantissa_
      rw [hz] at h1
      have hz' : i.mantissa_.toInt = 0 := by
        have : i.mantissa_.toInt.natAbs = 0 := by simpa using h1.symm
        omega
      exact Int64.toInt_inj.mp (by rw [hz']; rfl)
    exact IOUAmount.normalize_zero_exp _ mode i hone hi0


/-- An IOU amount converted from a value at most `10^18` in size has an offset at most `79`. -/
lemma STAmount.ofNumber_fractional_offset_le (n : Number) (mode : rounding_mode) (a : STAmount)
    (hn : n.isNormalized) (hlt : |n.toRat| ≤ 10 ^ 18) (hok : STAmount.ofNumber .fractional n mode = .ok a) :
    a.mOffset ≤ 79 := by
  rcases (STAmount.ofNumber_fractional_fczr n mode a hok).2 with hc | hz
  · have hm : a.mValue ≠ 0 := fun h => by have := hc.mant_lo; rw [h] at this; simp at this
    have hn0 := STAmount.ofNumber_source_ne_zero _ n mode a hok hm
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hn0
    have hnlt := Number.exponent_lt_of_abs_lt n hn hn0 1 (by norm_num; linarith)
    have hemin := Number.exponent_ge_min n hn hn0
    obtain ⟨hb, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional n mode a rfl hlo hhi hemin
      (by unfold maxExponent; omega) hok hm
    by_contra hcon
    push Not at hcon
    have h3 : (10 : ℚ) ^ (n.exponent_ + 3) ≤ 10 ^ (3 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have habs : |a.toRat| ≤ 10 ^ 18 + 10 ^ 3 := by
      have := abs_sub_abs_le_abs_sub a.toRat n.toRat
      linarith
    rw [STAmount.abs_toRat] at habs
    have hm15 : (10 : ℚ) ^ 15 ≤ a.mValue.toNat := by exact_mod_cast hc.mant_lo
    have h80 : (10 : ℚ) ^ (80 : ℤ) ≤ 10 ^ a.mOffset := zpow_le_zpow_right₀ (by norm_num) hcon
    have : (10 : ℚ) ^ 15 * 10 ^ (80 : ℤ) ≤ a.mValue.toNat * 10 ^ a.mOffset :=
      mul_le_mul hm15 h80 (by positivity) (by positivity)
    norm_num at this
    linarith
  · have hoff : a.mOffset = -100 := by
      rw [STAmount.ofNumber] at hok
      split at hok
      · exact absurd ‹NumericType.fractional.isIntegral = true› (by decide)
      · split at hok
        · exact absurd hok (by simp)
        · obtain ⟨v, -, hok⟩ := bind_ok_peel _ _ _ hok
          rw [STAmount.checked] at hok
          exact STAmount.canonicalize_fractional_zero_offset _ a mode rfl hok hz
    omega

/-- Rounding a nonnegative IOU amount, or a zero one, to a scale in `[-96, 79]` never overflows. -/
lemma STAmount.roundToExponent_ne_overflow (value : STAmount) (s : Int) (mode : rounding_mode)
    (hv : (value.IOUCanonical ∧ value.mIsNegative = false) ∨ value.mValue = 0) (hs_lo : -96 ≤ s)
    (hs_hi : s ≤ 79) : STAmount.roundToExponent value s mode ≠ .error .overflow := by
  rcases hv with ⟨hc, hneg⟩ | hz
  · obtain ⟨r, hr⟩ := STAmount.roundToExponent_ok_any value s mode hc hneg hs_lo hs_hi
    rw [hr]; simp
  · unfold STAmount.roundToExponent
    split
    · simp
    · rw [if_pos (by simp [STAmount.isZero, hz])]; simp


/-- Clamping an amount at most `9·10^17` in size onto its sum with a value at most `10^17` in size never overflows,
for a base exponent in `[-96, 79]`. -/
lemma clampToSumExponent_ne_overflow (A : Number) (delta : STAmount) (b : Int) (hA : A.isNormalized)
    (hAl : |A.toRat| ≤ 10 ^ 17) (hd : delta.CanonicalOrZero) (hdl : |delta.toRat| ≤ 9 * 10 ^ 17) (hb : -96 ≤ b)
    (hb' : b ≤ 79) : clampToSumExponent A delta b ≠ .error .overflow := by
  unfold clampToSumExponent
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · simp
  rename_i hint
  have hfr : delta.mNumericType = .fractional := by
    cases h : delta.mNumericType with
    | integral => exact absurd (by unfold STAmount.integral; rw [h]; rfl) hint
    | fractional => rfl
  -- the magnitude is a nonnegative IOU amount or zero
  have habs : ((if delta.negative = true then delta.operator_neg else delta).IOUCanonical ∧
      (if delta.negative = true then delta.operator_neg else delta).mIsNegative = false) ∨
      (if delta.negative = true then delta.operator_neg else delta).mValue = 0 := by
    rcases hd with hc | hz
    · have hio : delta.IOUCanonical := hc.2 (by simpa using hint)
      have hm : delta.mValue ≠ 0 := fun h => by have := hio.mant_lo; rw [h] at this; simp at this
      left
      by_cases hn : delta.negative = true
      · rw [if_pos hn]
        unfold STAmount.operator_neg
        rw [if_neg (by simpa using hm)]
        exact ⟨⟨hio.is_fractional, hio.mant_lo, hio.mant_hi, hio.exp_lo, hio.exp_hi⟩, by simpa using hn⟩
      · rw [if_neg hn]
        exact ⟨hio, by simpa using hn⟩
    · right
      have hm : delta.mValue = 0 := by simpa [STAmount.isZero] using hz
      split
      · unfold STAmount.operator_neg; rw [if_pos (by simp [hm])]; exact hm
      · exact hm
  obtain ⟨dn, hdn⟩ := hd.toNumber_ok
  obtain ⟨hdv, hdnn⟩ := hd.toNumber_exact dn hdn
  rw [hdn]
  simp only
  unfold postSumExponent
  have h200 : (10 : ℚ) ^ 17 < 10 ^ (200 : ℤ) := by norm_num
  obtain ⟨sum, hsum⟩ := Number.operator_add_ok_of_size A dn .to_nearest hA hdnn (by linarith)
    (by rw [hdv]; linarith)
  simp only [bind, Except.bind, hsum]
  have hsn := Number.operator_add_isNormalized_any A dn sum _ hA hdnn hsum
  have hsl : |sum.toRat| ≤ 10 ^ 18 := Number.abs_le_of_rounded sum _
    (operator_add_rounded_to_nearest A dn sum hA hdnn hsum) (by
      rw [hdv]
      calc |A.toRat + delta.toRat| ≤ |A.toRat| + |delta.toRat| := abs_add_le _ _
        _ ≤ 10 ^ 18 := by linarith)
  unfold numberExponent
  simp only [bind, Except.bind, pure, Except.pure]
  by_cases hz : sum.operator_eq Number.zero = true
  · rw [if_pos hz]
    exact STAmount.roundToExponent_ne_overflow _ _ _ habs hb hb'
  rw [if_neg hz]
  cases hof : STAmount.ofNumber delta.numericType sum .downward with
  | error e =>
    simp only
    intro h; cases h
    exact STAmount.ofNumber_ne_overflow _ sum _ hsn (by linarith) hof
  | ok a' =>
    simp only
    have hof' : STAmount.ofNumber .fractional sum .downward = .ok a' := by
      rw [← hfr]; exact hof
    have ha := STAmount.ofNumber_fractional_offset_le sum _ a' hsn hsl hof'
    exact STAmount.roundToExponent_ne_overflow _ _ _ habs (le_trans hb (le_max_left _ _))
      (max_le hb' ha)

/-- A nonzero canonical amount is at least `10⁻⁸¹` in size. -/
lemma STAmount.CanonicalOrZero.abs_ge (s : STAmount) (hc : s.CanonicalOrZero) (hm : s.mValue ≠ 0) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  have hc' : s.Canonical := hc.resolve_right (by simpa [STAmount.isZero] using hm)
  have hm1 : (1 : ℚ) ≤ s.mValue.toNat := by
    have : 1 ≤ s.mValue.toNat := by
      rcases Nat.eq_zero_or_pos s.mValue.toNat with h | h
      · exact absurd (by rw [← UInt64.toNat_inj]; simpa using h) hm
      · exact h
    exact_mod_cast this
  by_cases hint : s.integral = true
  · rw [(hc'.1 hint).1.offset_zero, zpow_zero, mul_one]
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      _ ≤ _ := hm1
  · have hio := hc'.2 (by simpa using hint)
    have h15 : (10 : ℚ) ^ 15 ≤ s.mValue.toNat := by exact_mod_cast hio.mant_lo
    have he : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ s.mOffset := zpow_le_zpow_right₀ (by norm_num) hio.exp_lo
    calc (10 : ℚ) ^ (-81 : ℤ) = 10 ^ 15 * 10 ^ (-96 : ℤ) := by norm_num
      _ ≤ s.mValue.toNat * 10 ^ s.mOffset := mul_le_mul h15 he (by positivity) (by positivity)

/-- A to-nearest result of a nonnegative value is nonnegative. -/
lemma Number.nonneg_of_rounded (r : Number) (q : ℚ) (h : r.RoundsToRepresentable q .to_nearest) (hq : 0 ≤ q) :
    0 ≤ r.toRat := by
  rcases h with ⟨n, hl, hr⟩ | ⟨n, hu, hr⟩
  · have := Number.lower_tight q n hl Number.zero (Or.inl rfl) (by rw [Number.toRat_zero]; exact hq)
    rw [hr]; rwa [Number.toRat_zero] at this
  · have := Number.le_upper q n hu
    rw [hr]; linarith

/-- A to-nearest product of two nonnegative values divided by a positive one is normalized, nonnegative and at most
`(1 + 10⁻¹⁸)²` times the exact quotient. -/
lemma Number.mul_div_facts (x y z P Q : Number) (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hz0 : 0 < z.toRat)
    (hP : x.operator_mul y .to_nearest = .ok P) (hQ : P.operator_div z .to_nearest = .ok Q) :
    Q.isNormalized ∧ 0 ≤ Q.toRat ∧ Q.toRat ≤ x.toRat * y.toRat / z.toRat * (1 + 1 / 10 ^ 18) ^ 2 := by
  have hPn := Number.operator_mul_isNormalized x y P _ hx hy hP
  have hQn := Number.operator_div_isNormalized P z Q _ hPn hz hQ
  have hP0 := Number.nonneg_of_rounded P _ (operator_mul_rounded_to_nearest x y P hx hy hP) (mul_nonneg hx0 hy0)
  have hQ0 := Number.nonneg_of_rounded Q _ (operator_div_rounded_to_nearest P z Q hPn hz hQ)
    (div_nonneg hP0 hz0.le)
  have hPl := Number.mul_abs_le x y P hx hy hP
  have hQl := Number.div_abs_le P z Q hPn hz hQ
  rw [abs_of_nonneg hP0, abs_of_nonneg (mul_nonneg hx0 hy0)] at hPl
  rw [abs_of_nonneg hQ0, abs_of_nonneg (div_nonneg hP0 hz0.le)] at hQl
  refine ⟨hQn, hQ0, le_trans hQl ?_⟩
  have h1 : P.toRat / z.toRat ≤ x.toRat * y.toRat * (1 + 1 / 10 ^ 18) / z.toRat :=
    div_le_div_of_nonneg_right hPl hz0.le
  calc P.toRat / z.toRat * (1 + 1 / 10 ^ 18)
      ≤ x.toRat * y.toRat * (1 + 1 / 10 ^ 18) / z.toRat * (1 + 1 / 10 ^ 18) :=
        mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ = x.toRat * y.toRat / z.toRat * (1 + 1 / 10 ^ 18) ^ 2 := by ring

/-- A nonzero amount converted to a `Number` is at least `10⁻²⁰⁰` in size. -/
lemma STAmount.CanonicalOrZero.number_ge (X : STAmount) (hX : X.CanonicalOrZero) (xn : Number)
    (hxv : xn.toRat = X.toRat) (hm : xn.mantissa_ ≠ 0) : (10 : ℚ) ^ (-200 : ℤ) ≤ |xn.toRat| := by
  have hne : X.toRat ≠ 0 := by rw [← hxv]; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hm
  have hm' : X.mValue ≠ 0 := fun h0 => hne ((STAmount.toRat_eq_zero_iff _).mpr h0)
  rw [hxv]
  exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) (STAmount.CanonicalOrZero.abs_ge X hX hm')

/-- A positive canonical amount: its mantissa fits `maxRep` and its exponent is in the IOU range. -/
lemma STAmount.Canonical.mantissa_exponent (a : STAmount) (hc : a.Canonical) :
    a.mValue.toNat ≤ maxRep.toNat ∧ (-96 : ℤ) ≤ a.exponent ∧ a.exponent ≤ 80 := by
  by_cases hint : a.integral = true
  · obtain ⟨hic, hmr⟩ := hc.1 hint
    refine ⟨le_trans hic.in_range hmr, ?_⟩
    rw [show a.exponent = a.mOffset from rfl, hic.offset_zero]; omega
  · have hiou := hc.2 (by simpa using hint)
    refine ⟨by have := hiou.mant_hi; rw [maxRep_val]; omega, hiou.exp_lo, hiou.exp_hi⟩

/-- The only error `isOverflow` flags is `overflow`. -/
lemma isOverflow_eq_true {e : Error} (h : isOverflow e = true) : e = .overflow := by
  cases e <;> simp_all [isOverflow]

/-- A canonical amount, or a zero one, converts to a `Number` without overflow. -/
lemma STAmount.CanonicalOrZero.toNumber_ne_overflow {s : STAmount} (hs : s.CanonicalOrZero) :
    s.toNumber .to_nearest ≠ .error .overflow := by
  obtain ⟨n, hn⟩ := hs.toNumber_ok
  rw [hn]; simp

end XRPL.Model.Protocol
