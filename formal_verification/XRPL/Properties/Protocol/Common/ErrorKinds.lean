import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Protocol.Number.Add.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Mul.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Div.Common.SuccessCondition
import XRPL.Properties.Protocol.STAmount.Range.Success

/-! # Which errors the Number and amount operations return

A vault transaction catches the overflow errors of its pricing and returns `tecPATH_DRY`. Every other error leaves
the transaction as an exception. The lemmas here sort the errors of the operations a deposit, a withdrawal and a
clawback run: an overflow error, a wrap, or for an XRP or MPT amount `outOfRange`. -/

namespace XRPL.Model.Protocol.ErrorKinds

open XRPL.Model.Protocol

/-- A subtraction of normalized Numbers fails only with an overflow error. -/
lemma number_sub_error {x y : Number} {mode : rounding_mode} {e : Error} (hx : x.isNormalized)
    (hy : y.isNormalized) (h : x.operator_sub y mode = .error e) : isOverflow e = true ∨ e = .wrap :=
  Or.inl (Number.operator_add_error_isOverflow hx (Number.operator_neg_isNormalized y hy) h)

/-- An addition of normalized Numbers fails only with an overflow error. -/
lemma number_add_error {x y : Number} {mode : rounding_mode} {e : Error} (hx : x.isNormalized)
    (hy : y.isNormalized) (h : x.operator_add y mode = .error e) : isOverflow e = true ∨ e = .wrap :=
  Or.inl (Number.operator_add_error_isOverflow hx hy h)

/-- A multiplication fails only with an overflow error. -/
lemma number_mul_error {x y : Number} {mode : rounding_mode} {e : Error}
    (h : x.operator_mul y mode = .error e) : isOverflow e = true ∨ e = .wrap :=
  Or.inl (Number.operator_mul_error_isOverflow h)

/-- A division fails only with an overflow error (a zero divisor is one) or a wrap. -/
lemma number_div_error {x y : Number} {mode : rounding_mode} {e : Error}
    (h : x.operator_div y mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold Number.operator_div at h
  split at h
  · cases h; exact Or.inl rfl
  split at h
  · cases h
  rcases hq : divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_ with e' | ⟨zm, ze, d⟩
  · rw [hq, err_bind] at h; cases h; exact Or.inr (divQuotient128_eq_error hq)
  · rw [hq, ok_bind] at h; exact Or.inl (doNormalize128_error_isOverflow largeRange_min_toNat_le h)

/-- Building a Number from a sign, a mantissa and an exponent fails only with an overflow error. -/
lemma number_normalized_error {neg : Bool} {m : UInt64} {ex : Int} {mode : rounding_mode} {e : Error}
    (h : Number.normalized neg m ex largeRange.min largeRange.max mode = .error e) :
    isOverflow e = true ∨ e = .wrap :=
  Or.inl (doNormalize_error_isOverflow largeRange_min_toNat_le h)

/-- Building a Number from an int64 mantissa and an exponent fails only with an overflow error. -/
lemma number_from_rep_error {m : Int64} {ex : Int} {mode : rounding_mode} {e : Error}
    (h : Number.from_rep m ex largeRange.min largeRange.max mode = .error e) : isOverflow e = true ∨ e = .wrap :=
  number_normalized_error h

/-- Dropping the fraction of a Number fails only with an overflow error. -/
lemma number_truncate_error {n : Number} {e : Error} (h : n.truncate = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  unfold Number.truncate at h
  split at h
  · cases h
  · exact number_normalized_error h

/-- A value times a rate in tenths of a basis point fails only with an overflow error or a wrap. -/
lemma tenthBips_error {value : Number} {bips : TenthBips32} {mode : rounding_mode} {e : Error}
    (h : tenthBipsOfValue value bips mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold tenthBipsOfValue at h
  dsimp only at h
  rcases hm : value.operator_mul bips.toNumber mode with e' | p
  · rw [hm, err_bind] at h; cases h; exact number_mul_error hm
  · rw [hm, ok_bind] at h; exact number_div_error h

/-- Normalizing a Number into a mantissa range fails only with an overflow error or a wrap. -/
lemma normalizeToRange_error {n : Number} {minM maxM : UInt64} {mode : rounding_mode} {e : Error}
    (hmin : minM.toNat ≤ 10 ^ 18) (h : n.normalizeToRange minM maxM mode = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  unfold Number.normalizeToRange at h
  split at h
  · rename_i e' he; cases h; exact Or.inl (doNormalize_error_isOverflow hmin he)
  · rename_i res hres
    rcases hm : res.mantissa_.toInt64Checked with e' | mant
    · rw [hm, err_bind] at h; cases h; exact Or.inr (UInt64.toInt64Checked_eq_error hm)
    rw [hm, ok_bind] at h
    by_cases hneg : res.negative_ = true
    · rw [if_pos hneg] at h
      rcases hn : mant.negChecked with e' | sm
      · rw [hn, err_bind] at h; cases h; exact Or.inr (Int64.negChecked_eq_error hn)
      · rw [hn, ok_bind] at h; cases h
    · rw [if_neg hneg] at h; cases h

/-- The digit-growing loop of `to_rep` fails only with an overflow error. -/
lemma growSpec_error {drops : rep} {offset : Int} {e : Error} (h : growSpec drops offset = .error e) :
    e = .overflow := by
  fun_induction growSpec drops offset <;> simp_all

/-- Converting a Number to an int64 fails only with an overflow error. -/
lemma to_rep_error {n : Number} {mode : rounding_mode} {e : Error} (h : n.to_rep mode = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  rw [Number.to_rep_eq_spec] at h
  unfold Number.to_repSpec at h
  dsimp only at h
  have hgrow : ∀ (c : Prop) [Decidable c] (drops : rep) (offset : Int) (e' : Error),
      (if c then growSpec drops offset else .ok drops) = .error e' → e' = .overflow := by
    intro c _ drops offset e' he
    split at he
    · exact growSpec_error he
    · cases he
  split at h
  · cases h
  split at h
  · rename_i e' he
    cases h
    rw [hgrow _ _ _ _ he]
    exact Or.inl rfl
  · split_ifs at h
    all_goals (cases h; exact Or.inl rfl)

/-- Converting a Number to an IOU mantissa and exponent fails only with an overflow error or a wrap. -/
lemma iou_fromNumber_error {n : Number} {mode : rounding_mode} {e : Error}
    (h : IOUAmount.fromNumber n mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold IOUAmount.fromNumber at h
  split at h
  · rename_i e' he; cases h; exact normalizeToRange_error (by decide) he
  · cases h

/-- Normalizing an IOU amount fails only with an overflow error or a wrap. -/
lemma iou_normalize_error {a : IOUAmount} {mode : rounding_mode} {e : Error}
    (h : a.normalize mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold IOUAmount.normalize at h
  split at h
  · cases h
  split at h
  · rename_i e' he; cases h; exact number_from_rep_error he
  split at h
  · rename_i e' he; cases h; exact iou_fromNumber_error he
  split_ifs at h
  cases h
  exact Or.inl rfl

/-- Converting a Number to an IOU amount fails only with an overflow error or a wrap. -/
lemma iou_ofNumber_error {n : Number} {mode : rounding_mode} {e : Error}
    (h : IOUAmount.ofNumber n mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold IOUAmount.ofNumber at h
  split at h
  · rename_i e' he; cases h; exact iou_fromNumber_error he
  split_ifs at h
  cases h
  exact Or.inl rfl

/-- Adding two IOU amounts fails only with an overflow error or a wrap. -/
lemma iou_add_error {x y : IOUAmount} {mode : rounding_mode} {e : Error}
    (h : x.operator_add y mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold IOUAmount.operator_add at h
  split_ifs at h
  split at h
  · rename_i e' he; cases h; exact number_from_rep_error he
  rename_i xn hxn
  split at h
  · rename_i e' he; cases h; exact number_from_rep_error he
  rename_i yn hyn
  split at h
  · rename_i e' he
    cases h
    exact number_add_error (Number.from_rep_isNormalized _ _ mode xn hxn)
      (Number.from_rep_isNormalized _ _ mode yn hyn) he
  · exact iou_ofNumber_error h

/-- Reading an amount as a Number fails only with an overflow error or a wrap. -/
lemma toNumber_error {s : STAmount} {mode : rounding_mode} {e : Error} (h : s.toNumber mode = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  unfold STAmount.toNumber at h
  split at h
  · rename_i hint
    split at h
    · rename_i e' he
      cases h
      unfold STAmount.intAmount at he
      rw [if_pos hint] at he
      rcases hv : s.signedDrops.toInt64Checked with e'' | v
      · rw [hv, err_bind] at he; cases he; exact Or.inr (Int.toInt64Checked_eq_error hv)
      · rw [hv, ok_bind] at he; cases he
    · exact number_from_rep_error h
  · rename_i hint
    split at h
    · rename_i e' he
      cases h
      unfold STAmount.iou at he
      rw [if_neg hint] at he
      exact iou_normalize_error he
    · exact number_from_rep_error h

/-- Bringing an IOU amount to its stored form fails only with an overflow error or a wrap. -/
lemma canonicalize_fractional_error {s : STAmount} {mode : rounding_mode} {e : Error}
    (hfr : ¬ s.integral = true) (h : s.canonicalize mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold STAmount.canonicalize at h
  rw [if_neg hfr] at h
  split at h
  · rename_i e' he
    cases h
    unfold STAmount.iou at he
    rw [if_neg hfr] at he
    exact iou_normalize_error he
  · cases h

/-- Converting a Number to an IOU amount fails only with an overflow error or a wrap. -/
lemma ofNumber_fractional_error {n : Number} {mode : rounding_mode} {e : Error}
    (h : STAmount.ofNumber .fractional n mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold STAmount.ofNumber at h
  dsimp only at h
  generalize (if decide (n.signum < 0) = true then n.operator_neg else n) = w at h
  rw [if_neg (by decide)] at h
  split at h
  · rename_i e' he; cases h; exact normalizeToRange_error (by decide) he
  · rename_i m ex hm
    rcases hv : m.toUInt64Checked with e' | value
    · rw [hv, err_bind] at h; cases h; exact Or.inr (Int64.toUInt64Checked_eq_error hv)
    · rw [hv, ok_bind] at h
      exact canonicalize_fractional_error (by simp [STAmount.unchecked, STAmount.integral, NumericType.isIntegral]) h

/-- An MPT amount from a mantissa within int64 and exponent 0 always exists. -/
lemma checked_int64_ok (m : UInt64) (neg : Bool) (mode : rounding_mode) (hm : m ≤ maxRep) :
    ∃ r, STAmount.checked .int64 m 0 neg mode = .ok r := by
  refine (STAmount.checked_ok_iff .int64 m 0 neg mode (Or.inr (Or.inr rfl)) hm).mpr ?_
  rw [STAmount.roundsInRange_int64_iff, STAmount.unchecked_toRat]
  refine roundsWithinUnits_of_abs_le mode _ 1 _ (by norm_num) ?_
  rw [abs_sign_mul_eq, zpow_zero, mul_one, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
  have h := UInt64.le_iff_toNat_le.mp hm
  have hr : maxRep.toNat = 9223372036854775807 := by decide
  rw [hr] at h
  exact_mod_cast h

/-- Converting a Number to an MPT amount fails only with an overflow error or a wrap. -/
lemma ofNumber_int64_error {n : Number} {mode : rounding_mode} {e : Error}
    (h : STAmount.ofNumber .int64 n mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold STAmount.ofNumber at h
  dsimp only at h
  generalize (if decide (n.signum < 0) = true then n.operator_neg else n) = w at h
  rw [if_pos (by decide)] at h
  split at h
  · rename_i e' he; cases h; exact to_rep_error he
  · rename_i r hr
    rcases hv : r.toUInt64Checked with e' | value
    · rw [hv, err_bind] at h; cases h; exact Or.inr (Int64.toUInt64Checked_eq_error hv)
    · rw [hv, ok_bind] at h
      obtain ⟨h0, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
      have hle : r.toUInt64 ≤ maxRep := by
        rw [UInt64.le_iff_toNat_le]
        have h1 := toUInt64_toNat_of_nonneg r (Int64.le_iff_toInt_le.mp h0)
        have h2 := r.toInt_lt
        have hr' : maxRep.toNat = 2 ^ 63 - 1 := by decide
        omega
      obtain ⟨res, hres⟩ := checked_int64_ok r.toUInt64 (decide (n.signum < 0)) mode hle
      rw [hres] at h
      cases h

/-- Adding two IOU amounts of one asset fails only with an overflow error or a wrap. -/
lemma add_fractional_error {v1 v2 : STAmount} {mode : rounding_mode} {e : Error}
    (h1 : v1.mNumericType = .fractional) (h2 : v2.mNumericType = .fractional)
    (h : v1.operator_add v2 mode = .error e) : isOverflow e = true ∨ e = .wrap := by
  have hi1 : ¬ v1.integral = true := by simp [STAmount.integral, h1, NumericType.isIntegral]
  have hi2 : ¬ v2.integral = true := by simp [STAmount.integral, h2, NumericType.isIntegral]
  unfold STAmount.operator_add at h
  split at h
  · rename_i hcmp
    simp [STAmount.areComparable, h1, h2] at hcmp
  split at h
  · cases h
  split at h
  · split at h
    · cases h; exact Or.inl rfl
    · exact canonicalize_fractional_error
        (by simp [STAmount.unchecked, STAmount.integral, h1, NumericType.isIntegral]) h
  split at h
  · rename_i e' he
    cases h
    unfold STAmount.iou at he
    rw [if_neg hi1] at he
    exact iou_normalize_error he
  split at h
  · rename_i e' he
    cases h
    unfold STAmount.iou at he
    rw [if_neg hi2] at he
    exact iou_normalize_error he
  split at h
  · rename_i e' he; cases h; exact iou_add_error he
  · exact canonicalize_fractional_error
      (by simp [STAmount.unchecked, STAmount.integral, NumericType.isIntegral]) h

/-- A type that is not XRP or an MPT is the IOU type. -/
lemma eq_fractional_of_not_integral {nt : NumericType} (h : ¬ nt.isIntegral = true) : nt = .fractional := by
  cases nt with
  | fractional => rfl
  | integral _ _ _ _ => exact absurd rfl h

/-- The sum of two IOU amounts is an IOU amount. -/
lemma add_fractional_type {v1 v2 r : STAmount} {mode : rounding_mode} (h1 : v1.mNumericType = .fractional)
    (h : v1.operator_add v2 mode = .ok r) : r.mNumericType = .fractional := by
  have hi : ¬ r.integral = true := STAmount.operator_add_fractional
    (by simp [STAmount.integral, h1, NumericType.isIntegral]) h
  exact eq_fractional_of_not_integral hi

/-- Rounding an IOU amount to an exponent fails only with an overflow error or a wrap. -/
lemma roundToExponent_error {value : STAmount} {exponent : Int} {mode : rounding_mode} {e : Error}
    (hfr : value.mNumericType = .fractional) (h : value.roundToExponent exponent mode = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  unfold STAmount.roundToExponent at h
  split_ifs at h
  split at h
  · rename_i e' he
    cases h
    exact canonicalize_fractional_error
      (by simp [STAmount.unchecked, STAmount.integral, hfr, NumericType.isIntegral]) he
  rename_i ref href
  have hrt : ref.mNumericType = .fractional := by
    rw [STAmount.canonicalize_mNumericType _ _ _ href]
    exact hfr
  split at h
  · rename_i e' he; cases h; exact add_fractional_error hfr hrt he
  · rename_i sum hsum
    exact add_fractional_error (add_fractional_type hfr hsum)
      (by rw [STAmount.operator_neg_mNumericType]; exact hrt) h

/-- The exponent a balance is stored at fails to compute only with an overflow error or a wrap, for an IOU. -/
lemma numberExponent_fractional_error {amount : Number} {exponent : Int} {e : Error}
    (h : numberExponent amount exponent .fractional = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold numberExponent at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split_ifs at h
  split at h
  · rename_i e' he; cases h; exact ofNumber_fractional_error he
  · cases h

/-- The exponent a balance has after a credit fails to compute only with an overflow error or a wrap, for an IOU. -/
lemma postSumExponent_fractional_error {amount delta : Number} {exponent : Int} {e : Error}
    (ha : amount.isNormalized) (hd : delta.isNormalized)
    (h : postSumExponent amount delta exponent .fractional = .error e) : isOverflow e = true ∨ e = .wrap := by
  unfold postSumExponent at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i e' he; cases h; exact number_add_error ha hd he
  · exact numberExponent_fractional_error h

/-- Clamping an amount onto the grid of a balance fails only with an overflow error or a wrap. -/
lemma clampToSumExponent_error {amount : Number} {delta : STAmount} {exponent : Int} {e : Error}
    (ha : amount.isNormalized) (h : clampToSumExponent amount delta exponent = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  unfold clampToSumExponent at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have habs : delta.mNumericType = .fractional →
      (if delta.negative = true then delta.operator_neg else delta).mNumericType = .fractional := by
    intro hfr
    split
    · rw [STAmount.operator_neg_mNumericType]; exact hfr
    · exact hfr
  generalize (if delta.negative = true then delta.operator_neg else delta) = dabs at h habs
  by_cases hint : delta.integral = true
  · rw [if_pos hint] at h; cases h
  rw [if_neg hint] at h
  have hfr : delta.mNumericType = .fractional := eq_fractional_of_not_integral hint
  split at h
  · rename_i e' he; cases h; exact toNumber_error he
  rename_i dn hdn
  split at h
  · rename_i e' he
    cases h
    have he' : postSumExponent amount dn exponent .fractional = .error e := by
      rw [← hfr]; exact he
    exact postSumExponent_fractional_error ha (STAmount.toNumber_isNormalized _ _ _ hdn) he'
  · exact roundToExponent_error (habs hfr) h

/-- Converting a Number to an IOU or MPT amount fails only with an overflow error or a wrap. -/
lemma ofNumber_error_of {nt : NumericType} {n : Number} {mode : rounding_mode} {e : Error}
    (hnt : nt = .fractional ∨ nt = NumericType.int64) (h : STAmount.ofNumber nt n mode = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  rcases hnt with rfl | rfl
  · exact ofNumber_fractional_error h
  · exact ofNumber_int64_error h

end XRPL.Model.Protocol.ErrorKinds
