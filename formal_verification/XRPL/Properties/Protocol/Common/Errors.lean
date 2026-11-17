import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TenthBips
import XRPL.Properties.Protocol.Common.FixedWidth
import XRPL.Properties.Protocol.Number.ToRep.Common.Proofs

/-! # Errors of the Protocol operations

Only a ledger object's `to_lawful` raises `Error.notLawful`. No Number or STAmount operation
returns it, so a transaction ending in `notLawful` failed its final lawfulness check. -/

namespace XRPL.Model.Protocol

/-- Split every `match` and `if` of a `_ ≠ .error .notLawful` goal and close each branch with
the lemmas for the calls it makes. -/
macro "split_ne_notLawful" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (repeat' (first | split | extract_lets)
             all_goals (try (intro hc; cases hc))
             all_goals first
               | (simp only [$args,*, ne_eq, not_false_eq_true]; done)
               | (simp only [$args,*] at *; done)
               | simp_all [$args,*]))

lemma Guard.doRoundUp_ne_notLawful (g : Guard) (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : internalrep) (mode : rounding_mode) (location : Error)
    (hloc : location ≠ .notLawful) :
    g.doRoundUp negative mantissa exponent minMantissa maxMantissa mode location ≠ .error .notLawful := by
  refine (Guard.doRoundUp_refines _ _ _ _ _ _ _ _).ne_error ?_ (by decide)
  unfold Guard.doRoundUpSpec
  have key : ∀ (c : Prop) [Decidable c] (r : RoundResult),
      (if c then (.error location : Except Error RoundResult) else .ok r) ≠ .error .notLawful := by
    intro c _ r; split <;> simp [hloc]
  exact key _ _

lemma doNormalize_scaleDown_ne_notLawful (maxMantissa m : UInt64) (e : Int) (g : Guard) :
    doNormalize_scaleDown maxMantissa m e g ≠ .error .notLawful := by
  fun_induction doNormalize_scaleDown maxMantissa m e g <;> simp_all

lemma doNormalize_scaleDown128_ne_notLawful (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard) :
    doNormalize_scaleDown128 maxMantissa m e g ≠ .error .notLawful := by
  rw [doNormalize_scaleDown128_eq_spec]
  fun_induction doNormalize_scaleDown128Spec maxMantissa m e g <;> simp_all

lemma doNormalize_capAtMaxRep_ne_notLawful (m : UInt64) (e : Int) (g : Guard) :
    doNormalize_capAtMaxRep m e g ≠ .error .notLawful := by
  unfold doNormalize_capAtMaxRep
  split
  · split <;> simp
  · simp

lemma doNormalize_ne_notLawful (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) :
    doNormalize negative mantissa exponent minMantissa maxMantissa mode ≠ .error .notLawful := by
  refine (doNormalize_refines _ _ _ _ _ _).ne_error ?_ (by decide)
  unfold doNormalizeSpec
  split
  · simp
  dsimp only
  split_ne_notLawful [doNormalize_scaleDown_ne_notLawful, doNormalize_capAtMaxRep_ne_notLawful,
    Guard.doRoundUp_ne_notLawful]

lemma doNormalize128_ne_notLawful (negative : Bool) (mantissa : UInt128) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) (stickyTail : Bool) :
    doNormalize128 negative mantissa exponent minMantissa maxMantissa mode stickyTail ≠ .error .notLawful := by
  rw [doNormalize128_eq_spec]
  unfold doNormalize128Spec
  split
  · simp
  dsimp only
  split_ne_notLawful [← doNormalize_scaleDown128_eq_spec, doNormalize_scaleDown128_ne_notLawful,
    doNormalize_capAtMaxRep_ne_notLawful, Guard.doRoundUp_ne_notLawful]

lemma Number.normalize_ne_notLawful (n : Number) (minMant maxMant : UInt64) (mode : rounding_mode) :
    n.normalize minMant maxMant mode ≠ .error .notLawful :=
  doNormalize_ne_notLawful _ _ _ _ _ _

lemma Number.normalizeToRange_ne_notLawful (n : Number) (minMant maxMant : UInt64) (mode : rounding_mode) :
    n.normalizeToRange minMant maxMant mode ≠ .error .notLawful := by
  unfold Number.normalizeToRange
  split
  · rename_i e he
    intro h; cases h; exact doNormalize_ne_notLawful _ _ _ _ _ _ he
  · exact bind_ne_error (UInt64.toInt64Checked_ne_notLawful _) fun _ =>
      bind_ne_error (ite_ne_error (Int64.negChecked_ne_notLawful _) nofun) fun _ => nofun

lemma Number.normalized_ne_notLawful (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMant maxMant : UInt64) (mode : rounding_mode) :
    Number.normalized negative mantissa exponent minMant maxMant mode ≠ .error .notLawful :=
  Number.normalize_ne_notLawful _ _ _ _

lemma Number.from_rep_ne_notLawful (mantissa : Int64) (exponent : Int) (minMant maxMant : UInt64)
    (mode : rounding_mode) :
    Number.from_rep mantissa exponent minMant maxMant mode ≠ .error .notLawful :=
  Number.normalized_ne_notLawful _ _ _ _ _ _

lemma Number.truncate_ne_notLawful (n : Number) : n.truncate ≠ .error .notLawful := by
  unfold Number.truncate
  split_ne_notLawful [Number.normalized_ne_notLawful]

lemma Number.operator_mul_ne_notLawful (x y : Number) (mode : rounding_mode) :
    x.operator_mul y mode ≠ .error .notLawful := by
  rw [Number.operator_mul_eq_spec]
  unfold Number.operator_mulSpec
  dsimp only
  split_ne_notLawful [Number.normalize_ne_notLawful, Guard.doRoundUp_ne_notLawful]

/-- The division quotient fails only on a wrap. The proof rewrites one step at a time, since unfolding its binds
by definition sends the kernel into deep recursion on the 128-bit literals. -/
lemma divQuotient128_eq_error {xm ym : UInt64} {xe ye : Int} {e : Error}
    (h : divQuotient128 xm ym xe ye = .error e) : e = .wrap := by
  unfold divQuotient128 at h
  dsimp only at h
  rcases h1 : BitVec.mulChecked (toUInt128 xm) 100000000000000000 with e1 | num
  · rw [h1, err_bind] at h; cases h; exact BitVec.mulChecked_eq_error h1
  rw [h1, ok_bind] at h
  by_cases hr : (num % toUInt128 ym != 0) = true
  · rw [if_pos hr] at h
    rcases h2 : BitVec.mulChecked (num % toUInt128 ym) 100000 with e2 | pn
    · rw [h2, err_bind] at h; cases h; exact BitVec.mulChecked_eq_error h2
    rw [h2, ok_bind] at h
    by_cases hc : (pn / toUInt128 ym != 0) = true
    · rw [if_pos hc] at h
      rcases h3 : BitVec.mulChecked (num / toUInt128 ym) 100000 with e3 | sc
      · rw [h3, err_bind] at h; cases h; exact BitVec.mulChecked_eq_error h3
      rw [h3, ok_bind] at h
      rcases h4 : BitVec.addChecked sc (pn / toUInt128 ym) with e4 | co
      · rw [h4, err_bind] at h; cases h; exact BitVec.addChecked_eq_error h4
      rw [h4, ok_bind] at h; cases h
    · rw [if_neg hc] at h; cases h
  · rw [if_neg hr] at h; cases h

lemma divQuotient128_ne_notLawful (xm ym : UInt64) (xe ye : Int) :
    divQuotient128 xm ym xe ye ≠ .error .notLawful :=
  fun h => nomatch divQuotient128_eq_error h

lemma Number.operator_div_ne_notLawful (x y : Number) (mode : rounding_mode) :
    x.operator_div y mode ≠ .error .notLawful := by
  unfold Number.operator_div
  split
  · simp
  split
  · exact nofun
  intro h
  rcases hq : divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_ with e | ⟨zm, ze, d⟩
  · rw [hq, err_bind] at h; cases h; exact divQuotient128_ne_notLawful _ _ _ _ hq
  · rw [hq, ok_bind] at h; exact doNormalize128_ne_notLawful _ _ _ _ _ _ _ h

lemma Number.operator_add_ne_notLawful (x y : Number) (mode : rounding_mode) :
    x.operator_add y mode ≠ .error .notLawful := by
  refine (Number.operator_add_refines _ _ _).ne_error ?_ (by decide)
  unfold Number.operator_addSpec checkSumAtTop
  split_ne_notLawful [Number.normalize_ne_notLawful, Guard.doRoundUp_ne_notLawful,
    doNormalize128_ne_notLawful, ok_bind]

lemma Number.operator_sub_ne_notLawful (x y : Number) (mode : rounding_mode) :
    x.operator_sub y mode ≠ .error .notLawful :=
  Number.operator_add_ne_notLawful _ _ _

lemma Number.power_ne_notLawful (base : Number) (n : Nat) : base.power n ≠ .error .notLawful := by
  fun_induction Number.power base n with
  | case1 => simp
  | case2 => simp
  | case3 k ih =>
    simp only [bind, Except.bind]
    split
    · rename_i e he; rw [he] at ih; exact ih
    · split_ne_notLawful [Number.operator_mul_ne_notLawful]

lemma growSpec_ne_notLawful (drops : rep) (offset : Int) : growSpec drops offset ≠ .error .notLawful := by
  fun_induction growSpec drops offset <;> simp_all

lemma Number.to_rep_ne_notLawful (n : Number) (mode : rounding_mode) :
    n.to_rep mode ≠ .error .notLawful := by
  rw [Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  dsimp only
  have hgrow : ∀ (c : Prop) [Decidable c] (drops : rep) (offset : Int),
      (if c then growSpec drops offset else .ok drops) ≠ .error .notLawful := by
    intro c _ drops offset; split
    · exact growSpec_ne_notLawful _ _
    · simp
  split_ne_notLawful [hgrow]

lemma IntAmount.ofNumber_ne_notLawful (n : Number) (mode : rounding_mode) :
    IntAmount.ofNumber n mode ≠ .error .notLawful := by
  unfold IntAmount.ofNumber
  split_ne_notLawful [Number.to_rep_ne_notLawful]

lemma IntAmount.toNumber_ne_notLawful (a : IntAmount) (mode : rounding_mode) :
    a.toNumber mode ≠ .error .notLawful :=
  Number.from_rep_ne_notLawful _ _ _ _ _

lemma IOUAmount.fromNumber_ne_notLawful (n : Number) (mode : rounding_mode) :
    IOUAmount.fromNumber n mode ≠ .error .notLawful := by
  unfold IOUAmount.fromNumber
  split_ne_notLawful [Number.normalizeToRange_ne_notLawful]

lemma IOUAmount.normalize_ne_notLawful (a : IOUAmount) (mode : rounding_mode) :
    a.normalize mode ≠ .error .notLawful := by
  unfold IOUAmount.normalize
  split_ne_notLawful [Number.from_rep_ne_notLawful, IOUAmount.fromNumber_ne_notLawful]

lemma IOUAmount.ofMantissaExp_ne_notLawful (m : Int64) (e : Int) (mode : rounding_mode) :
    IOUAmount.ofMantissaExp m e mode ≠ .error .notLawful :=
  IOUAmount.normalize_ne_notLawful _ _

lemma IOUAmount.ofNumber_ne_notLawful (n : Number) (mode : rounding_mode) :
    IOUAmount.ofNumber n mode ≠ .error .notLawful := by
  unfold IOUAmount.ofNumber
  split_ne_notLawful [IOUAmount.fromNumber_ne_notLawful]

lemma IOUAmount.toNumber_ne_notLawful (a : IOUAmount) (mode : rounding_mode) :
    a.toNumber mode ≠ .error .notLawful :=
  Number.from_rep_ne_notLawful _ _ _ _ _

lemma IOUAmount.operator_add_ne_notLawful (x y : IOUAmount) (mode : rounding_mode) :
    x.operator_add y mode ≠ .error .notLawful := by
  unfold IOUAmount.operator_add
  split_ne_notLawful [IOUAmount.toNumber_ne_notLawful, Number.operator_add_ne_notLawful,
    IOUAmount.ofNumber_ne_notLawful]

lemma STAmount.intAmount_ne_notLawful (s : STAmount) : s.intAmount ≠ .error .notLawful := by
  unfold STAmount.intAmount
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful []

lemma STAmount.iou_ne_notLawful (s : STAmount) (mode : rounding_mode) : s.iou mode ≠ .error .notLawful := by
  unfold STAmount.iou
  simp only [bind, Except.bind]
  split_ne_notLawful [IOUAmount.ofMantissaExp_ne_notLawful]

lemma STAmount.toNumber_ne_notLawful (s : STAmount) (mode : rounding_mode) :
    s.toNumber mode ≠ .error .notLawful := by
  unfold STAmount.toNumber
  split_ne_notLawful [STAmount.intAmount_ne_notLawful, IntAmount.toNumber_ne_notLawful,
    STAmount.iou_ne_notLawful, IOUAmount.toNumber_ne_notLawful]

lemma STAmount.canonicalize_ne_notLawful (s : STAmount) (mode : rounding_mode) :
    s.canonicalize mode ≠ .error .notLawful := by
  unfold STAmount.canonicalize
  split_ne_notLawful [IntAmount.ofNumber_ne_notLawful, STAmount.iou_ne_notLawful]

lemma STAmount.checked_ne_notLawful (nt : NumericType) (mValue : UInt64) (mOffset : Int) (mIsNegative : Bool)
    (mode : rounding_mode) : STAmount.checked nt mValue mOffset mIsNegative mode ≠ .error .notLawful :=
  STAmount.canonicalize_ne_notLawful _ _

lemma STAmount.ofIOUAmount_ne_notLawful (a : IOUAmount) (mode : rounding_mode) :
    STAmount.ofIOUAmount a mode ≠ .error .notLawful :=
  STAmount.canonicalize_ne_notLawful _ _

lemma STAmount.ofNumber_ne_notLawful (nt : NumericType) (n : Number) (mode : rounding_mode) :
    STAmount.ofNumber nt n mode ≠ .error .notLawful := by
  unfold STAmount.ofNumber
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.to_rep_ne_notLawful, STAmount.checked_ne_notLawful,
    Number.normalizeToRange_ne_notLawful]

lemma STAmount.operator_lt_ne_notLawful (lhs rhs : STAmount) :
    lhs.operator_lt rhs ≠ .error .notLawful := by
  unfold STAmount.operator_lt
  split_ne_notLawful []

lemma STAmount.operator_le_ne_notLawful (lhs rhs : STAmount) :
    lhs.operator_le rhs ≠ .error .notLawful := by
  unfold STAmount.operator_le
  split_ne_notLawful [STAmount.operator_lt_ne_notLawful]

lemma STAmount.operator_add_ne_notLawful (v1 v2 : STAmount) (mode : rounding_mode) :
    v1.operator_add v2 mode ≠ .error .notLawful := by
  unfold STAmount.operator_add
  simp only [bind, Except.bind]
  split_ne_notLawful [STAmount.checked_ne_notLawful, STAmount.canonicalize_ne_notLawful,
    STAmount.iou_ne_notLawful, IOUAmount.operator_add_ne_notLawful, STAmount.ofIOUAmount_ne_notLawful]

lemma STAmount.operator_sub_ne_notLawful (v1 v2 : STAmount) (mode : rounding_mode) :
    v1.operator_sub v2 mode ≠ .error .notLawful :=
  STAmount.operator_add_ne_notLawful _ _ _

lemma STAmount.roundToExponent_ne_notLawful (value : STAmount) (exponent : Int) (rounding : rounding_mode) :
    value.roundToExponent exponent rounding ≠ .error .notLawful := by
  unfold STAmount.roundToExponent
  split_ne_notLawful [STAmount.checked_ne_notLawful, STAmount.operator_add_ne_notLawful,
    STAmount.operator_sub_ne_notLawful]

lemma STAmount.roundToNumericType_ne_notLawful (nt : NumericType) (value : Number) (rounding : rounding_mode)
    (scale : Option Int) : STAmount.roundToNumericType nt value rounding scale ≠ .error .notLawful := by
  unfold STAmount.roundToNumericType
  split_ne_notLawful [STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful,
    STAmount.roundToExponent_ne_notLawful]

lemma Number.isOnExponentGrid_ne_notLawful (value : Number) (exponent : Int) (nt : NumericType) :
    value.isOnExponentGrid exponent nt ≠ .error .notLawful := by
  unfold Number.isOnExponentGrid
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.roundToNumericType_ne_notLawful]

lemma STAmount.isFractionalNonPositive_ne_notLawful (amount : STAmount) :
    amount.isFractionalNonPositive ≠ .error .notLawful := by
  unfold STAmount.isFractionalNonPositive
  split_ne_notLawful [STAmount.operator_le_ne_notLawful]

lemma numberExponent_ne_notLawful (amount : Number) (exponent : Int) (nt : NumericType) :
    numberExponent amount exponent nt ≠ .error .notLawful := by
  unfold numberExponent
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.ofNumber_ne_notLawful]

lemma postSumExponent_ne_notLawful (amount amountDelta : Number) (exponent : Int) (nt : NumericType) :
    postSumExponent amount amountDelta exponent nt ≠ .error .notLawful := by
  unfold postSumExponent
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.operator_add_ne_notLawful, numberExponent_ne_notLawful]

lemma sumRoundAndSubtract_ne_notLawful (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    (mode : rounding_mode) : sumRoundAndSubtract amount amountDelta exponent nt mode ≠ .error .notLawful := by
  unfold sumRoundAndSubtract
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.ofNumber_ne_notLawful, postSumExponent_ne_notLawful, Number.operator_add_ne_notLawful,
    STAmount.roundToNumericType_ne_notLawful, Number.operator_sub_ne_notLawful]

lemma clampToSumExponent_ne_notLawful (amount : Number) (amountDelta : STAmount) (exponent : Int) :
    clampToSumExponent amount amountDelta exponent ≠ .error .notLawful := by
  unfold clampToSumExponent
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.toNumber_ne_notLawful, postSumExponent_ne_notLawful,
    STAmount.roundToExponent_ne_notLawful]

lemma tenthBipsOfValue_ne_notLawful (value : Number) (bips : TenthBips32) (mode : rounding_mode) :
    tenthBipsOfValue value bips mode ≠ .error .notLawful := by
  unfold tenthBipsOfValue
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.operator_mul_ne_notLawful, Number.operator_div_ne_notLawful]

end XRPL.Model.Protocol
