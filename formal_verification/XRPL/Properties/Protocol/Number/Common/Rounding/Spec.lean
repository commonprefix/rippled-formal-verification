import Mathlib.Tactic
import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Common.FixedWidth
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.DropDigitEquivalence

/-! # Number internals with raw fixed-width arithmetic

Each `…Spec` function is a Number internal without the wrap checks. The proofs reason about these twins, and the
`_eq_spec` lemmas show that the checked function gives the twin's result when nothing wraps. -/

namespace XRPL.Model.Protocol

/-- `new` gives the result of `old`, or stops with `Error.wrap`. -/
def Refines {α : Type} (new old : Except Error α) : Prop := new = old ∨ new = .error .wrap

lemma Refines.refl {α : Type} (x : Except Error α) : Refines x x := Or.inl rfl

lemma Refines.wrap {α : Type} (old : Except Error α) : Refines (.error .wrap) old := Or.inr rfl

lemma Refines.bind {α β : Type} {x x' : Except Error α} {f f' : α → Except Error β} (hx : Refines x x')
    (hf : ∀ a, x' = .ok a → Refines (f a) (f' a)) : Refines (x >>= f) (x' >>= f') := by
  rcases hx with rfl | rfl
  · cases x with
    | error e => exact Or.inl rfl
    | ok a => rw [ok_bind, ok_bind]; exact hf a rfl
  · exact Or.inr rfl

lemma Refines.bind_ok {α β : Type} {A : Except Error α} {b : α} {K : α → Except Error β} {R : Except Error β}
    (hA : Refines A (.ok b)) (hK : Refines (K b) R) : Refines (A >>= K) R := by
  rcases hA with rfl | rfl
  · rw [ok_bind]; exact hK
  · exact Or.inr rfl

lemma Refines.ok_eq {α : Type} {new old : Except Error α} {r : α} (h : Refines new old) (hn : new = .ok r) :
    old = .ok r := by
  rcases h with rfl | rfl
  · exact hn
  · cases hn

lemma Refines.ne_error {α : Type} {new old : Except Error α} {e : Error} (h : Refines new old)
    (hold : old ≠ .error e) (he : e ≠ .wrap) : new ≠ .error e := by
  rcases h with rfl | rfl
  · exact hold
  · intro h'; cases h'; exact he rfl

lemma UInt64.addChecked_refines (a b : UInt64) : Refines (a.addChecked b) (.ok (a + b)) := by
  unfold UInt64.addChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

lemma UInt64.subChecked_refines (a b : UInt64) : Refines (a.subChecked b) (.ok (a - b)) := by
  unfold UInt64.subChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

lemma UInt64.mulChecked_refines (a b : UInt64) : Refines (a.mulChecked b) (.ok (a * b)) := by
  unfold UInt64.mulChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

lemma BitVec.subChecked_refines {w : Nat} (a b : BitVec w) : Refines (a.subChecked b) (.ok (a - b)) := by
  unfold BitVec.subChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

lemma BitVec.mulChecked_refines {w : Nat} (a b : BitVec w) : Refines (a.mulChecked b) (.ok (a * b)) := by
  unfold BitVec.mulChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

lemma BitVec.addChecked_refines {w : Nat} (a b : BitVec w) : Refines (a.addChecked b) (.ok (a + b)) := by
  unfold BitVec.addChecked; split
  · exact Refines.refl _
  · exact Refines.wrap _

/-- `pushOverflow` with raw arithmetic. -/
def Guard.pushOverflowSpec (g : Guard) (mantissa : UInt64) (mode : rounding_mode) : Guard :=
    if maxRep ≤ mantissa ∧ mantissa < maxRepUp then
        let spread := maxRepUp - maxRep
        let mantissa :=
            if mantissa % 10 < 9 then
                let midpoint := maxRep + spread / 2
                let r := g.round mode
                if r == 1 || (r == 0 && mantissa == midpoint) then mantissa + 1 else mantissa
            else mantissa
        let diff := mantissa - maxRep
        let digit := (diff * 10) / spread
        g.push digit
    else
        g

/-- `bringIntoRange` with a raw multiplication. -/
def Guard.bringIntoRangeSpec (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa : UInt64) : RoundResult :=
  let (mantissa, exponent) :=
    if mantissa < minMantissa ∧ mantissa ≠ 0 then (mantissa * 10, exponent - 1)
    else (mantissa, exponent)
  if exponent < minExponent ∨ mantissa = 0 then
    { negative_ := false, mantissa_ := 0, exponent_ := -2147483648 }
  else
    { negative_ := negative, mantissa_ := mantissa, exponent_ := exponent }

/-- `doRoundUp` with raw arithmetic. -/
def Guard.doRoundUpSpec (g : Guard) (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : internalrep) (mode : rounding_mode)
    (location : Error) : Except Error RoundResult :=
  let g := g.pushOverflowSpec mantissa mode
  let r := g.round mode
  let roundUp := r == 1 || (r == 0 && mantissa % 2 == 1)
  let res :=
    if roundUp then
      if mantissa < maxMantissa ∧ mantissa < maxRep then
        Guard.bringIntoRangeSpec negative (mantissa + 1) exponent minMantissa
      else if maxRep < mantissa ∧ mantissa < maxRepUp then
        Guard.bringIntoRangeSpec negative maxRepUp exponent minMantissa
      else
        let (g', mantissa, exponent) := g.doDropDigit mantissa exponent
        let r' := g'.round mode
        let roundUp' := r' == 1 || (r' == 0 && mantissa % 2 == 1)
        let mantissa := if roundUp' then mantissa + 1 else mantissa
        Guard.bringIntoRangeSpec negative mantissa exponent minMantissa
    else if maxRep < mantissa ∧ mantissa < maxRepUp then
      Guard.bringIntoRangeSpec negative maxRep exponent minMantissa
    else
      Guard.bringIntoRangeSpec negative mantissa exponent minMantissa
  if res.exponent_ > maxExponent then .error location
  else .ok res

lemma largeRange_min_toNat_le : largeRange.min.toNat ≤ 10 ^ 18 := by decide

lemma cMinValue_toNat_le : cMinValue.toNat ≤ 10 ^ 18 := by decide

/-- `pushOverflow` never wraps: it works on a mantissa in `[maxRep, maxRepUp)`, three values. -/
lemma Guard.pushOverflow_eq_spec (g : Guard) (m : UInt64) (mode : rounding_mode) :
    g.pushOverflow m mode = .ok (g.pushOverflowSpec m mode) := by
  unfold Guard.pushOverflow Guard.pushOverflowSpec
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h
    have hlo : maxRep.toNat ≤ m.toNat := UInt64.le_iff_toNat_le.mp h1
    have hhi : m.toNat < maxRepUp.toNat := UInt64.lt_iff_toNat_lt.mp h2
    have hrep : maxRep.toNat = 2 ^ 63 - 1 := by decide
    have hup : maxRepUp.toNat = 2 ^ 63 + 2 := by decide
    dsimp only
    have hm : (if m % 10 < 9 then
          (if ((g.round mode == 1 || (g.round mode == 0 && m == maxRep + (maxRepUp - maxRep) / 2)) = true)
            then m.addChecked 1 else pure m)
        else pure m)
        = .ok (if m % 10 < 9 then
          (if ((g.round mode == 1 || (g.round mode == 0 && m == maxRep + (maxRepUp - maxRep) / 2)) = true)
            then m + 1 else m)
        else m) := by
      split
      · split
        · exact UInt64.addChecked_of_lt (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
        · rfl
      · rfl
    rw [hm, ok_bind]
    generalize hm' : (if m % 10 < 9 then
          (if ((g.round mode == 1 || (g.round mode == 0 && m == maxRep + (maxRepUp - maxRep) / 2)) = true)
            then m + 1 else m)
        else m) = m'
    have hm'r : maxRep.toNat ≤ m'.toNat ∧ m'.toNat ≤ m.toNat + 1 := by
      rw [← hm']
      split
      · split
        · rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          omega
        · omega
      · omega
    have hle : maxRep ≤ m' := UInt64.le_iff_toNat_le.mpr hm'r.1
    rw [UInt64.subChecked_of_le hle, ok_bind]
    have hdiff : (m' - maxRep).toNat = m'.toNat - maxRep.toNat := UInt64.toNat_sub_of_le _ _ hle
    rw [UInt64.mulChecked_of_lt (by rw [hdiff, show (10 : UInt64).toNat = 10 from rfl]; omega), ok_bind]
    rfl
  · rfl

/-- `bringIntoRange` scales up at most a mantissa below `minMantissa`, which fits after the scaling when
`minMantissa ≤ 10^18`. -/
lemma Guard.bringIntoRange_eq_spec (negative : Bool) (m : UInt64) (e : Int) {minM : UInt64}
    (hmin : minM.toNat ≤ 10 ^ 18) :
    Guard.bringIntoRange negative m e minM = .ok (Guard.bringIntoRangeSpec negative m e minM) := by
  unfold Guard.bringIntoRange Guard.bringIntoRangeSpec
  by_cases h : m < minM ∧ m ≠ 0
  · have hlt : m.toNat < minM.toNat := UInt64.lt_iff_toNat_lt.mp h.1
    rw [ite_eq_left h, ite_eq_left h, UInt64.mulChecked_of_lt (by rw [show (10 : UInt64).toNat = 10 from rfl]; omega),
      ok_bind, pure_eq, ok_bind]
    dsimp only
    split <;> rfl
  · rw [ite_eq_right h, ite_eq_right h, pure_eq, ok_bind]
    dsimp only
    split <;> rfl

lemma Guard.bringIntoRange_refines (negative : Bool) (m : UInt64) (e : Int) (minM : UInt64) :
    Refines (Guard.bringIntoRange negative m e minM) (.ok (Guard.bringIntoRangeSpec negative m e minM)) := by
  unfold Guard.bringIntoRange Guard.bringIntoRangeSpec
  by_cases h : m < minM ∧ m ≠ 0
  · rw [ite_eq_left h, ite_eq_left h]
    rcases UInt64.mulChecked_refines m 10 with h' | h'
    · rw [h', ok_bind, pure_eq, ok_bind]
      dsimp only
      split <;> exact Refines.refl _
    · rw [h', err_bind, err_bind]; exact Refines.wrap _
  · rw [ite_eq_right h, ite_eq_right h, pure_eq, ok_bind]
    dsimp only
    split <;> exact Refines.refl _

/-- `doRoundUp` adds one only below `maxRep` or after dropping a digit, so it never wraps when
`minMantissa ≤ 10^18`. -/
lemma Guard.doRoundUp_eq_spec (g : Guard) (negative : Bool) (m : UInt64) (e : Int)
    {minM : UInt64} (maxM : UInt64) (mode : rounding_mode) (loc : Error) (hmin : minM.toNat ≤ 10 ^ 18) :
    g.doRoundUp negative m e minM maxM mode loc = g.doRoundUpSpec negative m e minM maxM mode loc := by
  unfold Guard.doRoundUp Guard.doRoundUpSpec
  rw [Guard.pushOverflow_eq_spec, ok_bind]
  dsimp only [Guard.doDropDigit]
  have hrep : maxRep.toNat = 2 ^ 63 - 1 := by decide
  have hm := m.toNat_lt
  have h10 : (10 : UInt64).toNat = 10 := rfl
  have h1u : (1 : UInt64).toNat = 1 := rfl
  split_ifs with h1 h2 h3 h4 h5 <;>
    simp (disch := (simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, h10, h1u] at *; omega))
      only [Guard.bringIntoRange_eq_spec _ _ _ hmin, UInt64.addChecked_of_lt, ok_bind, pure_eq] <;>
    simp_all

/-- `doNormalize_scaleUp` with a raw multiplication. -/
def doNormalize_scaleUpSpec (minMantissa : UInt64) (m : UInt64) (e : Int) : UInt64 × Int :=
  if m < minMantissa ∧ minExponent < e then
    doNormalize_scaleUpSpec minMantissa (m * 10) (e - 1)
  else (m, e)
termination_by (e - minExponent).toNat
decreasing_by omega

/-- `doNormalize` with the raw scale-up loop. -/
def doNormalizeSpec (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) : Except Error Number :=
  if mantissa == 0 then .ok Number.zero
  else
    let (m, e) := doNormalize_scaleUpSpec minMantissa mantissa exponent
    let g0 := if negative then Guard.new.set_negative else Guard.new
    match doNormalize_scaleDown maxMantissa m e g0 with
    | .error err => .error err
    | .ok (m, e, g) =>
      if e < minExponent || m < minMantissa then .ok Number.zero
      else
        match doNormalize_capAtMaxRep m e g with
        | .error err => .error err
        | .ok (m, e, g) =>
          match g.doRoundUp negative m e minMantissa maxMantissa mode .normalize2 with
          | .error err => .error err
          | .ok res => .ok res.toNumber

/-- `scaleDown128` with raw narrowing. -/
def scaleDown128Spec (m : UInt128) (e : Int) (g : Guard) : UInt64 × Int × Guard :=
  if h : m > toUInt128 maxRepUp then
    let d := toUInt64 (m % 10)
    scaleDown128Spec (m / 10) (e + 1) (g.push d)
  else (toUInt64 m, e, g)
termination_by m.toNat
decreasing_by
  rw [BitVec.toNat_udiv, show (10 : BitVec 128).toNat = 10 from rfl]
  exact Nat.div_lt_self (Nat.lt_of_le_of_lt (Nat.zero_le _) h) (by omega)

/-- `doNormalize_scaleDown128` with raw narrowing. -/
def doNormalize_scaleDown128Spec (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard)
    : Except Error (UInt128 × Int × Guard) :=
  if h : m > toUInt128 maxMantissa then
    if e ≥ maxExponent then .error .normalize1
    else doNormalize_scaleDown128Spec maxMantissa (m / 10) (e + 1) (g.push (toUInt64 (m % 10)))
  else .ok (m, e, g)
termination_by m.toNat
decreasing_by
  rw [BitVec.toNat_udiv, show (10 : BitVec 128).toNat = 10 from rfl]
  exact Nat.div_lt_self (Nat.lt_of_le_of_lt (Nat.zero_le _) h) (by omega)

/-- The scale-up loop of `doNormalize128` with a raw multiplication. -/
def doNormalize128_scaleUpSpec (minMantissa : UInt64) (m : UInt128) (e : Int) : UInt128 × Int :=
  if m < toUInt128 minMantissa ∧ minExponent < e then
    doNormalize128_scaleUpSpec minMantissa (m * 10) (e - 1)
  else (m, e)
termination_by (e - minExponent).toNat
decreasing_by omega

/-- `doNormalize128` with raw arithmetic. -/
def doNormalize128Spec (negative : Bool) (mantissa : UInt128) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode)
    (stickyTail : Bool := false) : Except Error Number :=
  if mantissa == 0 then .ok Number.zero
  else
    let (m, e) := doNormalize128_scaleUpSpec minMantissa mantissa exponent
    let g0 := if negative then Guard.new.set_negative else Guard.new
    let g0 := if stickyTail then g0.set_sticky else g0
    match doNormalize_scaleDown128Spec maxMantissa m e g0 with
    | .error err => .error err
    | .ok (m, e, g) =>
      if e < minExponent || m < toUInt128 minMantissa then .ok Number.zero
      else
        match doNormalize_capAtMaxRep (toUInt64 m) e g with
        | .error err => .error err
        | .ok (m, e, g) =>
          match g.doRoundUp negative m e minMantissa maxMantissa mode .normalize2 with
          | .error err => .error err
          | .ok res => .ok res.toNumber

/-- The `recover` loop of `operator_add` with raw arithmetic. -/
def recoverSpec (upperLimit : UInt128) (m : UInt128) (e : Int) (g : Guard) (fuel : Nat) :
    UInt128 × Int × Guard :=
  match fuel with
  | 0 => (m, e, g)
  | fuel + 1 =>
    if m < upperLimit ∧ ¬ g.empty then
      let (g', d) := g.pop
      recoverSpec upperLimit (m * 10 - toUInt128 d) (e - 1) g' fuel
    else (m, e, g)

/-- `operator_mul` with raw arithmetic. -/
def Number.operator_mulSpec (x y : Number) (mode : rounding_mode) : Except Error Number := do
  if x.operator_eq Number.zero then return x
  else if y.operator_eq Number.zero then return y
  else
    let zn := x.negative_ != y.negative_
    let zm128 := toUInt128 x.mantissa_ * toUInt128 y.mantissa_
    let ze := x.exponent_ + y.exponent_
    let g := if zn then Guard.new.set_negative else Guard.new
    let (zm, ze, g) := scaleDown128Spec zm128 ze g
    match g.doRoundUp zn zm ze largeRange.min largeRange.max mode .overflow with
    | .error err => .error err
    | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode

/-- `adjustExpand` with a raw multiplication. -/
def adjustExpandSpec (upperLimit expandM : UInt128) (expandE shrinkE : Int) : UInt128 × Int :=
  if shrinkE < expandE ∧ minExponent < expandE ∧ expandM < upperLimit then
    adjustExpandSpec upperLimit (expandM * 10) (expandE - 1) shrinkE
  else (expandM, expandE)
termination_by (expandE - shrinkE).toNat
decreasing_by omega

/-- `adjust` with a raw multiplication, and the digit drop without its early exit. -/
def adjustSpec (upperLimit expandM : UInt128) (expandE : Int) (shrinkM : UInt64) (shrinkE : Int) (g : Guard) :
    UInt128 × Int × UInt64 × Guard :=
  let (shrinkM, shrinkE, g) := adjustShrinkZeros g shrinkM shrinkE expandE
  let (expandM, expandE) := adjustExpandSpec upperLimit expandM expandE shrinkE
  let (shrinkM, _, g) := alignDownSpec shrinkM shrinkE g expandE
  (expandM, expandE, shrinkM, g)

/-- The aligned operands of `operator_add`: both mantissas on one exponent, and the guard of the digits dropped from
the operand with the smaller exponent. -/
def Number.addAlignSpec (x y : Number) : UInt128 × UInt128 × Int × Guard :=
  if x.exponent_ < y.exponent_ then
    let g := if x.negative_ then Guard.new.set_negative else Guard.new
    let (ym, e, xm, g) :=
      adjustSpec (toUInt128 largeRange.min * 1000) (toUInt128 y.mantissa_) y.exponent_ x.mantissa_ x.exponent_ g
    (toUInt128 xm, ym, e, g)
  else if x.exponent_ > y.exponent_ then
    let g := if y.negative_ then Guard.new.set_negative else Guard.new
    let (xm, e, ym, g) :=
      adjustSpec (toUInt128 largeRange.min * 1000) (toUInt128 x.mantissa_) x.exponent_ y.mantissa_ y.exponent_ g
    (xm, toUInt128 ym, e, g)
  else
    let g := if (x.mantissa_ < y.mantissa_ && x.negative_) || (y.mantissa_ < x.mantissa_ && y.negative_) then
      Guard.new.set_negative else Guard.new
    (toUInt128 x.mantissa_, toUInt128 y.mantissa_, x.exponent_, g)

/-- `operator_add` with raw arithmetic. -/
def Number.operator_addSpec (x y : Number) (mode : rounding_mode) : Except Error Number :=
  if y.operator_eq Number.zero then .ok x
  else if x.operator_eq Number.zero then .ok y
  else if x.operator_eq (y.operator_neg) then .ok Number.zero
  else
    let (xm, ym, xe, g) := Number.addAlignSpec x y
    if x.negative_ == y.negative_ then
      doNormalize128 x.negative_ (xm + ym) xe largeRange.min largeRange.max mode (!g.empty)
    else
      let (zm, zn) := if xm > ym then (xm - ym, x.negative_) else (ym - xm, y.negative_)
      let (zm, ze, g) := recoverSpec (toUInt128 largeRange.min * 1000) zm xe g 40
      let zm := if g.empty then zm else zm - 1
      doNormalize128 zn zm ze largeRange.min largeRange.max mode (!g.empty)

lemma doNormalize_scaleUp_eq_spec {minM : UInt64} (m : UInt64) (e : Int) (hmin : minM.toNat ≤ 10 ^ 18) :
    doNormalize_scaleUp minM m e = .ok (doNormalize_scaleUpSpec minM m e) := by
  induction m, e using doNormalize_scaleUpSpec.induct minM with
  | case1 m e h ih =>
    have hlt : m.toNat < minM.toNat := UInt64.lt_iff_toNat_lt.mp h.1
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, ite_eq_left h, ite_eq_left h,
      UInt64.mulChecked_of_lt (by rw [show (10 : UInt64).toNat = 10 from rfl]; omega), ok_bind]
    exact ih
  | case2 m e h =>
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, ite_eq_right h, ite_eq_right h]

lemma doNormalize_eq_spec (negative : Bool) (m : UInt64) (e : Int) {minM : UInt64} (maxM : UInt64)
    (mode : rounding_mode) (hmin : minM.toNat ≤ 10 ^ 18) :
    doNormalize negative m e minM maxM mode = doNormalizeSpec negative m e minM maxM mode := by
  unfold doNormalize doNormalizeSpec
  split
  · rfl
  · rw [doNormalize_scaleUp_eq_spec m e hmin]
    rfl

/-- A remainder by ten fits a `UInt64`. -/
lemma toNat_umod_ten_lt (m : UInt128) : (m % 10).toNat < 2 ^ 64 := by
  rw [BitVec.toNat_umod, show (10 : BitVec 128).toNat = 10 from rfl]
  have := Nat.mod_lt m.toNat (show 0 < 10 by omega)
  omega

lemma scaleDown128_eq_spec (m : UInt128) (e : Int) (g : Guard) :
    scaleDown128 m e g = .ok (scaleDown128Spec m e g) := by
  induction m, e, g using scaleDown128Spec.induct with
  | case1 m e g h d ih =>
    rw [scaleDown128, scaleDown128Spec, dite_eq_left h, dite_eq_left h, toUInt64Checked_of_lt (toNat_umod_ten_lt m),
      ok_bind]
    exact ih
  | case2 m e g h =>
    have hle : m.toNat ≤ (toUInt128 maxRepUp).toNat := not_lt.mp h
    have hup : maxRepUp.toNat = 2 ^ 63 + 2 := by decide
    rw [toNat_toUInt128] at hle
    rw [scaleDown128, scaleDown128Spec, dite_eq_right h, dite_eq_right h, toUInt64Checked_of_lt (by omega), ok_bind]
    rfl

lemma doNormalize_scaleDown128_eq_spec (maxM : UInt64) (m : UInt128) (e : Int) (g : Guard) :
    doNormalize_scaleDown128 maxM m e g = doNormalize_scaleDown128Spec maxM m e g := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct maxM with
  | case1 m e g h he =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dite_eq_left h, dite_eq_left h, ite_eq_left he,
      ite_eq_left he]
  | case2 m e g h he ih =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dite_eq_left h, dite_eq_left h, ite_eq_right he,
      ite_eq_right he, toUInt64Checked_of_lt (toNat_umod_ten_lt m), ok_bind]
    exact ih
  | case3 m e g h =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dite_eq_right h, dite_eq_right h]

/-- The mantissa `doNormalize_scaleDown128Spec` returns is at most `maxMantissa`. -/
lemma doNormalize_scaleDown128Spec_le {maxM : UInt64} {m m' : UInt128} {e e' : Int} {g g' : Guard}
    (h : doNormalize_scaleDown128Spec maxM m e g = .ok (m', e', g')) : m' ≤ toUInt128 maxM := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct maxM with
  | case1 m e g hm he =>
    rw [doNormalize_scaleDown128Spec, dite_eq_left hm, ite_eq_left he] at h; cases h
  | case2 m e g hm he ih =>
    rw [doNormalize_scaleDown128Spec, dite_eq_left hm, ite_eq_right he] at h; exact ih h
  | case3 m e g hm =>
    rw [doNormalize_scaleDown128Spec, dite_eq_right hm] at h
    cases h
    exact BitVec.not_lt.mp hm

lemma doNormalize128_scaleUp_eq_spec (minM : UInt64) (m : UInt128) (e : Int) :
    doNormalize128.scaleUp minM m e = .ok (doNormalize128_scaleUpSpec minM m e) := by
  induction m, e using doNormalize128_scaleUpSpec.induct minM with
  | case1 m e h ih =>
    have hlt : m.toNat < (toUInt128 minM).toNat := h.1
    have hmin := minM.toNat_lt
    rw [toNat_toUInt128] at hlt
    rw [doNormalize128.scaleUp, doNormalize128_scaleUpSpec, ite_eq_left h, ite_eq_left h,
      BitVec.mulChecked_of_lt (by rw [show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind]
    exact ih
  | case2 m e h =>
    rw [doNormalize128.scaleUp, doNormalize128_scaleUpSpec, ite_eq_right h, ite_eq_right h]

/-- `doNormalize128` never wraps: it scales a 128-bit mantissa up while it is below a 64-bit minimum, and
narrows only after scaling down to a 64-bit maximum. -/
lemma doNormalize128_eq_spec (negative : Bool) (m : UInt128) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (stickyTail : Bool) :
    doNormalize128 negative m e minM maxM mode stickyTail = doNormalize128Spec negative m e minM maxM mode stickyTail := by
  unfold doNormalize128 doNormalize128Spec
  split
  · rfl
  rw [doNormalize128_scaleUp_eq_spec]
  dsimp only
  rw [doNormalize_scaleDown128_eq_spec]
  rcases hd : doNormalize_scaleDown128Spec maxM (doNormalize128_scaleUpSpec minM m e).1
      (doNormalize128_scaleUpSpec minM m e).2
      (if stickyTail then (if negative then Guard.new.set_negative else Guard.new).set_sticky
       else if negative then Guard.new.set_negative else Guard.new) with err | ⟨m', e', g'⟩
  · rfl
  dsimp only
  split
  · rfl
  have hle := doNormalize_scaleDown128Spec_le hd
  have hmax := maxM.toNat_lt
  have hle' : m'.toNat ≤ maxM.toNat := by
    have := BitVec.le_def.mp hle
    rw [toNat_toUInt128] at this; exact this
  rw [toUInt64Checked_of_lt (by omega)]
  rfl

/-- `operator_mul` never wraps: the product of two 64-bit mantissas fits 128 bits. -/
lemma Number.operator_mul_eq_spec (x y : Number) (mode : rounding_mode) :
    x.operator_mul y mode = x.operator_mulSpec y mode := by
  unfold Number.operator_mul Number.operator_mulSpec
  split
  · rfl
  split
  · rfl
  have hx := x.mantissa_.toNat_lt
  have hy := y.mantissa_.toNat_lt
  rw [BitVec.mulChecked_of_lt (by
      rw [toNat_toUInt128, toNat_toUInt128]
      calc x.mantissa_.toNat * y.mantissa_.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
        _ = 2 ^ 128 := by norm_num), ok_bind]
  dsimp only
  rw [scaleDown128_eq_spec, ok_bind]
  rfl

/-- Close the `minMantissa ≤ 10^18` side condition of an `_eq_spec` rewrite. -/
macro "min_fit" : tactic => `(tactic| first
  | exact XRPL.Model.Protocol.largeRange_min_toNat_le
  | exact XRPL.Model.Protocol.cMinValue_toNat_le
  | assumption
  | (show _ ≤ 10 ^ 18; decide))

/-- Rewrite a `doRoundUp` at one of the model's minimum mantissas to its raw twin. -/
macro "rw_doRoundUp_spec" : tactic => `(tactic| first
  | rw [XRPL.Model.Protocol.Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ XRPL.Model.Protocol.largeRange_min_toNat_le]
  | rw [XRPL.Model.Protocol.Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ XRPL.Model.Protocol.cMinValue_toNat_le])

lemma Guard.doRoundUp_refines (g : Guard) (negative : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) :
    Refines (g.doRoundUp negative m e minM maxM mode loc) (g.doRoundUpSpec negative m e minM maxM mode loc) := by
  unfold Guard.doRoundUp Guard.doRoundUpSpec
  rw [Guard.pushOverflow_eq_spec, ok_bind]
  dsimp only [Guard.doDropDigit]
  refine Refines.bind_ok ?_ (Refines.refl _)
  split_ifs <;> first
    | exact Guard.bringIntoRange_refines _ _ _ _
    | exact Refines.bind_ok (UInt64.addChecked_refines _ _) (Guard.bringIntoRange_refines _ _ _ _)

/-- A successful `doRoundUp` gives the result of its raw twin. -/
lemma Guard.doRoundUp_ok_spec {g : Guard} {negative : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {loc : Error} {r : RoundResult} (h : g.doRoundUp negative m e minM maxM mode loc = .ok r) :
    g.doRoundUpSpec negative m e minM maxM mode loc = .ok r :=
  (Guard.doRoundUp_refines g negative m e minM maxM mode loc).ok_eq h

lemma doNormalize_scaleUp_refines (minM m : UInt64) (e : Int) :
    Refines (doNormalize_scaleUp minM m e) (.ok (doNormalize_scaleUpSpec minM m e)) := by
  induction m, e using doNormalize_scaleUpSpec.induct minM with
  | case1 m e h ih =>
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, ite_eq_left h, ite_eq_left h]
    exact Refines.bind_ok (UInt64.mulChecked_refines _ _) ih
  | case2 m e h =>
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, ite_eq_right h, ite_eq_right h]
    exact Refines.refl _

lemma doNormalize_refines (negative : Bool) (m : UInt64) (e : Int) (minM maxM : UInt64) (mode : rounding_mode) :
    Refines (doNormalize negative m e minM maxM mode) (doNormalizeSpec negative m e minM maxM mode) := by
  unfold doNormalize doNormalizeSpec
  split
  · exact Refines.refl _
  · rcases doNormalize_scaleUp_refines minM m e with h | h
    · rw [h]; exact Refines.refl _
    · rw [h]; exact Refines.wrap _

/-- A successful `doNormalize` gives the result of its raw twin. -/
lemma doNormalize_ok_spec {negative : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64} {mode : rounding_mode}
    {r : Number} (h : doNormalize negative m e minM maxM mode = .ok r) :
    doNormalizeSpec negative m e minM maxM mode = .ok r :=
  (doNormalize_refines negative m e minM maxM mode).ok_eq h

lemma recover_refines (u m : UInt128) (e : Int) (g : Guard) (fuel : Nat) :
    Refines (Number.operator_add.recover u m e g fuel) (.ok (recoverSpec u m e g fuel)) := by
  induction fuel generalizing m e g with
  | zero =>
    unfold Number.operator_add.recover recoverSpec
    exact Refines.refl _
  | succ n ih =>
    unfold Number.operator_add.recover recoverSpec
    split
    · dsimp only
      exact Refines.bind_ok (BitVec.mulChecked_refines _ _)
        (Refines.bind_ok (BitVec.subChecked_refines _ _) (ih _ _ _))
    · exact Refines.refl _

/-- `adjustExpand` multiplies only a mantissa below `upperLimit`, so it never wraps when ten times the limit fits. -/
lemma adjustExpand_eq_spec (u m : UInt128) (ee se : Int) (hu : u.toNat * 10 < 2 ^ 128) :
    adjustExpand u m ee se = .ok (adjustExpandSpec u m ee se) := by
  rw [adjustExpand, adjustExpandSpec]
  split
  · rename_i h
    have hlt : m.toNat < u.toNat := BitVec.lt_def.mp h.2.2
    rw [BitVec.mulChecked_of_lt (by rw [show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind]
    exact adjustExpand_eq_spec u _ _ se hu
  · rfl
termination_by (ee - se).toNat
decreasing_by omega

/-- `adjust` gives its raw twin when ten times the limit fits. -/
lemma adjust_eq_spec (u em : UInt128) (ee : Int) (sm : UInt64) (se : Int) (g : Guard)
    (hu : u.toNat * 10 < 2 ^ 128) : adjust u em ee sm se g = .ok (adjustSpec u em ee sm se g) := by
  unfold adjust adjustSpec
  generalize adjustShrinkZeros g sm se ee = s
  obtain ⟨sm', se', g'⟩ := s
  dsimp only
  rw [adjustExpand_eq_spec u em ee se' hu, ok_bind]
  generalize adjustExpandSpec u em ee se' = x
  obtain ⟨em', ee'⟩ := x
  dsimp only
  rw [doDropDigitWithTargetU64_eq_spec]
  generalize alignDownSpec sm' se' g' ee' = d
  obtain ⟨d1, d2, d3⟩ := d
  rfl

lemma Number.operator_add_refines (x y : Number) (mode : rounding_mode) :
    Refines (x.operator_add y mode) (x.operator_addSpec y mode) := by
  have hu : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := by decide
  unfold Number.operator_add Number.operator_addSpec
  split
  · exact Refines.refl _
  split
  · exact Refines.refl _
  split
  · exact Refines.refl _
  dsimp only
  refine Refines.bind_ok (b := Number.addAlignSpec x y) ?_ ?_
  · unfold Number.addAlignSpec
    split
    · rw [adjust_eq_spec _ _ _ _ _ _ hu, ok_bind]; exact Refines.refl _
    split
    · rw [adjust_eq_spec _ _ _ _ _ _ hu, ok_bind]; exact Refines.refl _
    · exact Refines.refl _
  generalize Number.addAlignSpec x y = a
  obtain ⟨xm, ym, xe, g⟩ := a
  dsimp only
  split
  · exact Refines.bind_ok (BitVec.addChecked_refines _ _) (Refines.refl _)
  · refine Refines.bind_ok (b := if xm > ym then (xm - ym, x.negative_) else (ym - xm, y.negative_)) ?_ ?_
    · split
      · exact Refines.bind_ok (BitVec.subChecked_refines _ _) (Refines.refl _)
      · exact Refines.bind_ok (BitVec.subChecked_refines _ _) (Refines.refl _)
    · generalize (if xm > ym then (xm - ym, x.negative_) else (ym - xm, y.negative_)) = d
      obtain ⟨d1, d2⟩ := d
      dsimp only
      refine Refines.bind_ok (recover_refines _ _ _ _ _) ?_
      generalize recoverSpec (toUInt128 largeRange.min * 1000) d1 xe g 40 = r
      obtain ⟨r1, r2, r3⟩ := r
      dsimp only
      refine Refines.bind_ok ?_ (Refines.refl _)
      split_ifs
      all_goals first
        | exact Refines.refl _
        | exact BitVec.subChecked_refines _ _

/-- A successful `operator_add` gives the result of its raw twin. -/
lemma Number.operator_add_ok_spec {x y : Number} {mode : rounding_mode} {z : Number}
    (h : x.operator_add y mode = .ok z) : x.operator_addSpec y mode = .ok z :=
  (Number.operator_add_refines x y mode).ok_eq h

lemma Guard.doRoundUpSpec_ne_wrap (g : Guard) (negative : Bool) (m : UInt64) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) {loc : Error} (hloc : loc ≠ .wrap) :
    g.doRoundUpSpec negative m e minM maxM mode loc ≠ .error .wrap := by
  unfold Guard.doRoundUpSpec
  dsimp only
  split_ifs <;> simp [hloc]

/-- `doRoundUp` never wraps when `minMantissa ≤ 10^18`. -/
lemma Guard.doRoundUp_ne_wrap (g : Guard) (negative : Bool) (m : UInt64) (e : Int) {minM : UInt64}
    (maxM : UInt64) (mode : rounding_mode) {loc : Error} (hmin : minM.toNat ≤ 10 ^ 18) (hloc : loc ≠ .wrap) :
    g.doRoundUp negative m e minM maxM mode loc ≠ .error .wrap := by
  rw [Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ hmin]
  exact Guard.doRoundUpSpec_ne_wrap _ _ _ _ _ _ _ hloc

lemma doNormalize_scaleDown_ne_wrap' (maxMantissa m : UInt64) (e : Int) (g : Guard) :
    doNormalize_scaleDown maxMantissa m e g ≠ .error .wrap := by
  fun_induction doNormalize_scaleDown maxMantissa m e g <;> simp_all

lemma doNormalize_capAtMaxRep_ne_wrap' (m : UInt64) (e : Int) (g : Guard) :
    doNormalize_capAtMaxRep m e g ≠ .error .wrap := by
  unfold doNormalize_capAtMaxRep
  split
  · split <;> simp
  · simp

lemma doNormalize_scaleDown128Spec_ne_wrap (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard) :
    doNormalize_scaleDown128Spec maxMantissa m e g ≠ .error .wrap := by
  fun_induction doNormalize_scaleDown128Spec maxMantissa m e g <;> simp_all

/-- `doNormalize` never wraps when `minMantissa ≤ 10^18`. -/
lemma doNormalize_ne_wrap (negative : Bool) (m : UInt64) (e : Int) {minM : UInt64} (maxM : UInt64)
    (mode : rounding_mode) (hmin : minM.toNat ≤ 10 ^ 18) :
    doNormalize negative m e minM maxM mode ≠ .error .wrap := by
  rw [doNormalize_eq_spec _ _ _ _ _ hmin]
  unfold doNormalizeSpec
  split
  · exact nofun
  dsimp only
  intro h
  split at h
  · rename_i err herr; cases h; exact doNormalize_scaleDown_ne_wrap' _ _ _ _ herr
  split at h
  · cases h
  split at h
  · rename_i err herr; cases h; exact doNormalize_capAtMaxRep_ne_wrap' _ _ _ herr
  split at h
  · rename_i err herr; cases h
    exact Guard.doRoundUp_ne_wrap _ _ _ _ _ _ hmin (by decide) herr
  · cases h

/-- `doNormalize128` never wraps when `minMantissa ≤ 10^18`. -/
lemma doNormalize128_ne_wrap (negative : Bool) (m : UInt128) (e : Int) {minM : UInt64} (maxM : UInt64)
    (mode : rounding_mode) (stickyTail : Bool) (hmin : minM.toNat ≤ 10 ^ 18) :
    doNormalize128 negative m e minM maxM mode stickyTail ≠ .error .wrap := by
  rw [doNormalize128_eq_spec]
  unfold doNormalize128Spec
  split
  · exact nofun
  dsimp only
  intro h
  split at h
  · rename_i err herr; cases h; exact doNormalize_scaleDown128Spec_ne_wrap _ _ _ _ herr
  split at h
  · cases h
  split at h
  · rename_i err herr; cases h; exact doNormalize_capAtMaxRep_ne_wrap' _ _ _ herr
  split at h
  · rename_i err herr; cases h
    exact Guard.doRoundUp_ne_wrap _ _ _ _ _ _ hmin (by decide) herr
  · cases h

end XRPL.Model.Protocol
