import Mathlib.Tactic
import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Common.FixedWidth
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec

/-! # Number internals with raw fixed-width arithmetic

Each `…Spec` function is a Number internal as it was before the wrap checks: the same code with raw fixed-width
operations, calling the other `Spec` helpers and the same checked functions otherwise. The proofs about the
Number internals reason about these twins. A checked function `Refines` its twin: it gives the twin's result, or
stops with `Error.wrap`. The `_eq_spec` lemmas show it gives the twin's result when nothing wraps. -/

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

/-- Below the top exponent the same-sign add check passes. -/
lemma checkSumAtTop_of_lt (z : UInt128) {e : Int} (h : e < maxExponent) : checkSumAtTop z e = .ok () := by
  simp [checkSumAtTop, h]

/-- A successful same-sign add passed its top-exponent check. -/
lemma checkSumAtTop_bind_ok {α : Type} {z : UInt128} {e : Int} {k : Unit → Except Error α} {r : α}
    (h : (checkSumAtTop z e >>= k) = .ok r) : k () = .ok r := by
  cases hc : checkSumAtTop z e with
  | error err => rw [hc] at h; cases h
  | ok u => rw [hc, ok_bind] at h; exact h

lemma Refines.ok_eq {α : Type} {new old : Except Error α} {r : α} (h : Refines new old) (hn : new = .ok r) :
    old = .ok r := by
  rcases h with rfl | rfl
  · exact hn
  · cases hn

lemma Refines.error_eq {α : Type} {new old : Except Error α} {e : Error} (h : Refines new old)
    (hn : new = .error e) : e = .wrap ∨ old = .error e := by
  rcases h with rfl | rfl
  · exact Or.inr hn
  · cases hn; exact Or.inl rfl

lemma Refines.ne_error {α : Type} {new old : Except Error α} {e : Error} (h : Refines new old)
    (hold : old ≠ .error e) (he : e ≠ .wrap) : new ≠ .error e := by
  rcases h with rfl | rfl
  · exact hold
  · intro h'; cases h'; exact he rfl

lemma Refines.eq_of_ne {α : Type} {new old : Except Error α} (h : Refines new old) (hn : new ≠ .error .wrap) :
    new = old := by
  rcases h with h | h
  · exact h
  · exact absurd h hn

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

lemma toUInt64Checked_refines (x : UInt128) : Refines (toUInt64Checked x) (.ok (toUInt64 x)) := by
  unfold toUInt64Checked; split
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
    rw [if_pos h, if_pos h, UInt64.mulChecked_of_lt (by rw [show (10 : UInt64).toNat = 10 from rfl]; omega),
      ok_bind, pure_eq, ok_bind]
    dsimp only
    split <;> rfl
  · rw [if_neg h, if_neg h, pure_eq, ok_bind]
    dsimp only
    split <;> rfl

lemma Guard.bringIntoRange_refines (negative : Bool) (m : UInt64) (e : Int) (minM : UInt64) :
    Refines (Guard.bringIntoRange negative m e minM) (.ok (Guard.bringIntoRangeSpec negative m e minM)) := by
  unfold Guard.bringIntoRange Guard.bringIntoRangeSpec
  by_cases h : m < minM ∧ m ≠ 0
  · rw [if_pos h, if_pos h]
    rcases UInt64.mulChecked_refines m 10 with h' | h'
    · rw [h', ok_bind, pure_eq, ok_bind]
      dsimp only
      split <;> exact Refines.refl _
    · rw [h', err_bind, err_bind]; exact Refines.wrap _
  · rw [if_neg h, if_neg h, pure_eq, ok_bind]
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
    first | rfl | simp_all

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

/-- `doDropDigit128` with raw narrowing. -/
def Guard.doDropDigit128Spec (g : Guard) (mantissa : UInt128) (exponent : Int) : Guard × UInt128 × Int :=
  (g.push (toUInt64 (mantissa % 10)), mantissa / 10, exponent + 1)

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

/-- `operator_add` with raw arithmetic. -/
def Number.operator_addSpec (x y : Number) (mode : rounding_mode) : Except Error Number := do
  if y.operator_eq Number.zero then return x
  else if x.operator_eq Number.zero then return y
  else if x.operator_eq (y.operator_neg) then return Number.zero
  else
    let xn := x.negative_
    let xm := x.mantissa_
    let xe := x.exponent_
    let yn := y.negative_
    let ym := y.mantissa_
    let ye := y.exponent_
    let (xm, xe, ym, _ye, g) :=
      if xe < ye then
        let g := if xn then Guard.new.set_negative else Guard.new
        let (xm', xe', g') := Number.operator_add.alignDown xm xe g ye
        (xm', xe', ym, ye, g')
      else if xe > ye then
        let g := if yn then Guard.new.set_negative else Guard.new
        let (ym', _ye', g') := Number.operator_add.alignDown ym ye g xe
        (xm, xe, ym', xe, g')
      else
        let g := if xn then Guard.new.set_negative else Guard.new
        (xm, xe, ym, ye, g)
    if xn == yn then
      let zm128 : UInt128 := toUInt128 xm + toUInt128 ym
      checkSumAtTop zm128 xe
      let (zm, xe, g) :=
        if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
          let (g', zm128', xe') := g.doDropDigit128Spec zm128 xe
          (toUInt64 zm128', xe', g')
        else (toUInt64 zm128, xe, g)
      match g.doRoundUp xn zm xe largeRange.min largeRange.max mode .overflow with
      | .error err => .error err
      | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode
    else
      let (zm128, zn, ze) :=
        if xm > ym then (toUInt128 xm - toUInt128 ym, xn, xe)
        else (toUInt128 ym - toUInt128 xm, yn, xe)
      let upperLimit : UInt128 := toUInt128 largeRange.min * 1000
      let (zm128, ze, g) := recoverSpec upperLimit zm128 ze g 40
      let stickyTail := !g.empty
      let zm128 := if g.empty then zm128 else zm128 - 1
      doNormalize128 zn zm128 ze largeRange.min largeRange.max mode stickyTail

lemma doNormalize_scaleUp_eq_spec {minM : UInt64} (m : UInt64) (e : Int) (hmin : minM.toNat ≤ 10 ^ 18) :
    doNormalize_scaleUp minM m e = .ok (doNormalize_scaleUpSpec minM m e) := by
  induction m, e using doNormalize_scaleUpSpec.induct minM with
  | case1 m e h ih =>
    have hlt : m.toNat < minM.toNat := UInt64.lt_iff_toNat_lt.mp h.1
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, if_pos h, if_pos h,
      UInt64.mulChecked_of_lt (by rw [show (10 : UInt64).toNat = 10 from rfl]; omega), ok_bind]
    exact ih
  | case2 m e h =>
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, if_neg h, if_neg h]

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
    rw [scaleDown128, scaleDown128Spec, dif_pos h, dif_pos h, toUInt64Checked_of_lt (toNat_umod_ten_lt m),
      ok_bind]
    exact ih
  | case2 m e g h =>
    have hle : m.toNat ≤ (toUInt128 maxRepUp).toNat := not_lt.mp h
    have hup : maxRepUp.toNat = 2 ^ 63 + 2 := by decide
    rw [toNat_toUInt128] at hle
    rw [scaleDown128, scaleDown128Spec, dif_neg h, dif_neg h, toUInt64Checked_of_lt (by omega), ok_bind]
    rfl

lemma doNormalize_scaleDown128_eq_spec (maxM : UInt64) (m : UInt128) (e : Int) (g : Guard) :
    doNormalize_scaleDown128 maxM m e g = doNormalize_scaleDown128Spec maxM m e g := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct maxM with
  | case1 m e g h he =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dif_pos h, dif_pos h, if_pos he, if_pos he]
  | case2 m e g h he ih =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dif_pos h, dif_pos h, if_neg he, if_neg he,
      toUInt64Checked_of_lt (toNat_umod_ten_lt m), ok_bind]
    exact ih
  | case3 m e g h =>
    rw [doNormalize_scaleDown128, doNormalize_scaleDown128Spec, dif_neg h, dif_neg h]

/-- The mantissa `doNormalize_scaleDown128Spec` returns is at most `maxMantissa`. -/
lemma doNormalize_scaleDown128Spec_le {maxM : UInt64} {m m' : UInt128} {e e' : Int} {g g' : Guard}
    (h : doNormalize_scaleDown128Spec maxM m e g = .ok (m', e', g')) : m' ≤ toUInt128 maxM := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct maxM with
  | case1 m e g hm he =>
    rw [doNormalize_scaleDown128Spec, dif_pos hm, if_pos he] at h; cases h
  | case2 m e g hm he ih =>
    rw [doNormalize_scaleDown128Spec, dif_pos hm, if_neg he] at h; exact ih h
  | case3 m e g hm =>
    rw [doNormalize_scaleDown128Spec, dif_neg hm] at h
    cases h
    exact BitVec.not_lt.mp hm

lemma doNormalize128_scaleUp_eq_spec (minM : UInt64) (m : UInt128) (e : Int) :
    doNormalize128.scaleUp minM m e = .ok (doNormalize128_scaleUpSpec minM m e) := by
  induction m, e using doNormalize128_scaleUpSpec.induct minM with
  | case1 m e h ih =>
    have hlt : m.toNat < (toUInt128 minM).toNat := h.1
    have hmin := minM.toNat_lt
    rw [toNat_toUInt128] at hlt
    rw [doNormalize128.scaleUp, doNormalize128_scaleUpSpec, if_pos h, if_pos h,
      BitVec.mulChecked_of_lt (by rw [show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind]
    exact ih
  | case2 m e h =>
    rw [doNormalize128.scaleUp, doNormalize128_scaleUpSpec, if_neg h, if_neg h]

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

lemma Guard.doDropDigit128_eq_spec (g : Guard) (m : UInt128) (e : Int) :
    g.doDropDigit128 m e = .ok (g.doDropDigit128Spec m e) := by
  unfold Guard.doDropDigit128 Guard.doDropDigit128Spec
  rw [toUInt64Checked_of_lt (toNat_umod_ten_lt m), ok_bind]
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
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, if_pos h, if_pos h]
    exact Refines.bind_ok (UInt64.mulChecked_refines _ _) ih
  | case2 m e h =>
    rw [doNormalize_scaleUp, doNormalize_scaleUpSpec, if_neg h, if_neg h]
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

lemma Number.operator_add_refines (x y : Number) (mode : rounding_mode) :
    Refines (x.operator_add y mode) (x.operator_addSpec y mode) := by
  unfold Number.operator_add Number.operator_addSpec
  split
  · exact Refines.refl _
  split
  · exact Refines.refl _
  split
  · exact Refines.refl _
  dsimp (config := { iota := false, proj := false, etaStruct := .none }) only
  generalize (if x.exponent_ < y.exponent_ then _ else _ : UInt64 × Int × UInt64 × Int × Guard) = t
  obtain ⟨xm, xe, ym, ye, g⟩ := t
  dsimp only
  split
  · refine Refines.bind_ok (BitVec.addChecked_refines _ _) ?_
    refine Refines.bind (Refines.refl _) fun _ _ => ?_
    refine Refines.bind_ok ?_ (Refines.refl _)
    split
    · rw [Guard.doDropDigit128_eq_spec, ok_bind]
      exact Refines.bind_ok (toUInt64Checked_refines _) (Refines.refl _)
    · exact Refines.bind_ok (toUInt64Checked_refines _) (Refines.refl _)
  · refine Refines.bind_ok (b := if xm > ym then (toUInt128 xm - toUInt128 ym, x.negative_, xe)
        else (toUInt128 ym - toUInt128 xm, y.negative_, xe)) ?_ ?_
    · split
      · exact Refines.bind_ok (BitVec.subChecked_refines _ _) (Refines.refl _)
      · exact Refines.bind_ok (BitVec.subChecked_refines _ _) (Refines.refl _)
    · refine Refines.bind_ok (recover_refines _ _ _ _ _) ?_
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
