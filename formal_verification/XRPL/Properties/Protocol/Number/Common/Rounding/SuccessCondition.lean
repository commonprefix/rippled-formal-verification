import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.Rounding.Spec
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.Basic

/-! # Exact success conditions for the rounding internals

`doNormalize128` succeeds exactly when `M * 10^e` is below `(maxRepUp + 1) * 10^maxExponent`. These lemmas also
bound when `doRoundUp` overflows, and show that every error of these internals is an overflow error. -/

namespace XRPL.Model.Protocol

/-- A computation that does not succeed, and whose errors are all overflow errors, fails with an overflow error. -/
lemma overflow_of_not_ok {α : Type} {r : Except Error α} (hnot : ¬ ∃ a, r = .ok a)
    (herr : ∀ err, r = .error err → isOverflow err = true) : ∃ err, r = .error err ∧ isOverflow err = true := by
  cases r with
  | ok a => exact absurd ⟨a, rfl⟩ hnot
  | error err => exact ⟨err, rfl, herr err rfl⟩

/-- The raw `doRoundUp` fails only with the error it was handed. -/
lemma Guard.doRoundUpSpec_error_eq {g : Guard} {neg : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {loc err : Error} (h : g.doRoundUpSpec neg m e minM maxM mode loc = .error err) :
    err = loc := by
  unfold Guard.doRoundUpSpec at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

/-- Every `doRoundUp` error is an overflow error when it is handed one. -/
lemma Guard.doRoundUp_error_isOverflow {g : Guard} {neg : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {loc err : Error} (hmin : minM.toNat ≤ 10 ^ 18) (hloc : isOverflow loc = true)
    (h : g.doRoundUp neg m e minM maxM mode loc = .error err) : isOverflow err = true := by
  rw [Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ hmin] at h
  rw [Guard.doRoundUpSpec_error_eq h]
  exact hloc

/-- The 128-bit scale-down loop fails only with `normalize1`. -/
lemma doNormalize_scaleDown128Spec_error_eq {maxM : UInt64} {m : UInt128} {e : Int} {g : Guard} {err : Error} :
    doNormalize_scaleDown128Spec maxM m e g = .error err → err = .normalize1 := by
  fun_induction doNormalize_scaleDown128Spec maxM m e g <;> simp_all

/-- The 64-bit scale-down loop fails only with `normalize1`. -/
lemma doNormalize_scaleDown_error_eq {maxM m : UInt64} {e : Int} {g : Guard} {err : Error} :
    doNormalize_scaleDown maxM m e g = .error err → err = .normalize1 := by
  fun_induction doNormalize_scaleDown maxM m e g <;> simp_all

/-- The `maxRepUp` cap fails only with `normalize1_5`. -/
lemma doNormalize_capAtMaxRep_error_eq {m : UInt64} {e : Int} {g : Guard} {err : Error}
    (h : doNormalize_capAtMaxRep m e g = .error err) : err = .normalize1_5 := by
  unfold doNormalize_capAtMaxRep at h
  split_ifs at h
  cases h
  rfl

/-- Every `doNormalize128` error is an overflow error. -/
lemma doNormalize128_error_isOverflow {negative : Bool} {m : UInt128} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {stickyTail : Bool} {err : Error} (hmin : minM.toNat ≤ 10 ^ 18)
    (h : doNormalize128 negative m e minM maxM mode stickyTail = .error err) : isOverflow err = true := by
  rw [doNormalize128_eq_spec] at h
  unfold doNormalize128Spec at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · rename_i err' herr; cases h; rw [doNormalize_scaleDown128Spec_error_eq herr]; rfl
  split at h
  · cases h
  split at h
  · rename_i err' herr; cases h; rw [doNormalize_capAtMaxRep_error_eq herr]; rfl
  split at h
  · rename_i err' herr; cases h
    exact Guard.doRoundUp_error_isOverflow hmin rfl herr
  · cases h

/-- Every `doNormalize` error is an overflow error. -/
lemma doNormalize_error_isOverflow {negative : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {err : Error} (hmin : minM.toNat ≤ 10 ^ 18)
    (h : doNormalize negative m e minM maxM mode = .error err) : isOverflow err = true := by
  rw [doNormalize_eq_spec _ _ _ _ _ hmin] at h
  unfold doNormalizeSpec at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · rename_i err' herr; cases h; rw [doNormalize_scaleDown_error_eq herr]; rfl
  split at h
  · cases h
  split at h
  · rename_i err' herr; cases h; rw [doNormalize_capAtMaxRep_error_eq herr]; rfl
  split at h
  · rename_i err' herr; cases h
    exact Guard.doRoundUp_error_isOverflow hmin rfl herr
  · cases h

/-- `bringIntoRangeSpec` never raises the exponent. -/
lemma Guard.bringIntoRangeSpec_exponent_le (neg : Bool) (m : UInt64) (e : Int) (minM : UInt64) {B : Int}
    (he : e ≤ B) (hB : -2147483648 ≤ B) : (Guard.bringIntoRangeSpec neg m e minM).exponent_ ≤ B := by
  unfold Guard.bringIntoRangeSpec
  split_ifs <;> dsimp only <;> split_ifs <;> dsimp only <;> omega

/-- A nonzero mantissa below the minimum is scaled up, which takes one off the exponent. -/
lemma Guard.bringIntoRangeSpec_exponent_le_of_lt (neg : Bool) (m : UInt64) (e : Int) (minM : UInt64) {B : Int}
    (hlt : m < minM) (hne : m ≠ 0) (he : e ≤ B + 1) (hB : -2147483648 ≤ B) :
    (Guard.bringIntoRangeSpec neg m e minM).exponent_ ≤ B := by
  unfold Guard.bringIntoRangeSpec
  rw [ite_eq_left ⟨hlt, hne⟩]
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- At `maxRep` and at `maxRepUp` the mantissa after one dropped digit, rounded up or not, is nonzero and below
the minimum. -/
private lemma carry_mantissa_small {m : UInt64} (hm : m ≤ maxRepUp)
    (h1 : ¬(m < largeRange.max ∧ m < maxRep)) (h2 : ¬(maxRep < m ∧ m < maxRepUp)) :
    (m / 10 < largeRange.min ∧ m / 10 ≠ 0) ∧ (m / 10 + 1 < largeRange.min ∧ m / 10 + 1 ≠ 0) := by
  have hcases : m = maxRep ∨ m = maxRepUp := by
    have hm' := UInt64.le_iff_toNat_le.mp hm
    have hrep : maxRep.toNat = 9223372036854775807 := rfl
    have hup : maxRepUp.toNat = 9223372036854775810 := rfl
    simp only [UInt64.lt_iff_toNat_lt, largeRange_max_val, hrep, hup] at h1 h2
    rw [hup] at hm'
    rcases Nat.lt_or_ge m.toNat 9223372036854775810 with h | h
    · left; apply UInt64.toNat_inj.mp; rw [hrep]; omega
    · right; apply UInt64.toNat_inj.mp; rw [hup]; omega
  rcases hcases with rfl | rfl <;> decide

/-- From a mantissa at most `maxRepUp` the raw `doRoundUp` rounds to an exponent no higher than the one it got. A
carry at the top of the mantissa range drops a digit and scales back up. -/
lemma Guard.doRoundUpSpec_exponent_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (loc : Error) {B : Int} (hm : m ≤ maxRepUp) (he : e ≤ B) (hB : -2147483648 ≤ B) :
    ∃ res : RoundResult, res.exponent_ ≤ B ∧
      g.doRoundUpSpec neg m e largeRange.min largeRange.max mode loc =
        (if res.exponent_ > maxExponent then .error loc else .ok res) := by
  unfold Guard.doRoundUpSpec
  dsimp only [Guard.doDropDigit]
  generalize hres : (if ((g.pushOverflowSpec m mode).round mode == 1 ||
      ((g.pushOverflowSpec m mode).round mode == 0 && m % 2 == 1)) = true then _ else _ : RoundResult) = res
  refine ⟨res, ?_, rfl⟩
  rw [← hres]
  split_ifs
  · exact Guard.bringIntoRangeSpec_exponent_le _ _ _ _ he hB
  · exact Guard.bringIntoRangeSpec_exponent_le _ _ _ _ he hB
  · rename_i h1 h2 _
    exact Guard.bringIntoRangeSpec_exponent_le_of_lt _ _ _ _ (carry_mantissa_small hm h1 h2).2.1
      (carry_mantissa_small hm h1 h2).2.2 (by omega) hB
  · rename_i h1 h2 _
    exact Guard.bringIntoRangeSpec_exponent_le_of_lt _ _ _ _ (carry_mantissa_small hm h1 h2).1.1
      (carry_mantissa_small hm h1 h2).1.2 (by omega) hB
  · exact Guard.bringIntoRangeSpec_exponent_le _ _ _ _ he hB
  · exact Guard.bringIntoRangeSpec_exponent_le _ _ _ _ he hB

/-- `doRoundUp` succeeds from a mantissa at most `maxRepUp`, at an exponent no higher than the one it got. -/
lemma Guard.doRoundUp_ok_of_le_maxRepUp (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (mode : rounding_mode) (loc : Error) (hm : m ≤ maxRepUp) (he : e ≤ maxExponent) :
    ∃ res, g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .ok res ∧
      res.exponent_ ≤ Max.max e (-2147483648) := by
  obtain ⟨res, hle, hspec⟩ := Guard.doRoundUpSpec_exponent_le g neg m e mode loc hm
    (le_max_left e (-2147483648)) (le_max_right e (-2147483648))
  have hmax : Max.max e (-2147483648) ≤ maxExponent := max_le he (by unfold maxExponent; norm_num)
  rw [Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ largeRange_min_toNat_le, hspec, ite_eq_right (by omega)]
  exact ⟨res, rfl, hle⟩

/-- `bringIntoRangeSpec` keeps a mantissa at or above the minimum. -/
lemma Guard.bringIntoRangeSpec_of_ge (neg : Bool) {μ : UInt64} {e : Int} (hge : largeRange.min ≤ μ)
    (he : minExponent ≤ e) :
    Guard.bringIntoRangeSpec neg μ e largeRange.min = { negative_ := neg, mantissa_ := μ, exponent_ := e } := by
  have hnlt : ¬ (μ < largeRange.min ∧ μ ≠ 0) := fun h => absurd h.1 (UInt64.not_lt.mpr hge)
  have hne : μ ≠ 0 := by rintro rfl; exact absurd hge (by decide)
  rw [bringIntoRange_noscale_result hnlt, ite_eq_right (not_or.mpr ⟨not_lt.mpr he, hne⟩)]

/-- `bringIntoRangeSpec` scales a nonzero mantissa below the minimum up by one digit. -/
lemma Guard.bringIntoRangeSpec_of_lt (neg : Bool) {μ : UInt64} {e : Int} (hlt : μ < largeRange.min) (hne : μ ≠ 0)
    (he : minExponent ≤ e - 1) :
    Guard.bringIntoRangeSpec neg μ e largeRange.min =
      { negative_ := neg, mantissa_ := μ * 10, exponent_ := e - 1 } := by
  have hmul : (μ * 10).toNat = μ.toNat * 10 := m_mul_ten_no_overflow (UInt64.lt_iff_toNat_lt.mp hlt)
  have hμ : μ.toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.mp h0)
  have hne10 : μ * 10 ≠ 0 := by
    intro h
    have h' := congrArg UInt64.toNat h
    rw [hmul] at h'
    exact hμ (by simpa using h')
  rw [bringIntoRange_rescale_result hlt hne, ite_eq_right (not_or.mpr ⟨not_lt.mpr he, hne10⟩)]

/-- The guard rounds an odd mantissa up: it is above the midpoint or at a tie. -/
def Guard.roundsUpOdd (g : Guard) (mode : rounding_mode) : Bool := g.round mode == 1 || g.round mode == 0

/-- The guard rounds up, and still rounds an odd mantissa up after one more dropped digit `0`. -/
def Guard.roundsUpTwice (g : Guard) (mode : rounding_mode) : Bool :=
  g.round mode == 1 && ((g.push 0).round mode == 1 || (g.push 0).round mode == 0)

/-- The four shapes of a `doRoundUp` result `(M', E')` from a mantissa `m` at an exponent `e ≥ maxExponent`. The
mantissa is scaled up without or with a round-up, stays within `maxRepUp`, or carries past it. -/
def Guard.TopShape (g : Guard) (mode : rounding_mode) (m : UInt64) (e : Int) (M' : UInt64) (E' : Int) : Prop :=
  (m.toNat < 10 ^ 18 ∧ (g.round mode == 1 || (g.round mode == 0 && m % 2 == 1)) = false ∧
      M'.toNat = m.toNat * 10 ∧ E' = e - 1) ∨
    (m.toNat + 1 < 10 ^ 18 ∧ (g.round mode == 1 || (g.round mode == 0 && m % 2 == 1)) = true ∧
      M'.toNat = (m.toNat + 1) * 10 ∧ E' = e - 1) ∨
    (10 ^ 18 ≤ m.toNat + 1 ∧ 10 ^ 18 ≤ M'.toNat ∧ M'.toNat ≤ 9223372036854775810 ∧ E' = e ∧
      (m.toNat = 9223372036854775810 → g.roundsUpTwice mode = false)) ∨
    (m.toNat = 9223372036854775810 ∧ g.roundsUpTwice mode = true ∧ M'.toNat = 9223372036854775820 ∧ E' = e)

/-- From a mantissa in `[922337203685477581, maxRepUp]` at an exponent `e ≥ maxExponent`, `doRoundUp` computes one
of the four `TopShape` results and fails exactly when its exponent is above `maxExponent`. -/
lemma Guard.doRoundUp_top_shape (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (loc : Error) (hlo : 922337203685477581 ≤ m.toNat) (hhi : m.toNat ≤ 9223372036854775810)
    (he : maxExponent ≤ e) :
    ∃ (M' : UInt64) (E' : Int),
      g.doRoundUp neg m e largeRange.min largeRange.max mode loc =
        (if E' > maxExponent then .error loc
         else .ok { negative_ := neg, mantissa_ := M', exponent_ := E' }) ∧
      g.TopShape mode m e M' E' := by
  have hemin : minExponent ≤ e - 1 := by unfold minExponent maxExponent at *; omega
  have hemin' : minExponent ≤ e := by omega
  have hemin'' : minExponent ≤ e + 1 - 1 := by omega
  have hrep : maxRep.toNat = 9223372036854775807 := rfl
  have hup : maxRepUp.toNat = 9223372036854775810 := rfl
  rw [Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ largeRange_min_toNat_le]
  unfold Guard.doRoundUpSpec
  dsimp only [Guard.doDropDigit]
  generalize hres : (if ((g.pushOverflowSpec m mode).round mode == 1 ||
      ((g.pushOverflowSpec m mode).round mode == 0 && m % 2 == 1)) = true then _ else _ : RoundResult) = res
  suffices h : ∃ (M' : UInt64) (E' : Int),
      res = { negative_ := neg, mantissa_ := M', exponent_ := E' } ∧ g.TopShape mode m e M' E' by
    obtain ⟨M', E', rfl, hs⟩ := h
    exact ⟨M', E', rfl, hs⟩
  subst hres
  by_cases hlt : m.toNat < 9223372036854775807
  · -- below the cusp: no overflow push, and the mantissa takes the plain round-up or stays
    rw [pushOverflow_noop_of_lt_maxRep (by rw [hrep]; exact hlt) g mode]
    have hC1 : m < largeRange.max ∧ m < maxRep :=
      ⟨UInt64.lt_iff_toNat_lt.mpr (by rw [largeRange_max_val]; omega),
        UInt64.lt_iff_toNat_lt.mpr (by rw [hrep]; exact hlt)⟩
    have hC2 : ¬ (maxRep < m ∧ m < maxRepUp) := fun h => by
      have := UInt64.lt_iff_toNat_lt.mp h.1
      rw [hrep] at this
      omega
    by_cases hru : (g.round mode == 1 || (g.round mode == 0 && m % 2 == 1)) = true
    · rw [ite_eq_left hru, ite_eq_left hC1]
      have hadd : (m + 1).toNat = m.toNat + 1 := m_add_one_no_overflow (by rw [hrep]; omega)
      by_cases hsm : m.toNat + 1 < 10 ^ 18
      · have hlt' : m + 1 < largeRange.min :=
          UInt64.lt_iff_toNat_lt.mpr (by rw [hadd, largeRange_min_val]; omega)
        have hne : m + 1 ≠ 0 := fun h0 => by
          have h' := congrArg UInt64.toNat h0
          rw [hadd] at h'
          simp at h'
        rw [Guard.bringIntoRangeSpec_of_lt neg hlt' hne hemin]
        refine ⟨(m + 1) * 10, e - 1, rfl, Or.inr (Or.inl ⟨hsm, hru, ?_, rfl⟩)⟩
        rw [m_mul_ten_no_overflow (UInt64.lt_iff_toNat_lt.mp hlt'), hadd]
      · have hge : largeRange.min ≤ m + 1 :=
          UInt64.le_iff_toNat_le.mpr (by rw [hadd, largeRange_min_val]; omega)
        rw [Guard.bringIntoRangeSpec_of_ge neg hge hemin']
        exact ⟨m + 1, e, rfl, Or.inr (Or.inr (Or.inl ⟨by omega, by rw [hadd]; omega, by rw [hadd]; omega, rfl,
          fun h => by omega⟩))⟩
    · rw [ite_eq_right hru, ite_eq_right hC2]
      have hru' := (Bool.not_eq_true _).mp hru
      by_cases hsm : m.toNat < 10 ^ 18
      · have hlt' : m < largeRange.min := UInt64.lt_iff_toNat_lt.mpr (by rw [largeRange_min_val]; omega)
        have hne : m ≠ 0 := by rintro rfl; simp at hlo
        rw [Guard.bringIntoRangeSpec_of_lt neg hlt' hne hemin]
        exact ⟨m * 10, e - 1, rfl,
          Or.inl ⟨hsm, hru', m_mul_ten_no_overflow (UInt64.lt_iff_toNat_lt.mp hlt'), rfl⟩⟩
      · have hge : largeRange.min ≤ m := UInt64.le_iff_toNat_le.mpr (by rw [largeRange_min_val]; omega)
        rw [Guard.bringIntoRangeSpec_of_ge neg hge hemin']
        exact ⟨m, e, rfl, Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, rfl, fun h => by omega⟩))⟩
  · -- the four mantissas from `maxRep` to `maxRepUp`
    have hm4 : m = 9223372036854775807 ∨ m = 9223372036854775808 ∨ m = 9223372036854775809 ∨
        m = 9223372036854775810 := by
      have h4 : m.toNat = 9223372036854775807 ∨ m.toNat = 9223372036854775808 ∨
          m.toNat = 9223372036854775809 ∨ m.toNat = 9223372036854775810 := by omega
      rcases h4 with h | h | h | h
      · exact Or.inl (UInt64.toNat_inj.mp h)
      · exact Or.inr (Or.inl (UInt64.toNat_inj.mp h))
      · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.mp h)))
      · exact Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.mp h)))
    rcases hm4 with rfl | rfl | rfl | rfl
    · simp only [show ¬((9223372036854775807 : UInt64) < largeRange.max ∧ (9223372036854775807 : UInt64) < maxRep)
          from by decide,
        show ¬(maxRep < (9223372036854775807 : UInt64) ∧ (9223372036854775807 : UInt64) < maxRepUp)
          from by decide, ite_false]
      split_ifs
      · rw [Guard.bringIntoRangeSpec_of_lt neg (by decide) (by decide) hemin'']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, by omega,
          fun h => absurd h (by decide)⟩))⟩
      · rw [Guard.bringIntoRangeSpec_of_lt neg (by decide) (by decide) hemin'']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, by omega,
          fun h => absurd h (by decide)⟩))⟩
      · rw [Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl,
          fun h => absurd h (by decide)⟩))⟩
    · simp only [show ¬((9223372036854775808 : UInt64) < largeRange.max ∧ (9223372036854775808 : UInt64) < maxRep)
          from by decide,
        show (maxRep < (9223372036854775808 : UInt64) ∧ (9223372036854775808 : UInt64) < maxRepUp)
          from by decide, and_self, ite_false, ite_true]
      split_ifs
      · rw [Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl,
          fun h => absurd h (by decide)⟩))⟩
      · rw [Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl,
          fun h => absurd h (by decide)⟩))⟩
    · simp only [show ¬((9223372036854775809 : UInt64) < largeRange.max ∧ (9223372036854775809 : UInt64) < maxRep)
          from by decide,
        show (maxRep < (9223372036854775809 : UInt64) ∧ (9223372036854775809 : UInt64) < maxRepUp)
          from by decide, and_self, ite_false, ite_true]
      split_ifs
      · rw [Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl,
          fun h => absurd h (by decide)⟩))⟩
      · rw [Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl,
          fun h => absurd h (by decide)⟩))⟩
    · rw [show g.pushOverflowSpec 9223372036854775810 mode = g from by
        unfold Guard.pushOverflowSpec; rw [ite_eq_right (by decide)]]
      simp only [show ¬((9223372036854775810 : UInt64) < largeRange.max ∧ (9223372036854775810 : UInt64) < maxRep)
          from by decide,
        show ¬(maxRep < (9223372036854775810 : UInt64) ∧ (9223372036854775810 : UInt64) < maxRepUp)
          from by decide,
        show ((9223372036854775810 : UInt64) % 2 == 1) = false from by decide,
        show (9223372036854775810 : UInt64) % 10 = 0 from by decide,
        show ((9223372036854775810 : UInt64) / 10 % 2 == 1) = true from by decide,
        ite_false, Bool.and_false, Bool.or_false, Bool.and_true]
      by_cases h1 : (g.round mode == 1) = true
      · rw [ite_eq_left h1]
        by_cases h2 : ((g.push 0).round mode == 1 || (g.push 0).round mode == 0) = true
        · rw [ite_eq_left h2, Guard.bringIntoRangeSpec_of_lt neg (by decide) (by decide) hemin'']
          refine ⟨_, _, rfl, Or.inr (Or.inr (Or.inr ⟨by decide, ?_, by decide, by omega⟩))⟩
          show (g.round mode == 1 && ((g.push 0).round mode == 1 || (g.push 0).round mode == 0)) = true
          rw [h1, h2]; rfl
        · rw [ite_eq_right h2, Guard.bringIntoRangeSpec_of_lt neg (by decide) (by decide) hemin'']
          refine ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, by omega, fun _ => ?_⟩))⟩
          show (g.round mode == 1 && ((g.push 0).round mode == 1 || (g.push 0).round mode == 0)) = false
          rw [h1, (Bool.not_eq_true _).mp h2]; rfl
      · rw [ite_eq_right h1, Guard.bringIntoRangeSpec_of_ge neg (by decide) hemin']
        refine ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, rfl, fun _ => ?_⟩))⟩
        show (g.round mode == 1 && ((g.push 0).round mode == 1 || (g.push 0).round mode == 0)) = false
        rw [(Bool.not_eq_true _).mp h1]; rfl

/-- Above `maxExponent`, `doRoundUp` fails on a mantissa in `[10^18, maxRepUp]`, since it keeps the exponent. -/
lemma Guard.doRoundUp_error_of_exp_gt (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (loc : Error) (hlo : 10 ^ 18 ≤ m.toNat) (hhi : m.toNat ≤ 9223372036854775810) (he : maxExponent < e) :
    g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .error loc := by
  obtain ⟨M', E', hspec, hshape⟩ := Guard.doRoundUp_top_shape g neg m e mode loc (by omega) hhi (le_of_lt he)
  have hE : E' = e := by
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h⟩
    · omega
    · omega
    · exact h
    · exact h
  rw [hspec, ite_eq_left (by omega)]

/-- A value `(F + δ) * 10^e` is below `(maxRepUp + 1) * 10^maxExponent` exactly when its whole part `F` is below
`(maxRepUp + 1) * 10^(maxExponent - e)`. -/
lemma scaled_lt_top_iff (F : ℕ) (δ : ℚ) (e : Int) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (he : e ≤ maxExponent) :
    ((F : ℚ) + δ) * (10 : ℚ) ^ e < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) ↔
      F < 9223372036854775811 * 10 ^ (maxExponent - e).toNat := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, maxExponent = e + (d : ℤ) := ⟨(maxExponent - e).toNat, by omega⟩
  have hd' : (maxExponent - e).toNat = d := by omega
  have hpos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  rw [hd', hd, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast,
    show (9223372036854775811 : ℚ) * ((10 : ℚ) ^ e * (10 : ℚ) ^ d)
      = (9223372036854775811 * (10 : ℚ) ^ d) * (10 : ℚ) ^ e from by ring,
    mul_lt_mul_iff_of_pos_right hpos]
  constructor
  · intro h
    have h' : (F : ℚ) < ((9223372036854775811 * 10 ^ d : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast h'
  · intro h
    have h' : ((F + 1 : ℕ) : ℚ) ≤ ((9223372036854775811 * 10 ^ d : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at h'
    linarith

/-- A fraction `δ` far below the whole part `F` does not decide whether `(F + δ) * 10^e` is below
`(maxRepUp + 1) * 10^maxExponent`, at any exponent. -/
lemma scaled_lt_top_iff_of_small (F : ℕ) (δ : ℚ) (e : Int) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδF : δ * 10 ^ 20 ≤ (F : ℚ)) :
    ((F : ℚ) + δ) * (10 : ℚ) ^ e < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) ↔
      (F : ℚ) * (10 : ℚ) ^ e < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  by_cases he : e ≤ maxExponent
  · have h0 := scaled_lt_top_iff F 0 e (le_refl 0) zero_lt_one he
    rw [add_zero] at h0
    rw [scaled_lt_top_iff F δ e hδ0 hδ1 he, h0]
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, e = maxExponent + (d : ℤ) := ⟨(e - maxExponent).toNat, by omega⟩
    have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
    rw [hd, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
    have hcancel : ∀ a : ℚ, a * (T * (10 : ℚ) ^ d) < 9223372036854775811 * T ↔
        a * (10 : ℚ) ^ d < 9223372036854775811 := fun a => by
      rw [show a * (T * (10 : ℚ) ^ d) = (a * (10 : ℚ) ^ d) * T from by ring, mul_lt_mul_iff_of_pos_right hT]
    rw [hcancel, hcancel]
    have hP : (0 : ℚ) < (10 : ℚ) ^ d := by positivity
    constructor
    · intro h
      nlinarith
    · intro h
      -- `F * 10^d` is a whole number below the bound, and `δ * 10^d` is below one
      have hnat : F * 10 ^ d < 9223372036854775811 := by exact_mod_cast h
      have hle : ((F * 10 ^ d + 1 : ℕ) : ℚ) ≤ 9223372036854775811 := by exact_mod_cast hnat
      push_cast at hle
      have hδP : δ * (10 : ℚ) ^ d * 10 ^ 20 ≤ (F : ℚ) * (10 : ℚ) ^ d := by nlinarith
      have h20 : ((10 : ℚ) ^ 20) = 100000000000000000000 := by norm_num
      rw [h20] at hδP
      have hexp : ((F : ℚ) + δ) * (10 : ℚ) ^ d = (F : ℚ) * (10 : ℚ) ^ d + δ * (10 : ℚ) ^ d := by ring
      rw [hexp]
      linarith

/-- The scale-up loop of `doNormalize128` keeps the value `m * 10^e`. It stops at a mantissa of at least `10^18`
or at the bottom exponent. -/
lemma doNormalize128_scaleUp_value (m : UInt128) (e : Int) :
    ((doNormalize128_scaleUpSpec largeRange.min m e).1.toNat : ℚ)
        * (10 : ℚ) ^ (doNormalize128_scaleUpSpec largeRange.min m e).2 = (m.toNat : ℚ) * (10 : ℚ) ^ e ∧
      (10 ^ 18 ≤ (doNormalize128_scaleUpSpec largeRange.min m e).1.toNat ∨
        (doNormalize128_scaleUpSpec largeRange.min m e).2 ≤ minExponent) := by
  induction m, e using doNormalize128_scaleUpSpec.induct (minMantissa := largeRange.min) with
  | case1 m e hcond IH =>
    rw [show doNormalize128_scaleUpSpec largeRange.min m e
        = doNormalize128_scaleUpSpec largeRange.min (m * 10) (e - 1) from by
      rw [doNormalize128_scaleUpSpec.eq_def]
      simp only [ite_eq_left hcond]]
    refine ⟨IH.1.trans ?_, IH.2⟩
    have hlt : m.toNat < 1000000000000000000 := by
      have := BitVec.lt_def.mp hcond.1
      rwa [toNat_toUInt128, largeRange_min_val] at this
    have hmul : (m * 10).toNat = m.toNat * 10 := by
      rw [BitVec.toNat_mul, show (10 : UInt128).toNat = 10 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmul, zpow_sub_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
    push_cast
    ring
  | case2 m e hcond =>
    rw [show doNormalize128_scaleUpSpec largeRange.min m e = (m, e) from by
      rw [doNormalize128_scaleUpSpec.eq_def]; simp only [ite_eq_right hcond]]
    refine ⟨rfl, ?_⟩
    by_cases hm : m < toUInt128 largeRange.min
    · exact Or.inr (not_lt.mp fun h => hcond ⟨hm, h⟩)
    · left
      have := BitVec.le_def.mp (BitVec.not_lt.mp hm)
      rwa [toNat_toUInt128, largeRange_min_val] at this

/-- The scale-down loop of `doNormalize128` errors only on a mantissa at or above
`(maxRepUp + 1) * 10^(maxExponent - e)`. Otherwise its output stays on the same side of that bound. -/
lemma doNormalize_scaleDown128_top_cases (m : UInt128) (e : Int) (g : Guard) (he : e ≤ maxExponent) :
    (∃ err, doNormalize_scaleDown128Spec largeRange.max m e g = .error err ∧
        9223372036854775811 * 10 ^ (maxExponent - e).toNat ≤ m.toNat) ∨
      (∃ (m' : UInt128) (e' : Int) (g' : Guard),
        doNormalize_scaleDown128Spec largeRange.max m e g = .ok (m', e', g') ∧
        e' ≤ maxExponent ∧ m'.toNat ≤ 9999999999999999999 ∧
        (m'.toNat < 9223372036854775811 * 10 ^ (maxExponent - e').toNat ↔
          m.toNat < 9223372036854775811 * 10 ^ (maxExponent - e).toNat)) := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct largeRange.max with
  | case1 m e g hm hetop =>
    left
    refine ⟨.normalize1, by rw [doNormalize_scaleDown128Spec, dite_eq_left hm, ite_eq_left hetop], ?_⟩
    have hgt : 9999999999999999999 < m.toNat := by
      have := BitVec.lt_def.mp hm
      rwa [toNat_toUInt128, largeRange_max_val] at this
    have hd : (maxExponent - e).toNat = 0 := by omega
    rw [hd, pow_zero]
    omega
  | case2 m e g hm hetop IH =>
    have hstep : doNormalize_scaleDown128Spec largeRange.max m e g
        = doNormalize_scaleDown128Spec largeRange.max (m / 10) (e + 1) (g.push (toUInt64 (m % 10))) := by
      rw [doNormalize_scaleDown128Spec, dite_eq_left hm, ite_eq_right hetop]
    have hdiv : (m / 10 : UInt128).toNat = m.toNat / 10 := by
      rw [BitVec.toNat_udiv, show (10 : UInt128).toNat = 10 from rfl]
    have hd : (maxExponent - e).toNat = (maxExponent - (e + 1)).toNat + 1 := by omega
    rw [hstep, hd, pow_succ]
    rw [hdiv] at IH
    set P := (10 : ℕ) ^ (maxExponent - (e + 1)).toNat
    rcases IH (by omega) with ⟨err, herr, hge⟩ | ⟨m', e', g', hok, he', hm', hiff⟩
    · exact Or.inl ⟨err, herr, by omega⟩
    · exact Or.inr ⟨m', e', g', hok, he', hm', hiff.trans (by omega)⟩
  | case3 m e g hm =>
    right
    have hle : m.toNat ≤ 9999999999999999999 := by
      have := BitVec.le_def.mp (BitVec.not_lt.mp hm)
      rwa [toNat_toUInt128, largeRange_max_val] at this
    exact ⟨m, e, g, by rw [doNormalize_scaleDown128Spec, dite_eq_right hm], he, hle, Iff.rfl⟩

/-- `doNormalize128` succeeds exactly when its input `M * 10^e` is below `(maxRepUp + 1) * 10^maxExponent`, in every
rounding mode. -/
lemma doNormalize128_ok_iff_value (zn : Bool) (M : UInt128) (e : Int) (mode : rounding_mode) (sticky : Bool) :
    (∃ result, doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result) ↔
      (M.toNat : ℚ) * (10 : ℚ) ^ e < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  by_cases hM0 : (M == 0) = true
  · have hM : M.toNat = 0 := by rw [beq_iff_eq] at hM0; rw [hM0]; rfl
    refine iff_of_true ⟨Number.zero, by unfold doNormalize128; rw [ite_eq_left hM0]⟩ ?_
    rw [hM, Nat.cast_zero, zero_mul]
    exact mul_pos (by norm_num) hT
  rw [doNormalize128_eq_spec]
  unfold doNormalize128Spec
  rw [ite_eq_right hM0]
  simp only []
  rcases hsu : doNormalize128_scaleUpSpec largeRange.min M e with ⟨M₁, e₁⟩
  simp only []
  obtain ⟨hval, hexit⟩ : (M₁.toNat : ℚ) * (10 : ℚ) ^ e₁ = (M.toNat : ℚ) * (10 : ℚ) ^ e ∧
      (10 ^ 18 ≤ M₁.toNat ∨ e₁ ≤ minExponent) := by
    have h := doNormalize128_scaleUp_value M e
    rw [hsu] at h; exact h
  rw [← hval]
  set g₀ : Guard := (if sticky = true
      then (if zn then Guard.new.set_negative else Guard.new).set_sticky
      else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
  have hmru : maxRepUp.toNat = 9223372036854775810 := rfl
  by_cases he₁ : e₁ ≤ maxExponent
  · have hbridge := scaled_lt_top_iff M₁.toNat 0 e₁ (le_refl 0) zero_lt_one he₁
    rw [add_zero] at hbridge
    rw [hbridge]
    rcases doNormalize_scaleDown128_top_cases M₁ e₁ g₀ he₁ with
      ⟨err, hsd, hge⟩ | ⟨m', e', g', hsd, he', hm', hiff'⟩
    · rw [hsd]
      simp only []
      exact iff_of_false (by rintro ⟨r, hr⟩; cases hr) (by omega)
    rw [hsd, ← hiff']
    simp only []
    have hP1 : 1 ≤ 10 ^ (maxExponent - e').toNat := Nat.one_le_pow _ _ (by norm_num)
    have hP10 : e' < maxExponent → 10 ≤ 10 ^ (maxExponent - e').toNat := fun h =>
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (maxExponent - e').toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfit : m'.toNat < 2 ^ 64 := by omega
    by_cases hund : (e' < minExponent || m' < toUInt128 largeRange.min) = true
    · rw [ite_eq_left hund]
      refine iff_of_true ⟨Number.zero, rfl⟩ ?_
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hund
      rcases hund with h | h
      · have := hP10 (by unfold minExponent maxExponent at *; omega)
        set P := 10 ^ (maxExponent - e').toNat
        omega
      · have := BitVec.lt_def.mp h
        rw [toNat_toUInt128, largeRange_min_val] at this
        set P := 10 ^ (maxExponent - e').toNat
        omega
    rw [ite_eq_right hund]
    unfold doNormalize_capAtMaxRep
    by_cases hcap : toUInt64 m' > maxRepUp
    · have hgt : 9223372036854775810 < m'.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hcap
        rwa [toNat_toUInt64 hfit, hmru] at this
      rw [ite_eq_left hcap]
      by_cases hetop : e' ≥ maxExponent
      · rw [ite_eq_left hetop]
        simp only []
        refine iff_of_false (by rintro ⟨r, hr⟩; cases hr) ?_
        have hd : (maxExponent - e').toNat = 0 := by omega
        rw [hd, pow_zero]
        omega
      · rw [ite_eq_right hetop]
        simp only [divu10]
        have hq : toUInt64 m' / 10 ≤ maxRepUp := by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, toNat_toUInt64 hfit, hmru,
            show (10 : UInt64).toNat = 10 from rfl]
          omega
        obtain ⟨res, hru, -⟩ := Guard.doRoundUp_ok_of_le_maxRepUp (g'.push (toUInt64 m' % 10)) zn
          (toUInt64 m' / 10) (e' + 1) mode .normalize2 hq (by omega)
        rw [hru]
        refine iff_of_true ⟨res.toNumber, rfl⟩ ?_
        have := hP10 (by omega)
        set P := 10 ^ (maxExponent - e').toNat
        omega
    · rw [ite_eq_right hcap]
      simp only []
      have hle : m'.toNat ≤ 9223372036854775810 := by
        have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hcap)
        rwa [toNat_toUInt64 hfit, hmru] at this
      obtain ⟨res, hru, -⟩ := Guard.doRoundUp_ok_of_le_maxRepUp g' zn (toUInt64 m') e' mode .normalize2
        (UInt64.not_lt.mp hcap) he'
      rw [hru]
      refine iff_of_true ⟨res.toNumber, rfl⟩ ?_
      set P := 10 ^ (maxExponent - e').toNat
      omega
  · -- above `maxExponent` the scaled-up mantissa has 19 digits, so no step can bring the exponent back
    have hM₁ : 10 ^ 18 ≤ M₁.toNat := hexit.resolve_right (by unfold minExponent maxExponent at *; omega)
    refine iff_of_false ?_ ?_
    · by_cases hgt : M₁ > toUInt128 largeRange.max
      · rw [show doNormalize_scaleDown128Spec largeRange.max M₁ e₁ g₀ = .error .normalize1 from by
          rw [doNormalize_scaleDown128Spec, dite_eq_left hgt, ite_eq_left (by omega)]]
        simp only []
        rintro ⟨r, hr⟩; cases hr
      · rw [show doNormalize_scaleDown128Spec largeRange.max M₁ e₁ g₀ = .ok (M₁, e₁, g₀) from by
          rw [doNormalize_scaleDown128Spec, dite_eq_right hgt]]
        simp only []
        have hle : M₁.toNat ≤ 9999999999999999999 := by
          have := BitVec.le_def.mp (BitVec.not_lt.mp hgt)
          rwa [toNat_toUInt128, largeRange_max_val] at this
        have hfit : M₁.toNat < 2 ^ 64 := by omega
        have hund : ¬ (e₁ < minExponent || M₁ < toUInt128 largeRange.min) = true := by
          rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          rintro (h | h)
          · unfold minExponent maxExponent at *; omega
          · have := BitVec.lt_def.mp h
            rw [toNat_toUInt128, largeRange_min_val] at this
            omega
        rw [ite_eq_right hund]
        unfold doNormalize_capAtMaxRep
        by_cases hcap : toUInt64 M₁ > maxRepUp
        · rw [ite_eq_left hcap, ite_eq_left (by omega)]
          simp only []
          rintro ⟨r, hr⟩; cases hr
        · rw [ite_eq_right hcap]
          simp only []
          have hcap' : (toUInt64 M₁).toNat ≤ 9223372036854775810 := by
            have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hcap)
            rwa [hmru] at this
          rw [Guard.doRoundUp_error_of_exp_gt g₀ zn (toUInt64 M₁) e₁ mode .normalize2
            (by rw [toNat_toUInt64 hfit]; exact hM₁) hcap' (by omega)]
          rintro ⟨r, hr⟩; cases hr
    · have h10 : (10 : ℚ) ^ (maxExponent : ℤ) * 10 ≤ (10 : ℚ) ^ e₁ := by
        rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hMq : (1000000000000000000 : ℚ) ≤ (M₁.toNat : ℚ) := by exact_mod_cast hM₁
      generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT h10 ⊢
      generalize (10 : ℚ) ^ e₁ = P at h10 ⊢
      nlinarith

/-- `doNormalize128` at an exponent `e ≤ maxExponent` succeeds exactly when its mantissa is below
`(maxRepUp + 1) * 10^(maxExponent - e)`. -/
lemma doNormalize128_ok_iff (zn : Bool) (M : UInt128) (e : Int) (mode : rounding_mode) (sticky : Bool)
    (he : e ≤ maxExponent) :
    (∃ result, doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result) ↔
      M.toNat < 9223372036854775811 * 10 ^ (maxExponent - e).toNat := by
  have h := scaled_lt_top_iff M.toNat 0 e (le_refl 0) zero_lt_one he
  rw [add_zero] at h
  exact (doNormalize128_ok_iff_value zn M e mode sticky).trans h

/-- A guard holds the fraction zero exactly when it is empty. -/
lemma represents_empty_iff {g : Guard} {f : ℚ} (hg : represents g f) : g.empty = true ↔ f = 0 := by
  refine ⟨fun h => represents_empty_eq_zero h hg, fun hf => ?_⟩
  obtain ⟨x, hx_nn, -, hf_eq, hxbit, -⟩ := hg
  have hdv : (0 : ℚ) ≤ (decimalValue g.digits_ : ℚ) / 10 ^ 16 := by positivity
  have hx0 : x = 0 := by linarith
  have hdv0 : decimalValue g.digits_ = 0 := by
    have h' : (decimalValue g.digits_ : ℚ) / 10 ^ 16 = 0 := by linarith
    rcases div_eq_zero_iff.mp h' with h | h
    · exact_mod_cast h
    · norm_num at h
  have hd : g.digits_ = 0 := by
    by_contra hne
    have := decimalValue_pos_of_ne_zero _ hne
    omega
  have hxb : g.xbit_ = false := by
    by_contra hne
    have : x > 0 := hxbit.mp (by simpa using hne)
    linarith
  show (g.digits_ == 0 && !g.xbit_) = true
  rw [hd, hxb]
  rfl

/-- In `to_nearest` an odd mantissa rounds up exactly when the dropped fraction is at least one half. -/
lemma Guard.roundsUpOdd_to_nearest {g : Guard} {f : ℚ} (hg : represents g f) :
    g.roundsUpOdd .to_nearest = true ↔ 1 / 2 ≤ f := by
  unfold Guard.roundsUpOdd
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  by_cases hemp : g.empty = true
  · have hf : f = 0 := represents_empty_eq_zero hemp hg
    have hr : g.round .to_nearest = -2 := by unfold Guard.round; rw [ite_eq_left hemp]
    rw [hr, hf]
    constructor
    · rintro (h | h) <;> exact absurd h (by decide)
    · intro h; norm_num at h
  · obtain ⟨h1, -, h0⟩ := round_correct hemp hg
    rw [h1, h0]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm

/-- In `to_nearest` a round-up never survives one more dropped digit `0`, since the new top digit is `0`. -/
lemma Guard.roundsUpTwice_to_nearest (g : Guard) : g.roundsUpTwice .to_nearest = false := by
  have hsize : g.digits_.toNat ≤ 2 ^ 64 - 1 := by
    have := UInt64.toNat_lt_size g.digits_; simp only [UInt64.size] at this; omega
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have htop : (g.push 0).digits_.toNat < 5764607523034234880 := by
    rw [toNat_push_digits, h0]; omega
  unfold Guard.roundsUpTwice
  rcases Guard.round_to_nearest_of_top_lt_five _ htop with h | h <;> rw [h] <;> simp

/-- In a directed mode both round-up decisions are the plain one, since a tie never arises and one more dropped
digit `0` changes nothing. -/
lemma Guard.roundsUp_directed (g : Guard) (mode : rounding_mode) (hm : mode ≠ .to_nearest) :
    g.roundsUpOdd mode = (g.round mode == 1) ∧ g.roundsUpTwice mode = (g.round mode == 1) := by
  have h0 : (g.round mode == 0) = false := by
    rw [Guard.round_directed_eq g mode hm]
    cases mode
    · exact absurd rfl hm
    all_goals (dsimp only; split_ifs <;> rfl)
  unfold Guard.roundsUpOdd Guard.roundsUpTwice
  rw [Guard.push_zero_round_directed g mode hm, h0, Bool.or_false]
  exact ⟨rfl, Bool.and_self _⟩

/-- `towards_zero` never rounds up. -/
lemma Guard.round_towards_zero_ne_one (g : Guard) : (g.round .towards_zero == 1) = false := by
  rw [Guard.round_directed_eq g .towards_zero (by decide)]
  dsimp only
  split_ifs <;> rfl

/-- `downward` rounds a mantissa up exactly when the value is negative and a nonzero fraction was dropped. -/
lemma Guard.round_downward_eq_one_iff {g : Guard} {f : ℚ} (hg : represents g f) :
    (g.round .downward == 1) = true ↔ (g.sbit_ = true ∧ 0 < f) := by
  have hf0 := represents_nonneg hg
  have hemp := represents_empty_iff hg
  rw [Guard.round_directed_eq g .downward (by decide)]
  dsimp only
  by_cases he : g.empty = true
  · have hf : f = 0 := hemp.mp he
    rw [ite_eq_left he, hf]
    simp
  · have hf : 0 < f := lt_of_le_of_ne hf0 fun h => he (hemp.mpr h.symm)
    rw [ite_eq_right he]
    cases hs : g.sbit_ <;> simp [hf]

/-- `upward` rounds a mantissa up exactly when the value is positive and a nonzero fraction was dropped. -/
lemma Guard.round_upward_eq_one_iff {g : Guard} {f : ℚ} (hg : represents g f) :
    (g.round .upward == 1) = true ↔ (g.sbit_ = false ∧ 0 < f) := by
  have hf0 := represents_nonneg hg
  have hemp := represents_empty_iff hg
  rw [Guard.round_directed_eq g .upward (by decide)]
  dsimp only
  by_cases he : g.empty = true
  · have hf : f = 0 := hemp.mp he
    rw [ite_eq_left he, hf]
    simp
  · have hf : 0 < f := lt_of_le_of_ne hf0 fun h => he (hemp.mpr h.symm)
    rw [ite_eq_right he]
    cases hs : g.sbit_ <;> simp [hf]

end XRPL.Model.Protocol
