import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.Basic

/-! # The normalized mantissa stays within the range

`doNormalize` returns a mantissa of at most `maxMantissa` when the range sits below `maxRep` and a scaled-up
minimum fits it, as the 16-digit range of `normalizeToRange` does. -/

namespace XRPL.Model.Protocol

/-- `bringIntoRangeSpec` keeps a bound that its scale-up keeps. -/
lemma bringIntoRangeSpec_mantissa_toNat_le {neg : Bool} {X : UInt64} {e : Int} {minM : UInt64} {B : Nat}
    (hB : B < 2 ^ 64) (hX : X.toNat ≤ B) (hscale : X.toNat < minM.toNat → X.toNat * 10 ≤ B) :
    (Guard.bringIntoRangeSpec neg X e minM).mantissa_.toNat ≤ B := by
  unfold Guard.bringIntoRangeSpec
  dsimp only
  split
  · rename_i h
    have hlt : X.toNat < minM.toNat := UInt64.lt_iff_toNat_lt.mp h.1
    have h10 : (X * 10).toNat = X.toNat * 10 := by
      rw [UInt64.toNat_mul, show (10 : UInt64).toNat = 10 from rfl, Nat.mod_eq_of_lt (by have := hscale hlt; omega)]
    dsimp only
    split
    · simp
    · rw [h10]; exact hscale hlt
  · dsimp only
    split
    · simp
    · exact hX

/-- `doRoundUpSpec` keeps a mantissa of the range within `maxMantissa`. -/
lemma doRoundUpSpec_mantissa_le {g : Guard} {neg : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {loc : Error} {r : RoundResult}
    (hlo : minM.toNat ≤ m.toNat) (hhi : m.toNat ≤ maxM.toNat) (hmax : maxM.toNat < maxRep.toNat)
    (hrange : minM.toNat * 10 ≤ maxM.toNat + 1) (htwo : 2 ≤ maxM.toNat)
    (h : g.doRoundUpSpec neg m e minM maxM mode loc = .ok r) : r.mantissa_.toNat ≤ maxM.toNat := by
  have hrep : maxRep.toNat = 2 ^ 63 - 1 := by decide
  have hm_lt : m.toNat < maxRep.toNat := by omega
  have hB : maxM.toNat < 2 ^ 64 := by omega
  have h10 : (10 : UInt64).toNat = 10 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hnc : ¬ (maxRep < m ∧ m < maxRepUp) := fun hc => by
    have := UInt64.lt_iff_toNat_lt.mp hc.1; omega
  unfold Guard.doRoundUpSpec at h
  rw [pushOverflow_noop_of_lt_maxRep hm_lt] at h
  dsimp only [Guard.doDropDigit] at h
  have key : ∀ x : RoundResult,
      (if x.exponent_ > maxExponent then (.error loc : Except Error RoundResult) else .ok x) = .ok r → r = x := by
    intro x hx
    split at hx
    · cases hx
    · cases hx; rfl
  obtain rfl := key _ h
  have hdiv : (m / 10).toNat = m.toNat / 10 := by rw [UInt64.toNat_div, h10]
  have hdiv1 : (m / 10 + 1).toNat = m.toNat / 10 + 1 := by
    rw [UInt64.toNat_add, hdiv, h1, Nat.mod_eq_of_lt (by omega)]
  have hadd : (m + 1).toNat = m.toNat + 1 := by rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  split_ifs <;> first
    | exact absurd ‹maxRep < m ∧ m < maxRepUp› hnc
    | exact bringIntoRangeSpec_mantissa_toNat_le hB
        (by have := UInt64.lt_iff_toNat_lt.mp ‹m < maxM ∧ m < maxRep›.1; omega) (fun _ => by omega)
    | exact bringIntoRangeSpec_mantissa_toNat_le hB (by omega) (fun _ => by omega)

/-- `doNormalize_scaleDown` returns a mantissa of at most `maxMantissa`. -/
lemma doNormalize_scaleDown_le {maxM m m' : UInt64} {e e' : Int} {g g' : Guard}
    (h : doNormalize_scaleDown maxM m e g = .ok (m', e', g')) : m' ≤ maxM := by
  induction m, e, g using doNormalize_scaleDown.induct maxM with
  | case1 m e g hm he =>
    rw [doNormalize_scaleDown, dif_pos hm, if_pos he] at h; cases h
  | case2 m e g hm he ih =>
    rw [doNormalize_scaleDown, dif_pos hm, if_neg he] at h; exact ih h
  | case3 m e g hm =>
    rw [doNormalize_scaleDown, dif_neg hm] at h
    cases h
    exact UInt64.not_lt.mp hm

/-- `doNormalize` returns a mantissa of at most `maxMantissa` when the range sits below `maxRep`. -/
lemma doNormalize_mantissa_le {neg : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64} {mode : rounding_mode}
    {r : Number} (hmax : maxM.toNat < maxRep.toNat) (hrange : minM.toNat * 10 ≤ maxM.toNat + 1)
    (htwo : 2 ≤ maxM.toNat) (h : doNormalize neg m e minM maxM mode = .ok r) : r.mantissa_.toNat ≤ maxM.toNat := by
  replace h := doNormalize_ok_spec h
  unfold doNormalizeSpec at h
  split at h
  · cases h; simp [Number.zero]
  dsimp only at h
  split at h
  · cases h
  rename_i m2 e2 g2 hsd
  have hle := UInt64.le_iff_toNat_le.mp (doNormalize_scaleDown_le hsd)
  split at h
  · cases h; simp [Number.zero]
  rename_i hck
  have hge : minM.toNat ≤ m2.toNat := by
    have : ¬ m2 < minM := fun h' => hck (by simp [h'])
    exact UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp this)
  have hcap : doNormalize_capAtMaxRep m2 e2 g2 = .ok (m2, e2, g2) := by
    unfold doNormalize_capAtMaxRep
    rw [if_neg (fun h' => by
      have := UInt64.lt_iff_toNat_lt.mp h'
      have : maxRepUp.toNat = 2 ^ 63 + 2 := by decide
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega)]
  rw [hcap] at h
  dsimp only at h
  split at h
  · cases h
  rename_i res hres
  cases h
  exact doRoundUpSpec_mantissa_le hge hle hmax hrange htwo (Guard.doRoundUp_ok_spec hres)

end XRPL.Model.Protocol
