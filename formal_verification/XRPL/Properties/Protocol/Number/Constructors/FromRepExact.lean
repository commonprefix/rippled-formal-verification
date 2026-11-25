import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.AlgorithmicFacts
import XRPL.Properties.Protocol.Number.Normalize.Common.Underflow
import XRPL.Properties.Protocol.Number.Constructors.Common.Proofs

/-! # `from_rep` is value-exact on any in-range `Int64` mantissa

`from_rep` scales an `Int64` mantissa into `[10¹⁸, 10¹⁹)` exactly. The one exception is `Int64.minValue`, whose
magnitude `2⁶³` lands in the cusp above `maxRep` and gets rounded, so the theorem excludes it. -/

namespace XRPL.Model.Protocol

/-- `doNormalize_scaleUpSpec` never drops the exponent below `minExponent`. -/
lemma doNormalize_scaleUp_exp_ge (minMant m : UInt64) (e : Int) :
    minExponent ≤ e → minExponent ≤ (doNormalize_scaleUpSpec minMant m e).2 := by
  sorry

/-- `doNormalize_scaleUpSpec` does not increase the exponent. -/
lemma doNormalize_scaleUp_exp_le (minMant m : UInt64) (e : Int) :
    (doNormalize_scaleUpSpec minMant m e).2 ≤ e := by
  sorry

/-- With `minMant ≤ 10¹⁸`, `doNormalize_scaleUpSpec` keeps the mantissa below `10¹⁹`. -/
lemma doNormalize_scaleUp_lt19 (minMant m : UInt64) (e : Int)
    (hminMant : minMant.toNat ≤ 10 ^ 18) :
    m.toNat < 10 ^ 19 → (doNormalize_scaleUpSpec minMant m e).1.toNat < 10 ^ 19 := by
  sorry

/-- `doNormalize_scaleUpSpec` exits either at the input (no scaling) or at a multiple of 10
(at least one `×10` step). Requires `minMant ≤ 10¹⁸` so the scaling steps don't overflow. -/
lemma doNormalize_scaleUp_id_or_mul10 (minMant m : UInt64) (e : Int)
    (hminMant : minMant.toNat ≤ 10 ^ 18) (hm19 : m.toNat < 10 ^ 19) :
    (doNormalize_scaleUpSpec minMant m e).1 = m ∨ (doNormalize_scaleUpSpec minMant m e).1.toNat % 10 = 0 := by
  sorry

/-- `doNormalize_scaleUpSpec` exits either at the input mantissa or at least one exponent lower. -/
lemma doNormalize_scaleUp_id_or_exp_lt (minMant m : UInt64) (e : Int) :
    (doNormalize_scaleUpSpec minMant m e).1 = m ∨ (doNormalize_scaleUpSpec minMant m e).2 ≤ e - 1 := by
  sorry

set_option maxHeartbeats 800000 in
-- unfolds the full normalize pipeline (scaleUp / scaleDown / capAtMaxRep / doRoundUp)
/-- With enough exponent room, `doNormalize` scales any mantissa `m ∈ [1, maxRep]` into `largeRange` with no
rounding, in every mode, and returns a normalized number of the same value `m · 10^e`. -/
lemma doNormalize_largeRange_exact (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (h_pos : 1 ≤ m.toNat) (h_le : m.toNat ≤ maxRep.toNat)
    (he_lo : minExponent + 18 ≤ e) (he_hi : e ≤ maxExponent) :
    ∃ M : UInt64, ∃ e1 : Int,
      doNormalize neg m e largeRange.min largeRange.max mode = .ok ⟨neg, M, e1⟩ ∧
      (M.toNat : ℚ) * 10 ^ e1 = (m.toNat : ℚ) * 10 ^ e ∧ Number.isnormal ⟨neg, M, e1⟩ := by
  sorry

/-- With enough exponent room, `from_rep` is exact on any `Int64` mantissa except `Int64.minValue` (magnitude
`2⁶³`, the `pushOverflow` cusp): the result equals `mantissa · 10^e` and is normalized, in every mode. -/
theorem Number.from_rep_exact (mantissa : Int64) (e : Int) (mode : rounding_mode)
    (h_ne_min : mantissa ≠ Int64.minValue)
    (he_lo : minExponent + 18 ≤ e) (he_hi : e ≤ maxExponent) :
    ∃ result : Number,
      Number.from_rep mantissa e largeRange.min largeRange.max mode = .ok result ∧
      result.toRat = (mantissa.toInt : ℚ) * 10 ^ e ∧ result.isNormalized := by
  sorry

end XRPL.Model.Protocol
