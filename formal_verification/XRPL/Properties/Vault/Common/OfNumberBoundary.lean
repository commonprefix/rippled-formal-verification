import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.AlgorithmicFacts

/-! # Boundary facts for the fractional `ofNumber` pipeline

The IOU `ofNumber` rounding lemmas (`ofNumber_iou_within_ulp`,
`ofNumber_iou_within_half_ulp`, `ofNumber_iou_rounds_within`,
`ofNumber_iou_snap_pos`) require a 19-digit source mantissa and
`r.exponent_ + 4 ≤ maxExponent`. This file derives those hypotheses from the
success of the run itself, so the vault accuracy proofs can consume the ULP
bounds without free-floating side conditions:

* **success bounds the source exponent** — a successful fractional `ofNumber`
  with nonzero result forces `r.exponent_ ≤ 80` (`checked` errors above
  `cMaxOffset`, and the 16-digit `doNormalize` never lowers the exponent of an
  in-range mantissa);
* **fractional outputs are `IOUCanonical`-or-zero** — every producer in the
  vault exchange pipeline (`canonicalize`, `checked`, `ofNumber`,
  `operator_add`/`operator_sub`, `roundToExponent`) yields a canonical 16-digit
  record or a zero-mantissa record;
* **directional `to_rep` facts** — `.downward` on a sign-cleared normalized
  `Number` is the integer floor, and `.to_nearest` lands within `1/2`. -/

namespace XRPL.Model.Protocol

/-! ## The 16-digit `doRoundUp`/`doNormalize` output shape -/

/-- Round-trip of a sub-`2^63` `UInt64` through `Int64` and back. -/
private lemma uint64_toInt64_toUInt64 (m : UInt64) (h : m.toNat < 2 ^ 63) :
    m.toInt64.toUInt64 = m := by
  apply UInt64.toNat_inj.mp
  have h1 := toUInt64_toNat_of_nonneg m.toInt64
    (by rw [UInt64.toInt64_toInt_of_lt _ h]; positivity)
  rw [UInt64.toInt64_toInt_of_lt _ h] at h1
  exact_mod_cast h1

/-- **`doRoundUp` output at the 16-digit range.** For an in-range input mantissa
the result is the `bringIntoRange` zero flush or a 16-digit record whose
exponent moved by at most one step up and stayed within
`[minExponent, maxExponent]`. -/
lemma doRoundUp_16_ok_facts (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (mode : rounding_mode) (loc : String) (res : RoundResult)
    (hmin : cMinValue.toNat ≤ m.toNat) (hmax : m.toNat ≤ cMaxValue.toNat)
    (hok : g.doRoundUp neg m e cMinValue cMaxValue mode loc = .ok res) :
    (res.negative_ = false ∧ res.mantissa_ = 0 ∧ res.exponent_ = -2147483648) ∨
    (10 ^ 15 ≤ res.mantissa_.toNat ∧ res.mantissa_.toNat < 10 ^ 16 ∧
     minExponent ≤ res.exponent_ ∧ res.exponent_ ≤ maxExponent ∧
     res.negative_ = neg ∧ e ≤ res.exponent_ ∧ res.exponent_ ≤ e + 1) := by
  rw [cMinValue_val] at hmin
  rw [cMaxValue_val] at hmax
  have hlt_maxRep : m.toNat < maxRep.toNat := by rw [maxRep_val]; omega
  unfold Guard.doRoundUp at hok
  simp only [] at hok
  rw [pushOverflow_noop_of_lt_maxRep hlt_maxRep g mode] at hok
  trace_state
  sorry
