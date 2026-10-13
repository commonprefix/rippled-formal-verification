import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Compare.Common.Proofs
import XRPL.Properties.Protocol.Number.Common.Constants

/-! # `CmpFaithful` from two canonical amounts

The deposit limit guard compares the stored charge against the configured maximum,
and the `STAmount` comparison lemmas need a `CmpFaithful` premise. This file builds
it from two `Canonical` amounts plus the zero-sign facts (vacuous whenever the
amounts are nonzero) and records that `Canonical` implies `ExactCanonical` (the
`ExactCanonical` shape and its `toNumber` exactness live in `STAmountToNumber`). -/

namespace XRPL.Model.Protocol

/-- A deposit-ready `Canonical` amount is `ExactCanonical`: the integral carried
bound `maxValue ≤ maxRep` forces the stored magnitude below `2^63`. -/
lemma STAmount.Canonical.exactCanonical (s : STAmount) (hc : s.Canonical) :
    s.ExactCanonical := by
  by_cases hint : s.integral = true
  · obtain ⟨hic, hmax⟩ := hc.1 hint
    refine Or.inr ⟨hic, ?_⟩
    have h63 : maxRep.toNat ≤ 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    calc s.mValue.toNat ≤ s.mNumericType.maxValue.toNat := hic.in_range
      _ ≤ maxRep.toNat := hmax
      _ ≤ 2 ^ 63 - 1 := h63
  · have hfr : s.integral = false := by
      cases hb : s.integral with
      | false => rfl
      | true => exact absurd hb hint
    exact Or.inl (hc.2 hfr)

/-- **`CmpFaithful` from two canonical amounts.** Comparable canonical amounts of
the same kind are comparison-faithful: fractional pairs are 16-digit banded, and
integral pairs share `mOffset = 0`. The zero-sign obligations are supplied by the
caller (vacuous for a nonzero amount). -/
lemma STAmount.CmpFaithful.ofCanonical (lhs rhs : STAmount)
    (hc1 : lhs.Canonical) (hc2 : rhs.Canonical)
    (hcmp : STAmount.areComparable lhs rhs = true)
    (h0l : lhs.mValue = 0 → lhs.mIsNegative = false)
    (h0r : rhs.mValue = 0 → rhs.mIsNegative = false) :
    STAmount.CmpFaithful lhs rhs := by
  have htyeq : lhs.mNumericType = rhs.mNumericType := by
    unfold STAmount.areComparable at hcmp; exact beq_iff_eq.mp hcmp
  by_cases hint : lhs.integral = true
  · have hrint : rhs.integral = true := by
      unfold STAmount.integral at hint ⊢; rw [← htyeq]; exact hint
    exact STAmount.CmpFaithful.ofIntegral lhs rhs (hc1.1 hint).1 (hc2.1 hrint).1 hcmp h0l h0r
  · have hlfr : lhs.integral = false := by
      cases hb : lhs.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hrfr : rhs.integral = false := by
      unfold STAmount.integral at hlfr ⊢; rw [← htyeq]; exact hlfr
    exact STAmount.CmpFaithful.ofIOU lhs rhs (hc1.2 hlfr) (hc2.2 hrfr) hcmp

/-- **`CmpFaithful` from two `ExactCanonical` amounts.** Same dispatch as
`ofCanonical`, keyed on the value-canonical (`ExactCanonical`) form each side has. -/
lemma STAmount.CmpFaithful.ofExactCanonical (lhs rhs : STAmount)
    (hc1 : lhs.ExactCanonical) (hc2 : rhs.ExactCanonical)
    (hcmp : STAmount.areComparable lhs rhs = true)
    (h0l : lhs.mValue = 0 → lhs.mIsNegative = false)
    (h0r : rhs.mValue = 0 → rhs.mIsNegative = false) :
    STAmount.CmpFaithful lhs rhs := by
  have htyeq : lhs.mNumericType = rhs.mNumericType := by
    unfold STAmount.areComparable at hcmp; exact beq_iff_eq.mp hcmp
  rcases hc1 with hio1 | ⟨hint1, _⟩
  · have hrfr : rhs.mNumericType.isIntegral = false := by
      rw [← htyeq]; rw [hio1.is_fractional]; decide
    rcases hc2 with hio2 | ⟨hint2, _⟩
    · exact STAmount.CmpFaithful.ofIOU lhs rhs hio1 hio2 hcmp
    · exact absurd hint2.is_integral (by rw [hrfr]; exact Bool.false_ne_true)
  · have hlint : lhs.mNumericType.isIntegral = true := hint1.is_integral
    rcases hc2 with hio2 | ⟨hint2, _⟩
    · exact absurd hlint (by rw [htyeq, hio2.is_fractional]; decide)
    · exact STAmount.CmpFaithful.ofIntegral lhs rhs hint1 hint2 hcmp h0l h0r

end XRPL.Model.Protocol
