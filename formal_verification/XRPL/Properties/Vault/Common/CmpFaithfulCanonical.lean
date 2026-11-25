import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Compare.Common.Proofs
import XRPL.Properties.Protocol.Number.Common.Constants

/-! # `CmpFaithful` from two exact-canonical amounts

The `STAmount` comparison lemmas need a `CmpFaithful` premise. This file builds it from two `ExactCanonical`
amounts. -/

namespace XRPL.Model.Protocol

/-- Two comparable `ExactCanonical` amounts satisfy `CmpFaithful`: two IOU amounts have 16-digit mantissas and
two integral amounts have offset `0`. The caller gives the zero-sign facts. -/
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
