import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable

/-! # Proofs that IOU addition rounds to nearest

IOU addition adds two 19-digit Numbers and then rounds the sum to 16 digits. When the exact sum is itself a
Number the first step is exact, so only the 16-digit rounding is left and it is to nearest. -/

namespace XRPL.Model.Protocol

/-- Proof of `STAmount.operator_add_nearest_iou`. -/
lemma STAmount.operator_add_nearest_iou_proof (v1 v2 result : STAmount) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) (hfit : ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result) (hne : result.mValue ≠ 0) :
    |result.toRat - (v1.toRat + v2.toRat)| ≤ (10 : ℚ) ^ result.mOffset / 2 := by
  have h_truth_ne := STAmount.operator_add_iou_truth_ne_of_result v1 v2 result _ h1 h2 hok hne
  obtain ⟨xn, yn, sum, sumI, hrv, hexp_br, hofn, hsumI_ne, h_lo, h_hi, he_lo, he_hi,
      hxn_val, hyn_val, hxn_norm, hyn_norm, -, -, -, hsum_ne, hadd⟩ :=
    STAmount.operator_add_iou_decompose_anyMode v1 v2 result .to_nearest h1 h2 h_truth_ne hok hne
  obtain ⟨n, hn, hnv⟩ := hfit

  -- the exact sum is a Number, so the 19-digit sum is exact
  have hnear := Number.operator_add_nearest xn yn sum hxn_norm hyn_norm hadd (Or.inl hsum_ne) n hn
  rw [hxn_val, hyn_val, hnv, sub_self, abs_zero] at hnear
  have hsum : sum.toRat = v1.toRat + v2.toRat := by
    have := abs_nonpos_iff.mp hnear
    linarith

  -- the 16-digit rounding of that sum is within half a unit of the result
  have hexp : sum.exponent_ + 3 ≤ result.mOffset := by
    show sum.exponent_ + 3 ≤ result.exponent
    rw [hexp_br]
    exact IOUAmount.ofNumber_exp_ge sum .to_nearest sumI h_lo h_hi he_lo he_hi hofn hsumI_ne
  have hsnap := IOUAmount.ofNumber_within_half_ulp sum sumI h_lo h_hi he_lo he_hi hofn hsumI_ne
  rw [← hrv, hsum] at hsnap
  have hle : (10 : ℚ) ^ (sum.exponent_ + 3) ≤ (10 : ℚ) ^ result.mOffset :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  linarith

/-- The left operand of the witness, `1000000000000001`, is a canonical IOU amount. -/
lemma STAmount.add_nearest_witness_canonical_left :
    (⟨.fractional, 1000000000000001, 0, false⟩ : STAmount).IOUCanonical :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The right operand of the witness, `0.4996` with either sign, is a canonical IOU amount. -/
lemma STAmount.add_nearest_witness_canonical_right (neg : Bool) :
    (⟨.fractional, 4996000000000000, -16, neg⟩ : STAmount).IOUCanonical := by
  cases neg <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The exact sum `1000000000000000.5004` is rounded to `...000.500` and then to `...000`, not to `...001`. -/
lemma STAmount.operator_add_nearest_witness :
    STAmount.operator_add ⟨.fractional, 1000000000000001, 0, false⟩
        ⟨.fractional, 4996000000000000, -16, true⟩ .to_nearest
      = .ok ⟨.fractional, 1000000000000000, 0, false⟩ := by
  decide +kernel

/-- The result is `0.5004` of a unit away from the exact sum. -/
lemma STAmount.operator_add_nearest_witness_gap :
    (10 : ℚ) ^ (⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).mOffset / 2 <
      |(⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).toRat -
        ((⟨.fractional, 1000000000000001, 0, false⟩ : STAmount).toRat +
          (⟨.fractional, 4996000000000000, -16, true⟩ : STAmount).toRat)| := by
  have hr : (⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).toRat = 1000000000000000 := by
    decide +kernel
  have h1 : (⟨.fractional, 1000000000000001, 0, false⟩ : STAmount).toRat = 1000000000000001 := by
    decide +kernel
  have h2 : (⟨.fractional, 4996000000000000, -16, true⟩ : STAmount).toRat = -(4996 / 10000) := by
    decide +kernel
  rw [hr, h1, h2, zpow_zero]
  norm_num [abs_of_neg]

end XRPL.Model.Protocol
