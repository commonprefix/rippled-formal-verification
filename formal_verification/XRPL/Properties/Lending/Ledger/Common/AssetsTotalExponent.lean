import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Lending.Loan.Common.PayFit
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.SettledVault

/-! # A downward IOU amount never overflows

Rounding a positive value below `10^96` down to an IOU amount never carries past the IOU ceiling. -/

namespace XRPL.Model.Protocol

/-- A downward IOU `ofNumber` of a positive value below `10^96` never throws. Rounding down never carries past
the IOU ceiling. -/
lemma STAmount.ofNumber_fractional_downward_ok (r : Number) (hn : r.isNormalized) (hpos : 0 < r.toRat)
    (hlt : r.toRat < 10 ^ 96) : ∃ result, STAmount.ofNumber .fractional r .downward = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hr_ne
  have hneg := Number.negative_false_of_pos r hpos
  have hre_lo := Number.exponent_ge_min r hn hr_ne
  have hre_hi : r.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt r 77 hn hneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  by_cases h4 : r.exponent_ + 4 ≤ cMaxOffset
  · exact STAmount.ofNumber_fractional_ok r .downward hr_lo hr_hi hre_lo h4
  have hco : cMaxOffset = 80 := rfl
  have hme : maxExponent = 32768 := rfl
  have he77 : r.exponent_ = 77 := by omega
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok r .downward hr_lo hr_hi (by omega) (by omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts r .downward mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hdown := normalizeToRange_16_downward r mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hrange := normalizeToRange_16_exp_range r .downward mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  -- a carry would need a value of at least `10^96`
  have hexp_hi : exp ≤ cMaxOffset := by
    by_contra hc
    have hexp : exp = 81 := by omega
    have hm15 : (10 : ℚ) ^ 15 ≤ (mant.toInt : ℚ) := by
      have h' : ((10 ^ 15 : ℕ) : ℤ) ≤ mant.toInt := by omega
      exact_mod_cast h'
    rw [hexp] at hdown
    have : (10 : ℚ) ^ 15 * 10 ^ (81 : ℤ) ≤ (mant.toInt : ℚ) * 10 ^ (81 : ℤ) :=
      mul_le_mul_of_nonneg_right hm15 (by positivity)
    norm_num at this
    linarith
  have hs : decide (r.signum < 0) = false := by
    simpa using Number.signum_nonneg_of_negative_false r hneg
  have hnorm' : r.normalizeToRange kMinValue kMaxValue .downward = .ok (mant, exp) := hnorm
  unfold STAmount.ofNumber
  rw [if_neg (by decide), hs]
  simp only [Bool.false_eq_true, if_false, hnorm']
  have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp false).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
  have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops.toInt64
      = if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant.toUInt64 exp false).mValue.toNat < 10 ^ 16 from hmtu_hi),
        signed_mantissa_toInt false mant.toUInt64 h_fit]
    show (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    simp
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp false).iou .downward
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp false .downward hmtu_lo hmtu_hi
      (by omega) (by omega)
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by omega)]
  split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.Protocol
