import XRPL.Properties.Lending.Loan.Common.RoundAnySign
import XRPL.Properties.Lending.Loan.Common.PayCharge
import XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal
import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional

/-! # An overpayment tail that adds nothing

The overpayment tail first rounds the amount towards zero at LoanScale. An amount the asset holds exactly rounds
to at most itself, so when the instalments already took the whole amount the tail returns the payment as it was. -/

namespace XRPL.Model.Protocol

/-- The 16-digit rounding towards zero keeps the exponent three above, it never carries. -/
private lemma normalizeToRange_towards_zero_exp (n : Number) (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue .towards_zero = .ok (mant, exp)) : exp = n.exponent_ + 3 := by
  obtain ⟨g, -, -, -, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .towards_zero h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 := m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  have hnr : n.normalizeToRange cMinValue cMaxValue .towards_zero
      = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64 else (n.mantissa_ / 10 / 10 / 10).toInt64,
        n.exponent_ + 3) := by
    unfold Number.normalizeToRange
    rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .towards_zero .normalize2
      (round_bool_towards_zero g _) (by rw [hcMin, hm3]; omega) (by rw [hcMax, hm3]; omega) (by omega)
      (by omega)]
    exact Number.normalizeToRange_tail (by dsimp only [RoundResult.toNumber]; rw [hm3]; omega)
  rw [hnr] at hok
  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
  exact hok.2.symm

/-- A towards-zero IOU `ofNumber` of a positive value below `10^96` never throws. Rounding towards zero never
carries past the IOU ceiling. -/
private lemma STAmount.ofNumber_fractional_towards_zero_ok (r : Number) (hn : r.isNormalized) (hpos : 0 < r.toRat)
    (hlt : r.toRat < 10 ^ 96) : ∃ result, STAmount.ofNumber .fractional r .towards_zero = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hr_ne
  have hneg := Number.negative_false_of_pos r hpos
  have hre_lo := Number.exponent_ge_min r hn hr_ne
  have hre_hi : r.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt r 77 hn hneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  by_cases h4 : r.exponent_ + 4 ≤ cMaxOffset
  · exact STAmount.ofNumber_fractional_ok r .towards_zero hr_lo hr_hi hre_lo h4
  have hco : cMaxOffset = 80 := rfl
  have hme : maxExponent = 32768 := rfl
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok r .towards_zero hr_lo hr_hi (by omega) (by omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts r .towards_zero mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hexp := normalizeToRange_towards_zero_exp r mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  have hexp_hi : exp ≤ cMaxOffset := by omega
  -- the stored IOU amount is the truncated mantissa at an exponent within the ceiling
  have hs : decide (r.signum < 0) = false := by
    simpa using Number.signum_nonneg_of_negative_false r hneg
  have hnorm' : r.normalizeToRange kMinValue kMaxValue .towards_zero = .ok (mant, exp) := hnorm
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
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp false).iou .towards_zero
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    rw [STAmount.iou_of_lt .towards_zero h_int h_fit]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp false .towards_zero hmtu_lo hmtu_hi
      (by omega) (by omega)
  rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using hmant_pos)), ok_bind,
    STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by omega)]
  split_ifs <;> exact ⟨_, rfl⟩

/-- An amount at least zero that the asset holds exactly rounds towards zero without error, at a scale in
`[-81, 0]`. -/
private lemma STAmount.roundToNumericType_towards_zero_ok (nt : NumericType) (x : Number) (s : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hrep : STAmount.isRounded nt x = false)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hs : -81 ≤ s ∧ s ≤ 0) :
    ∃ c, STAmount.roundToNumericType nt x .towards_zero (some s) = .ok c := by
  have hR := (STAmount.isRounded_eq_false_iff nt x hx h0).mp hrep
  rcases hasset with rfl | hnt
  · by_cases hsmall : x.toRat < 10 ^ 90
    · obtain ⟨c, hc, -⟩ := STAmount.roundToNumericType_frac_ok_abs x .towards_zero s hx
        (by rw [abs_of_nonneg h0]; exact hsmall) ⟨by omega, by omega⟩
      exact ⟨c, hc⟩
    push Not at hsmall
    have hpos : 0 < x.toRat := lt_of_lt_of_le (by norm_num) hsmall
    -- the asset holds it exactly, so it is below `10^96`
    have hlt : x.toRat < 10 ^ 96 := by
      rcases hR with h | ⟨m, e, -, hm, -, he, hv⟩
      · rw [h]; norm_num
      · rw [hv]
        have hm' : (m : ℚ) < 10 ^ 16 := by exact_mod_cast hm
        have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
        calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := mul_lt_mul_of_pos_right hm' (zpow_pos (by norm_num) _)
          _ ≤ 10 ^ 16 * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left he' (by norm_num)
          _ = 10 ^ 96 := by norm_num
    obtain ⟨ret, hof⟩ := STAmount.ofNumber_fractional_towards_zero_ok x hx hpos hlt
    have hx0 : x.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
    obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hx0
    have hemin := Number.exponent_ge_min x hx hx0
    have he70 : (70 : ℤ) < x.exponent_ := Number.exponent_gt_of_abs_ge x hx hx0 70 (by
      rw [abs_of_nonneg h0]; linarith [show (10 : ℚ) ^ ((70 : ℤ) + 19) = 10 ^ 89 by norm_num,
        show (10 : ℚ) ^ 89 < 10 ^ 90 by norm_num])
    have hxe : x.exponent_ ≤ 77 :=
      Number.exponent_le_of_toRat_lt x 77 hx (Number.negative_false_of_pos x hpos) (by unfold minExponent; norm_num)
        (by norm_num; linarith)
    have hint : ret.integral = false := by
      unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ ret hof]; rfl
    have hre : STAmount.roundToExponent ret s .towards_zero = .ok ret := by
      apply STAmount.roundToExponent_eq_self
      by_cases hz : ret.mValue = 0
      · exact Or.inr (Or.inl (by simp [STAmount.isZero, hz]))
      · have := (STAmount.ofNumber_iou_within_ulp .fractional x .towards_zero ret rfl hlo hhi hemin
          (by unfold maxExponent; omega) hof hz).2
        exact Or.inr (Or.inr (by omega))
    obtain ⟨c, hc, -⟩ := (STAmount.ofNumber_fractional_fczr x .towards_zero ret hof).toNumber_ok .towards_zero
    refine ⟨c, ?_⟩
    unfold STAmount.roundToNumericType
    rw [hof]
    simp only [hint, Bool.false_eq_true, ↓reduceIte]
    rw [hre]
    exact hc
  · have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
    have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
    have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
    obtain ⟨hden, hcap, hmax⟩ : x.toRat.den = 1 ∧ x.toRat ≤ 2 ^ 63 - 1 ∧ x.toRat ≤ nt.maxValue.toNat := by
      rcases hR with h | h
      · rw [h]; exact ⟨rfl, by norm_num, by positivity⟩
      · rcases hnt with rfl | rfl
        all_goals
          obtain ⟨-, k, hk, hk', hv⟩ := h
          rw [hv]
          refine ⟨Rat.den_natCast k, ?_, by exact_mod_cast hk⟩
          have h1 : ((k : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by exact_mod_cast hk'
          have h2 : ((2 ^ 63 - 1 : ℕ) : ℚ) = 2 ^ 63 - 1 := by norm_num
          linarith
    obtain ⟨ret, hof⟩ := STAmount.ofNumber_integral_ok_of_le nt x .towards_zero hint hmo hx
      (Number.negative_false_of_nonneg x hx h0) hden hcap hmax
    obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical nt x .towards_zero ret hint hof
    have hret_int : ret.integral = true := by unfold STAmount.integral; rw [hrnt]; exact hint
    obtain ⟨c, hc', -, -, -⟩ := STAmount.toNumber_integral_exact ret .towards_zero hc (by rw [hrnt]; exact hmr)
    refine ⟨c, ?_⟩
    unfold STAmount.roundToNumericType
    rw [hof]
    simp only [hret_int, ↓reduceIte]
    exact hc'

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private UnsettledPayment.applyOverpayment from XRPL.Model.Lending.Loan.LoanPay
open private STAmount.roundToNumericType_towards_zero_some_le from XRPL.Properties.Lending.Loan.Common.PayCharge

/-- The overpayment tail adds nothing when the instalments already took the whole amount, an amount at least
zero that the loan's asset holds exactly. -/
lemma UnsettledPayment.applyOverpayment_skips (p : UnsettledPayment Vault) (amount : Number)
    (hN : amount.isNormalized) (h0 : 0 ≤ amount.toRat)
    (hrep : STAmount.isRounded p.loan.broker.numericType amount = false)
    (hasset : p.loan.broker.numericType = .fractional ∨ p.loan.broker.numericType = .native ∨
      p.loan.broker.numericType = .int64)
    (hs : -81 ≤ p.loan.loanScale ∧ p.loan.loanScale ≤ 0)
    (htN : p.totalPaid.isNormalized) (hge : amount.toRat ≤ p.totalPaid.toRat) :
    UnsettledPayment.applyOverpayment p amount = .ok p := by
  obtain ⟨c, hc⟩ := STAmount.roundToNumericType_towards_zero_ok _ amount _ hN h0 hrep hasset hs
  have hcN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hc
  obtain ⟨-, hcle⟩ := STAmount.roundToNumericType_towards_zero_some_le _ amount c _ hN h0
    ⟨by omega, by omega⟩ hc
  have hlt : p.totalPaid.operator_lt c = false := (operator_lt_eq_false_iff _ _ htN hcN).mpr (by linarith)
  unfold UnsettledPayment.applyOverpayment
  simp only [hc, hlt, bind, Except.bind, Bool.and_false, Bool.false_and, Bool.not_false, ↓reduceIte, pure,
    Except.pure]

end XRPL.Model.Lending
