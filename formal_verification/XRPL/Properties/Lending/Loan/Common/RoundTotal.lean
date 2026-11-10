import XRPL.Properties.Lending.Loan.Common.NumberTotal
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Lending.Loan.Common.RoundToNearest
import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Vault.Proofs.Support.IOUTotality

/-! # Rounding to an asset never fails within range

An IOU amount rounds to a scale in every mode, so a nonnegative number below `10^90` rounds to an IOU amount at
any scale in `[-96, 79]`. A nonnegative number a unit below the maximum of XRP or an MPT rounds to it too. -/

namespace XRPL.Model.Protocol

/-- A nonnegative number below `10^90` rounds to an IOU amount at a scale in `[-96, 79]`, in every mode. -/
lemma STAmount.roundToNumericType_frac_ok (x : Number) (mode : rounding_mode) (s : Int) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hlt : x.toRat < 10 ^ 90) (hs : -96 ≤ s ∧ s ≤ 79) :
    ∃ y, STAmount.roundToNumericType .fractional x mode (some s) = .ok y := by
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr x mode hx (by rw [abs_of_nonneg h0]; exact hlt)
  have hret0 := STAmount.ofNumber_nonneg .fractional x mode ret hx (Number.negative_false_of_nonneg x hx h0) hret
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  obtain ⟨rd, hrd⟩ : ∃ rd, STAmount.roundToExponent ret s mode = .ok rd := by
    rcases hretf.2 with hc' | hz
    · exact STAmount.roundToExponent_ok_any ret s mode hc' (STAmount.mIsNegative_false_of_nonneg ret hret0 (by
        intro h0; have := hc'.mant_lo; rw [h0] at this; exact absurd this (by decide))) hs.1 hs.2
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd s mode hretf hrd
  obtain ⟨y, hy, -, -⟩ := hrdf.toNumber_ok mode
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
  rw [hrd]
  exact hy

/-- A nonnegative number a unit below the maximum of XRP or an MPT rounds to that asset, in every mode and
at any scale. -/
lemma STAmount.roundToNumericType_integral_ok (nt : NumericType) (x : Number) (mode : rounding_mode)
    (s : Option Int) (hnt : nt = .native ∨ nt = .int64) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmax : x.toRat + 1 ≤ nt.maxValue.toNat) :
    ∃ y, STAmount.roundToNumericType nt x mode s = .ok y := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  have hcap : x.toRat ≤ 2 ^ 63 - 2 := by
    have : (nt.maxValue.toNat : ℚ) ≤ maxRep.toNat := by exact_mod_cast hmr
    have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    linarith
  obtain ⟨ret, hret⟩ := STAmount.ofNumber_integral_ok_of_lt nt x mode hint hmo hx h0 hcap hmax
  obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical nt x mode ret hint hret
  have hret_int : ret.integral = true := by
    unfold STAmount.integral; rw [hrnt]; exact hint
  obtain ⟨y, hy, -, -, -⟩ := STAmount.toNumber_integral_exact ret mode hc (by rw [hrnt]; exact hmr)
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  cases s with
  | none => exact hy
  | some s => simp only [hret_int, ↓reduceIte]; exact hy

/-- A downward credit of a nonnegative delta onto a nonnegative IOU amount never throws while their sum is
below `10^89`, at a base exponent in `[-81, 79]`. A sum too big for the base exponent rounds at a coarser one. -/
lemma sumRoundAndSubtract_frac_downward_ok_any (A c : Number) (b : Int) (hA : A.isNormalized) (hc : c.isNormalized)
    (hA0 : 0 ≤ A.toRat) (hc0 : 0 ≤ c.toRat) (hb : -81 ≤ b ∧ b ≤ 79) (hlt : A.toRat + c.toRat < 10 ^ 89) :
    ∃ st, sumRoundAndSubtract A c b .fractional .downward = .ok st ∧ st.FracCanonZero := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  -- the exponent of the sum, at most `79`
  obtain ⟨s0, hs0⟩ := Number.operator_add_ok_of_lt A c .to_nearest hA hc hA0 (by linarith) hc0 (by linarith)
  have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
  have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0 (by linarith)
  have hs0lt : s0.toRat < 10 ^ 90 := by
    have := (Number.add_near _ _ _ hA hc hs0).le (by linarith)
    nlinarith
  obtain ⟨e, hex⟩ : ∃ e, numberExponent s0 b .fractional = .ok e := by
    unfold numberExponent
    by_cases hz : s0.operator_eq Number.zero = true
    · rw [if_pos hz]; exact ⟨b, rfl⟩
    · rw [if_neg hz]
      obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s0 .downward hs0n
        (by rw [abs_of_nonneg hs00]; exact hs0lt)
      rw [hst]
      exact ⟨_, rfl⟩
  have heb : b ≤ e := numberExponent_ge _ _ _ _ hex
  have he79 : e ≤ 79 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b e hs0n hs00 (by omega) hex (by omega)
    have h1 : (10 : ℚ) ^ (90 : ℤ) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (90 : ℤ) = 10 ^ 90 := by norm_num
    linarith
  have hpse : postSumExponent A c b .fractional = .ok e := by
    unfold postSumExponent; rw [hs0, ok_bind]; exact hex
  obtain ⟨sm, hsm⟩ := Number.operator_add_ok_of_lt A c .downward hA hc hA0 (by linarith) hc0 (by linarith)
  have hsmn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsm
  have hsmle : sm.toRat ≤ A.toRat + c.toRat := by
    by_cases h0 : sm.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero sm h0]; linarith
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward A c sm hA hc hsm h0
    rw [hv]; exact Number.lower_le _ l hl
  have hsm0 : 0 ≤ sm.toRat := by
    by_cases h0 : sm.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero sm h0]
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward A c sm hA hc hsm h0
    rw [hv]
    have := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; linarith)
    rwa [Number.toRat_zero] at this
  obtain ⟨sm', hround⟩ := STAmount.roundToNumericType_frac_ok sm .downward e hsmn hsm0 (by linarith)
    ⟨by omega, he79⟩
  have hsm'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have hsm'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hsmn hsm0 (Or.inr (Or.inr rfl))
    ⟨by omega, by omega⟩ hround
  have hsm'le := XRPL.Model.Lending.STAmount.roundToNumericType_frac_downward_le _ _ _ hsmn hsm0
    ⟨by omega, by omega⟩ hround
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_abs sm' A .downward hsm'n hA
    (by rw [abs_of_nonneg hsm'0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hA0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
  have hdn : d.isNormalized := Number.operator_add_isNormalized_any _ _ _ _ hsm'n
    (Number.operator_neg_isNormalized A hA) hd
  have hdlt : |d.toRat| < 10 ^ 90 := by
    by_cases h0 : d.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero d h0, abs_zero]; norm_num
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward sm' A.operator_neg d hsm'n
      (Number.operator_neg_isNormalized A hA) hd h0
    rw [Number.toRat_neg] at hl
    have hle : d.toRat ≤ sm'.toRat + -A.toRat := by rw [hv]; exact Number.lower_le _ l hl
    have hge : -A.toRat ≤ d.toRat := by
      rw [hv]
      have := Number.lower_tight _ l hl A.operator_neg (Number.operator_neg_isNormalized A hA)
        (by rw [Number.toRat_neg]; linarith)
      rwa [Number.toRat_neg] at this
    rw [abs_lt]
    constructor <;> nlinarith
  obtain ⟨st, hst, hstf⟩ := STAmount.ofNumber_fractional_ok_fczr d .downward hdn hdlt
  refine ⟨st, ?_, hstf⟩
  unfold sumRoundAndSubtract
  rw [if_neg (by decide)]
  show (pure PUnit.unit >>= fun _ => (do
      let exponent ← postSumExponent A c b NumericType.fractional
      let sum ← A.operator_add c rounding_mode.downward
      let sum' ← STAmount.roundToNumericType NumericType.fractional sum rounding_mode.downward (some exponent)
      let amountDelta' ← sum'.operator_sub A rounding_mode.downward
      STAmount.ofNumber NumericType.fractional amountDelta' rounding_mode.downward)) = _
  rw [show (pure PUnit.unit : Except Error PUnit) = .ok PUnit.unit from rfl, ok_bind, hpse, ok_bind, hsm, ok_bind,
    hround, ok_bind, show sm'.operator_sub A .downward = .ok d from hd, ok_bind, hst]

/-- A downward credit onto an XRP or MPT amount never throws while the delta is nonnegative and a unit below
the asset's maximum. -/
lemma sumRoundAndSubtract_integral_ok (A c : Number) (b : Int) (nt : NumericType) (mode : rounding_mode)
    (hnt : nt = .native ∨ nt = .int64) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hmax : c.toRat + 1 ≤ nt.maxValue.toNat) :
    ∃ st, sumRoundAndSubtract A c b nt mode = .ok st := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  have hcap : c.toRat ≤ 2 ^ 63 - 2 := by
    have : (nt.maxValue.toNat : ℚ) ≤ maxRep.toNat := by exact_mod_cast hmr
    have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    linarith
  obtain ⟨st, hst⟩ := STAmount.ofNumber_integral_ok_of_lt nt c mode hint hmo hc hc0 hcap hmax
  refine ⟨st, ?_⟩
  unfold sumRoundAndSubtract
  rw [if_pos hint, hst]
  rfl

end XRPL.Model.Protocol
