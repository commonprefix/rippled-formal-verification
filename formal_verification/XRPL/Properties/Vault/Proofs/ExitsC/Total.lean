import XRPL.Properties.Vault.Proofs.Support.NormalizeFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # Totality of the payout arithmetic at small exponents -/

namespace XRPL.Model.SingleAssetVault.ExitsC

open XRPL.Model.Protocol

lemma scaleUp_exp_le (minM m : UInt64) (e : Int) : (doNormalize_scaleUp minM m e).2 ≤ e := by
  induction m, e using doNormalize_scaleUp.induct (minMantissa := minM) with
  | case1 m e hcond IH =>
    rw [doNormalize_scaleUp.eq_def, if_pos hcond]
    omega
  | case2 m e hcond =>
    rw [doNormalize_scaleUp.eq_def, if_neg hcond]

lemma scaleDown_ok (maxM : UInt64) (d : ℕ) :
    ∀ (m : UInt64) (e : Int) (g : Guard),
      m.toNat < (maxM.toNat + 1) * 10 ^ d →
      e + (d : Int) ≤ maxExponent →
      ∃ (m' : UInt64) (e' : Int) (g' : Guard),
        doNormalize_scaleDown maxM m e g = .ok (m', e', g') ∧ e ≤ e' ∧ e' ≤ e + (d : Int) := by
  induction d with
  | zero =>
    intro m e g hm _
    have hnotgt : ¬ m > maxM := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; rw [pow_zero, mul_one] at hm; omega
    exact ⟨m, e, g, by rw [doNormalize_scaleDown.eq_def, dif_neg hnotgt], le_refl _, by simp⟩
  | succ d IH =>
    intro m e g hm he
    by_cases hgt : m > maxM
    · have hne : ¬ (e ≥ maxExponent) := by push_cast at he; omega
      have hmdiv : (m / 10 : UInt64).toNat = m.toNat / 10 := by
        rw [UInt64.toNat_div]; rfl
      have hm10 : (m / 10 : UInt64).toNat < (maxM.toNat + 1) * 10 ^ d := by
        rw [hmdiv]; rw [pow_succ] at hm
        exact Nat.div_lt_of_lt_mul (by linarith)
      obtain ⟨m', e', g', hok, hle1, hle2⟩ :=
        IH (m / 10) (e + 1) (g.push (m % 10)) hm10 (by push_cast at he ⊢; omega)
      refine ⟨m', e', g', ?_, by omega, by push_cast at hle2 ⊢; omega⟩
      rw [doNormalize_scaleDown.eq_def, dif_pos hgt, if_neg hne]; exact hok
    · exact ⟨m, e, g, by rw [doNormalize_scaleDown.eq_def, dif_neg hgt], le_refl _,
        by push_cast; omega⟩

/-- `doNormalize` never errors below the exponent ceiling. -/
lemma doNormalize_ok (neg : Bool) (M : UInt64) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (he : e + 22 ≤ maxExponent) :
    ∃ r, doNormalize neg M e minM maxM mode = .ok r := by
  unfold doNormalize
  by_cases hM : (M == 0) = true
  · rw [if_pos hM]; exact ⟨Number.zero, rfl⟩
  rw [if_neg hM]
  simp only []
  rcases hsu : doNormalize_scaleUp minM M e with ⟨m1, e1⟩
  simp only []
  have he1 : e1 ≤ e := by have := scaleUp_exp_le minM M e; rw [hsu] at this; exact this
  have hm1 : m1.toNat < (maxM.toNat + 1) * 10 ^ 20 := by
    calc m1.toNat < 2 ^ 64 := m1.toNat_lt
      _ ≤ 1 * 10 ^ 20 := by norm_num
      _ ≤ (maxM.toNat + 1) * 10 ^ 20 := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨m2, e2, g2, hsd, -, he2⟩ := scaleDown_ok maxM 20 m1 e1
    (if neg then Guard.new.set_negative else Guard.new) hm1 (by push_cast; omega)
  rw [hsd]
  simp only []
  by_cases hund : (e2 < minExponent || m2 < minM) = true
  · rw [if_pos hund]; exact ⟨Number.zero, rfl⟩
  rw [if_neg hund]
  obtain ⟨m3, e3, g3, hcap, he3⟩ := doNormalize_capAtMaxRep_ok_of_exp m2 e2 g2 (by push_cast at he2; omega)
  rw [hcap]
  simp only []
  obtain ⟨res, hru⟩ := Guard.doRoundUp_ok_of_exp_le g3 neg m3 e3 minM maxM mode .normalize2
    (by push_cast at he2; omega)
  rw [hru]
  exact ⟨res.toNumber, rfl⟩

lemma add_ok (x y : Number) (mode : rounding_mode) (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ + 30 ≤ maxExponent) (hye : y.exponent_ + 30 ≤ maxExponent) :
    ∃ r, x.operator_add y mode = .ok r :=
  Number.operator_add_ok_of_exp x y mode hx hy (by omega) (by omega)

lemma sub_ok (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ ≤ 100) (hye : y.exponent_ ≤ 100) :
    ∃ r, x.operator_sub y .to_nearest = .ok r := by
  have hme : maxExponent = 32768 := rfl
  have hyn : y.operator_neg.exponent_ + 30 ≤ maxExponent := by
    unfold Number.operator_neg
    split
    · unfold Number.zero; simp only []; omega
    · simp only []; omega
  exact add_ok x y.operator_neg .to_nearest hx (Number.operator_neg_isNormalized y hy)
    (by omega) hyn

lemma iou_ofNumber_zero (n : Number) (mode : rounding_mode) (hm : n.mantissa_ = 0) :
    ∃ r, (match IOUAmount.ofNumber n mode with
      | .error e => (Except.error e : Except Error STAmount)
      | .ok sumI => STAmount.ofIOUAmount sumI mode) = .ok r := by
  have h0 : IOUAmount.ofNumber n mode = .ok IOUAmount.zero := by
    have hd : doNormalize n.negative_ n.mantissa_ n.exponent_ cMinValue cMaxValue mode
        = .ok Number.zero := by
      unfold doNormalize; rw [hm]; rfl
    unfold IOUAmount.ofNumber IOUAmount.fromNumber Number.normalizeToRange
    rw [hd]
    rfl
  rw [h0]
  exact ⟨_, STAmount.ofIOU_zero_rec mode⟩

/-- The downward 16-digit repack of a nonnegative `Number` below the IOU ceiling. -/
lemma iou_ofNumber_down_ok (n : Number) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (he : n.exponent_ ≤ 77) :
    ∃ r, (match IOUAmount.ofNumber n .downward with
      | .error e => (Except.error e : Except Error STAmount)
      | .ok sumI => STAmount.ofIOUAmount sumI .downward) = .ok r := by
  by_cases hm : n.mantissa_ = 0
  · exact iou_ofNumber_zero n .downward hm
  obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hm
  have helo : minExponent ≤ n.exponent_ := by
    rcases hn with h | ⟨_, _, _, h, _⟩
    · exact absurd (by rw [h]; rfl) hm
    · exact h
  have hme : maxExponent = 32768 := rfl
  obtain ⟨res, hres⟩ := doNormalize_ok n.negative_ n.mantissa_ n.exponent_ cMinValue cMaxValue
    .downward (by omega)
  cases hntr : n.normalizeToRange cMinValue cMaxValue .downward with
  | error e =>
    unfold Number.normalizeToRange at hntr
    rw [hres] at hntr
    exact absurd hntr (by simp)
  | ok pr =>
    obtain ⟨mant, exp⟩ := pr
    obtain ⟨-, hexp⟩ := normalizeToRange_16_floor_pos n mant exp .downward (Or.inl rfl) hneg
      hlo hhi (by omega) (by omega) hntr
    obtain ⟨⟨hmlo, hmhi⟩, -, ⟨hsg, -⟩⟩ := normalizeToRange_iou_ok_facts n .downward mant exp
      hlo hhi (by omega) (by omega) hntr
    have hof : IOUAmount.ofNumber n .downward =
        (if exp < cMinOffset then .ok IOUAmount.zero else .ok ⟨mant, exp⟩) := by
      unfold IOUAmount.ofNumber IOUAmount.fromNumber
      rw [hntr]
      simp only []
      rw [if_neg (by unfold cMaxOffset; omega)]
    rw [hof]
    split_ifs with hlt
    · exact ⟨_, STAmount.ofIOU_zero_rec .downward⟩
    · have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
      have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
      refine ⟨_, STAmount.ofIOU_canonical ⟨mant, exp⟩ .downward ⟨?_, ?_, ?_, ?_⟩⟩
      · show 10 ^ 15 ≤ mant.toInt.natAbs; omega
      · show mant.toInt.natAbs < 10 ^ 16; omega
      · show (-96 : ℤ) ≤ exp; unfold cMinOffset at hlt; omega
      · show exp ≤ 80; omega

/-- A nonnegative downward sum of two canonical amounts below the IOU ceiling. -/
lemma iou_add_down_ok (v1 v2 : STAmount) (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h0 : 0 ≤ v1.toRat + v2.toRat) (hhi : v1.toRat + v2.toRat < 10 ^ (96 : ℤ)) :
    ∃ r, STAmount.operator_add v1 v2 .downward = .ok r := by
  rw [STAmount.operator_add_iou_unfold v1 v2 .downward hc1 hc2]
  have hme : maxExponent = 32768 := rfl
  have hmi : minExponent = -32768 := rfl
  have hx := lift_isNormalized v1.mIsNegative v1.mValue v1.mOffset hc1.mant_lo hc1.mant_hi
    (by have := hc1.exp_lo; omega) (by have := hc1.exp_hi; omega)
  have hy := lift_isNormalized v2.mIsNegative v2.mValue v2.mOffset hc2.mant_lo hc2.mant_hi
    (by have := hc2.exp_lo; omega) (by have := hc2.exp_hi; omega)
  have hxv := lift_toRat v1 hc1.mant_hi
  have hyv := lift_toRat v2 hc2.mant_hi
  obtain ⟨n, hn⟩ := add_ok _ _ .downward hx hy
    (by show v1.mOffset - 3 + 30 ≤ _; have := hc1.exp_hi; omega)
    (by show v2.mOffset - 3 + 30 ≤ _; have := hc2.exp_hi; omega)
  rw [hn]
  simp only []
  by_cases hnm : n.mantissa_ = 0
  · exact iou_ofNumber_zero n .downward hnm
  have hnn := operator_add_isNormalized _ _ n .downward hx hy hn hnm
  obtain ⟨m, hlo, hval⟩ := operator_add_rounded_downward _ _ n hx hy hn hnm
  rw [hxv, hyv] at hlo
  have hle : n.toRat ≤ v1.toRat + v2.toRat := by rw [hval]; exact Number.lower_le _ m hlo
  have hge : 0 ≤ n.toRat := by
    rw [hval]
    have := Number.lower_tight _ m hlo Number.zero (Or.inl rfl) (by rw [Number.toRat_zero]; exact h0)
    rwa [Number.toRat_zero] at this
  have hneg := Number.negative_false_of_nonneg n hnn hge
  have he : n.exponent_ ≤ 77 := by
    by_contra hc
    have hbig : (10 : ℚ) ^ (96 : ℤ) ≤ n.toRat := by
      rw [Number.toRat_of_nonneg n hneg]
      have h18 : ((10 ^ 18 : ℕ) : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by
        exact_mod_cast (hnn.mantissaBounds_nat hnm).1
      have hpe : (10 : ℚ) ^ (78 : ℤ) ≤ 10 ^ n.exponent_ :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      calc (10 : ℚ) ^ (96 : ℤ) = ((10 ^ 18 : ℕ) : ℚ) * 10 ^ (78 : ℤ) := by norm_num
        _ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ :=
          mul_le_mul h18 hpe (by positivity) (by positivity)
    linarith
  exact iou_ofNumber_down_ok n hnn hneg he

lemma rte_ok (p : STAmount) (hc : p.IOUCanonical) (hn : p.mIsNegative = false) (s : ℤ)
    (hlo : -96 ≤ s) (hhi : s ≤ 80) (hlt : p.mOffset < s) :
    ∃ a, STAmount.roundToExponent p s .downward = .ok a := by
  have hint : ¬ p.integral = true := by
    unfold STAmount.integral; rw [hc.is_fractional]; decide
  have hz : ¬ p.isZero = true := by
    unfold STAmount.isZero
    have := hc.mant_lo
    intro h
    rw [beq_iff_eq.mp h] at this; simp at this
  unfold STAmount.roundToExponent
  rw [if_neg hint, if_neg hz, if_neg (show ¬ p.exponent ≥ s from by
    show ¬ p.mOffset ≥ s; omega)]
  have href : STAmount.checked p.mNumericType kMinValue s p.negative .downward
      = .ok ⟨.fractional, kMinValue, s, false⟩ := by
    rw [hc.is_fractional, show p.negative = false from hn]
    exact STAmount.checked_reference s false _ hlo hhi
  rw [href]
  simp only []
  have hk : kMinValue.toNat = 10 ^ 15 := by decide
  have hcr : STAmount.IOUCanonical ⟨.fractional, kMinValue, s, false⟩ :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; rw [hk],
      by show kMinValue.toNat < 10 ^ 16; rw [hk]; norm_num, hlo, hhi⟩
  have hrefv : (⟨.fractional, kMinValue, s, false⟩ : STAmount).toRat = 10 ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg _ rfl]; show (kMinValue.toNat : ℚ) * _ = _; rw [hk]; norm_num
  have hs10 : (10 : ℚ) ^ s ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hhi
  have hspos : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hp0 : 0 ≤ p.toRat := STAmount.toRat_nonneg_of p hn
  have hplt : p.toRat < 10 ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg p hn]
    have hm : (p.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
    have he : (10 : ℚ) ^ p.mOffset ≤ 10 ^ (s - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hes : (10 : ℚ) ^ (s - 1) * 10 = 10 ^ s := by
      rw [zpow_sub₀ (by norm_num), zpow_one]; field_simp
    have hpe : (0 : ℚ) < 10 ^ p.mOffset := zpow_pos (by norm_num) _
    calc (p.mValue.toNat : ℚ) * 10 ^ p.mOffset < 10 ^ 16 * 10 ^ p.mOffset :=
          mul_lt_mul_of_pos_right hm hpe
      _ ≤ 10 ^ 16 * 10 ^ (s - 1) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 10 ^ 15 * 10 ^ s := by rw [← hes]; ring
  obtain ⟨sum, hsum⟩ := iou_add_down_ok p ⟨.fractional, kMinValue, s, false⟩ hc hcr
    (by rw [hrefv]; positivity)
    (by rw [hrefv]; nlinarith)
  rw [hsum]
  simp only []
  obtain ⟨k, hk15, hsnt, hsmv, hsoff, hsneg, -⟩ := STAmount.roundToExponent_sum_spec p s .downward
    hc hlt hlo hhi sum (by rw [hc.is_fractional, hn]; exact hsum)
  rw [hn] at hsneg
  have hcs : sum.IOUCanonical :=
    ⟨by rw [hsnt]; exact hc.is_fractional, by omega, by omega, by rw [hsoff]; exact hlo,
      by rw [hsoff]; exact hhi⟩
  have hsv : sum.toRat = (10 ^ 15 + k) * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg sum hsneg, hsmv, hsoff]; push_cast; ring
  have hrn : (⟨.fractional, kMinValue, s, false⟩ : STAmount).operator_neg.toRat
      = -(10 ^ 15 * 10 ^ s) := by
    rw [STAmount.operator_neg_toRat, hrefv]
  have hk0 : (0 : ℚ) ≤ k := by positivity
  have hkle : (k : ℚ) ≤ 10 ^ 15 := by exact_mod_cast hk15
  unfold STAmount.operator_sub
  exact iou_add_down_ok sum _ hcs hcr.operator_neg
    (by rw [hsv, hrn]; nlinarith) (by rw [hsv, hrn]; nlinarith)

end XRPL.Model.SingleAssetVault.ExitsC
