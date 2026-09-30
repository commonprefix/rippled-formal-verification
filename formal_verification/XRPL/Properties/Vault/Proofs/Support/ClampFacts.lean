import XRPL.Properties.Protocol.STAmount.Sub.RoundsWithin
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Vault.Proofs.Support.FracCanon
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts

/-! # Grid rounding and the sum clamp

Facts about `STAmount.roundToExponent` and `clampToSumExponent`. -/

namespace XRPL.Model.Protocol

open XRPL.Model.SingleAssetVault (bind_ok_peel)

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- **Sum-branch shape.** The non-negative (deposit) branch of the clamp ends in a
fractional `ofNumber`, so the reported amount is canonical-or-zero: every
intermediate stays normalized, which is all the final pack needs. No value bound
is involved, hence no exponent-range obligation. -/
lemma clampToSumExponent_sum_shape (amount : Number) (delta reported : STAmount)
    (hamt : amount.isNormalized)
    (hdc : delta.IOUCanonical ∨ delta.mValue = 0)
    (hfrac : delta.integral = false)
    (hbr : delta.negative = false)
    (hcl : clampToSumExponent amount delta = .ok reported) :
    reported.mNumericType = delta.mNumericType ∧
      (reported.IOUCanonical ∨ reported.mValue = 0) := by
  have hnt : delta.numericType.isIntegral = false := hfrac
  unfold clampToSumExponent at hcl
  simp only [hbr, pure_bind] at hcl
  rw [if_neg (by simp [hfrac])] at hcl
  obtain ⟨pe, -, hcl⟩ := bind_ok_peel _ _ _ hcl
  rw [if_neg (by simp)] at hcl
  obtain ⟨sum, hsum, hcl⟩ := bind_ok_peel _ _ _ hcl
  obtain ⟨d, hd, hcl⟩ := bind_ok_peel _ _ _ hcl
  unfold sumAndRoundToExponent at hsum
  obtain ⟨dn, hdn, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s1, hs1, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s2, hs2, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s3, hs3, hsum⟩ := bind_ok_peel _ _ _ hsum
  -- the delta converts exactly, so the partial sum stays normalized
  have hdn_norm : dn.isNormalized := by
    rcases hdc with h | h
    · obtain ⟨sn, hsn, -, hsnn⟩ := STAmount.toNumber_iou_exact delta .downward h
      rw [show dn = sn from Except.ok.inj (hdn.symm.trans hsn)]; exact hsnn
    · rw [STAmount.toNumber_zero_eq delta .downward dn h hdn]; exact Or.inl rfl
  have hs2_shape : s2.IOUCanonical ∨ s2.mValue = 0 := by
    by_cases hs1m : s1.mantissa_ = 0
    · refine Or.inr ?_
      by_contra hne
      exact (STAmount.ofNumber_source_ne_zero delta.numericType s1 .downward s2 hs2 hne) hs1m
    · exact STAmount.ofNumber_frac_shape delta.numericType s1 .downward s2 hnt
        (operator_add_isNormalized amount dn s1 .downward hamt hdn_norm hs1 hs1m) hs2
  have hs2_nt : s2.mNumericType = .fractional := by
    rw [STAmount.ofNumber_mNumericType delta.numericType s1 .downward s2 hs2]
    cases h : delta.numericType with
    | fractional => rfl
    | integral mv mo ms msh => rw [h] at hnt; simp [NumericType.isIntegral] at hnt
  have hs3_fcz := STAmount.roundToExponent_fczr s2 s3 pe .downward ⟨hs2_nt, hs2_shape⟩ hs3
  have hsum_norm : sum.isNormalized := by
    rcases hs3_fcz.2 with hiou | hz
    · obtain ⟨sn, hsn, -, hsnn⟩ := STAmount.toNumber_iou_exact s3 .downward hiou
      rw [show sum = sn from Except.ok.inj (hsum.symm.trans hsn)]; exact hsnn
    · rw [STAmount.toNumber_zero_eq s3 .downward sum hz hsum]; exact Or.inl rfl
  have hd_norm : d.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz sum amount d hsum_norm hamt hd
  exact ⟨STAmount.ofNumber_mNumericType delta.numericType d .to_nearest reported hcl,
    STAmount.ofNumber_frac_shape delta.numericType d .to_nearest reported hnt hd_norm hcl⟩

/-- In the negative (withdraw/clawback) clamp branch a zero priced payout is
reported as zero: `roundToExponent` is the identity on a zero amount. -/
lemma clampToSumExponent_neg_zero (amount : Number) (priced reported : STAmount)
    (hz : priced.mValue = 0)
    (hbr : (priced.operator_neg).negative = true)
    (hcl : clampToSumExponent amount priced.operator_neg = .ok reported) :
    reported.mValue = 0 := by
  have hid : priced.operator_neg = priced := by unfold STAmount.operator_neg; simp [hz]
  rw [hid] at hcl hbr
  unfold clampToSumExponent at hcl
  simp only [hbr, if_true, hid, pure_bind] at hcl
  by_cases hint : priced.integral = true
  · simp only [hint, if_true] at hcl
    rw [← Except.ok.inj hcl]; exact hz
  · rw [if_neg hint] at hcl
    obtain ⟨pe, -, hcl⟩ := bind_ok_peel _ _ _ hcl
    unfold STAmount.roundToExponent at hcl
    rw [if_neg hint, if_pos (show priced.isZero = true by unfold STAmount.isZero; simp [hz])] at hcl
    rw [← Except.ok.inj hcl]; exact hz

/-- **The clamp is inert on an integral amount.** `clampToSumExponent` snaps a
delta to the grid of `amount + delta`, but an integral delta is already on every
grid coarser than one unit, so the call returns the delta's magnitude unchanged.
This is why the `_integral` accuracy variants carry no clamp term. -/
lemma clampToSumExponent_integral (amount : Number) (amountDelta : STAmount)
    (hint : amountDelta.integral = true) :
    clampToSumExponent amount amountDelta =
      .ok (if amountDelta.negative then amountDelta.operator_neg else amountDelta) := by
  unfold clampToSumExponent
  simp only [hint, if_pos]
  rfl

/-- On an integral vault the deposit clamp is the identity: an integral charge
already sits on the grid of `assetsTotal + charge`. -/
lemma clampToSumExponent_integral_nonneg (amount : Number) (a c : STAmount)
    (hint : a.integral = true) (hnn : 0 ≤ a.toRat)
    (hcl : clampToSumExponent amount a = .ok c) : c = a := by
  rw [clampToSumExponent_integral amount a hint] at hcl
  rw [← Except.ok.inj hcl]
  by_cases hz : a.mValue = 0
  · have hid : a.operator_neg = a := by unfold STAmount.operator_neg; simp [hz]
    simp [hid]
  · have hsgn : a.mIsNegative = false := by
      by_contra h
      have := STAmount.toRat_neg_of a (by simpa using h) hz
      linarith
    simp [STAmount.negative, hsgn]

/-- **The downward `roundToExponent` of a nonnegative value is nonnegative.** The
early exits pass the value through (already nonnegative); the truncation path
floors `value` onto the `10 ^ s` grid, and the floor of a nonnegative value is
nonnegative (`0` is a grid point below it), so the stored result never goes
negative. Uses only the `[-96, 80]` scale range (available from `IOUCanonical`),
never the tighter `-81` the exact-floor characterization needs. -/
lemma STAmount.roundToExponent_downward_nonneg (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    0 ≤ result.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]; exact hnn
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, _, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        by_cases hrv : result.mValue = 0
        · rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
        · by_cases hk0 : k = 0
          · -- exact cancellation: `k = 0` forces `sum = refA`, so `operator_sub sum refA` is a
            -- self-difference and flushes to the canonical zero, contradicting `result.mValue ≠ 0`.
            exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            obtain ⟨_, hgap⟩ := hrw
            have hgap2 : (sum.toRat - refA.toRat) - result.toRat
                ≤ |sum.toRat - refA.toRat| * IOUAmount.εDirected := hgap
            rw [abs_of_pos htruth_pos] at hgap2
            have hεlt : IOUAmount.εDirected < 1 := by
              have h1 : (10 : ℚ) ^ (-15 : ℤ) = 1 / 10 ^ 15 := by
                rw [show ((-15) : ℤ) = -(15 : ℕ) from rfl, zpow_neg, zpow_natCast]; norm_num
              show 11 / (2 ^ 63 - 18 : ℚ) + (10 : ℚ) ^ (-15 : ℤ)
                + 11 / (2 ^ 63 - 18 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) < 1
              rw [h1]; norm_num
            have hε1 : (0 : ℚ) < 1 - IOUAmount.εDirected := by linarith [hεlt]
            have hlb : (sum.toRat - refA.toRat) - (sum.toRat - refA.toRat) * IOUAmount.εDirected
                ≤ result.toRat := by linarith [hgap2]
            have hpos_lb : 0 < (sum.toRat - refA.toRat)
                - (sum.toRat - refA.toRat) * IOUAmount.εDirected := by
              nlinarith [mul_pos htruth_pos hε1]
            linarith [hlb, hpos_lb]

/-- **`roundToExponent` downward never raises the value.** The truncating
`.downward` pass keeps a nonnegative amount at or below its input: it rounds
`value.toRat` down onto the `10^s` grid (`⌊value/10^s⌋·10^s ≤ value`), and the
internal `reference + sub` rounds down again, so `result.toRat ≤ value.toRat`.
Works across the full `[-96, 80]` scale range (no `-81` grid-exactness needed). -/
lemma STAmount.roundToExponent_downward_le (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.toRat ≤ value.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, h_dw, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        -- `k = ⌊value/10^s⌋`, so `sum - refA = ⌊value/10^s⌋·10^s ≤ value`
        have hkval : (k : ℤ) = ⌊value.toRat / 10 ^ s⌋ := by
          have hh := h_dw rfl
          rw [hneg, if_neg (by decide : ¬ (false = true)), abs_of_nonneg hnn] at hh
          exact hh
        have hsr_le : sum.toRat - refA.toRat ≤ value.toRat := by
          rw [htruth]
          have hfl : (k : ℚ) = (⌊value.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast hkval
          rw [hfl]
          have hle : (⌊value.toRat / 10 ^ s⌋ : ℚ) ≤ value.toRat / 10 ^ s := Int.floor_le _
          calc (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s
              ≤ (value.toRat / 10 ^ s) * 10 ^ s :=
                mul_le_mul_of_nonneg_right hle (le_of_lt h_pow_s_pos)
            _ = value.toRat := by field_simp
        by_cases hrv : result.mValue = 0
        · have hr0 : result.toRat = 0 := by
            rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
          rw [hr0]; exact hnn
        · by_cases hk0 : k = 0
          · exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            have hle : result.toRat ≤ sum.toRat - refA.toRat := hrw.1
            linarith [hle, hsr_le]

/-- **`postSumExponent` reduction.** It prices the delta, forms the post-operation
total, and reports the exponent of that total's on-ledger form. -/
lemma postSumExponent_reduces (amount : Number) (delta : STAmount) (s : ℤ)
    (hps : postSumExponent amount delta = .ok s) :
    ∃ (dn sum : Number) (a : STAmount),
      delta.toNumber .to_nearest = .ok dn ∧
      amount.operator_add dn .to_nearest = .ok sum ∧
      STAmount.ofNumber delta.numericType sum .to_nearest = .ok a ∧
      a.exponent = s := by
  unfold postSumExponent numberExponent at hps
  obtain ⟨dn, hdn, hps⟩ := bind_ok_peel _ _ _ hps
  obtain ⟨sum, hsum, hps⟩ := bind_ok_peel _ _ _ hps
  obtain ⟨a, ha, hps⟩ := bind_ok_peel _ _ _ hps
  exact ⟨dn, sum, a, hdn, hsum, ha, Except.ok.inj hps⟩

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- **The clamp's sum branch never reports a positive amount from a zero delta.**
Every step from the pre-sum total to the recovered post-sum total rounds DOWNWARD,
so the difference the branch reports is non-positive — and `ofNumber` carries that
sign through. This is what makes the sum branch unreachable on a successful
withdraw, where the `tecPRECISION_LOSS` guard demands a strictly positive payout. -/
lemma clampToSumExponent_sum_zero_nonpos (amount : Number) (delta reported : STAmount)
    (hamt : amount.isNormalized) (hamt_nn : 0 ≤ amount.toRat)
    (hdz : delta.mValue = 0)
    (hfrac : delta.integral = false)
    (hbr : delta.negative = false)
    (hcl : clampToSumExponent amount delta = .ok reported) :
    reported.toRat ≤ 0 := by
  have hnt : delta.numericType.isIntegral = false := hfrac
  have hamt_neg : amount.negative_ = false := Number.negative_false_of_normalized_nonneg amount hamt hamt_nn
  unfold clampToSumExponent at hcl
  simp only [hbr, pure_bind] at hcl
  rw [if_neg (by simp [hfrac])] at hcl
  obtain ⟨pe, hpe, hcl⟩ := bind_ok_peel _ _ _ hcl
  rw [if_neg (by simp)] at hcl
  obtain ⟨sum3, hsum, hcl⟩ := bind_ok_peel _ _ _ hcl
  obtain ⟨d, hd, hcl⟩ := bind_ok_peel _ _ _ hcl
  unfold sumAndRoundToExponent at hsum
  obtain ⟨dn, hdn, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s1, hs1, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s2, hs2, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s3, hs3, hsum⟩ := bind_ok_peel _ _ _ hsum
  have hdn0 : dn = Number.zero := STAmount.toNumber_zero_eq delta .downward dn hdz hdn
  have hs1_eq : s1 = amount := by
    rw [hdn0] at hs1
    unfold Number.operator_add at hs1
    rw [if_pos (by decide)] at hs1
    exact (Except.ok.inj hs1).symm
  rw [hs1_eq] at hs2
  have hdnt : delta.numericType = .fractional := by
    cases h : delta.numericType with
    | fractional => rfl
    | integral mv mo ms msh => rw [h] at hnt; simp [NumericType.isIntegral] at hnt
  -- the recovered post-sum total never exceeds the pre-sum one: every step rounds down
  have hsum3_le : sum3.toRat ≤ amount.toRat ∧ sum3.isNormalized := by
    by_cases hs2z : s2.mValue = 0
    · -- the post-sum total underflows; `roundToExponent` passes a zero through
      have hs3_eq : s3 = s2 := by
        unfold STAmount.roundToExponent at hs3
        rw [if_neg (by show ¬ s2.mNumericType.isIntegral = true
                       rw [STAmount.ofNumber_mNumericType delta.numericType amount .downward s2 hs2,
                         hdnt]
                       decide),
            if_pos (show s2.isZero = true by unfold STAmount.isZero; simp [hs2z])] at hs3
        exact (Except.ok.inj hs3).symm
      rw [hs3_eq] at hsum
      rw [STAmount.toNumber_zero_eq s2 .downward sum3 hs2z hsum, Number.toRat_zero]
      exact ⟨hamt_nn, Or.inl rfl⟩
    · obtain ⟨hs2_le, -, hs2_nn⟩ :=
        STAmount.ofNumber_downward_floor_bounds delta.numericType amount s2 hamt hamt_neg hs2 hs2z
      have hs2c : s2.IOUCanonical := by
        rcases STAmount.ofNumber_frac_shape delta.numericType amount .downward s2 hnt hamt hs2 with
          h | h
        · exact h
        · exact absurd h hs2z
      have hamtm : amount.mantissa_ ≠ 0 :=
        STAmount.ofNumber_source_ne_zero delta.numericType amount .downward s2 hs2 hs2z
      -- `pe` is the exponent of the 16-digit pack of the post-sum total, hence in IOU range
      obtain ⟨dn', sum', a, hdn', hsum', ha, haexp⟩ := postSumExponent_reduces amount delta pe hpe
      have hdn'0 : dn' = Number.zero := STAmount.toNumber_zero_eq delta .to_nearest dn' hdz hdn'
      have hsum'_eq : sum' = amount := by
        rw [hdn'0] at hsum'
        unfold Number.operator_add at hsum'
        rw [if_pos (by decide)] at hsum'
        exact (Except.ok.inj hsum').symm
      rw [hsum'_eq] at ha
      have hanz : a.mValue ≠ 0 := by
        intro haz
        have hlt := STAmount.ofNumber_fractional_zero_below_min delta.numericType amount a
          .to_nearest hnt hamt hamt_neg hamtm ha haz
        have hfloor := STAmount.canonical_disj_abs_toRat_ge s2 (Or.inl hs2c) hs2z
        rw [abs_of_nonneg hs2_nn] at hfloor
        linarith
      have hac : a.IOUCanonical := by
        rcases STAmount.ofNumber_frac_shape delta.numericType amount .to_nearest a hnt hamt ha with
          h | h
        · exact h
        · exact absurd h hanz
      have hpe_lo : (-96 : ℤ) ≤ pe := by rw [← haexp]; exact hac.exp_lo
      have hpe_hi : pe ≤ 80 := by rw [← haexp]; exact hac.exp_hi
      have hs3_le : s3.toRat ≤ s2.toRat :=
        STAmount.roundToExponent_downward_le s2 s3 pe hs2c hpe_lo hpe_hi hs2_nn hs3
      have hs3_fcz := STAmount.roundToExponent_fczr s2 s3 pe .downward
        ⟨hs2c.is_fractional, Or.inl hs2c⟩ hs3
      rcases hs3_fcz.2 with hiou | hz3
      · obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact s3 .downward hiou
        rw [show sum3 = sn from Except.ok.inj (hsum.symm.trans hsn)]
        exact ⟨by rw [hval]; linarith, hnorm⟩
      · rw [STAmount.toNumber_zero_eq s3 .downward sum3 hz3 hsum, Number.toRat_zero]
        exact ⟨hamt_nn, Or.inl rfl⟩
  obtain ⟨hsum3_le', hsum3_norm⟩ := hsum3_le
  -- so the reported delta is non-positive, and `ofNumber` carries the sign through
  have hd_np : d.toRat ≤ 0 := by
    by_cases hdm : d.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero d hdm]
    by_cases ham : amount.mantissa_ = 0
    · -- subtracting a zero: the difference IS the post-sum total, which is `≤ amount = 0`
      have hya : amount.operator_neg = Number.zero := by unfold Number.operator_neg; simp [ham]
      have hres : d = sum3 := by
        unfold Number.operator_sub at hd
        rw [hya] at hd
        unfold Number.operator_add at hd
        rw [if_pos (by decide)] at hd
        exact (Except.ok.inj hd).symm
      have ha0 : amount.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero amount ham
      rw [hres]; linarith
    by_cases hsm : sum3.mantissa_ = 0
    · -- a zero post-sum total: the difference is the negated pre-sum total
      have hs0 : sum3 = Number.zero := Number.eq_zero_of_mantissa_zero sum3 hsum3_norm hsm
      have hyne : ¬ (amount.operator_neg).operator_eq Number.zero = true := by
        intro h
        have hmne : (amount.operator_neg).mantissa_ ≠ 0 := by
          rw [show (amount.operator_neg).mantissa_ = amount.mantissa_ from by
            unfold Number.operator_neg; simp [ham]]
          exact ham
        rw [Number.operator_eq_zero_false_of_mantissa_ne _ hmne] at h
        exact absurd h (by simp)
      have hres : d = amount.operator_neg := by
        unfold Number.operator_sub at hd
        unfold Number.operator_add at hd
        rw [if_neg hyne, if_pos (show sum3.operator_eq Number.zero = true from by
          rw [hs0]; decide)] at hd
        exact (Except.ok.inj hd).symm
      rw [hres]
      refine Number.toRat_nonpos_of_negative _ ?_
      unfold Number.operator_neg
      simp [ham, hamt_neg]
    by_cases heq : sum3.operator_eq amount = true
    · have := Number.operator_sub_eq_zero_of_operator_eq sum3 amount d hsm ham heq hd
      exact absurd (by rw [this]; rfl : d.mantissa_ = 0) hdm
    · exact Number.operator_sub_to_nearest_le sum3 amount Number.zero d hsum3_norm hamt
        (Or.inl rfl) hsm ham (by simpa using heq) hd hdm
        (by rw [Number.toRat_zero]; linarith)
  by_cases hrz : reported.mValue = 0
  · rw [STAmount.toRat_signed, hrz]; simp
  have hdm : d.mantissa_ ≠ 0 :=
    STAmount.ofNumber_source_ne_zero delta.numericType d .to_nearest reported hcl hrz
  have hd_norm : d.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz sum3 amount d hsum3_norm hamt hd
  have hdneg : d.negative_ = true := by
    by_contra h
    have hf : d.negative_ = false := by simpa using h
    have hnn := Number.toRat_nonneg_of_nonnegative d hf
    exact (Number.toRat_ne_zero_of_mantissa_ne_zero d hdm) (le_antisymm hd_np hnn)
  exact STAmount.ofNumber_signtrue_nonpos delta.numericType d .to_nearest reported hnt hd_norm
    hdneg hcl

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- **The clamp's sum branch never reports more than it was handed.** Every step
from the pre-sum total to the recovered post-sum total rounds DOWNWARD, so the
difference the branch reports is at most the delta itself — the deposit-side
counterpart of `clampToSumExponent_neg_bracket`. -/
lemma clampToSumExponent_sum_le (amount : Number) (delta reported : STAmount)
    (hamt : amount.isNormalized) (hamt_nn : 0 ≤ amount.toRat)
    (hdc : delta.IOUCanonical ∨ delta.mValue = 0)
    (hdnn : 0 ≤ delta.toRat)
    (hfrac : delta.integral = false)
    (hbr : delta.negative = false)
    (hcl : clampToSumExponent amount delta = .ok reported) :
    reported.toRat ≤ delta.toRat := by
  rcases hdc with hdc | hdz
  case inr =>
    have hnp := clampToSumExponent_sum_zero_nonpos amount delta reported hamt hamt_nn hdz hfrac
      hbr hcl
    have hd0 : delta.toRat = 0 := (STAmount.toRat_eq_zero_iff delta).mpr hdz
    linarith
  have hnt : delta.numericType.isIntegral = false := hfrac
  have hdnt : delta.numericType = .fractional := by
    cases h : delta.numericType with
    | fractional => rfl
    | integral mv mo ms msh => rw [h] at hnt; simp [NumericType.isIntegral] at hnt
  have hamt_neg : amount.negative_ = false := Number.negative_false_of_normalized_nonneg amount hamt hamt_nn
  unfold clampToSumExponent at hcl
  simp only [hbr, pure_bind] at hcl
  rw [if_neg (by simp [hfrac])] at hcl
  obtain ⟨pe, hpe, hcl⟩ := bind_ok_peel _ _ _ hcl
  rw [if_neg (by simp)] at hcl
  obtain ⟨sum3, hsum, hcl⟩ := bind_ok_peel _ _ _ hcl
  obtain ⟨d, hd, hcl⟩ := bind_ok_peel _ _ _ hcl
  unfold sumAndRoundToExponent at hsum
  obtain ⟨dn, hdn, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s1, hs1, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s2, hs2, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s3, hs3, hsum⟩ := bind_ok_peel _ _ _ hsum
  -- the delta is canonical, so its `Number` form is exact
  obtain ⟨hdnval, hdnnorm⟩ : dn.toRat = delta.toRat ∧ dn.isNormalized := by
    obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact delta .downward hdc
    rw [show dn = sn from Except.ok.inj (hdn.symm.trans hsn)]; exact ⟨hval, hnorm⟩
  obtain ⟨hs1_le, hs1_nn⟩ := Number.operator_add_downward_nonneg_le amount dn s1 hamt hdnnorm
    hamt_nn (by rw [hdnval]; exact hdnn) hs1
  rw [hdnval] at hs1_le
  -- the recovered post-sum total never exceeds the exact one: every step rounds down
  have hsum3 : sum3.toRat ≤ amount.toRat + delta.toRat ∧ sum3.isNormalized := by
    by_cases hs2z : s2.mValue = 0
    · -- the post-sum total underflows; `roundToExponent` passes a zero through
      have hs3_eq : s3 = s2 := by
        unfold STAmount.roundToExponent at hs3
        rw [if_neg (by show ¬ s2.mNumericType.isIntegral = true
                       rw [STAmount.ofNumber_mNumericType delta.numericType s1 .downward s2 hs2,
                         hdnt]
                       decide),
            if_pos (show s2.isZero = true by unfold STAmount.isZero; simp [hs2z])] at hs3
        exact (Except.ok.inj hs3).symm
      rw [hs3_eq] at hsum
      rw [STAmount.toNumber_zero_eq s2 .downward sum3 hs2z hsum, Number.toRat_zero]
      exact ⟨by linarith, Or.inl rfl⟩
    · have hs1m : s1.mantissa_ ≠ 0 :=
        STAmount.ofNumber_source_ne_zero delta.numericType s1 .downward s2 hs2 hs2z
      have hs1norm : s1.isNormalized :=
        operator_add_isNormalized amount dn s1 .downward hamt hdnnorm hs1 hs1m
      have hs1neg : s1.negative_ = false := Number.negative_false_of_normalized_nonneg s1 hs1norm hs1_nn
      obtain ⟨hs2_le, -, hs2_nn⟩ :=
        STAmount.ofNumber_downward_floor_bounds delta.numericType s1 s2 hs1norm hs1neg hs2 hs2z
      have hs2c : s2.IOUCanonical := by
        rcases STAmount.ofNumber_frac_shape delta.numericType s1 .downward s2 hnt hs1norm hs2 with
          h | h
        · exact h
        · exact absurd h hs2z
      -- the grid exponent is the post-sum pack's; a zero pack is the `-100` sentinel,
      -- below the IOU window, so `roundToExponent`'s third early exit makes it the identity
      obtain ⟨dn', sum', a, hdn', hsum', ha, haexp⟩ := postSumExponent_reduces amount delta pe hpe
      obtain ⟨hz100, hrange⟩ :=
        STAmount.ofNumber_frac_exp_range delta.numericType sum' .to_nearest a hnt ha
      have hs3_le : s3.toRat ≤ s2.toRat := by
        by_cases haz : a.mValue = 0
        · have hpe100 : pe = -100 := by rw [← haexp]; exact hz100 haz
          have hge : s2.exponent ≥ pe := by
            have := hs2c.exp_lo
            show pe ≤ s2.mOffset
            omega
          have hid : s3 = s2 := by
            unfold STAmount.roundToExponent at hs3
            rw [if_neg (by show ¬ s2.mNumericType.isIntegral = true
                           rw [hs2c.is_fractional]; decide),
                if_neg (by show ¬ s2.isZero = true; unfold STAmount.isZero; simp [hs2z]),
                if_pos hge] at hs3
            exact (Except.ok.inj hs3).symm
          rw [hid]
        · obtain ⟨hlo, hhi⟩ := hrange haz
          rw [haexp] at hlo hhi
          exact STAmount.roundToExponent_downward_le s2 s3 pe hs2c hlo hhi hs2_nn hs3
      have hs3_fcz := STAmount.roundToExponent_fczr s2 s3 pe .downward
        ⟨hs2c.is_fractional, Or.inl hs2c⟩ hs3
      rcases hs3_fcz.2 with hiou | hz3
      · obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact s3 .downward hiou
        rw [show sum3 = sn from Except.ok.inj (hsum.symm.trans hsn)]
        exact ⟨by rw [hval]; linarith, hnorm⟩
      · rw [STAmount.toNumber_zero_eq s3 .downward sum3 hz3 hsum, Number.toRat_zero]
        exact ⟨by linarith, Or.inl rfl⟩
  obtain ⟨hsum3_le, hsum3_norm⟩ := hsum3
  -- so the reported delta never exceeds the priced one
  have hd_norm : d.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz sum3 amount d hsum3_norm hamt hd
  have hd_le : d.toRat ≤ delta.toRat := by
    by_cases hdm : d.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero d hdm]; exact hdnn
    by_cases ham : amount.mantissa_ = 0
    · -- subtracting a zero: the difference IS the post-sum total
      have hya : amount.operator_neg = Number.zero := by unfold Number.operator_neg; simp [ham]
      have hres : d = sum3 := by
        unfold Number.operator_sub at hd
        rw [hya] at hd
        unfold Number.operator_add at hd
        rw [if_pos (by decide)] at hd
        exact (Except.ok.inj hd).symm
      have ha0 : amount.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero amount ham
      rw [hres]; linarith
    by_cases hsm : sum3.mantissa_ = 0
    · -- a zero post-sum total: the difference is the negated pre-sum total
      have hs0 : sum3 = Number.zero := Number.eq_zero_of_mantissa_zero sum3 hsum3_norm hsm
      have hyne : ¬ (amount.operator_neg).operator_eq Number.zero = true := by
        intro h
        have hmne : (amount.operator_neg).mantissa_ ≠ 0 := by
          rw [show (amount.operator_neg).mantissa_ = amount.mantissa_ from by
            unfold Number.operator_neg; simp [ham]]
          exact ham
        rw [Number.operator_eq_zero_false_of_mantissa_ne _ hmne] at h
        exact absurd h (by simp)
      have hres : d = amount.operator_neg := by
        unfold Number.operator_sub at hd
        unfold Number.operator_add at hd
        rw [if_neg hyne, if_pos (show sum3.operator_eq Number.zero = true from by
          rw [hs0]; decide)] at hd
        exact (Except.ok.inj hd).symm
      have : d.toRat ≤ 0 := by
        rw [hres]
        refine Number.toRat_nonpos_of_negative _ ?_
        unfold Number.operator_neg
        simp [ham, hamt_neg]
      linarith
    by_cases heq : sum3.operator_eq amount = true
    · have := Number.operator_sub_eq_zero_of_operator_eq sum3 amount d hsm ham heq hd
      exact absurd (by rw [this]; rfl : d.mantissa_ = 0) hdm
    · refine Number.operator_sub_to_nearest_le sum3 amount dn d hsum3_norm hamt hdnnorm hsm ham
        (by simpa using heq) hd hdm ?_ |>.trans (le_of_eq hdnval)
      rw [hdnval]; linarith
  by_cases hdneg : d.negative_ = true
  · exact le_trans (STAmount.ofNumber_signtrue_nonpos delta.numericType d .to_nearest reported hnt
      hd_norm hdneg hcl) hdnn
  · rw [hdnt] at hcl
    exact STAmount.ofNumber_frac_le_canonical d delta reported hd_norm (by simpa using hdneg) hdc
      hbr hd_le hcl

/-- On an integral delta the clamp returns the delta's magnitude, so it changes
nothing but the sign bit: type, offset and mantissa all carry through. -/
lemma clampToSumExponent_integral_fields (amount : Number) (s r : STAmount)
    (hint : s.integral = true)
    (hok : clampToSumExponent amount s = .ok r) :
    r.mNumericType = s.mNumericType ∧ r.mOffset = s.mOffset ∧ r.mValue = s.mValue := by
  rw [clampToSumExponent_integral amount s hint] at hok
  rw [← Except.ok.inj hok]
  split
  · exact STAmount.operator_neg_fields s
  · exact ⟨rfl, rfl, rfl⟩

end XRPL.Model.Protocol
