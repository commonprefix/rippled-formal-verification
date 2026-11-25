import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerSteps
import XRPL.Properties.Lending.LoanBroker.Common.CoverCredit
import XRPL.Properties.Vault.Proofs.Support.NoOverflow

/-! # The cover transactions never end in an exception within the asset's range

A cover deposit needs CoverAvailable plus the amount within the asset's maximum (FV_M3_10). A withdrawal and a
clawback build amounts no larger than CoverAvailable and the amount asked for. -/

namespace XRPL.Model.Protocol

/-- An IOU amount made from a Number within `2 * 10^89` in size has an exponent of at most 79. -/
lemma STAmount.ofNumber_fractional_offset_le_cap (n : Number) (mode : rounding_mode) (a : STAmount)
    (hn : n.isNormalized) (hlt : |n.toRat| ≤ 2 * iouProofCap)
    (hok : STAmount.ofNumber .fractional n mode = .ok a) : a.mOffset ≤ 79 := by
  unfold iouProofCap at hlt
  rcases (STAmount.ofNumber_fractional_fczr n mode a hok).2 with hc | hz
  · have hm : a.mValue ≠ 0 := fun h => by have := hc.mant_lo; rw [h] at this; simp at this
    have hn0 := STAmount.ofNumber_source_ne_zero _ n mode a hok hm
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hn0
    have hnlt := Number.exponent_lt_of_abs_lt n hn hn0 72 (by norm_num; linarith)
    have hemin := Number.exponent_ge_min n hn hn0
    obtain ⟨hb, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional n mode a rfl hlo hhi hemin
      (by unfold maxExponent; omega) hok hm
    by_contra hcon
    push Not at hcon
    have h3 : (10 : ℚ) ^ (n.exponent_ + 3) ≤ 10 ^ (74 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have habs : |a.toRat| ≤ 2 * 10 ^ 89 + 10 ^ (74 : ℤ) := by
      have := abs_sub_abs_le_abs_sub a.toRat n.toRat
      linarith
    rw [STAmount.abs_toRat] at habs
    have hm15 : (10 : ℚ) ^ 15 ≤ a.mValue.toNat := by exact_mod_cast hc.mant_lo
    have h80 : (10 : ℚ) ^ (80 : ℤ) ≤ 10 ^ a.mOffset := zpow_le_zpow_right₀ (by norm_num) hcon
    have : (10 : ℚ) ^ 15 * 10 ^ (80 : ℤ) ≤ a.mValue.toNat * 10 ^ a.mOffset :=
      mul_le_mul hm15 h80 (by positivity) (by positivity)
    norm_num at this habs
    linarith
  · have hoff : a.mOffset = -100 := by
      rw [STAmount.ofNumber] at hok
      split at hok
      · exact absurd ‹NumericType.fractional.isIntegral = true› (by decide)
      · split at hok
        · exact absurd hok (by simp)
        · obtain ⟨v, -, hok⟩ := bind_ok_peel _ _ _ hok
          rw [STAmount.checked] at hok
          exact STAmount.canonicalize_fractional_zero_offset _ a mode rfl hok hz
    omega

/-- The exponent of an IOU balance after a credit or debit computes while the new balance is within `2 * 10^89` in
size. It is at least the base exponent and at most 79. -/
lemma postSumExponent_frac_ok_of_cap (A c : Number) (b : Int) (hA : A.isNormalized) (hc : c.isNormalized)
    (hAl : |A.toRat| < 10 ^ 96) (hcl : |c.toRat| < 10 ^ 96) (hb : b ≤ 0)
    (hsum : |A.toRat + c.toRat| ≤ 2 * iouProofCap) :
    ∃ e, postSumExponent A c b .fractional = .ok e ∧ b ≤ e ∧ e ≤ 79 := by
  obtain ⟨s, hs, hsn⟩ := Number.operator_add_total_of_abs A c .to_nearest hA hc hAl hcl
  obtain ⟨lo, hi, hlo, hhi, hlov, hhiv⟩ := iouProofCap_two_number
  have hcap0 : (0 : ℚ) ≤ iouProofCap := by unfold iouProofCap; positivity
  obtain ⟨hs1, hs2⟩ := Number.operator_add_between A c s lo hi .to_nearest hA hc hs hlo hhi (by rw [hlov]; linarith)
    (by rw [hhiv]; linarith) (by rw [hlov]; exact (abs_le.mp hsum).1) (by rw [hhiv]; exact (abs_le.mp hsum).2)
  have hsabs : |s.toRat| ≤ 2 * iouProofCap :=
    abs_le.mpr ⟨by rw [← hlov]; exact hs1, by rw [← hhiv]; exact hs2⟩
  have hne : ∃ e, numberExponent s b .fractional = .ok e ∧ e ≤ 79 := by
    unfold numberExponent
    by_cases hz : s.operator_eq Number.zero = true
    · rw [ite_eq_left hz]; exact ⟨b, rfl, by omega⟩
    · rw [ite_eq_right hz]
      obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s .downward hsn
        (lt_of_le_of_lt hsabs (by unfold iouProofCap; norm_num))
      have hoff := STAmount.ofNumber_fractional_offset_le_cap s .downward st hsn hsabs hst
      rw [hst]
      exact ⟨_, rfl, max_le (by omega) hoff⟩
  obtain ⟨e, he, he79⟩ := hne
  refine ⟨e, ?_, numberExponent_ge _ _ _ _ he, he79⟩
  unfold postSumExponent
  rw [hs, ok_bind]
  exact he

/-- The exponent of an XRP or MPT balance after a credit computes while the new balance is within the asset's
maximum. -/
lemma postSumExponent_integral_ok_of_cap (A c : Number) (b : Int) (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hint : nt.isIntegral = true) (hA : A.isNormalized)
    (hc : c.isNormalized) (hAl : |A.toRat| < 10 ^ 96) (hcl : |c.toRat| < 10 ^ 96) (h0 : 0 ≤ A.toRat + c.toRat)
    (hsum : A.toRat + c.toRat ≤ nt.maxValue.toNat) : ∃ e, postSumExponent A c b nt = .ok e := by
  obtain ⟨s, hs, hsn⟩ := Number.operator_add_total_of_abs A c .to_nearest hA hc hAl hcl
  obtain ⟨w, hw, hwv⟩ := NumericType.maxAmount_number nt hasset
  have hmax : nt.maxAmount = nt.maxValue.toNat := by unfold NumericType.maxAmount; rw [ite_eq_left hint]
  obtain ⟨hs1, hs2⟩ := Number.operator_add_between A c s Number.zero w .to_nearest hA hc hs
    Number.zero_isNormalized hw (by rw [Number.toRat_zero]) (by rw [hwv, hmax]; positivity)
    (by rw [Number.toRat_zero]; exact h0) (by rw [hwv, hmax]; exact hsum)
  rw [Number.toRat_zero] at hs1
  unfold postSumExponent
  rw [hs, ok_bind]
  unfold numberExponent
  by_cases hz : s.operator_eq Number.zero = true
  · rw [ite_eq_left hz]; exact ⟨b, rfl⟩
  · rw [ite_eq_right hz]
    obtain ⟨st, hst⟩ := STAmount.ofNumber_ok_of_asset_cap nt s .downward hasset hsn hs1
      (fun _ => by rw [← hmax, ← hwv]; exact hs2) (fun h => by rw [hint] at h; cases h)
    rw [hst]
    exact ⟨_, rfl⟩

/-- On XRP or an MPT the floored credit is the amount converted to the asset. -/
lemma sumRoundAndSubtract_integral_eq (A c : Number) (b : Int) (nt : NumericType) (mode : rounding_mode)
    (hint : nt.isIntegral = true) : sumRoundAndSubtract A c b nt mode = STAmount.ofNumber nt c mode := by
  unfold sumRoundAndSubtract
  simp only [hint, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  cases STAmount.ofNumber nt c mode <;> rfl

/-- The floored credit of an XRP or MPT balance is the amount itself, which converts within the asset's maximum. -/
lemma sumRoundAndSubtract_integral_ok_of_cap (A c : Number) (b : Int) (nt : NumericType) (mode : rounding_mode)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hint : nt.isIntegral = true) (hc : c.isNormalized)
    (hc0 : 0 ≤ c.toRat) (hcap : c.toRat ≤ nt.maxValue.toNat) :
    ∃ st, sumRoundAndSubtract A c b nt mode = .ok st := by
  obtain ⟨st, hst⟩ := STAmount.ofNumber_ok_of_asset_cap nt c mode hasset hc hc0 (fun _ => hcap)
    (fun h => by rw [hint] at h; cases h)
  exact ⟨st, by rw [sumRoundAndSubtract_integral_eq A c b nt mode hint, hst]⟩

/-- The floored credit of an IOU balance computes while the new balance is within `10^89`. -/
lemma sumRoundAndSubtract_frac_downward_ok_of_cap (A c : Number) (b : Int) (hA : A.isNormalized)
    (hc : c.isNormalized) (hA0 : 0 ≤ A.toRat) (hc0 : 0 ≤ c.toRat) (hb : -10 ≤ b ∧ b ≤ 0)
    (hsum : A.toRat + c.toRat ≤ iouProofCap) : ∃ st, sumRoundAndSubtract A c b .fractional .downward = .ok st := by
  have hcapv : iouProofCap = 10 ^ 89 := rfl
  have h8996 : (10 : ℚ) ^ 89 < 10 ^ 96 := by norm_num
  have h8990 : (10 : ℚ) ^ 89 < 10 ^ 90 := by norm_num
  have hAl : |A.toRat| < 10 ^ 96 := by rw [abs_of_nonneg hA0]; linarith
  have hcl : |c.toRat| < 10 ^ 96 := by rw [abs_of_nonneg hc0]; linarith
  obtain ⟨e, he, hbe, he79⟩ := postSumExponent_frac_ok_of_cap A c b hA hc hAl hcl hb.2
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  obtain ⟨lo, hi, hlo, hhi, hlov, hhiv⟩ := iouProofCap_number

  obtain ⟨sm, hsm, hsmn⟩ := Number.operator_add_total_of_abs A c .downward hA hc hAl hcl
  obtain ⟨hsm0, hsmle⟩ := Number.operator_add_between A c sm Number.zero hi .downward hA hc hsm
    Number.zero_isNormalized hhi (by rw [Number.toRat_zero]) (by rw [hhiv, hcapv]; positivity)
    (by rw [Number.toRat_zero]; linarith) (by rw [hhiv]; exact hsum)
  rw [Number.toRat_zero] at hsm0
  rw [hhiv, hcapv] at hsmle
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr sm .downward hsmn
    (by rw [abs_of_nonneg hsm0]; linarith)
  have hretle : 0 ≤ ret.toRat ∧ ret.toRat ≤ sm.toRat := by
    by_cases hz : ret.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero ret hz]; exact ⟨le_refl _, hsm0⟩
    · obtain ⟨h1, -, h2⟩ := STAmount.ofNumber_downward_floor_bounds .fractional sm ret hsmn
        (Number.negative_false_of_nonneg sm hsmn hsm0) hret hz
      exact ⟨h2, h1⟩
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  obtain ⟨rd, hrd, hrdle⟩ : ∃ rd, STAmount.roundToExponent ret e .downward = .ok rd ∧
      0 ≤ rd.toRat ∧ rd.toRat ≤ ret.toRat := by
    rcases hretf.2 with hc' | hz
    · obtain ⟨rd, hrd⟩ := STAmount.roundToExponent_downward_ok ret e hc'
        (STAmount.mIsNegative_false_of_nonneg ret hretle.1 (by
          intro h0; have := hc'.mant_lo; rw [h0] at this; exact absurd this (by decide)))
        (by omega) (by omega)
      exact ⟨rd, hrd, STAmount.roundToExponent_downward_nonneg ret rd e hc' (by omega) (by omega) hretle.1 hrd,
        STAmount.roundToExponent_downward_le ret rd e hc' (by omega) (by omega) hretle.1 hrd⟩
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret e _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz]))),
        hretle.1, le_refl _⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd e .downward hretf hrd
  obtain ⟨sm', hsm', hsm'n, -⟩ := hrdf.toNumber_ok .downward
  have hsm'v : sm'.toRat = rd.toRat := by
    rcases hrdf.2 with hc' | hz
    · rw [STAmount.toNumber_iou_canonical rd .downward hc', Except.ok.injEq] at hsm'
      rw [← hsm']; exact STAmount.toNumber_iou_canonical_toRat rd hc'
    · have hfr : rd.integral = false := by unfold STAmount.integral; rw [hrdf.1]; rfl
      rw [STAmount.toNumber_zero_fractional rd _ hfr hz, Except.ok.injEq] at hsm'
      rw [← hsm', Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero rd hz]
  have hround : STAmount.roundToNumericType .fractional sm .downward (some e) = .ok sm' := by
    unfold STAmount.roundToNumericType
    rw [hret]
    simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
    rw [hrd]
    exact hsm'

  have hsm'0 : 0 ≤ sm'.toRat := by rw [hsm'v]; exact hrdle.1
  have hsm'le : sm'.toRat ≤ 10 ^ 89 := by rw [hsm'v]; linarith [hrdle.2, hretle.2]
  obtain ⟨d, hd, hdn⟩ := Number.operator_sub_total_of_abs sm' A .downward hsm'n hA
    (by rw [abs_of_nonneg hsm'0]; linarith) hAl
  obtain ⟨hd1, hd2⟩ := Number.operator_sub_between sm' A d lo hi .downward hsm'n hA hd hlo hhi
    (by rw [hlov, hcapv]; norm_num) (by rw [hhiv, hcapv]; positivity) (by rw [hlov, hcapv]; linarith)
    (by rw [hhiv, hcapv]; linarith)
  rw [hlov, hcapv] at hd1
  rw [hhiv, hcapv] at hd2
  obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr d .downward hdn
    (by rw [abs_lt]; constructor <;> linarith)
  refine ⟨st, ?_⟩
  unfold sumRoundAndSubtract
  rw [ite_eq_right (by decide)]
  show (pure PUnit.unit >>= fun _ => (do
      let exponent ← postSumExponent A c b NumericType.fractional
      let sum ← A.operator_add c rounding_mode.downward
      let sum' ← STAmount.roundToNumericType NumericType.fractional sum rounding_mode.downward (some exponent)
      let amountDelta' ← sum'.operator_sub A rounding_mode.downward
      STAmount.ofNumber NumericType.fractional amountDelta' rounding_mode.downward)) = _
  rw [show (pure PUnit.unit : Except Error PUnit) = .ok PUnit.unit from rfl, ok_bind, he, ok_bind, hsm, ok_bind,
    hround, ok_bind, hd, ok_bind, hst]

/-- An amount above zero has a value at least zero. -/
lemma STAmount.nonneg_of_signum_pos (r : STAmount) (h : 0 < r.signum) : 0 ≤ r.toRat := by
  unfold STAmount.signum at h
  split at h
  · omega
  · split at h
    · omega
    · exact STAmount.toRat_nonneg_of r (by simpa using ‹¬ r.mIsNegative = true›)

/-- A canonical amount of an asset is below `10^96` in size. -/
lemma STAmount.Canonical.abs_lt (a : STAmount) (hc : a.Canonical) : |a.toRat| < 10 ^ 96 := by
  rw [STAmount.abs_toRat]
  by_cases hint : a.integral = true
  · obtain ⟨hic, hmax⟩ := hc.1 hint
    rw [hic.offset_zero, zpow_zero, mul_one]
    have h1 : a.mValue.toNat < 2 ^ 64 := UInt64.toNat_lt_size _
    have h2 : (a.mValue.toNat : ℚ) < 2 ^ 64 := by exact_mod_cast h1
    linarith [show (2 : ℚ) ^ 64 < 10 ^ 96 by norm_num]
  · have hic := hc.2 (by simpa using hint)
    have hm : (a.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hic.mant_hi
    have hp : (10 : ℚ) ^ a.mOffset ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hic.exp_hi
    have hp0 : (0 : ℚ) < 10 ^ a.mOffset := zpow_pos (by norm_num) _
    calc (a.mValue.toNat : ℚ) * 10 ^ a.mOffset < 10 ^ 16 * 10 ^ a.mOffset := mul_lt_mul_of_pos_right hm hp0
      _ ≤ 10 ^ 16 * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 10 ^ 96 := by norm_num

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The amount a cover deposit credits is an amount of the asset, from zero to the amount offered. -/
lemma LoanBroker.roundedCoverAmount_facts (lb : LoanBroker) (v : Vault) (amount r : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hcan : amount.Canonical)
    (hnn : 0 ≤ amount.toRat) (hok : (lb.roundedCoverAmount v amount).run = .ok (.ok r)) :
    r.CanonicalOrZero ∧ 0 ≤ r.toRat ∧ r.toRat ≤ amount.toRat := by
  have hbase := v.baseExponent_bounds
  obtain ⟨aN, -, hs, hsig⟩ := LoanBroker.roundedCoverAmount_ok lb v amount r hok
  have hle := (LoanBroker.roundedCoverAmount_le lb v amount r hcan hnn
    ⟨by rw [Vault.pool_baseExponent]; omega, by rw [Vault.pool_baseExponent]; omega⟩ hok).1
  refine ⟨?_, STAmount.nonneg_of_signum_pos r hsig, hle⟩
  rw [hnt] at hs
  cases hint : v.numericType.isIntegral
  · rw [NumericType.eq_fractional_of_not_integral hint] at hs
    exact (sumRoundAndSubtract_frac_fczr _ _ _ _ r hs).canonicalOrZero
  · rw [sumRoundAndSubtract_integral_eq _ _ _ _ _ hint] at hs
    exact (STAmount.ofNumber_canonicalOrZero _ _ _ _ (fun _ => hasset.maxValue_le hint) hs).1

/-- The rounding of a cover deposit never throws while CoverAvailable plus the amount is within the asset's
range. -/
lemma LoanBroker.roundedCoverAmount_total (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hcan : amount.Canonical)
    (hnn : 0 ≤ amount.toRat) (hrange : lb.coverAvailable.toRat + amount.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat + amount.toRat ≤ iouProofCap) :
    ∃ x, (lb.roundedCoverAmount v amount).run = .ok x := by
  have hbase := v.baseExponent_bounds
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  obtain ⟨aN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok (Or.inl hcan)
  obtain ⟨haNv, haNn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hcan) aN haN
  obtain ⟨st, hst⟩ : ∃ st, sumRoundAndSubtract lb.coverAvailable aN v.baseExponent lb.numericType .downward
      = .ok st := by
    rw [hnt]
    cases hint : v.numericType.isIntegral
    · rw [NumericType.eq_fractional_of_not_integral hint]
      exact sumRoundAndSubtract_frac_downward_ok_of_cap _ _ _ hcn haNn hc0 (by rw [haNv]; exact hnn)
        ⟨hbase.1, hbase.2.1⟩ (by rw [haNv]; exact hiou hint)
    · refine sumRoundAndSubtract_integral_ok_of_cap _ _ _ _ _ hasset hint haNn (by rw [haNv]; exact hnn) ?_
      have hmax : v.numericType.maxAmount = v.numericType.maxValue.toNat := by
        unfold NumericType.maxAmount; rw [ite_eq_left hint]
      rw [haNv, ← hmax]
      linarith
  simp only [LoanBroker.roundedCoverAmount]
  unfold_ter
  simp only [haN, Vault.pool_baseExponent, hst]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The Open-limit check of a cover credit never throws while CoverAvailable plus the credit is within the asset's
range. -/
lemma LoanBroker.checkCoverOpenLimit_total (lb : LoanBroker) (v : Vault) (r : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hr : r.CanonicalOrZero)
    (hr0 : 0 ≤ r.toRat) (hrange : lb.coverAvailable.toRat + r.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat + r.toRat ≤ iouProofCap) :
    ∃ ter, lb.checkCoverOpenLimit v r = .ok ter := by
  have hbase := v.baseExponent_bounds
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  obtain ⟨rN, hrN⟩ := hr.toNumber_ok
  obtain ⟨hrNv, hrNn⟩ := hr.toNumber_exact rN hrN
  have hcl : |lb.coverAvailable.toRat| < 10 ^ 96 := by rw [abs_of_nonneg hc0]; linarith
  have hrl : |rN.toRat| < 10 ^ 96 := by rw [hrNv, abs_of_nonneg hr0]; linarith
  obtain ⟨e, he⟩ : ∃ e, postSumExponent lb.coverAvailable rN v.baseExponent lb.numericType = .ok e := by
    rw [hnt]
    cases hint : v.numericType.isIntegral
    · rw [NumericType.eq_fractional_of_not_integral hint]
      obtain ⟨e, he, -⟩ := postSumExponent_frac_ok_of_cap _ _ v.baseExponent hcn hrNn hcl hrl hbase.2.1
        (by rw [hrNv, abs_of_nonneg (by linarith)]; linarith [hiou hint])
      exact ⟨e, he⟩
    · have hmax : v.numericType.maxAmount = v.numericType.maxValue.toNat := by
        unfold NumericType.maxAmount; rw [ite_eq_left hint]
      exact postSumExponent_integral_ok_of_cap _ _ _ _ hasset hint hcn hrNn hcl hrl (by rw [hrNv]; linarith)
        (by rw [hrNv, ← hmax]; exact hrange)
  obtain ⟨c', hc', -⟩ := Number.operator_add_total_of_abs lb.coverAvailable rN .towards_zero hcn hrNn hcl hrl
  obtain ⟨L, hL, -⟩ := Vault.pool_openLimit_ok v
  unfold LoanBroker.checkCoverOpenLimit
  simp only [bind, Except.bind, pure, Except.pure, hrN, Vault.pool_baseExponent, he, hc', hL]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The LoanBrokerCoverDeposit checks never throw while CoverAvailable plus the amount is within the asset's
range. -/
lemma LoanBroker.canCoverDeposit_total (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hcan : amount.Canonical)
    (hnn : 0 ≤ amount.toRat) (hrange : lb.coverAvailable.toRat + amount.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat + amount.toRat ≤ iouProofCap) :
    ∃ ter, lb.canCoverDeposit v amount = .ok ter := by
  obtain ⟨x, hx⟩ := LoanBroker.roundedCoverAmount_total lb v amount hasset hnt hcan hnn hrange hiou
  unfold LoanBroker.canCoverDeposit
  simp only [bind, Except.bind, pure, Except.pure, hx]
  cases x with
  | error ter => exact ⟨ter, rfl⟩
  | ok r =>
    obtain ⟨hrc, hr0, hrle⟩ := LoanBroker.roundedCoverAmount_facts lb v amount r hasset hnt hcan hnn hx
    exact LoanBroker.checkCoverOpenLimit_total lb v r hasset hnt hrc hr0 (by linarith)
      (fun hint => by linarith [hiou hint])

/-- A cover deposit that passed its checks fails only the broker re-check. -/
lemma LoanBroker.coverDeposit_error_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hcan : amount.Canonical)
    (hnn : 0 ≤ amount.toRat) (hrange : lb.coverAvailable.toRat + amount.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat + amount.toRat ≤ iouProofCap) {e : Error}
    (h : (lb.coverDeposit v amount).run = .error e) : e = .notLawful := by
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  obtain ⟨x, hx⟩ := LoanBroker.roundedCoverAmount_total lb v amount hasset hnt hcan hnn hrange hiou
  simp only [ExceptT.run] at hx
  simp only [LoanBroker.coverDeposit] at h
  unfold_ter at h
  rw [hx] at h
  cases x with
  | error ter => simp at h
  | ok r =>
    obtain ⟨hrc, hr0, hrle⟩ := LoanBroker.roundedCoverAmount_facts lb v amount r hasset hnt hcan hnn hx
    dsimp only at h
    cases happ : lb.applyCoverTransaction .credit r with
    | error e' =>
      rw [happ] at h
      cases h
      exact LoanBroker.applyCoverTransaction_error lb .credit r hrc (by rw [abs_of_nonneg hr0]; linarith)
        (by linarith) happ
    | ok y => rw [happ] at h; cases h

/-- A cover deposit that passed its preflight names a canonical amount above zero. -/
lemma LendingTx.preflight_coverDeposit_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (amount : STAmount) (hpre : (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS) :
    amount.Canonical ∧ 0 ≤ amount.toRat := by
  have hc : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true] at hc
  have hpos := hc.2
  simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hpos
  obtain ⟨hcan, -⟩ := isCanonicalAmount_canonical amount _ hasset.maxValue_le hc.1 hpos.2
  exact ⟨hcan, STAmount.toRat_nonneg_of amount hpos.1⟩

/-- Proof body of the LoanBrokerCoverDeposit line: on a reachable ledger it returns a result code while
CoverAvailable plus the amount is within the asset's maximum, and within `10^89` for an IOU. -/
lemma LendingLedger.loanBrokerCoverDeposit_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : STAmount)
    (hrange : ∀ b, l.broker? i = some b →
      b.coverAvailable.toRat + amount.toRat ≤ l.vault.numericType.maxAmount)
    (hiou : l.vault.numericType.isIntegral = false → ∀ b, l.broker? i = some b →
      b.coverAvailable.toRat + amount.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverDeposit i amount)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerCoverDeposit i amount)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    obtain ⟨hcan, hnn⟩ := LendingTx.preflight_coverDeposit_canonical l hr.holdsAsset i amount hpre
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · have hc := ‹LoanBroker.canCoverDeposit _ l.vault amount = .error e›
      have hbr := ‹l.broker? i = some _›
      obtain ⟨ter, hter⟩ := LoanBroker.canCoverDeposit_total _ l.vault amount hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hcan hnn (hrange _ hbr) (fun hint => hiou hint _ hbr)
      rw [hter] at hc
      cases hc
    · have hbr := ‹l.broker? i = some _›
      have hd := ‹LoanBroker.coverDeposit _ l.vault amount = .error e›
      obtain rfl := LoanBroker.coverDeposit_error_notLawful _ l.vault amount hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hcan hnn (hrange _ hbr) (fun hint => hiou hint _ hbr) hd
      exact LendingLedger.loanBrokerCoverDeposit_ne_notLawful l hr i amount hrun

end XRPL.Model.Lending
