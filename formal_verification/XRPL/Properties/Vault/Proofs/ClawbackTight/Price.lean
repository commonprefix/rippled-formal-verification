import XRPL.Properties.Vault.Proofs.ClawbackTight.Shares
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow

/-! # Asset pricing of the destroyed shares -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

lemma tiny_le : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 1 / 8 := by
  have h : (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-19 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
  have h2 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (-19 : ℤ) = 1 / 10 := by norm_num
  have h3 : (0 : ℚ) ≤ 10 ^ (18 : ℕ) := by positivity
  calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
      ≤ (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (-19 : ℤ) := mul_le_mul_of_nonneg_left h h3
    _ = 1 / 10 := h2
    _ ≤ 1 / 8 := by norm_num

/-- An underflowing two-stage quotient has an exact value below `1/4`. -/
lemma pipe_underflow (x y z p q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hz : z.isNormalized) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hz1 : 1 ≤ z.toRat)
    (hmul : x.operator_mul y .to_nearest = .ok p) (hdiv : p.operator_div z .to_nearest = .ok q)
    (hq : q.mantissa_ = 0) : x.toRat * y.toRat / z.toRat ≤ 1 / 4 := by
  have hxy0 := mul_nonneg hx0 hy0
  have hz0 : 0 < z.toRat := by linarith
  have hle : x.toRat * y.toRat / z.toRat ≤ x.toRat * y.toRat := div_le_self hxy0 hz1
  by_cases hxm : x.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero x hxm]; norm_num
  by_cases hym : y.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero y hym]; norm_num
  have ht := tiny_le
  by_cases hpm : p.mantissa_ = 0
  · have := operator_mul_underflow_truth_small x y p _ hx hy hxm hym hmul hpm
    rw [abs_of_nonneg hxy0] at this
    linarith
  · have hpn := operator_mul_result_isNormalized _ _ _ _ hx hy hxm hym hmul hpm
    have hzm := operator_div_divisor_ne_zero _ _ _ _ hz hdiv
    have hu := operator_div_underflow_truth_small p z q _ hpn hz hpm hzm hdiv hq
    have hw1 := operator_mul_rounds_to_nearest x y p hx hy hmul hpm
    simp only [RoundsWithin, RatValued.toRat] at hw1
    change |p.toRat - x.toRat * y.toRat| ≤ |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7)) at hw1
    rw [abs_of_nonneg hxy0] at hw1
    have ha : x.toRat * y.toRat * (5 / (2 ^ 63 + 7)) ≤ x.toRat * y.toRat * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by norm_num) hxy0
    have hp : x.toRat * y.toRat / 2 ≤ |p.toRat| := by
      have := (abs_le.mp hw1).1
      have := le_abs_self p.toRat
      linarith
    rw [abs_div, abs_of_pos hz0, div_lt_iff₀ hz0] at hu
    rw [div_le_iff₀ hz0]
    nlinarith

lemma one_le_sharesTotal (v : Vault) (h : v.sharesTotal.mantissa_ ≠ 0) : 1 ≤ v.sharesTotal.toRat := by
  have hne := Number.toRat_ne_zero_of_mantissa_ne_zero _ h
  have hpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg (Ne.symm hne)
  have := rat_one_le_sub_of_lt v.sharesTotal.toRat 0 v.wf.sharesTotal_int rfl hpos
  linarith

/-- The priced recovery of `sd` shares: the rounded quotient of the pipeline, or an
underflow to zero from an ideal below `1/4`. -/
lemma price_core (v : Vault) (hnav : v.WithdrawNavExact false) (sd priced : STAmount)
    (hsd : NumExact sd) (hsd0 : 0 ≤ sd.toRat)
    (h : v.sharesToAssetsWithdraw sd false = .ok priced) :
    (priced.mValue = 0 ∧ v.idealAssetsClawback sd.toRat ≤ 1 / 4) ∨
    ∃ an : Number, an.isNormalized ∧ an.mantissa_ ≠ 0 ∧ an.negative_ = false ∧
      0 < v.idealAssetsClawback sd.toRat ∧
      |an.toRat - v.idealAssetsClawback sd.toRat| ≤ v.idealAssetsClawback sd.toRat * depositε ∧
      STAmount.ofNumber v.numericType an .to_nearest = .ok priced := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  · obtain ⟨nav, hsub, hz⟩ : ∃ nav, v.assetsTotal.operator_sub v.lossUnrealized .to_nearest = .ok nav ∧
        (nav.mantissa_ == 0) = true := ⟨_, ‹_›, ‹_›⟩
    obtain ⟨-, hnavv, -⟩ := nav_facts v hnav nav hsub
    refine Or.inl ⟨STAmount.zero_mValue _, ?_⟩
    unfold RawVault.idealAssetsClawback
    rw [← hnavv, Number.toRat_eq_zero_of_mantissa_zero _ (by simpa using hz)]
    norm_num
  obtain ⟨nav, sn, nv, an, hsub, hsn, hmul, hdiv, hof⟩ : ∃ nav sn nv an : Number,
      v.assetsTotal.operator_sub v.lossUnrealized .to_nearest = .ok nav ∧
      sd.toNumber .to_nearest = .ok sn ∧ nav.operator_mul sn .to_nearest = .ok nv ∧
      nv.operator_div v.sharesTotal .to_nearest = .ok an ∧
      STAmount.ofNumber v.numericType an .to_nearest = .ok priced :=
    ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  obtain ⟨hnavn, hnavv, hnav0⟩ := nav_facts v hnav nav hsub
  obtain ⟨hsnn, hsnv⟩ := hsd sn hsn
  have hSm := operator_div_divisor_ne_zero _ _ _ _ v.wf.sharesTotal_norm hdiv
  have hS1 := one_le_sharesTotal v hSm
  have hideal : nav.toRat * sn.toRat / v.sharesTotal.toRat = v.idealAssetsClawback sd.toRat := by
    unfold RawVault.idealAssetsClawback; rw [sharesTotal_eq, hsnv, hnavv]
  by_cases ham : an.mantissa_ = 0
  · refine Or.inl ⟨?_, ?_⟩
    · by_contra hne
      exact STAmount.ofNumber_source_ne_zero _ _ _ _ hof hne ham
    · rw [← hideal]
      exact pipe_underflow _ _ _ _ _ hnavn hsnn v.wf.sharesTotal_norm hnav0 (by rw [hsnv]; exact hsd0)
        hS1 hmul hdiv ham
  · have hS0 : 0 < v.sharesTotal.toRat := by linarith
    obtain ⟨hann, hI, hb⟩ := pipe _ _ _ _ _ hnavn hsnn v.wf.sharesTotal_norm hnav0
      (by rw [hsnv]; exact hsd0) hS0 hmul hdiv ham
    rw [hideal] at hI hb
    have hε : (0 : ℚ) ≤ depositε ∧ depositε ≤ 1 / 2 := by unfold depositε; norm_num
    have hapos : 0 < an.toRat := by
      have := (abs_le.mp hb).1
      have : v.idealAssetsClawback sd.toRat * depositε ≤ v.idealAssetsClawback sd.toRat * (1 / 2) :=
        mul_le_mul_of_nonneg_left hε.2 hI.le
      linarith
    exact Or.inr ⟨an, hann, ham, Number.negative_false_of_pos an hapos, hI, hb, hof⟩

end XRPL.Model.SingleAssetVault.ClwTight

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

/-- `.to_nearest` `ofNumber` onto an integral type lands within half a unit. -/
lemma ofNumber_integral_half (nt : NumericType) (n : Number) (result : STAmount)
    (hnt : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) :
    |result.toRat - n.toRat| ≤ 1 / 2 := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hnt] at hok
  cases hr : n.to_rep .to_nearest with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .to_nearest intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hres : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result .to_nearest
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hnt) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    rw [hres]
    exact Number.to_rep_to_nearest_within_half n intValue hn hneg hr

/-- The packed recovery lies within half a unit of its own last digit of the
pipeline quotient. -/
lemma ofNumber_half (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hm : n.mantissa_ ≠ 0) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result)
    (hfr : nt.isIntegral = false → result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ 1 / 2 * (10 : ℚ) ^ result.exponent ∧
      (nt.isIntegral = true → result.mOffset = 0) ∧
      (nt.isIntegral = false → result.IOUCanonical) := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨-, hoff, -⟩ := STAmount.ofNumber_integral_facts nt n _ result hint hok
    refine ⟨?_, fun _ => hoff, fun h => absurd hint (by rw [h]; decide)⟩
    rw [show result.exponent = 0 from hoff, zpow_zero, mul_one]
    exact ofNumber_integral_half nt n result hint hn hneg hok
  · have hnt := fractional_of_not_integral nt hint
    subst hnt
    have hz := hfr rfl
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hm
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hm
      · exact hlo
    obtain ⟨hcan, hexp_hi⟩ := STAmount.ofNumber_iou_ok_facts n _ result hlo hhi hexp_lo hok hz
    obtain ⟨hb, he⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional n result rfl hlo hhi
      hexp_lo hexp_hi hok hz
    refine ⟨le_trans hb ?_, fun h => absurd h (by decide), fun _ => hcan⟩
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10) he
    linarith

end XRPL.Model.SingleAssetVault.ClwTight
