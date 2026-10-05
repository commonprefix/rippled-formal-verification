import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.NormalizeFacts
import XRPL.Properties.Vault.Proofs.WithdrawMono.Grid
import XRPL.Properties.Vault.Proofs.WithdrawMono.OfNumber

/-! # The deposit clamp undercharges by less than one post-sum grid step -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

lemma p10 (a : ℤ) (k : ℕ) : (10 : ℚ) ^ (a + (k : ℤ)) = 10 ^ a * 10 ^ k := by
  rw [zpow_add₀ (by norm_num), zpow_natCast]

/-- A positive integer below `2^63` times `10^j` is a normalized `Number`. -/
lemma exists_normalized_scaled (V : ℕ) (j : ℤ) (h1 : 1 ≤ V) (h2 : V < 2 ^ 63)
    (hj_lo : -32000 ≤ j) (hj_hi : j ≤ 32000) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧ w.toRat = (V : ℚ) * 10 ^ j := by
  obtain ⟨w, hw, hwn, hwv⟩ := Number.exists_normalized_of_pos_nat V h1 h2
  have hwm : w.mantissa_ ≠ 0 := by
    intro h; rw [Number.toRat_eq_zero_of_mantissa_zero w h] at hwv
    have : (0 : ℚ) < V := by exact_mod_cast h1
    linarith
  obtain ⟨hlo, hhi, hst, hemin, hemax⟩ : largeRange.min ≤ w.mantissa_ ∧ w.mantissa_ ≤ largeRange.max ∧
      (w.mantissa_ ≤ maxRep ∨ w.mantissa_.toNat % 10 = 0) ∧
      minExponent ≤ w.exponent_ ∧ w.exponent_ ≤ maxExponent := by
    rcases hw with h0 | h
    · exact absurd (by rw [h0]; rfl) hwm
    · exact h
  have hwv' : (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ = V := by
    rw [← Number.toRat_of_nonneg w hwn]; exact hwv
  have hwe : -18 ≤ w.exponent_ ∧ w.exponent_ ≤ 0 := by
    obtain ⟨hml, hmh⟩ := hw.mantissaBounds_nat hwm
    have hml' : ((10 : ℚ) ^ 18) ≤ (w.mantissa_.toNat : ℚ) := by exact_mod_cast hml
    have hmh' : (w.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hmh
    have hV1 : (1 : ℚ) ≤ V := by exact_mod_cast h1
    have hV2 : (V : ℚ) < 2 ^ 63 := by exact_mod_cast h2
    constructor
    · by_contra hc
      push Not at hc
      have : (10 : ℚ) ^ w.exponent_ ≤ 10 ^ (-19 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h19 : (10 : ℚ) ^ 19 * 10 ^ (-19 : ℤ) = 1 := by norm_num
      have : (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ < 1 := by
        calc (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ ≤ (w.mantissa_.toNat : ℚ) * 10 ^ (-19 : ℤ) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ < 10 ^ 19 * 10 ^ (-19 : ℤ) := mul_lt_mul_of_pos_right hmh' (by positivity)
          _ = 1 := h19
      linarith
    · by_contra hc
      push Not at hc
      have : (10 : ℚ) ^ (1 : ℤ) ≤ 10 ^ w.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : (10 : ℚ) ^ 19 ≤ (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ := by
        calc (10 : ℚ) ^ 19 = 10 ^ 18 * 10 ^ (1 : ℤ) := by norm_num
          _ ≤ (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ :=
              mul_le_mul hml' this (by positivity) (by positivity)
      have : (2 : ℚ) ^ 63 < 10 ^ 19 := by norm_num
      linarith
  refine ⟨⟨false, w.mantissa_, w.exponent_ + j⟩, Or.inr ⟨hlo, hhi, hst, ?_, ?_⟩, rfl, ?_⟩
  · show minExponent ≤ w.exponent_ + j; unfold minExponent; omega
  · show w.exponent_ + j ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show (w.mantissa_.toNat : ℚ) * 10 ^ (w.exponent_ + j) = (V : ℚ) * 10 ^ j
    rw [zpow_add₀ (by norm_num), ← mul_assoc, hwv']

/-- A fractional `ofNumber` (any mode) of a nonnegative source never drops below a
16-digit grid point `mz·10^E` lying under the source. -/
lemma ofNumber_frac_ge (n : Number) (result : STAmount) (mode : rounding_mode)
    (mz : ℕ) (E : ℤ)
    (hn : n.isNormalized) (hnneg : n.negative_ = false)
    (hmz : mz < 10 ^ 16) (hle : (mz : ℚ) * 10 ^ E ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) (hrz : result.mValue ≠ 0) :
    (mz : ℚ) * 10 ^ E ≤ result.toRat := by
  have hnm : n.mantissa_ ≠ 0 :=
    STAmount.ofNumber_source_ne_zero .fractional n mode result hok hrz
  obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hnm
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnm
    · exact hlo
  have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
    STAmount.ofNumber_iou_success_exp_range n mode result hlo19 hhi19 hexp_lo hok hrz
  obtain ⟨mant, exp, hnorm, hval, -⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n mode result rfl hnneg
      hlo19 hhi19 hexp_lo hexp_hi hok hrz
  obtain ⟨k, hk, -, hkval⟩ :=
    normalizeToRange_16_bracket n mode mant exp hlo19 hhi19 (by omega) (by omega) hnorm
  rw [hnneg] at hkval
  simp only [Bool.false_eq_true, if_false, one_mul] at hkval
  have hnval : n.toRat = (n.mantissa_.toNat : ℚ) * (10:ℚ) ^ n.exponent_ :=
    Number.toRat_of_nonneg n hnneg
  set M : ℕ := n.mantissa_.toNat with hM
  have hrval : result.toRat = (k : ℚ) * (10:ℚ) ^ (n.exponent_ + 3) := by rw [hval, hkval]
  have hkge : M / 1000 ≤ k := by rcases hk with h | h <;> omega
  have hkgeq : ((M / 1000 : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast hkge
  have hpe : (0:ℚ) < (10:ℚ) ^ (n.exponent_ + 3) := zpow_pos (by norm_num) _
  rw [hrval]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hkgeq (le_of_lt hpe))
  rcases le_or_gt (n.exponent_ + 3) E with hE | hE
  · -- the grid point sits on a grid at least as coarse as the result's
    obtain ⟨t, ht⟩ : ∃ t : ℕ, E = n.exponent_ + 3 + t := ⟨(E - (n.exponent_ + 3)).toNat, by omega⟩
    have hsplit : (mz : ℚ) * 10 ^ E = ((mz * 10 ^ t : ℕ) : ℚ) * 10 ^ (n.exponent_ + 3) := by
      rw [ht, zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
    rw [hsplit] at hle ⊢
    have h3 : (10:ℚ) ^ (n.exponent_ + 3) = (10:ℚ) ^ n.exponent_ * 1000 := by
      rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
    rw [hnval, h3] at hle
    have hpn : (0:ℚ) < (10:ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have hle' : ((mz * 10 ^ t : ℕ) : ℚ) * 1000 ≤ (M : ℚ) := by
      have := hle
      rw [show ((mz * 10 ^ t : ℕ) : ℚ) * ((10:ℚ) ^ n.exponent_ * 1000)
          = ((mz * 10 ^ t : ℕ) : ℚ) * 1000 * (10:ℚ) ^ n.exponent_ by ring] at this
      exact le_of_mul_le_mul_right this hpn
    have hleN : (mz * 10 ^ t) * 1000 ≤ M := by exact_mod_cast hle'
    have : mz * 10 ^ t ≤ M / 1000 := by omega
    have hq : ((mz * 10 ^ t : ℕ) : ℚ) ≤ ((M / 1000 : ℕ) : ℚ) := by exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hq (le_of_lt hpe)
  · -- a finer grid point stays below the result's leading decade
    have hmzq : (mz : ℚ) < 10 ^ 16 := by exact_mod_cast hmz
    have hM1000 : 10 ^ 15 ≤ M / 1000 := by omega
    have hM1000q : ((10:ℚ) ^ 15) ≤ ((M / 1000 : ℕ) : ℚ) := by exact_mod_cast hM1000
    have hpE : (0:ℚ) < (10:ℚ) ^ E := zpow_pos (by norm_num) _
    have hstep : (10:ℚ) ^ (16 : ℤ) * 10 ^ E ≤ (10:ℚ) ^ (15 : ℤ) * 10 ^ (n.exponent_ + 3) := by
      rw [← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h16 : ((10:ℚ) ^ (16:ℤ)) = (10:ℚ) ^ 16 := by norm_num
    have h15 : ((10:ℚ) ^ (15:ℤ)) = (10:ℚ) ^ 15 := by norm_num
    rw [h16, h15] at hstep
    calc (mz : ℚ) * 10 ^ E ≤ 10 ^ 16 * 10 ^ E := mul_le_mul_of_nonneg_right (le_of_lt hmzq) (le_of_lt hpE)
      _ ≤ 10 ^ 15 * 10 ^ (n.exponent_ + 3) := hstep
      _ ≤ ((M / 1000 : ℕ) : ℚ) * 10 ^ (n.exponent_ + 3) :=
          mul_le_mul_of_nonneg_right hM1000q (le_of_lt hpe)

/-- A nonnegative canonical IOU amount lies in the decade band of its exponent. -/
lemma canon_band (s : STAmount) (hc : s.IOUCanonical) (hn : s.mIsNegative = false) :
    (10 : ℚ) ^ (s.exponent + 15) ≤ s.toRat ∧ s.toRat < (10 : ℚ) ^ (s.exponent + 16) := by
  rw [STAmount.toRat_of_nonneg s hn]
  have hlo : ((10 : ℚ) ^ 15) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast hc.mant_lo
  have hhi : (s.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
  have hp : (0 : ℚ) < 10 ^ s.mOffset := zpow_pos (by norm_num) _
  have e15 : (10 : ℚ) ^ (s.exponent + 15) = 10 ^ 15 * 10 ^ s.mOffset := by
    rw [zpow_add₀ (by norm_num)]; show (10:ℚ) ^ s.mOffset * 10 ^ (15:ℤ) = _; norm_num; ring
  have e16 : (10 : ℚ) ^ (s.exponent + 16) = 10 ^ 16 * 10 ^ s.mOffset := by
    rw [zpow_add₀ (by norm_num)]; show (10:ℚ) ^ s.mOffset * 10 ^ (16:ℤ) = _; norm_num; ring
  rw [e15, e16]
  exact ⟨mul_le_mul_of_nonneg_right hlo (le_of_lt hp), mul_lt_mul_of_pos_right hhi hp⟩

/-- Exponent comparison from values: a nonnegative canonical amount at least
`10^(j+15)` has exponent at least `j`. -/
lemma canon_exp_ge (s : STAmount) (hc : s.IOUCanonical) (hn : s.mIsNegative = false) (j : ℤ)
    (h : (10 : ℚ) ^ (j + 15) ≤ s.toRat) : j ≤ s.exponent := by
  by_contra hlt
  push Not at hlt
  have := (canon_band s hc hn).2
  have : (10 : ℚ) ^ (s.exponent + 16) ≤ 10 ^ (j + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

/-- The post-sum exponent `e` of a positive canonical delta `p` on a nonnegative total
`A`: `e` is at least `p`'s exponent, and `A + p` lies in `(9999999999999999490·10^(e-4),
10^(e+16))`, so `10^e` is one step of the 16-digit grid at the post-sum magnitude. -/
lemma post_exp_facts (A : Number) (p : STAmount) (e : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hp : p.IOUCanonical) (hpneg : p.mIsNegative = false)
    (he : postSumExponent A p = .ok e) :
    p.exponent ≤ e ∧ (-96 : ℤ) ≤ e ∧ e ≤ 80 ∧
    A.toRat + p.toRat < (10 : ℚ) ^ (e + 16) ∧
    (9999999999999999490 : ℚ) * 10 ^ (e - 4) < A.toRat + p.toRat := by
  obtain ⟨dn, sum, a, hdn, hsum, ha, hae⟩ := postSumExponent_reduces A p e he
  have hpfrac : p.numericType = .fractional := hp.is_fractional
  rw [hpfrac] at ha
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest hp
  rw [show dn = sn from Except.ok.inj (hdn.symm.trans hsn)] at hsum
  have hp0 : 0 < p.toRat := STAmount.toRat_pos_of p hpneg (by have := hp.mant_lo; intro h; rw [h] at this; simp at this)
  have hrsum := operator_add_rounded_to_nearest A sn sum hA hsnn hsum
  rw [hsnv] at hrsum
  -- `sum ≥ p`
  have hsum_ge : p.toRat ≤ sum.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized sum _ hrsum sn hsnn (by rw [hsnv]; linarith)
    rwa [hsnv] at this
  have hsum_norm : sum.isNormalized := by
    rcases hrsum with ⟨n, hn, hv⟩ | ⟨n, hn, hv⟩
    · exact operator_add_isNormalized_to_nearest_sz A sn sum hA hsnn hsum
    · exact operator_add_isNormalized_to_nearest_sz A sn sum hA hsnn hsum
  have hsum_neg : sum.negative_ = false :=
    Number.negative_false_of_nonneg sum hsum_norm (by linarith)
  have hsum_m : sum.mantissa_ ≠ 0 := by
    intro h; rw [Number.toRat_eq_zero_of_mantissa_zero sum h] at hsum_ge; linarith
  -- the pack is nonzero
  have ham : a.mValue ≠ 0 := by
    intro hz
    have := STAmount.ofNumber_iou_zero_below_min .fractional sum .to_nearest a (by decide)
      hsum_norm hsum_neg hsum_m ha hz
    have h1 := (canon_band p hp hpneg).1
    have h2 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (p.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by have := hp.exp_lo; show (-81 : ℤ) ≤ p.mOffset + 15; omega)
    linarith
  have hac : a.IOUCanonical := by
    rcases STAmount.ofNumber_frac_shape .fractional sum .to_nearest a (by decide) hsum_norm ha with h | h
    · exact h
    · exact absurd h ham
  have haneg : a.mIsNegative = false := by
    have hnn := (WdMono.ofNumber_facts .fractional sum a hsum_norm (by linarith) ha).1
    by_contra h
    rw [Bool.not_eq_false] at h
    have := STAmount.toRat_neg_of a h ham
    linarith
  have hpval : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent := STAmount.toRat_of_nonneg p hpneg
  have he_lo : (-96 : ℤ) ≤ e := by rw [← hae]; exact hac.exp_lo
  have he_hi : e ≤ 80 := by rw [← hae]; exact hac.exp_hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `a ≥ p`, so its exponent is at least `p`'s
    have hage : p.toRat ≤ a.toRat := by
      have := ofNumber_frac_ge sum a .to_nearest p.mValue.toNat p.exponent hsum_norm hsum_neg
        hp.mant_hi (by rw [← hpval]; exact hsum_ge) ha ham
      rwa [← hpval] at this
    rw [← hae]
    exact canon_exp_ge a hac haneg p.exponent (le_trans (canon_band p hp hpneg).1 hage)
  · exact he_lo
  · exact he_hi
  · by_contra hge
    push Not at hge
    obtain ⟨w, hw, -, hwv⟩ := exists_normalized_scaled (10 ^ 15) (e + 1) (by norm_num) (by norm_num)
      (by omega) (by omega)
    have hwv' : w.toRat = (10 : ℚ) ^ (e + 16) := by
      rw [hwv, show e + 16 = (e + 1) + ((15 : ℕ) : ℤ) by push_cast; ring, p10]; push_cast; ring
    have hsw : w.toRat ≤ sum.toRat :=
      Number.RoundsToRepresentable.ge_of_ge_normalized sum _ hrsum w hw (by rw [hwv']; exact hge)
    have hage := ofNumber_frac_ge sum a .to_nearest (10 ^ 15) (e + 1) hsum_norm hsum_neg
      (by norm_num) (by rw [← hwv]; exact hsw) ha ham
    have : e + 1 ≤ a.exponent := canon_exp_ge a hac haneg (e + 1) (by
      rw [show e + 1 + 15 = (e + 1) + 15 by ring, zpow_add₀ (by norm_num)]
      push_cast at hage; norm_num at hage ⊢; linarith)
    omega
  · by_contra hle
    push Not at hle
    obtain ⟨w, hw, -, hwv⟩ := exists_normalized_scaled 999999999999999949 (e - 3) (by norm_num)
      (by norm_num) (by omega) (by omega)
    have hwv' : w.toRat = (9999999999999999490 : ℚ) * 10 ^ (e - 4) := by
      rw [hwv, show e - 3 = 1 + (e - 4) by ring, zpow_add₀ (by norm_num)]; push_cast; ring
    have hsw : sum.toRat ≤ w.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized sum _ hrsum w hw (by rw [hwv']; exact hle)
    have hlt : sum.toRat < WdMono.carryPt (e - 4) := by
      unfold WdMono.carryPt
      have : (0 : ℚ) < 10 ^ (e - 4) := zpow_pos (by norm_num) _
      linarith
    have hiff := WdMono.exp_ge_iff sum a hsum_norm (by linarith) ha (e - 4) (by omega)
    have : ¬ (e - 4 + 4 ≤ a.exponent) := fun h => absurd (hiff.mp h) (not_le.mpr hlt)
    omega

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- **The sum clamp undercharges by at most one post-sum grid step.** For a positive
canonical delta `p` whose clamped record `c` is positive, `p - 10^e ≤ c`, where `e` is
the post-sum exponent. -/
lemma clamp_sum_ge (A : Number) (p c : STAmount) (e : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hp : p.IOUCanonical) (hpneg : p.mIsNegative = false)
    (he : postSumExponent A p = .ok e)
    (hcl : clampToSumExponent A p = .ok c) (hc : 0 < c.toRat) :
    p.toRat - 10 ^ e ≤ c.toRat := by
  obtain ⟨hpe_le, he_lo, he_hi, hsum_hi, hsum_lo⟩ := post_exp_facts A p e hA hA0 hp hpneg he
  have hg : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  by_cases hsmall : p.toRat ≤ 10 ^ e
  · linarith
  push Not at hsmall
  have hfrac : p.integral = false := by unfold STAmount.integral; rw [hp.is_fractional]; rfl
  have hbr : p.negative = false := hpneg
  have hnt : p.numericType = .fractional := hp.is_fractional
  have hcm : c.mValue ≠ 0 := by
    intro h; rw [STAmount.toRat_signed, h] at hc; simp at hc
  unfold clampToSumExponent at hcl
  simp only [hbr, pure_bind, Bool.false_eq_true, ↓reduceIte] at hcl
  rw [if_neg (by simp [hfrac])] at hcl
  obtain ⟨pe, hpe, hcl⟩ := bind_ok_peel _ _ _ hcl
  have hpee : pe = e := Except.ok.inj (hpe.symm.trans he)
  subst pe
  obtain ⟨sum3, hsum, hcl⟩ := bind_ok_peel _ _ _ hcl
  obtain ⟨d, hd, hcl⟩ := bind_ok_peel _ _ _ hcl
  rw [hnt] at hcl
  unfold sumAndRoundToExponent at hsum
  simp only [hnt] at hsum
  obtain ⟨dn, hdn, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s1, hs1, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s2, hs2, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨s3, hs3, hsum⟩ := bind_ok_peel _ _ _ hsum
  obtain ⟨hdnval, hdnnorm⟩ : dn.toRat = p.toRat ∧ dn.isNormalized := by
    obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact p .downward hp
    rw [show dn = sn from Except.ok.inj (hdn.symm.trans hsn)]; exact ⟨hval, hnorm⟩
  have hp0 : 0 < p.toRat := lt_trans hg hsmall
  -- the recovered post-sum total and the reported difference are normalized
  have hs2fcz : s2.FracCanonZero := by
    refine ⟨STAmount.ofNumber_mNumericType .fractional s1 .downward s2 hs2, ?_⟩
    by_cases hs2z : s2.mValue = 0
    · exact Or.inr hs2z
    · have hs1n := operator_add_isNormalized A dn s1 .downward hA hdnnorm hs1
        (STAmount.ofNumber_source_ne_zero _ s1 .downward s2 hs2 hs2z)
      rcases STAmount.ofNumber_frac_shape .fractional s1 .downward s2 (by decide) hs1n hs2 with h | h
      · exact Or.inl h
      · exact absurd h hs2z
  have hs3fcz := STAmount.roundToExponent_fczr s2 s3 _ .downward hs2fcz hs3
  have hsum3 : sum3.isNormalized ∧ (s3.mValue ≠ 0 → sum3.toRat = s3.toRat) ∧
      (s3.mValue = 0 → sum3 = Number.zero) := by
    rcases hs3fcz.2 with h | h
    · obtain ⟨sn, hsn, hv, hnorm⟩ := STAmount.toNumber_iou_exact s3 .downward h
      rw [show sum3 = sn from Except.ok.inj (hsum.symm.trans hsn)]
      exact ⟨hnorm, fun _ => hv, fun hz => absurd hz (by have := h.mant_lo; intro h0; rw [h0] at this; simp at this)⟩
    · have := STAmount.toNumber_zero_eq s3 .downward sum3 h hsum
      exact ⟨by rw [this]; exact Or.inl rfl, fun hz => absurd h hz, fun _ => this⟩
  obtain ⟨hs3n, hs3v, hs3z⟩ := hsum3
  have hdnorm : d.isNormalized := operator_sub_isNormalized_to_nearest_sz sum3 A d hs3n hA hd
  have hdm : d.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional d .to_nearest c hcl hcm
  have hdneg : d.negative_ = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    have := STAmount.ofNumber_signtrue_nonpos .fractional d .to_nearest c (by decide) hdnorm h hcl
    linarith
  have hd0 : 0 < d.toRat := Number.toRat_pos_of_not_negative d hdneg hdm
  have hrd := operator_sub_rounded_to_nearest sum3 A d hs3n hA hd
  have hsA : A.toRat < sum3.toRat := by
    by_contra hle
    push Not at hle
    have := Number.RoundsToRepresentable.nonpos_of_nonpos d _ hrd (by linarith)
    linarith
  have hs3m : s3.mValue ≠ 0 := by
    intro hz; rw [hs3z hz, Number.toRat_zero] at hsA; linarith
  have hs2m : s2.mValue ≠ 0 := by
    intro hz
    have hid : s3 = s2 := by
      unfold STAmount.roundToExponent at hs3
      rw [if_neg (by show ¬ s2.mNumericType.isIntegral = true; rw [hs2fcz.1]; decide),
          if_pos (show s2.isZero = true by unfold STAmount.isZero; simp [hz])] at hs3
      exact (Except.ok.inj hs3).symm
    exact hs3m (by rw [hid]; exact hz)
  have hs1m : s1.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero _ s1 .downward s2 hs2 hs2m
  have hs1n : s1.isNormalized := operator_add_isNormalized A dn s1 .downward hA hdnnorm hs1 hs1m
  have hs2c : s2.IOUCanonical := by
    rcases hs2fcz.2 with h | h
    · exact h
    · exact absurd h hs2m
  have hs1neg : s1.negative_ = false := by
    obtain ⟨-, h⟩ := Number.operator_add_downward_nonneg_le A dn s1 hA hdnnorm hA0
      (by rw [hdnval]; linarith) hs1
    exact Number.negative_false_of_nonneg s1 hs1n h
  -- the grid point `K·10^e` just below the exact post-sum total
  set t : ℚ := A.toRat + p.toRat with ht
  set K : ℤ := ⌊t / 10 ^ e⌋ with hK
  have hKle : (K : ℚ) * 10 ^ e ≤ t := by
    have := Int.floor_le (t / 10 ^ e)
    calc (K : ℚ) * 10 ^ e ≤ t / 10 ^ e * 10 ^ e := mul_le_mul_of_nonneg_right this (le_of_lt hg)
      _ = t := by field_simp
  have hKgt : t - 10 ^ e < (K : ℚ) * 10 ^ e := by
    have := Int.lt_floor_add_one (t / 10 ^ e)
    have h2 : t / 10 ^ e * 10 ^ e < ((K : ℚ) + 1) * 10 ^ e := mul_lt_mul_of_pos_right this hg
    rw [div_mul_cancel₀ _ (ne_of_gt hg)] at h2
    linarith
  have hK1 : 1 ≤ K := by
    by_contra hlt
    push Not at hlt
    have : (K : ℚ) ≤ 0 := by exact_mod_cast (show K ≤ 0 by omega)
    have h4 : (10 : ℚ) ^ e ≤ 9999999999999999490 * 10 ^ (e - 4) := by
      rw [show e = (e - 4) + ((4 : ℕ) : ℤ) by push_cast; ring, p10]
      have : (0 : ℚ) < 10 ^ (e - 4) := zpow_pos (by norm_num) _
      norm_num; nlinarith
    nlinarith
  have hK16 : K < 10 ^ 16 := by
    have : (K : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := by
      calc (K : ℚ) * 10 ^ e ≤ t := hKle
        _ < 10 ^ (e + 16) := hsum_hi
        _ = 10 ^ 16 * 10 ^ e := by
          rw [show e + 16 = e + ((16 : ℕ) : ℤ) by push_cast; ring, p10]; ring
    have := lt_of_mul_lt_mul_right this (le_of_lt hg)
    exact_mod_cast this
  have hKnat : ((K.toNat : ℕ) : ℚ) = (K : ℚ) := by
    have : ((K.toNat : ℕ) : ℤ) = K := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  obtain ⟨w, hw, -, hwv⟩ := exists_normalized_scaled K.toNat e (by omega) (by omega) (by omega) (by omega)
  rw [hKnat] at hwv
  -- every downward stage keeps the grid point
  have hs1ge : (K : ℚ) * 10 ^ e ≤ s1.toRat := by
    obtain ⟨n, hn, hv⟩ := operator_add_rounded_downward A dn s1 hA hdnnorm hs1 hs1m
    rw [hv, ← hwv]
    exact Number.lower_tight _ n hn w hw (by rw [hwv, hdnval]; exact hKle)
  have hs2ge : (K : ℚ) * 10 ^ e ≤ s2.toRat := by
    have := ofNumber_frac_ge s1 s2 .downward K.toNat e hs1n hs1neg (by omega)
      (by rw [hKnat]; exact hs1ge) hs2 hs2m
    rwa [hKnat] at this
  have hs2pos : 0 < s2.toRat := lt_of_lt_of_le (by positivity) hs2ge
  have hs3ge : (K : ℚ) * 10 ^ e ≤ s3.toRat :=
    (WdMono.rte_facts s2 s3 e hs2c hs2pos he_hi hs3).2.2.2 hs3m K hs2ge
  rw [← hs3v hs3m] at hs3ge
  -- the reported difference keeps `p - 10^e`
  have hpval : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent := STAmount.toRat_of_nonneg p hpneg
  obtain ⟨u, hu⟩ : ∃ u : ℕ, e = p.exponent + u := ⟨(e - p.exponent).toNat, by omega⟩
  have hgu : (10 : ℚ) ^ e = ((10 ^ u : ℕ) : ℚ) * 10 ^ p.exponent := by
    rw [hu, p10]; push_cast; ring
  have hVpos : 10 ^ u < p.mValue.toNat := by
    have : ((10 ^ u : ℕ) : ℚ) * 10 ^ p.exponent < (p.mValue.toNat : ℚ) * 10 ^ p.exponent := by
      rw [← hgu, ← hpval]; exact hsmall
    have := lt_of_mul_lt_mul_right this (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 10) p.exponent))
    exact_mod_cast this
  set V : ℕ := p.mValue.toNat - 10 ^ u with hV
  have hVq : (V : ℚ) * 10 ^ p.exponent = p.toRat - 10 ^ e := by
    rw [hgu, hpval, hV, Nat.cast_sub (le_of_lt hVpos)]; ring
  have hV16 : V < 10 ^ 16 := lt_of_le_of_lt (Nat.sub_le _ _) hp.mant_hi
  have hV1 : 1 ≤ V := Nat.le_sub_of_add_le (by omega)
  obtain ⟨z, hz, -, hzv⟩ := exists_normalized_scaled V p.exponent hV1 (lt_trans hV16 (by norm_num))
    (by have := hp.exp_lo; show (-32000 : ℤ) ≤ p.mOffset; omega)
    (by have := hp.exp_hi; show p.mOffset ≤ 32000; omega)
  rw [hVq] at hzv
  have hdge : p.toRat - 10 ^ e ≤ d.toRat := by
    rw [← hzv]
    exact Number.RoundsToRepresentable.ge_of_ge_normalized d _ hrd z hz (by rw [hzv]; linarith)
  have := ofNumber_frac_ge d c .to_nearest V p.exponent hdnorm hdneg hV16
    (by rw [hVq]; exact hdge) hcl hcm
  rwa [hVq] at this

end XRPL.Model.SingleAssetVault.DepTight
