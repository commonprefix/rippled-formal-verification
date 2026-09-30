import XRPL.Properties.Vault.Proofs.DepositTight

/-! # Sharp deposit charge bounds

The charge's `mul`/`div` stage error is below `2·10⁻¹⁸`. The lower bound keeps the
clamp's grid exponent and splits on whether the priced charge shares it. -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

lemma charge_underflow_mul (nav s ST t : ℚ)
    (hs : 0 < s) (hnav : 0 < nav) (hST : 1 ≤ ST)
    (hmul : nav * s < t) :
    nav * s / ST < t := by
  have hSTpos : 0 < ST := by linarith
  have h1 : nav * s / ST ≤ nav * s := by
    rw [div_le_iff₀ hSTpos]; nlinarith [mul_pos hnav hs]
  linarith

lemma charge_underflow_div (nav s ST P t : ℚ)
    (hs : 0 < s) (hnav : 0 < nav) (hSTpos : 0 < ST)
    (hmul : |P - nav * s| ≤ |nav * s| * (5 / (2 ^ 63 + 7)))
    (hdiv : |P / ST| < t) :
    nav * s / ST < 2 * t := by
  have hnavs : 0 < nav * s := mul_pos hnav hs
  rw [abs_of_pos hnavs] at hmul
  have hmb := abs_le.mp hmul
  have hPpos : 0 < P := by nlinarith [hmb.1, hnavs]
  have hPST : P / ST < t := by rw [abs_of_pos (div_pos hPpos hSTpos)] at hdiv; exact hdiv
  have hNAV : nav * s ≤ P * 2 := by nlinarith [hmb.2, hnavs]
  have hle2 : nav * s / ST ≤ 2 * (P / ST) := by
    rw [div_le_iff₀ hSTpos, show 2 * (P / ST) * ST = 2 * P from by
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hSTpos)]]
    linarith
  linarith

lemma charge_nonempty_sharp (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      STAmount.ofNumber v.numericType Q .to_nearest = .ok c ∧
      0 < v.idealChargeDeposit shares.toRat ∧
      ((Q.mantissa_ ≠ 0 ∧ Q.isNormalized ∧ Q.negative_ = false ∧
        |Q.toRat - v.idealChargeDeposit shares.toRat|
          ≤ v.idealChargeDeposit shares.toRat * (2 / 10 ^ 18)) ∨
      (Q.mantissa_ = 0 ∧ v.idealChargeDeposit shares.toRat ≤ (10 : ℚ) ^ (-32700 : ℤ))) := by
  set nav : ℚ := v.depositNav with hnav_def
  set s : ℚ := shares.toRat with hs_def
  set ST : ℚ := v.sharesTotal.toRat with hST_def
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hnav_pos : 0 < nav := by
    rw [hnav_def]; unfold RawVault.depositNav; exact hApos
  have hST_pos : 0 < ST := by
    have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
      absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
    have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [hST_def, ← hcast]; exact this
  have hST_one : 1 ≤ ST := by
    have hnum_pos : 0 < ST.num := Rat.num_pos.mpr hST_pos
    have hcast : ST = (ST.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den ST]
      rw [hST_def, v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
  have hideal : v.idealChargeDeposit s = nav * s / ST := by
    unfold RawVault.idealChargeDeposit
    rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
  unfold sharesToAssetsDeposit at hsad
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  have hnavnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hnavv : v.assetsTotal.toRat = nav := rfl
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  rw [hshNeq] at hsnval hsnnorm
  have hshN_val : shN.toRat = s := by rw [hsnval]
  have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
  have hshNm : shN.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
  refine ⟨Q, hc, by rw [hideal]; exact hidpos, ?_⟩
  by_cases hQm : Q.mantissa_ ≠ 0
  · left
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.assetsTotal shN P .to_nearest hnavnorm hsnnorm hmz hshNm hP hPm
    have hQnorm : Q.isNormalized :=
      operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm v.wf.sharesTotal_norm
        hPm hSTm hQ hQm
    have hmulb : |P.toRat - nav * s| ≤ nav * s * (5 / (2 ^ 63 + 7)) := by
      have h : |P.toRat - v.assetsTotal.toRat * shN.toRat|
          ≤ |v.assetsTotal.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
        operator_mul_rounds_to_nearest v.assetsTotal shN P hnavnorm hsnnorm hP hPm
      rwa [hnavv, hshN_val, abs_of_nonneg (by positivity : (0 : ℚ) ≤ nav * s)] at h
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hmulb
      have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith [mul_pos hnav_pos hshpos]
    have hPN_pos : 0 < P.toRat / ST := div_pos hPpos hST_pos
    have hdivb : |Q.toRat - P.toRat / ST| ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) := by
      have h : |Q.toRat - P.toRat / ST| ≤ |P.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
        operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm v.wf.sharesTotal_norm hQ hQm
      rwa [abs_of_pos hPN_pos] at h
    have hQpos : 0 < Q.toRat := by
      have := abs_le.mp hdivb; nlinarith
    have h3 : |Q.toRat * ST - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
      have hrw : Q.toRat * ST - P.toRat = (Q.toRat - P.toRat / ST) * ST := by field_simp
      calc |Q.toRat * ST - P.toRat|
          = |Q.toRat - P.toRat / ST| * ST := by rw [hrw, abs_mul, abs_of_pos hST_pos]
        _ ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
              nlinarith [hST_pos, abs_nonneg (Q.toRat - P.toRat / ST), hdivb]
        _ = P.toRat * (6 / (2 ^ 63 - 3)) := by
              rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
    have hcomp := div_pipeline_rel_bound ST ST (nav * s) P.toRat Q.toRat 0
      (5 / (2 ^ 63 + 7)) (6 / (2 ^ 63 - 3)) (2 / 10 ^ 18)
      (mul_pos hnav_pos hshpos) (le_of_lt hQpos)
      (by rw [sub_self, abs_zero, mul_zero])
      hmulb h3 (le_refl 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
    refine ⟨hQm, hQnorm, hQneg, ?_⟩
    rw [hideal]
    have heq : Q.toRat - nav * s / ST = (Q.toRat * ST - nav * s) / ST := by field_simp
    rw [heq, abs_div, abs_of_pos hST_pos, div_le_iff₀ hST_pos]
    calc |Q.toRat * ST - nav * s| ≤ nav * s * (2 / 10 ^ 18) := hcomp
      _ = nav * s / ST * (2 / 10 ^ 18) * ST := by field_simp
  · right
    push_neg at hQm
    refine ⟨hQm, ?_⟩
    rw [hideal]
    have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
    have h_le : 2 * (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-32700 : ℤ) := by
      rw [show (10 : ℚ) ^ (-32700 : ℤ) = (10 : ℚ) ^ (50 : ℤ) * (10 : ℚ) ^ (-32750 : ℤ) from by
        rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num]
      nlinarith [hu_pos, show (2 : ℚ) ≤ (10 : ℚ) ^ (50 : ℤ) from by norm_num]
    have hbound : nav * s / ST < 2 * (10 : ℚ) ^ (-32750 : ℤ) := by
      by_cases hPm0 : P.mantissa_ = 0
      · have hsmall := operator_mul_underflow_truth_small v.assetsTotal shN P .to_nearest
          hnavnorm hsnnorm hmz hshNm hP hPm0
        rw [abs_of_pos (mul_pos (by rw [hnavv]; exact hnav_pos) hshN_pos), hunit, hnavv,
          hshN_val] at hsmall
        have := charge_underflow_mul nav s ST _ hshpos hnav_pos hST_one hsmall
        linarith
      · have hsmall := operator_div_underflow_truth_small P v.sharesTotal Q .to_nearest
          (operator_mul_result_isNormalized v.assetsTotal shN P .to_nearest hnavnorm hsnnorm hmz
            hshNm hP hPm0)
          v.wf.sharesTotal_norm hPm0 hSTm hQ hQm
        rw [hunit] at hsmall
        have hmulbound := operator_mul_rounds_to_nearest v.assetsTotal shN P hnavnorm hsnnorm hP hPm0
        rw [hnavv, hshN_val] at hmulbound
        exact charge_underflow_div nav s ST P.toRat _ hshpos hnav_pos hST_pos hmulbound hsmall
    linarith [hbound, h_le]

lemma charge_sharp (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    0 ≤ r.amountDeposit'.toRat ∧ 0 ≤ v.idealChargeDeposit r.sharesIssued.toRat ∧
    (v.numericType.isIntegral = false →
      r.amountDeposit'.IOUCanonical ∧ 0 < r.amountDeposit'.toRat) ∧
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      v.idealChargeDeposit r.sharesIssued.toRat * (2 / 10 ^ 18) +
        1 / 2 * (10 : ℚ) ^ r.amountDeposit'.exponent ∧
    ∃ ep : ℤ, (∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → ep ≤ e) ∧
      ∃ G : ℚ, 0 ≤ G ∧ G ≤ 3 / 2 * (10 : ℚ) ^ ep ∧
        (G ≤ 21 / 20 * (10 : ℚ) ^ ep ∨ (10 : ℚ) ^ (ep + 14) ≤ r.amountDeposit'.toRat) ∧
        v.idealChargeDeposit r.sharesIssued.toRat * (1 - 2 / 10 ^ 18) - G ≤
          r.amountDeposit'.toRat := by
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, hanz, _, _, _, hcd, _, _, _, _, _, _,
    hamt, hshr, _⟩ := DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
  obtain ⟨p, hcdp, hclamp, hfnp⟩ := hcd rfl
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount p sh hcdp
  have hamt_canon : amount.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit amount v.assetsTotal hcanon hround
      with h | h
    · exact h
    · rw [h] at hanz; exact absurd hanz (by decide)
  have hamt_nn : 0 ≤ amount.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
  have hamt_mv : amount.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hanz; exact hanz)
  have hamt_pos : 0 < amount.toRat :=
    lt_of_le_of_ne hamt_nn (Ne.symm (fun h => hamt_mv ((STAmount.toRat_eq_zero_iff amount).mp h)))
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amount shares hamt_canon hamt_pos hats hsz
  have hcr : r.amountDeposit' = c := hamt
  have hsr : r.sharesIssued = shares := by rw [hshr]; exact hsheq
  rw [hcr, hsr]
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hATnn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hpnn : 0 ≤ p.toRat := sharesToAssetsDeposit_nonneg v shares p hshc hshnt hshpos hsad
  have hrle : c.toRat ≤ p.toRat := DepRnd.Vault.deposit_charge_le v shares p c hshc hshnt hshpos hsad hclamp
  have hrnn : 0 ≤ c.toRat :=
    Vault.deposit_charge_nonneg v shares p c hshc hshnt hshpos hsad hclamp hfnp
  have hle_amt : amount.toRat ≤ amountDeposit.toRat :=
    rtve_le amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
  have hcmp_ty : STAmount.areComparable p amount = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; rw [STAmount.areComparable_comm]; simpa using hcond
  have hpriced_le : p.toRat ≤ amount.toRat := by
    by_cases hc0 : p.mValue = 0
    · rw [(STAmount.toRat_eq_zero_iff _).mpr hc0]; exact hamt_nn
    · have hexact : p.ExactCanonical := by
        rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares p hshc hshnt hsad with h | h0
        · exact h
        · exact absurd h0 hc0
      have hcmpF : STAmount.CmpFaithful p amount :=
        STAmount.CmpFaithful.ofExactCanonical p amount hexact
          (STAmount.Canonical.exactCanonical amount hamt_canon) hcmp_ty
          (fun h => absurd h hc0) (fun h => absurd h hamt_mv)
      exact computeDeposit_success_charge_le v amount p sh hcmpF hcdp
  have hcty : p.mNumericType = v.numericType := sharesToAssetsDeposit_mNumericType v shares p hsad
  have hamt_ty : amount.mNumericType = v.numericType := by
    have hb := hcmp_ty; unfold STAmount.areComparable at hb
    exact (beq_iff_eq.mp hb).symm.trans hcty
  have hx_ty : amountDeposit.mNumericType = v.numericType := by
    rw [← hamt_ty]
    exact (roundToVaultExponent_mNumericType amountDeposit v.assetsTotal amount hcanon hround).symm
  have hδ : (0 : ℚ) ≤ 2 / 10 ^ 18 := by norm_num
  by_cases hint : v.numericType.isIntegral = true
  · ------------------------------------------------------------------ integral vault
    have hid : c = p :=
      clampToSumExponent_integral_nonneg v.assetsTotal p c
        (by show p.mNumericType.isIntegral = true; rw [hcty]; exact hint) hpnn hclamp
    subst hid
    have hxint : amountDeposit.integral = true := by
      show amountDeposit.mNumericType.isIntegral = true; rw [hx_ty]; exact hint
    have hc_exp0 : ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → 0 ≤ e :=
      fun e he => le_of_eq (post_exp_integral v.assetsTotal amountDeposit e hxint he).symm
    by_cases hmz : v.assetsTotal.mantissa_ = 0
    · obtain ⟨hex, -⟩ := charge_empty_integral v shares c hint hshc hshnt hshpos hmz hsad
      have hI0 : 0 ≤ v.idealChargeDeposit shares.toRat := by rw [← hex]; exact hpnn
      refine ⟨hrnn, hI0, fun h => absurd hint (by rw [h]; decide), ?_, 0, hc_exp0, 0, le_rfl, by positivity, Or.inl (by positivity), ?_⟩
      · rw [hex, sub_self]; positivity
      · rw [hex]; nlinarith
    · obtain ⟨Q, hQc, hIpos, hQcases⟩ := charge_nonempty_sharp v shares c hshc hshnt hshpos hmz hsad
      set I := v.idealChargeDeposit shares.toRat with hI
      rcases hQcases with ⟨hm, hn, hneg, hb⟩ | ⟨hm, hb⟩
      · obtain ⟨z, hz, -, hzQ, hoff, -, -⟩ :=
          WdMono.int_pack v.numericType hint Q c hn (Number.toRat_nonneg_of_nonnegative Q hneg) hQc
        have hb' := abs_le.mp hb
        have hzQ' := abs_le.mp hzQ
        refine ⟨hrnn, hIpos.le, fun h => absurd hint (by rw [h]; decide), ?_, 0, hc_exp0, 1 / 2, by norm_num, by norm_num, Or.inl (by norm_num), ?_⟩
        · have : c.exponent = 0 := hoff
          rw [this, hz]; norm_num; linarith
        · rw [hz]; norm_num; linarith
      · have hc0 : c.mValue = 0 := by
          by_contra hne
          exact (STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest c hint hQc hne) hm
        have hcz : c.toRat = 0 := (STAmount.toRat_eq_zero_iff c).mpr hc0
        have htiny : (10 : ℚ) ^ (-32700 : ℤ) ≤ 1 / 2 :=
          le_trans (zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10)
            (show (-32700 : ℤ) ≤ -1 by norm_num)) (by norm_num)
        refine ⟨hrnn, hIpos.le, fun h => absurd hint (by rw [h]; decide), ?_, 0, hc_exp0, 1 / 2, by norm_num, by norm_num, Or.inl (by norm_num), ?_⟩
        · rw [hcz]
          have : (0 : ℚ) < 10 ^ c.exponent := zpow_pos (by norm_num) _
          nlinarith [mul_nonneg (le_of_lt hIpos) hδ]
        · rw [hcz]; norm_num; nlinarith [mul_nonneg (le_of_lt hIpos) hδ]
  · ------------------------------------------------------------------ fractional vault
    have hintf : v.numericType.isIntegral = false := by simpa using hint
    have hvfrac : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral _ _ _ _ => rw [h] at hintf; simp [NumericType.isIntegral] at hintf
    have hpfrac : p.integral = false := by
      show p.mNumericType.isIntegral = false; rw [hcty]; exact hintf
    have hpcz : p.IOUCanonical ∨ p.mValue = 0 := by
      by_cases h0 : p.mValue = 0
      · exact Or.inr h0
      · rcases sharesToAssetsDeposit_disj_canonical v shares p hshc hshnt hsad h0 with h | h
        · exact Or.inl h
        · exfalso; have := h.is_integral; rw [hcty] at this; rw [this] at hintf; exact absurd hintf (by decide)
    have hpty : p.mNumericType = .fractional := by rw [hcty, hvfrac]
    have hcty' : c.mNumericType = .fractional := clamp_nt v.assetsTotal p c v.wf.assetsTotal_norm hpty hpcz hclamp
    have hcfrac : c.integral = false := by unfold STAmount.integral; rw [hcty']; rfl
    obtain ⟨hcm, hcneg⟩ := STAmount.fnp_false_pos c hcfrac hfnp
    have hc_pos : 0 < c.toRat := STAmount.toRat_pos_of c hcneg hcm
    have hp_pos : 0 < p.toRat := lt_of_lt_of_le hc_pos hrle
    have hpm : p.mValue ≠ 0 := fun h => by
      rw [(STAmount.toRat_eq_zero_iff p).mpr h] at hp_pos; exact lt_irrefl _ hp_pos
    have hpc : p.IOUCanonical := hpcz.resolve_right hpm
    have hpneg : p.mIsNegative = false := STAmount.mIsNegative_false_of_pos p hp_pos
    have hcc : c.IOUCanonical := by
      rcases (clampToSumExponent_sum_shape v.assetsTotal p c v.wf.assetsTotal_norm hpcz hpfrac
        hpneg hclamp).2 with h | h
      · exact h
      · exact absurd h hcm
    obtain ⟨ep, hep⟩ := clamp_post_exists v.assetsTotal p c hpfrac hpneg hclamp
    have hcl_ge := clamp_sum_ge v.assetsTotal p c ep v.wf.assetsTotal_norm hATnn hpc hpneg hep
      hclamp hc_pos
    obtain ⟨hpe_le, -, -, -, -⟩ := post_exp_facts v.assetsTotal p ep v.wf.assetsTotal_norm hATnn hpc
      hpneg hep
    have hxfrac : amountDeposit.integral = false := by
      unfold STAmount.integral; rw [hx_ty]; exact hintf
    have hxc : amountDeposit.IOUCanonical := hcanon.2 hxfrac
    have hxneg : amountDeposit.mIsNegative = false := STAmount.mIsNegative_false_of_pos _ hpos
    have hamtfrac : amount.mNumericType = .fractional := by rw [hamt_ty, hvfrac]
    set I := v.idealChargeDeposit shares.toRat with hI
    obtain ⟨Q, hQI, hQp, hQle, hI0⟩ : ∃ Q : ℚ, |Q - I| ≤ I * (2 / 10 ^ 18) ∧
        |p.toRat - Q| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent ∧
        (c.exponent < p.exponent → c.toRat ≤ Q) ∧ 0 ≤ I := by
      by_cases hmz : v.assetsTotal.mantissa_ = 0
      · have hex : p.toRat = I :=
          empty_frac_charge_exact v amount shares p hintf hmz hamt_canon hamtfrac hats hsz hsad
        refine ⟨I, by rw [sub_self, abs_zero]; exact mul_nonneg (by rw [← hex]; exact hpnn) hδ,
          by rw [hex, sub_self, abs_zero]; positivity, fun _ => by rw [← hex]; exact hrle,
          by rw [← hex]; exact hpnn⟩
      · obtain ⟨Qn, hQc, hIpos, hQcases⟩ := charge_nonempty_sharp v shares p hshc hshnt hshpos hmz hsad
        rw [hvfrac] at hQc
        rcases hQcases with ⟨hQm, hQn, hQneg, hb⟩ | ⟨hQm, -⟩
        swap
        · exact absurd (STAmount.ofNumber_source_ne_zero _ Qn .to_nearest p hQc hpm) (by simpa using hQm)
        obtain ⟨-, -, hhalf, -, -⟩ := WdMono.frac_pack Qn p hQn hQneg hQm hQc hpm
        refine ⟨Qn.toRat, hb, hhalf, fun hce => ?_, hIpos.le⟩
        have hce_lo : (-96 : ℤ) ≤ c.exponent := hcc.exp_lo
        have hGc := top_canon (p.exponent - 1)
          (by have := hcc.exp_lo; have : c.mOffset < p.mOffset := hce; show (-96 : ℤ) ≤ p.mOffset - 1; omega)
          (by have := hpc.exp_hi; show p.mOffset - 1 ≤ 80; omega)
        have hGv : (⟨.fractional, 9999999999999999, p.exponent - 1, false⟩ : STAmount).toRat
            = 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) := by
          have h9 : (9999999999999999 : UInt64).toNat = 9999999999999999 := by decide
          rw [STAmount.toRat_of_nonneg _ rfl]
          show ((9999999999999999 : UInt64).toNat : ℚ) * 10 ^ (p.exponent - 1) = _
          rw [h9]; push_cast; ring
        have hQG : 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) < Qn.toRat := by
          by_contra hle
          push_neg at hle
          have := STAmount.ofNumber_frac_le_canonical Qn _ p hQn hQneg hGc rfl (by rw [hGv]; exact hle) hQc
          rw [hGv] at this
          have h1 := (canon_band p hpc hpneg).1
          have h2 : (10 : ℚ) ^ (p.exponent + 15) = 10 ^ (p.exponent - 1) * 10 ^ 16 := by
            rw [show p.exponent + 15 = (p.exponent - 1) + ((16 : ℕ) : ℤ) by push_cast; ring, p10]
          have h3 : (0 : ℚ) < 10 ^ (p.exponent - 1) := zpow_pos (by norm_num) _
          nlinarith
        have hcG : c.toRat ≤ 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) := by
          rw [STAmount.toRat_of_nonneg c hcneg]
          have hm : (c.mValue.toNat : ℚ) ≤ 9999999999999999 := by
            have := hcc.mant_hi; exact_mod_cast (show c.mValue.toNat ≤ 9999999999999999 by omega)
          have he : (10 : ℚ) ^ c.mOffset ≤ 10 ^ (p.exponent - 1) :=
            zpow_le_zpow_right₀ (by norm_num)
              (by have : c.mOffset < p.mOffset := hce; show c.mOffset ≤ p.mOffset - 1; omega)
          have : (0 : ℚ) ≤ 10 ^ c.mOffset := le_of_lt (zpow_pos (by norm_num) _)
          calc (c.mValue.toNat : ℚ) * 10 ^ c.mOffset ≤ 9999999999999999 * 10 ^ c.mOffset :=
                mul_le_mul_of_nonneg_right hm this
            _ ≤ 9999999999999999 * 10 ^ (p.exponent - 1) := by linarith
        linarith
    have hb := abs_le.mp hQI
    have hp' := abs_le.mp hQp
    have hpow_pe : (10 : ℚ) ^ p.exponent ≤ 10 ^ ep := zpow_le_zpow_right₀ (by norm_num) hpe_le
    have hgpos : (0 : ℚ) < 10 ^ ep := zpow_pos (by norm_num) _
    refine ⟨hrnn, hI0, fun _ => ⟨hcc, hc_pos⟩, ?_, ep, fun e he => postSumExponent_mono v.assetsTotal p amountDeposit ep e
        v.wf.assetsTotal_norm hATnn hpc hpneg hxc hxneg (by linarith) hep he,
      10 ^ ep + 1 / 2 * 10 ^ p.exponent, by positivity, by linarith, ?_, by linarith⟩
    · by_cases hce : c.exponent < p.exponent
      · have := hQle hce
        have : (0 : ℚ) ≤ 10 ^ c.exponent := le_of_lt (zpow_pos (by norm_num) _)
        linarith
      · push_neg at hce
        have : (10 : ℚ) ^ p.exponent ≤ 10 ^ c.exponent := zpow_le_zpow_right₀ (by norm_num) hce
        linarith
    · rcases lt_or_eq_of_le hpe_le with hlt | heq
      · left
        have h1 : (10 : ℚ) ^ p.exponent ≤ 10 ^ (ep - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : (10 : ℚ) ^ ep = 10 ^ (ep - 1) * 10 := by
          rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        nlinarith
      · right
        have h1 := (canon_band p hpc hpneg).1
        rw [heq] at h1
        have h2 : (10 : ℚ) ^ (ep + 15) = 10 ^ (ep + 14) * 10 := by
          rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        have h3 : (10 : ℚ) ^ (ep + 14) = 10 ^ ep * 10 ^ (14 : ℕ) := by
          rw [show ep + 14 = ep + ((14 : ℕ) : ℤ) by push_cast; ring, p10]
        nlinarith

end XRPL.Model.SingleAssetVault.DilG
