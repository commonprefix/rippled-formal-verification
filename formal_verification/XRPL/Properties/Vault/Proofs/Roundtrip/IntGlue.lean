import XRPL.Properties.Vault.Proofs.Roundtrip.AddCusp
import XRPL.Properties.Vault.Proofs.Roundtrip.IntArith
import XRPL.Properties.Vault.Proofs.Dilution.Charge
import XRPL.Properties.Vault.Proofs.Dilution.Deposit
import XRPL.Properties.Vault.Proofs.WithdrawTight

/-! # Integral charge and payout as rounded quotients

On an integral asset the charge and the payout are the integer packs of a `mul`/`div`
pipeline: an integer within the certificate of `int_div_cert` of the pipeline's quotient,
which is within the product's relative error of the ideal amount. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma charge_pq (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ shN P Q : Number, shN.toRat = shares.toRat ∧ shN.isNormalized ∧
      v.assetsTotal.operator_mul shN .to_nearest = .ok P ∧
      P.operator_div v.sharesTotal .to_nearest = .ok Q ∧
      STAmount.ofNumber v.numericType Q .to_nearest = .ok c := by
  unfold sharesToAssetsDeposit at hsad
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  subst hshNeq
  exact ⟨sn, P, Q, hsnval, hsnnorm, hP, hQ, hc⟩

/-- The integer pack of a positive quotient, with its certificate; an underflowing
quotient is replaced by the exact value, which is then negligible. -/
lemma pack_cert (nt : NumericType) (hint : nt.isIntegral = true) (x y Q : Number) (c : STAmount)
    (hx : x.isNormalized) (hy : y.isNormalized) (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hv : 0 < x.toRat / y.toRat) (hdiv : x.operator_div y .to_nearest = .ok Q)
    (hof : STAmount.ofNumber nt Q .to_nearest = .ok c) :
    ∃ z : ℤ, c.toRat = z ∧ 0 ≤ z ∧ (z : ℚ) ≤ 9223372036854775807 ∧ c.exponent = 0 ∧
      (x.toRat / y.toRat < 9223372036854775807 → |(z : ℚ) - x.toRat / y.toRat| ≤ 69 / 125) ∧
      (925 * 10 ^ 15 ≤ x.toRat / y.toRat → x.toRat / y.toRat < 9223372036854775807 →
        |(z : ℚ) - x.toRat / y.toRat| ≤ 1 / 2) ∧
      (9223372036854775807 ≤ x.toRat / y.toRat → (z : ℚ) = 9223372036854775807) ∧
      (93 * 10 ^ 15 ≤ x.toRat / y.toRat → x.toRat / y.toRat < 922 * 10 ^ 15 →
        |(z : ℚ) - x.toRat / y.toRat| ≤ 11 / 20) := by
  obtain ⟨-, hoff, hmx⟩ := STAmount.ofNumber_integral_facts nt Q .to_nearest c hint hof
  have hexp : c.exponent = 0 := hoff
  by_cases hQm : Q.mantissa_ = 0
  · have hc0 : c.mValue = 0 := by
      by_contra h; exact STAmount.ofNumber_integral_source_ne_zero nt Q .to_nearest c hint hof h hQm
    have hcz : c.toRat = 0 := (STAmount.toRat_eq_zero_iff c).mpr hc0
    have hsm := operator_div_underflow_truth_small x y Q .to_nearest hx hy hxm hym hdiv hQm
    rw [abs_of_pos hv] at hsm
    have htiny : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 1 / 10 := by
      have : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-19 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by norm_num [minExponent])
      have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (-19 : ℤ) = 1 / 10 := by norm_num
      rw [← h2]; exact mul_le_mul_of_nonneg_left this (by positivity)
    refine ⟨0, by rw [hcz]; simp, le_rfl, by norm_num, hexp, fun _ => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_⟩
    · push_cast; rw [abs_le]; constructor <;> linarith
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
  have hQn := operator_div_result_isNormalized x y Q .to_nearest hx hy hxm hym hdiv hQm
  have hQ0 : 0 ≤ Q.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg Q _
    (operator_div_rounded_to_nearest x y Q hx hy hdiv) hv.le
  obtain ⟨z, hz, hz0, hzQ, -, -, -⟩ := WdMono.int_pack nt hint Q c hQn hQ0 hof
  have hzM : (z : ℚ) ≤ 9223372036854775807 := by
    by_cases hcn : c.mIsNegative = true
    · have h1 := STAmount.toRat_of_neg c hcn
      have h2 : (0 : ℚ) ≤ (c.mValue.toNat : ℚ) * 10 ^ c.mOffset := by positivity
      have : c.toRat ≤ 0 := by rw [h1]; linarith
      rw [hz] at this; linarith
    · have hcn' : c.mIsNegative = false := by simpa using hcn
      rw [← hz, STAmount.toRat_of_nonneg c hcn', hoff, zpow_zero, mul_one]
      have : (c.mValue.toNat : ℚ) ≤ (maxRep.toNat : ℚ) := by exact_mod_cast hmx
      rw [show (maxRep.toNat : ℚ) = 9223372036854775807 by
        rw [show maxRep.toNat = 9223372036854775807 by decide]; norm_num] at this
      exact this
  have hcert := int_div_cert x y Q hx hy hdiv hv z hzQ hzM
  exact ⟨z, hz, hz0, hzM, hexp, hcert.1, hcert.2.1, hcert.2.2,
    int_div_mid x y Q hx hy hdiv hv z hzQ⟩

lemma tiny_le (x : ℚ) (h : x < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)) : x < 1 / 10 := by
  have : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-19 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num [minExponent])
  have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (-19 : ℤ) = 1 / 10 := by norm_num
  have h3 := mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ 10 ^ (18 : ℕ) by positivity)
  rw [h2] at h3
  linarith

/-- The certificate of an integral charge on a non-empty vault. -/
lemma charge_int_cert (v : Vault) (shares p : STAmount) (hint : v.numericType.isIntegral = true)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat) (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok p) :
    ∃ (Y : ℚ) (z : ℤ), p.toRat = z ∧ 0 ≤ z ∧ (z : ℚ) ≤ 9223372036854775807 ∧ p.exponent = 0 ∧
      |Y - v.idealChargeDeposit shares.toRat| ≤
        v.idealChargeDeposit shares.toRat * (5 / (2 ^ 63 + 7)) ∧
      (Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 69 / 125) ∧
      (925 * 10 ^ 15 ≤ Y → Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 1 / 2) ∧
      (9223372036854775807 ≤ Y → (z : ℚ) = 9223372036854775807) ∧
      (93 * 10 ^ 15 ≤ Y → Y < 922 * 10 ^ 15 → |(z : ℚ) - Y| ≤ 11 / 20) := by
  obtain ⟨shN, P, Q, hshNv, hshNn, hP, hQ, hof⟩ := charge_pq v shares p hshc hshnt hmz hsad
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hST : 0 < v.sharesTotal.toRat := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    exact DilG.shares_pos_of_total v hApos
  have hST1 : 1 ≤ v.sharesTotal.toRat := by
    have hnum : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hST
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hST)
  have hshNm : shN.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshNv]; exact ne_of_gt hshpos)
  set T := v.assetsTotal.toRat with hTdef
  set S := v.sharesTotal.toRat with hSdef
  set s := shares.toRat with hsdef
  have hideal : v.idealChargeDeposit s = T * s / S := by
    unfold RawVault.idealChargeDeposit
    rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; rfl
  have hTs : 0 < T * s := mul_pos hApos hshpos
  have hI0 : 0 ≤ T * s / S := by positivity
  rw [hideal]
  by_cases hPm : P.mantissa_ = 0
  · have hQm : Q.mantissa_ = 0 := by
      by_contra h
      exact operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ h hPm
    have hp0 : p.mValue = 0 := by
      by_contra h; exact STAmount.ofNumber_integral_source_ne_zero _ Q .to_nearest p hint hof h hQm
    obtain ⟨-, hoff, -⟩ := STAmount.ofNumber_integral_facts _ Q .to_nearest p hint hof
    have hsm := operator_mul_underflow_truth_small v.assetsTotal shN P .to_nearest
      v.wf.assetsTotal_norm hshNn hmz hshNm hP hPm
    rw [hshNv, abs_of_pos hTs] at hsm
    have hI : T * s / S < 1 / 10 := by
      have := tiny_le _ hsm
      have : T * s / S ≤ T * s := div_le_self hTs.le hST1
      linarith
    refine ⟨T * s / S, 0, (STAmount.toRat_eq_zero_iff p).mpr hp0, le_rfl, by norm_num, hoff,
      by rw [sub_self, abs_zero]; positivity, fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · push_cast; rw [zero_sub, abs_neg, abs_of_nonneg hI0]; linarith
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
  have hPn := operator_mul_result_isNormalized v.assetsTotal shN P .to_nearest v.wf.assetsTotal_norm
    hshNn hmz hshNm hP hPm
  have hmulb : |P.toRat - T * s| ≤ T * s * (5 / (2 ^ 63 + 7)) := by
    have h : |P.toRat - v.assetsTotal.toRat * shN.toRat| ≤
        |v.assetsTotal.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest v.assetsTotal shN P v.wf.assetsTotal_norm hshNn hP hPm
    rwa [hshNv, abs_of_pos hTs] at h
  have hPpos : 0 < P.toRat := by
    have := abs_le.mp hmulb
    have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
    nlinarith
  have hv : 0 < P.toRat / S := div_pos hPpos hST
  obtain ⟨z, hz, hz0, hzM, hexp, h1, h2, h3, h4⟩ :=
    pack_cert _ hint P v.sharesTotal Q p hPn v.wf.sharesTotal_norm hPm hSTm hv hQ hof
  refine ⟨P.toRat / S, z, hz, hz0, hzM, hexp, ?_, h1, h2, h3, h4⟩
  have heq : P.toRat / S - T * s / S = (P.toRat - T * s) / S := by ring
  rw [heq, abs_div, abs_of_pos hST, div_le_iff₀ hST]
  calc |P.toRat - T * s| ≤ T * s * (5 / (2 ^ 63 + 7)) := hmulb
    _ = T * s / S * (5 / (2 ^ 63 + 7)) * S := by field_simp

/-- The certificate of an integral payout's priced amount. -/
lemma payout_int_cert (v : Vault) (sh p : STAmount) (hint : v.numericType.isIntegral = true)
    (hsc : sh.Canonical) (hsp : 0 < sh.toRat) (hnav : v.WithdrawNavExact false)
    (hSTpos : 0 < v.sharesTotal.toRat)
    (hp : v.sharesToAssetsWithdraw sh false = .ok p) :
    ∃ (X : ℚ) (z : ℤ), p.toRat = z ∧ 0 ≤ z ∧ (z : ℚ) ≤ 9223372036854775807 ∧
      |X - v.idealAssetsWithdraw false sh.toRat| ≤
        v.idealAssetsWithdraw false sh.toRat * (5 / (2 ^ 63 + 7)) ∧
      (X < 9223372036854775807 → |(z : ℚ) - X| ≤ 69 / 125) ∧
      (925 * 10 ^ 15 ≤ X → X < 9223372036854775807 → |(z : ℚ) - X| ≤ 1 / 2) ∧
      (9223372036854775807 ≤ X → (z : ℚ) = 9223372036854775807) ∧
      (93 * 10 ^ 15 ≤ X → X < 922 * 10 ^ 15 → |(z : ℚ) - X| ≤ 11 / 20) := by
  obtain ⟨nav, hnavq, hnavn, hcase⟩ := WdAcc.price_cases v sh p false hnav hp
  have hnav0 : 0 ≤ nav.toRat := by rw [hnavq]; exact WdTight.nav_nonneg v false
  have hideal : v.idealAssetsWithdraw false sh.toRat =
      nav.toRat * sh.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdraw
    rw [hnavq, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rw [hideal]
  rcases hcase with ⟨hnm, rfl⟩ | ⟨hnm, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · have hn0 : nav.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero nav hnm
    rw [hn0, zero_mul, zero_div]
    refine ⟨0, 0, STAmount.toRat_eq_zero_of_mValue_zero _ (STAmount.zero_mValue _), le_rfl,
      by norm_num, by norm_num, fun _ => by norm_num, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hsc)
  obtain rfl : sn = sn0 := Except.ok.inj (hsn.symm.trans hsn0)
  have hsnm : sn.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnv]; exact hsp.ne')
  have hST1 : 1 ≤ v.sharesTotal.toRat := by
    have hnum : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hSTpos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hSTpos)
  have hnpos : 0 < nav.toRat :=
    lt_of_le_of_ne hnav0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero nav hnm))
  rw [show sh.toRat = sn.toRat from hsnv.symm]
  have hT0 : 0 < nav.toRat * sn.toRat := mul_pos hnpos (by rw [hsnv]; exact hsp)
  have hJ0 : 0 ≤ nav.toRat * sn.toRat / v.sharesTotal.toRat := by positivity
  by_cases hNSm : NS.mantissa_ = 0
  · have hanm : an.mantissa_ = 0 := by
      by_contra h
      exact operator_div_numerator_ne_zero_sz NS v.sharesTotal an .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv h hNSm
    have hp0 : p.mValue = 0 := by
      by_contra h; exact STAmount.ofNumber_integral_source_ne_zero _ an .to_nearest p hint hof h hanm
    have hsm := operator_mul_underflow_truth_small nav sn NS .to_nearest hnavn hsnn hnm hsnm hmul hNSm
    rw [abs_of_pos hT0] at hsm
    have hI : nav.toRat * sn.toRat / v.sharesTotal.toRat < 1 / 10 := by
      have := tiny_le _ hsm
      have : nav.toRat * sn.toRat / v.sharesTotal.toRat ≤ nav.toRat * sn.toRat :=
        div_le_self hT0.le hST1
      linarith
    refine ⟨nav.toRat * sn.toRat / v.sharesTotal.toRat, 0,
      (STAmount.toRat_eq_zero_iff p).mpr hp0, le_rfl, by norm_num,
      by rw [sub_self, abs_zero]; positivity, fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · push_cast; rw [zero_sub, abs_neg, abs_of_nonneg hJ0]; linarith
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
  have hNSn := WdMono.mul_norm nav sn NS hnavn hsnn hmul
  have hmulb : |NS.toRat - nav.toRat * sn.toRat| ≤ nav.toRat * sn.toRat * (5 / (2 ^ 63 + 7)) := by
    have h : |NS.toRat - nav.toRat * sn.toRat| ≤ |nav.toRat * sn.toRat| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest nav sn NS hnavn hsnn hmul hNSm
    rwa [abs_of_pos hT0] at h
  have hNSpos : 0 < NS.toRat := by
    have := abs_le.mp hmulb
    have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
    nlinarith
  have hv : 0 < NS.toRat / v.sharesTotal.toRat := div_pos hNSpos hSTpos
  obtain ⟨z, hz, hz0, hzM, -, h1, h2, h3, h4⟩ :=
    pack_cert _ hint NS v.sharesTotal an p hNSn v.wf.sharesTotal_norm hNSm hSTm hv hdiv hof
  refine ⟨NS.toRat / v.sharesTotal.toRat, z, hz, hz0, hzM, ?_, h1, h2, h3, h4⟩
  have heq : NS.toRat / v.sharesTotal.toRat - nav.toRat * sn.toRat / v.sharesTotal.toRat =
      (NS.toRat - nav.toRat * sn.toRat) / v.sharesTotal.toRat := by ring
  rw [heq, abs_div, abs_of_pos hSTpos, div_le_iff₀ hSTpos]
  calc |NS.toRat - nav.toRat * sn.toRat| ≤ nav.toRat * sn.toRat * (5 / (2 ^ 63 + 7)) := hmulb
    _ = nav.toRat * sn.toRat / v.sharesTotal.toRat * (5 / (2 ^ 63 + 7)) * v.sharesTotal.toRat := by
        field_simp

lemma deposit_total_add (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    ∃ cN, cN.toRat = r.amountDeposit'.toRat ∧ cN.isNormalized ∧
      v.assetsTotal.operator_add cN .to_nearest = .ok r.vault'.assetsTotal := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, -, -, -, hcomp,
    hcN, -, hat, -, -, -, hamt, -, hrv⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
  have hamCanon : am.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit am v.assetsTotal hcanon hround
      with hc | hz
    · exact hc
    · rw [hz] at hamz; exact absurd hamz (by decide)
  have ham_nn : 0 ≤ am.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit am v.assetsTotal hcanon (le_of_lt hpos) hround
  have ham_ne : am.mValue ≠ 0 := by
    unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
  have ham_pos : 0 < am.toRat :=
    lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
  obtain ⟨pr, hcp, hclamp, -⟩ := hcomp rfl
  obtain ⟨shares, hats, hshz, hsad, _, -⟩ := computeDeposit_success_reduces v am pr sC hcp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hshpos : 0 < shares.toRat := assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
  obtain ⟨hval, hnorm⟩ :=
    Vault.deposit_charge_toNumber_facts v shares pr aD cN hshc hshnt hshpos hsad hclamp hcN
  have hTeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  refine ⟨cN, by rw [hamt]; exact hval, hnorm, ?_⟩
  rw [hTeq]; exact hat

/-- A non-negative `Number` with an integral pack is at most `maxRep`. -/
lemma int_cap (nt : NumericType) (hint : nt.isIntegral = true) (n : Number) (a : STAmount)
    (hn : n.isNormalized) (hn0 : 0 ≤ n.toRat) (hok : STAmount.ofNumber nt n .to_nearest = .ok a) :
    n.toRat ≤ 9223372036854775807 := by
  obtain ⟨z, hz, -, hzn, hoff, hmx, -⟩ := WdMono.int_pack nt hint n a hn hn0 hok
  have hzM : (z : ℚ) ≤ 9223372036854775807 := by
    by_cases hcn : a.mIsNegative = true
    · have h1 := STAmount.toRat_of_neg a hcn
      have h2 : (0 : ℚ) ≤ (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := by positivity
      have : a.toRat ≤ 0 := by rw [h1]; linarith
      rw [hz] at this; linarith
    · have hcn' : a.mIsNegative = false := by simpa using hcn
      rw [← hz, STAmount.toRat_of_nonneg a hcn', hoff, zpow_zero, mul_one]
      have : (a.mValue.toNat : ℚ) ≤ (maxRep.toNat : ℚ) := by exact_mod_cast hmx
      rw [show (maxRep.toNat : ℚ) = 9223372036854775807 by
        rw [show maxRep.toNat = 9223372036854775807 by decide]; norm_num] at this
      exact this
  have hzn' := abs_le.mp hzn
  by_contra h; push_neg at h
  obtain ⟨w, hw⟩ := num_int_of_ge n hn (by linarith)
  have := int_eq_of_close z w (by rw [← hw]; exact hzn)
  subst this
  linarith

end XRPL.Model.SingleAssetVault.RtT
