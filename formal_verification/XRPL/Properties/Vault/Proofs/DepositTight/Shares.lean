import XRPL.Properties.Protocol.Number.Normalize.RoundsWithin
import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Proofs.DepositTight.DivSharp

/-! # Accuracy of the deposit share count -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- Relative error budget of the two `Number` stages (`mul`, `div`) of the share
pricing: `(1 + 5/(2^63+7))·(1 + divSharpε) - 1 < 1.1·10⁻¹⁸`. -/

lemma sharesε_le : sharesε ≤ depositε := by unfold sharesε; rw [depositε_eq]; norm_num

lemma shares_spec (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (_hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false) :
    ∃ q : ℚ, shares.toRat = (⌊q⌋ : ℚ) ∧
      |q - v.idealSharesDeposit amount.toRat| ≤
        v.idealSharesDeposit amount.toRat * sharesε ∧
      0 < v.idealSharesDeposit amount.toRat := by
  unfold assetsToSharesDeposit at hok
  have hmv : shares.mValue ≠ 0 :=
    ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    have h00 : amount.toRat = 0 := by
      rw [STAmount.toRat_signed, h0]
      simp
    exact absurd h00 (ne_of_gt hpos)
  have hnegam : amount.mIsNegative = false := STAmount.mIsNegative_false_of_pos amount hpos
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize (amount · 10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the ideal
    have hA0 : v.toExact.assetsTotal = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
    have hideal : v.idealSharesDeposit amount.toRat
        = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℕ) := by
      unfold RawVault.idealSharesDeposit
      rw [if_pos hA0]
    have hideal_pos : 0 < v.idealSharesDeposit amount.toRat := by
      rw [hideal]; positivity
    -- the normalize input denotes the ideal
    have hin : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat = v.idealSharesDeposit amount.toRat := by
      rw [Number.toRat_of_nonneg _ rfl, hideal, STAmount.toRat_of_nonneg amount hnegam]
      show (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ)) = _
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
      ring
    -- the nonzero chain
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    -- the normalize is `RoundsWithin` the ideal
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hround := normalize_rounds_to_nearest _ n1 hn1cast hn1m
    rw [hin] at hround
    have hround' : |n1.toRat - v.idealSharesDeposit amount.toRat|
        ≤ v.idealSharesDeposit amount.toRat * sharesε := by
      have h1 : |n1.toRat - v.idealSharesDeposit amount.toRat|
          ≤ |v.idealSharesDeposit amount.toRat| * (5 / (2 ^ 63 + 7)) := hround
      rw [abs_of_pos hideal_pos] at h1
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left (by unfold sharesε; norm_num) (le_of_lt hideal_pos)
    -- n1 is positive and normalized, so truncate floors it
    have hn1pos : 0 < n1.toRat := by
      have := abs_le.mp hround'
      have hsmall : sharesε < 1 := by unfold sharesε; norm_num
      nlinarith [hideal_pos]
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest
        (show amount.mValue ≠ 0 from hamv) hn1cast hn1m
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    -- the int64 packing is exact
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    exact ⟨n1.toRat, by rw [hshval, hn2val], hround', hideal_pos⟩
  · -- nonempty vault: shares = ⌊(S·amount)/assetsTotal rounded⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, hQ, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the divisor is `assetsTotal` exactly: there is no subtraction stage
    set navN := v.assetsTotal with hnavN_eq
    have hApos : 0 < v.toExact.assetsTotal := by
      rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
      · exact h
      · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
    have hnav_pos : 0 < v.depositNav := by
      unfold RawVault.depositNav; exact hApos
    have hS_pos : 0 < v.sharesTotal.toRat := by
      rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
      · exact h
      · exfalso
        have hz : v.toExact.sharesTotal = 0 := by
          show v.sharesTotal.toRat.num.toNat = 0
          rw [← h]
          rfl
        have := (v.exact.empty_shares hz).1
        exact absurd this.symm (ne_of_lt hApos)
    have hS_one : 1 ≤ v.sharesTotal.toRat := by
      have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
      have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
        rw [v.wf.sharesTotal_int]
        simp
      rw [hcast]
      exact_mod_cast hnum_pos
    have hSm : v.sharesTotal.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    have hanm : amountN.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hanval]; exact hpos.ne')
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hQm : Q.mantissa_ ≠ 0 := Number.truncate_source_ne_zero Q T hT hTm
    -- navN = assetsTotal exactly, so the pricing value equals depositNav with no rounding
    have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
    have hnavm : navN.mantissa_ ≠ 0 := hmz
    have hnavN_eqNav : navN.toRat = v.depositNav := by rw [hnavN_eq]; rfl
    have hnavbound : |navN.toRat - v.depositNav| ≤ v.depositNav * (555 / 10 ^ 21) := by
      rw [hnavN_eqNav, sub_self, abs_zero]
      exact mul_nonneg (le_of_lt hnav_pos) (by norm_num)
    have hnavN_pos : 0 < navN.toRat := by rw [hnavN_eqNav]; exact hnav_pos
    -- the product stage
    have hPm : P.mantissa_ ≠ 0 := by
      intro h0
      have hsmall := operator_mul_underflow_truth_small v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP h0
      have hcombo : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
          = (10 : ℚ) ^ (-32750 : ℤ) := by
        rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num [minExponent]
      rw [hcombo] at hsmall
      have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.sharesTotal.toRat * amountN.toRat| := by
        rw [abs_mul]
        have h1 : (1 : ℚ) ≤ |v.sharesTotal.toRat| := by
          rw [abs_of_pos hS_pos]; exact hS_one
        have h2 : (10 : ℚ) ^ (-81 : ℤ) ≤ |amountN.toRat| := by
          rw [hanval]
          exact STAmount.Canonical.abs_toRat_ge amount hc hamv
        nlinarith [abs_nonneg amountN.toRat]
      have hmono : (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      linarith
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP hPm
    have hPbound := operator_mul_rounds_to_nearest v.sharesTotal amountN P
      v.wf.sharesTotal_norm hannorm hP hPm
    set T0 : ℚ := v.sharesTotal.toRat * amount.toRat with hT0_def
    have hT0_pos : 0 < T0 := mul_pos hS_pos hpos
    have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
      have h1 : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7)) := hPbound
      rw [hanval, ← hT0_def, abs_of_pos hT0_pos] at h1
      exact h1
    -- the division stage
    have hQbound : |Q.toRat - P.toRat / navN.toRat|
        ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := by
      have h := operator_div_rounds_to_nearest_sharp P navN Q hPnorm hnavnorm hQ hQm
      unfold divSharpε at h
      exact h
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hPb
      have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith
    have hPN_pos : 0 < P.toRat / navN.toRat := div_pos hPpos hnavN_pos
    have hQpos : 0 < Q.toRat := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := hQbound
      rw [abs_of_pos hPN_pos] at h1
      have := abs_le.mp h1
      nlinarith
    have h3 : |Q.toRat * navN.toRat - P.toRat| ≤ P.toRat * (555 / 10 ^ 21) := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ P.toRat / navN.toRat * (555 / 10 ^ 21) := by
        have h0 := hQbound
        have h0' : |Q.toRat - P.toRat / navN.toRat|
            ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := h0
        rw [abs_of_pos hPN_pos] at h0'
        exact h0'
      have h2 : |Q.toRat - P.toRat / navN.toRat| * navN.toRat
          = |Q.toRat * navN.toRat - P.toRat| := by
        have hNne : navN.toRat ≠ 0 := hnavN_pos.ne'
        rw [show Q.toRat * navN.toRat - P.toRat
          = (Q.toRat - P.toRat / navN.toRat) * navN.toRat from by field_simp]
        rw [abs_mul, abs_of_pos hnavN_pos]
      calc |Q.toRat * navN.toRat - P.toRat|
          = |Q.toRat - P.toRat / navN.toRat| * navN.toRat := h2.symm
        _ ≤ P.toRat / navN.toRat * (555 / 10 ^ 21) * navN.toRat := by nlinarith [hnavN_pos]
        _ = P.toRat * (555 / 10 ^ 21) := by field_simp
    -- compose the three stages
    have hnavb0 : |navN.toRat - v.depositNav| ≤ v.depositNav * 0 := by
      rw [hnavN_eqNav, sub_self, abs_zero, mul_zero]
    have hcomp := div_pipeline_rel_bound v.depositNav navN.toRat T0 P.toRat Q.toRat
      0 (5 / (2 ^ 63 + 7)) (555 / 10 ^ 21) sharesε hT0_pos
      (le_of_lt hQpos) hnavb0 hPb h3 (le_refl 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by unfold sharesε; norm_num) (by unfold sharesε; norm_num)
    -- the ideal is the exact quotient
    have hideal : v.idealSharesDeposit amount.toRat = T0 / v.depositNav := by
      unfold RawVault.idealSharesDeposit
      rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hT0_def]
    have hideal_pos : 0 < v.idealSharesDeposit amount.toRat := by
      rw [hideal]; positivity
    -- floor and exact packing
    have hQnorm : Q.isNormalized :=
      operator_div_result_isNormalized P navN Q .to_nearest hPnorm hnavnorm hPm hnavm hQ hQm
    obtain ⟨hTval, hTnorm⟩ :=
      Number.truncate_floor Q T hQnorm (Number.negative_false_of_pos Q hQpos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    refine ⟨Q.toRat, by rw [hshval, hTval], ?_, hideal_pos⟩
    rw [hideal]
    have heq1 : Q.toRat - T0 / v.depositNav
        = (Q.toRat * v.depositNav - T0) / v.depositNav := by
      field_simp
    rw [heq1, abs_div, abs_of_pos hnav_pos, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hcomp (le_of_lt hnav_pos)

end XRPL.Model.SingleAssetVault.DepTight
