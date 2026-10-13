import XRPL.Properties.Vault.Proofs.DepositTight.Exponent
import XRPL.Properties.Vault.Proofs.DepositTight.Price
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge

/-! # Deposit charge helpers: rounding, exponents, the empty integral charge -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- `roundToVaultExponent` never raises a nonnegative canonical amount. -/
lemma rtve_le (amountDeposit result : STAmount) (assetsTotal : Number)
    (hc : amountDeposit.Canonical) (hnn : 0 ≤ amountDeposit.toRat)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok result) :
    result.toRat ≤ amountDeposit.toRat := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    rw [← Except.ok.inj hok]
  · have hfr : amountDeposit.integral = false := by simpa using hint
    have hiou : amountDeposit.IOUCanonical := hc.2 hfr
    have h_mv_ne : amountDeposit.mValue ≠ 0 := by
      intro h0; have := hiou.mant_lo; rw [h0] at this; simp at this
    have h_notZero : ¬ amountDeposit.isZero = true := by
      unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    simp only [pure_bind] at hok
    obtain ⟨ps, hps, hrx⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨dn, sum, a, -, -, ha, hae⟩ := postSumExponent_reduces assetsTotal amountDeposit ps hps
    obtain ⟨h100, hrange⟩ := STAmount.ofNumber_frac_exp_range amountDeposit.numericType sum
      .to_nearest a (by show amountDeposit.mNumericType.isIntegral = false; rw [hiou.is_fractional]; rfl) ha
    by_cases haz : a.mValue = 0
    · have hps100 : ps = -100 := by rw [← hae]; exact h100 haz
      subst hps100
      have hge : amountDeposit.exponent ≥ (-100 : ℤ) := by
        have := hiou.exp_lo; show (-100 : ℤ) ≤ amountDeposit.mOffset; omega
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_neg h_notZero, if_pos hge] at hrx
      rw [← Except.ok.inj hrx]
    · obtain ⟨hlo, hhi⟩ := hrange haz
      rw [hae] at hlo hhi
      exact STAmount.roundToExponent_downward_le amountDeposit result ps hiou hlo hhi hnn hrx

/-- A successful fractional sum clamp has computed a post-sum exponent. -/
lemma clamp_post_exists (A : Number) (p c : STAmount)
    (hfrac : p.integral = false) (hbr : p.negative = false)
    (hcl : clampToSumExponent A p = .ok c) :
    ∃ e, postSumExponent A p = .ok e := by
  unfold clampToSumExponent at hcl
  simp only [hbr, pure_bind] at hcl
  rw [if_neg (by simp [hfrac])] at hcl
  obtain ⟨pe, hpe, -⟩ := bind_ok_peel _ _ _ hcl
  exact ⟨pe, hpe⟩

/-- On an integral amount the post-sum exponent is `0`. -/
lemma post_exp_integral (A : Number) (x : STAmount) (e : ℤ) (hint : x.integral = true)
    (he : postSumExponent A x = .ok e) : e = 0 := by
  obtain ⟨-, sum, a, -, -, ha, hae⟩ := postSumExponent_reduces A x e he
  obtain ⟨-, hoff, -⟩ := STAmount.ofNumber_integral_facts x.numericType sum .to_nearest a hint ha
  rw [← hae]; exact hoff

/-- On an empty integral vault the priced charge is the ideal one exactly. -/
lemma charge_empty_integral (v : Vault) (shares c : STAmount)
    (hint : v.numericType.isIntegral = true)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat) (hmz : v.assetsTotal.mantissa_ = 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    c.toRat = v.idealChargeDeposit shares.toRat ∧ c.toRat = shares.toRat := by
  have hshmax : shares.mValue.toNat ≤ maxRep.toNat := by
    have hr := hshc.in_range; rw [hshnt] at hr
    calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
      _ = maxRep.toNat := by decide
  unfold sharesToAssetsDeposit at hsad
  have hA0 : v.toExact.assetsTotal = 0 :=
    Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
  have hscale : v.scale = 0 := v.wf.scale_integral hint
  have hshexp : shares.exponent = 0 := hshc.offset_zero
  have hideal : v.idealChargeDeposit shares.toRat = shares.toRat := by
    unfold RawVault.idealChargeDeposit
    rw [if_pos hA0, hscale]
    show shares.toRat / (10 : ℚ) ^ (0 : UInt8).toNat = shares.toRat
    norm_num
  rw [if_pos hmz] at hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  rw [STAmount.checked] at hc
  have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
    show shares.exponent - (v.scale.toNat : ℤ) = 0
    rw [hshexp, hscale]; rfl
  have hval0 : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
    show shares.mantissa.toNat ≤ maxRep.toNat
    exact hshmax
  have hcval := STAmount.canonicalize_integral_toRat _ c .to_nearest
    (show (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
  have hun : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_offset_zero
      (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false) hoff0]
    unfold STAmount.signedDrops STAmount.unchecked STAmount.mantissa
    simp
  have hsh : shares.toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_offset_zero shares hshexp]
    unfold STAmount.signedDrops
    rw [STAmount.mIsNegative_false_of_pos shares hshpos]
    simp
  rw [hideal, hcval, hun, hsh]
  exact ⟨rfl, rfl⟩

/-- The clamp keeps a fractional delta's numeric type on both branches. -/
lemma clamp_nt (A : Number) (p c : STAmount) (hA : A.isNormalized)
    (hfrac : p.mNumericType = .fractional) (hpc : p.IOUCanonical ∨ p.mValue = 0)
    (hcl : clampToSumExponent A p = .ok c) : c.mNumericType = .fractional := by
  have hpi : p.integral = false := by unfold STAmount.integral; rw [hfrac]; rfl
  by_cases hbr : p.negative = true
  · unfold clampToSumExponent at hcl
    simp only [hbr, if_true, pure_bind] at hcl
    rw [if_neg (by simp [hpi])] at hcl
    obtain ⟨pe, -, hcl⟩ := bind_ok_peel _ _ _ hcl
    have hfcz : p.operator_neg.FracCanonZero := by
      unfold STAmount.operator_neg
      split
      · exact ⟨hfrac, hpc⟩
      · refine ⟨hfrac, ?_⟩
        rcases hpc with h | h
        · exact Or.inl ⟨h.is_fractional, h.mant_lo, h.mant_hi, h.exp_lo, h.exp_hi⟩
        · exact Or.inr h
    exact (STAmount.roundToExponent_fczr _ c pe .downward hfcz hcl).1
  · have hbr' : p.negative = false := by simpa using hbr
    rw [(clampToSumExponent_sum_shape A p c hA hpc hpi hbr' hcl).1, hfrac]

end XRPL.Model.SingleAssetVault.DepTight
