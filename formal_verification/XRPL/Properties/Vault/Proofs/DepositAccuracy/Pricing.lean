import XRPL.Properties.Vault.Proofs.Support.DepositPricing
import XRPL.Properties.Vault.Proofs.Support.RoundToVaultExponent

/-! # Deposit pricing accuracy

Error budgets of the charge pipeline, the pricing chains of `assetsToSharesDeposit`, and its
monotonicity in the deposited amount. -/

set_option maxRecDepth 4000

namespace XRPL.Model.SingleAssetVault.DepAcc

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- Compose the three stage errors of `T0 / nav` computed as
`(T0·(1+δ₂)) / (nav·(1+δ₁))` then rounded once more: the result stays within
relative error `E` of `T0 / nav`, given the numeric closure conditions. -/
lemma div_pipeline_rel_bound (nav N T0 PP QQ ε₁ ε₂ ε₃ E : ℚ)
    (hT0 : 0 < T0) (hQQ : 0 ≤ QQ)
    (h1 : |N - nav| ≤ nav * ε₁)
    (h2 : |PP - T0| ≤ T0 * ε₂)
    (h3 : |QQ * N - PP| ≤ PP * ε₃)
    (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hε₂1 : ε₂ < 1)
    (hε₃ : 0 ≤ ε₃) (hε₃1 : ε₃ ≤ 1)
    (hup : (1 + ε₂) * (1 + ε₃) ≤ (1 + E) * (1 - ε₁))
    (hlo : (1 - E) * (1 + ε₁) ≤ (1 - ε₂) * (1 - ε₃)) :
    |QQ * nav - T0| ≤ T0 * E := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  obtain ⟨h3l, h3r⟩ := abs_le.mp h3
  have hPP : 0 < PP := by nlinarith
  rw [abs_le]
  constructor
  · -- lower side: T0 * (1 - E) ≤ QQ * nav
    have key : T0 * ((1 - E) * (1 + ε₁)) ≤ QQ * nav * (1 + ε₁) := by
      have s1 : T0 * ((1 - E) * (1 + ε₁)) ≤ T0 * ((1 - ε₂) * (1 - ε₃)) := by nlinarith
      have s2 : T0 * ((1 - ε₂) * (1 - ε₃)) ≤ PP * (1 - ε₃) := by nlinarith
      have s3 : PP * (1 - ε₃) ≤ QQ * N := by nlinarith
      have s4 : QQ * N ≤ QQ * nav * (1 + ε₁) := by nlinarith
      linarith
    have hpos : (0 : ℚ) < 1 + ε₁ := by linarith
    nlinarith [key]
  · -- upper side: QQ * nav ≤ T0 * (1 + E)
    have key : QQ * nav * (1 - ε₁) ≤ T0 * ((1 + E) * (1 - ε₁)) := by
      have s1 : QQ * nav * (1 - ε₁) ≤ QQ * N := by nlinarith
      have s2 : QQ * N ≤ PP * (1 + ε₃) := by nlinarith
      have s3 : PP * (1 + ε₃) ≤ T0 * ((1 + ε₂) * (1 + ε₃)) := by nlinarith
      have s4 : T0 * ((1 + ε₂) * (1 + ε₃)) ≤ T0 * ((1 + E) * (1 - ε₁)) := by nlinarith
      linarith
    have hpos : (0 : ℚ) < 1 - ε₁ := by linarith
    nlinarith [key]

/-- The deposit stage budget as a plain fraction. -/
lemma depositε_eq : depositε = 1 / 100000000000000000 := by
  unfold depositε
  rw [show ((-17) : ℤ) = -(17 : ℕ) from rfl, zpow_neg, zpow_natCast]
  norm_num

/-- The combined `sub`+`mul` relative error of the charge numerator stays within
the clean bound `12 / (2^63 - 3)`. -/
lemma charge_eps2_bound :
    (1 + 6 / (2 ^ 63 - 3 : ℚ)) * (5 / (2 ^ 63 + 7)) + 6 / (2 ^ 63 - 3) ≤ 12 / (2 ^ 63 - 3) := by
  norm_num

/-- Upper closure of the charge `sub`/`mul`/`div` pipeline within `depositε`. -/
lemma charge_pipeline_up :
    ((1 : ℚ) + 12 / (2 ^ 63 - 3)) * (1 + 6 / (2 ^ 63 - 3))
      ≤ (1 + depositε) * (1 - 0) := by
  rw [depositε_eq]; norm_num

/-- Lower closure of the charge `sub`/`mul`/`div` pipeline within `depositε`. -/
lemma charge_pipeline_lo :
    ((1 : ℚ) - depositε) * (1 + 0)
      ≤ (1 - 12 / (2 ^ 63 - 3)) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [depositε_eq]; norm_num

/-- Cross-multiplied upper bound: a quotient's numerator error bounds the quotient
above by the exact ratio times `(1 + ε)`. Kept abstract so the arithmetic solvers
never unfold the `depositNav`/`sharesTotal` rationals. -/
private lemma charge_div_upper (A B D ε : ℚ) (hD : 0 < D) (h : |A * D - B| ≤ B * ε) :
    A ≤ B / D * (1 + ε) := by
  have hab := abs_le.mp h
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  nlinarith [hab.2]

/-- Ceiling combine: a value within `+1` of `Q ≤ I·(1+ε)` overshoots `I` by at most
`1 + I·ε`. Abstract so the solver stays off the vault rationals. -/
private lemma charge_ceiling (I Q c ε : ℚ) (hQ : Q ≤ I * (1 + ε)) (hc : c ≤ Q + 1) :
    c - I ≤ 1 + I * ε := by nlinarith

/-- **Integral charge overcharge bound.** On a lawful integral vault the taken
amount `c = sharesToAssetsDeposit v shares` overshoots the exact charge by less
than one whole unit plus the relative stage error: the empty branch is exact, and
the nonempty branch is `⌈nav·shares/sharesTotal⌉` (upward `ofNumber`), whose
integer ceiling adds at most `1` on top of the `depositε` pipeline error. -/
lemma sharesToAssetsDeposit_charge_integral_bound (v : Vault) (_amount shares c : STAmount)
    (hint : v.numericType.isIntegral = true)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ v.idealChargeDeposit shares.toRat ∧
    c.toRat - v.idealChargeDeposit shares.toRat ≤
      1 + v.idealChargeDeposit shares.toRat * depositε := by
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hshmax : shares.mValue.toNat ≤ maxRep.toNat := by
    have hr := hshc.in_range; rw [hshnt] at hr
    calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
      _ = maxRep.toNat := by decide
  obtain ⟨hcc, hcnt⟩ := sharesToAssetsDeposit_integral_canonical v shares c hint hsad
  unfold sharesToAssetsDeposit at hsad
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: `c = shares` exactly, `idealCharge = shares` (scale 0)
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
    have hcshares : c.toRat = shares.toRat := by rw [hcval, hun, hsh]
    rw [hideal, hcshares]
    refine ⟨le_of_lt hshpos, ?_⟩
    have : (0 : ℚ) ≤ shares.toRat * depositε := mul_nonneg (le_of_lt hshpos) hεnn
    linarith
  · -- nonempty vault: three-stage pipeline into an upward `ofNumber`
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
      have hne : v.toExact.sharesTotal ≠ 0 := by
        intro h0
        exact absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
      have : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
        have : 0 < v.toExact.sharesTotal := Nat.pos_of_ne_zero hne
        exact_mod_cast this
      rw [hST_def, ← hcast]; exact this
    have hideal : v.idealChargeDeposit shares.toRat = nav * s / ST := by
      unfold RawVault.idealChargeDeposit
      rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
    have hideal_nonneg : 0 ≤ v.idealChargeDeposit shares.toRat := by
      rw [hideal]; exact le_of_lt hidpos
    refine ⟨hideal_nonneg, ?_⟩
    rw [hideal]
    -- reduce the charge pipeline
    rw [if_neg hmz] at hsad
    obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    set navN := v.assetsTotal with hnavN_eq
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hc0 : c.mValue = 0
    · -- degenerate underflow: the charge is zero, overcharge is nonpositive
      have hc_zero : c.toRat = 0 := by
        rw [STAmount.toRat_signed]
        have : c.mValue.toNat = 0 := by rw [hc0]; rfl
        rw [this]; simp
      rw [hc_zero]
      have : (0 : ℚ) ≤ nav * s / ST * depositε := mul_nonneg (le_of_lt hidpos) hεnn
      linarith
    · -- genuine charge: run the relative composition
      have hQm : Q.mantissa_ ≠ 0 :=
        STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest c hint hc hc0
      have hnavnorm : navN.isNormalized := by rw [hnavN_eq]; exact v.wf.assetsTotal_norm
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnval hsnnorm
      have hshN_val : shN.toRat = s := by rw [hsnval]
      have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
      have hshNm : shN.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
      have hSTnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, _⟩ :=
        operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      obtain ⟨_, hnavbound, _, hnavN_pos⟩ :=
        Vault.depositNav_facts v navN hmz hnavm hnavN_eq
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm hSTnorm hPm hSTm hQ hQm
      -- stage bounds
      have hmulb : |P.toRat - navN.toRat * shN.toRat|
          ≤ navN.toRat * shN.toRat * (5 / (2 ^ 63 + 7)) := by
        have h : |P.toRat - navN.toRat * shN.toRat|
            ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPm
        rwa [abs_of_nonneg (by positivity : (0 : ℚ) ≤ navN.toRat * shN.toRat)] at h
      have hsubb : |navN.toRat - nav| ≤ nav * (6 / (2 ^ 63 - 3)) := hnavbound
      have hPpos : 0 < P.toRat := by
        have := abs_le.mp hmulb
        have hε : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
        nlinarith [mul_pos hnavN_pos hshN_pos]
      have hPN_pos : 0 < P.toRat / ST := div_pos hPpos hST_pos
      have hdivb : |Q.toRat - P.toRat / ST| ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) := by
        have h : |Q.toRat - P.toRat / ST| ≤ |P.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm hSTnorm hQ hQm
        rwa [abs_of_pos hPN_pos] at h
      have hQpos : 0 < Q.toRat := by
        have := abs_le.mp hdivb
        nlinarith
      -- h2 : the combined `sub`+`mul` numerator error
      have hnN_le : navN.toRat ≤ nav * (1 + 6 / (2 ^ 63 - 3)) := by
        have := abs_le.mp hsubb; nlinarith
      have h2 : |P.toRat - nav * s| ≤ nav * s * (12 / (2 ^ 63 - 3)) := by
        have htri : |P.toRat - nav * s|
            ≤ |P.toRat - navN.toRat * s| + |navN.toRat * s - nav * s| :=
          abs_sub_le _ _ _
        have hb1 : |P.toRat - navN.toRat * s| ≤ navN.toRat * s * (5 / (2 ^ 63 + 7)) := by
          rw [← hshN_val]; exact hmulb
        have hb2 : |navN.toRat * s - nav * s| ≤ nav * s * (6 / (2 ^ 63 - 3)) := by
          rw [show navN.toRat * s - nav * s = (navN.toRat - nav) * s from by ring, abs_mul,
            abs_of_pos hshpos]
          have := abs_le.mp hsubb
          nlinarith [hshpos]
        have hkey : navN.toRat * s * (5 / (2 ^ 63 + 7)) + nav * s * (6 / (2 ^ 63 - 3))
            ≤ nav * s * (12 / (2 ^ 63 - 3)) := by
          have he2 := charge_eps2_bound
          nlinarith [hnN_le, hshpos, hnav_pos, mul_pos hnav_pos hshpos, he2,
            mul_nonneg (le_of_lt hnav_pos) (le_of_lt hshpos)]
        linarith
      -- h3 : the division stage
      have h3 : |Q.toRat * ST - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
        have hrw : Q.toRat * ST - P.toRat = (Q.toRat - P.toRat / ST) * ST := by
          field_simp
        calc |Q.toRat * ST - P.toRat|
            = |Q.toRat - P.toRat / ST| * ST := by rw [hrw, abs_mul, abs_of_pos hST_pos]
          _ ≤ P.toRat / ST * (6 / (2 ^ 63 - 3)) * ST := by
                nlinarith [hST_pos, abs_nonneg (Q.toRat - P.toRat / ST), hdivb]
          _ = P.toRat * (6 / (2 ^ 63 - 3)) := by
                rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hST_pos)]
      -- compose
      have hcomp := div_pipeline_rel_bound ST ST (nav * s) P.toRat Q.toRat 0
        (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3)) depositε
        (mul_pos hnav_pos hshpos) (le_of_lt hQpos)
        (by rw [sub_self, abs_zero, mul_zero])
        h2 h3 (le_refl 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        charge_pipeline_up charge_pipeline_lo
      -- Q ≤ ideal · (1 + depositε)
      have hQ_up : Q.toRat ≤ nav * s / ST * (1 + depositε) :=
        charge_div_upper Q.toRat (nav * s) ST depositε hST_pos hcomp
      -- within one of the ceiling
      have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
      have hwithin := STAmount.ofNumber_integral_within_one v.numericType Q .to_nearest c
        hint hQnorm hQneg hc
      have hc_le : c.toRat ≤ Q.toRat + 1 := by
        have h := (abs_lt.mp hwithin).2; linarith only [h]
      exact charge_ceiling (nav * s / ST) Q.toRat c.toRat depositε hQ_up hc_le

/-- `roundToVaultExponent` never changes the numeric type: the integral pass is
the identity, and the fractional pass stays fractional (the `FracCanonZero`
pipeline preserves the type). -/
lemma roundToVaultExponent_mNumericType (a : STAmount) (asset : Number) (r : STAmount)
    (hc : a.Canonical) (hok : roundToVaultExponent a asset = .ok r) :
    r.mNumericType = a.mNumericType := by
  by_cases hint : a.integral = true
  · rw [roundToVaultExponent_integral a asset hint] at hok
    rw [← Except.ok.inj hok]
  · have hfr : a.integral = false := by
      cases hb : a.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hcz : (STAmount.FracCanonZero a) := ⟨(hc.2 hfr).is_fractional, Or.inl (hc.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    simp only [pure_bind] at hok
    obtain ⟨postScale, _, hrx⟩ := bind_ok_peel _ _ _ hok
    have heq : r = r := rfl
    rw [heq] at hrx
    rw [(STAmount.roundToExponent_fczr a r postScale .downward hcz hrx).1]
    exact hcz.1.symm

/-- **The recorded deposit charge is non-negative.** On an integral vault the clamp
is the identity, so the priced charge's own non-negativity carries; on a fractional
one the `tecPRECISION_LOSS` guard has already rejected anything `≤ 0`. -/
lemma Vault.deposit_charge_nonneg (v : Vault) (shares priced c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent v.assetsTotal priced = .ok c)
    (hfnp : c.isFractionalNonPositive = .ok false) :
    0 ≤ c.toRat := by
  have hpnn : 0 ≤ priced.toRat := sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v shares priced hsad
  by_cases hint : v.numericType.isIntegral = true
  · rw [clampToSumExponent_integral_nonneg v.assetsTotal priced c
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl]
    exact hpnn
  have hpfrac : priced.integral = false := by
    show priced.mNumericType.isIntegral = false; rw [hpnt]; simpa using hint
  by_cases hbr : priced.negative = true
  · -- a set sign bit on a non-negative charge forces a zero, where the clamp is the identity
    have hpz : priced.mValue = 0 := by
      by_contra hz
      have := STAmount.toRat_neg_of priced hbr hz
      linarith
    have hid : priced.operator_neg = priced := by unfold STAmount.operator_neg; simp [hpz]
    have hcz : c.mValue = 0 :=
      clampToSumExponent_neg_zero v.assetsTotal priced c hpz (by rw [hid]; exact hbr)
        (by rw [hid]; exact hcl)
    rw [STAmount.toRat_signed, hcz]; simp
  · -- sum branch: the clamp keeps the fractional type, so the guard applies
    have hcnt : c.mNumericType = priced.mNumericType :=
      (clampToSumExponent_sum_shape v.assetsTotal priced c v.wf.assetsTotal_norm
        (by by_cases hpz : priced.mValue = 0
            · exact Or.inr hpz
            · rcases sharesToAssetsDeposit_disj_canonical v shares priced hshc hshnt hsad hpz with
                h | h
              · exact Or.inl h
              · exfalso
                have := h.is_integral
                rw [hpnt] at this
                exact hint this)
        hpfrac (by simpa using hbr) hcl).1
    have hcfrac : c.integral = false := by
      show c.mNumericType.isIntegral = false
      rw [hcnt]; exact hpfrac
    exact STAmount.nonneg_of_fnp c hcfrac hfnp

/-- Full nonempty-vault pricing chain of `assetsToSharesDeposit` with every stage's
normalization / nonzero-mantissa / positivity fact. -/
lemma deposit_nonempty_chain_facts (v : Vault) (hne : v.assetsTotal.mantissa_ ≠ 0)
    (amount shares : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    ∃ (amountN navN P T0 T : Number),
      amountN.toRat = amount.toRat ∧ amountN.isNormalized ∧ amountN.mantissa_ ≠ 0 ∧
      navN = v.assetsTotal ∧
      navN.isNormalized ∧ navN.mantissa_ ≠ 0 ∧ 0 < navN.toRat ∧
      v.sharesTotal.mantissa_ ≠ 0 ∧
      v.sharesTotal.operator_mul amountN .to_nearest = .ok P ∧
      P.isNormalized ∧ P.mantissa_ ≠ 0 ∧
      P.operator_div navN .to_nearest = .ok T0 ∧
      T0.isNormalized ∧ T0.mantissa_ ≠ 0 ∧ 0 < T0.toRat ∧
      T0.truncate = .ok T ∧ T.isNormalized ∧ T.mantissa_ ≠ 0 ∧ T.toRat.den = 1 ∧
      STAmount.ofNumber .int64 T .to_nearest = .ok shares := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  unfold assetsToSharesDeposit at hok
  rw [if_neg hne] at hok
  obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
  have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
  rw [hsh'] at hsh
  have hTm : T.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
  have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
  set navN := v.assetsTotal with hnavN_eq
  have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
  have hnavm : navN.mantissa_ ≠ 0 :=
    operator_div_divisor_ne_zero P navN T0 .to_nearest hnavnorm hT0
  have hPm : P.mantissa_ ≠ 0 :=
    operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
      (Number.not_operator_eq_zero_of_mantissa_ne hnavm) hT0 hT0m
  obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
  have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
  rw [haneq] at hanval hannorm
  obtain ⟨hSTm, hanm⟩ :=
    operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
  have hPnorm : P.isNormalized :=
    operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
      v.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
  have hT0norm : T0.isNormalized :=
    operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hnavm hT0 hT0m
  have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact le_of_lt hpos
  have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hPnn : 0 ≤ P.toRat := by
    have hb : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
        ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
      operator_mul_rounds_to_nearest v.sharesTotal amountN P
        v.wf.sharesTotal_norm hannorm hP hPm
    rw [abs_of_nonneg (mul_nonneg hSTnn hann)] at hb
    have hab := abs_le.mp hb
    nlinarith [mul_nonneg hSTnn hann]
  obtain ⟨_, _, _, hnavpos⟩ := Vault.depositNav_facts v navN hne hnavm hnavN_eq
  have hPNnn : 0 ≤ P.toRat / navN.toRat := div_nonneg hPnn (le_of_lt hnavpos)
  have hT0nn : 0 ≤ T0.toRat := by
    have hb : |T0.toRat - P.toRat / navN.toRat|
        ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) :=
      operator_div_rounds_to_nearest P navN T0 hPnorm hnavnorm hT0 hT0m
    rw [abs_of_nonneg hPNnn] at hb
    have hab := abs_le.mp hb
    nlinarith [hPNnn]
  have hT0pos : 0 < T0.toRat :=
    lt_of_le_of_ne hT0nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T0 hT0m))
  obtain ⟨hTval, hTnorm⟩ :=
    Number.truncate_floor T0 T hT0norm (Number.negative_false_of_pos T0 hT0pos) hT
  exact ⟨amountN, navN, P, T0, T, hanval, hannorm, hanm, hnavN_eq, hnavnorm, hnavm, hnavpos,
    hSTm, hP, hPnorm, hPm, hT0, hT0norm, hT0m, hT0pos, hT, hTnorm hTm, hTm,
    (by rw [hTval]; exact Rat.den_intCast _), hsh⟩

/-- **Empty-vault pricing chain of `assetsToSharesDeposit`.** On an empty vault the
`Number.normalized` step scales a `≤ 19`-digit mantissa into `largeRange` with no
rounding (`doNormalize_largeRange_exact`), so the exact source value of the truncation
is `amount · 10^scale`; the issued shares are its floor. -/
lemma deposit_empty_chain_facts (v : Vault) (hscale : v.scale.toNat ≤ 18)
    (amount shares : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    ∃ (n1 n2 : Number),
      n1.isNormalized ∧ n1.negative_ = false ∧
      n1.toRat = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℤ) ∧
      n1.truncate = .ok n2 ∧ n2.isNormalized ∧ n2.toRat.den = 1 ∧
      STAmount.ofNumber .int64 n2 .to_nearest = .ok shares := by
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  unfold assetsToSharesDeposit at hok
  rw [if_pos hmz] at hok
  obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
  have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
  rw [hsh'] at hsh
  -- `amount` positive: non-negative sign and a nonzero mantissa
  have hposneg : amount.mIsNegative = false :=
    Number.negative_false_of_pos ⟨amount.mIsNegative, amount.mValue, amount.mOffset⟩
      (by rw [← STAmount.toRat_eq_number]; exact hpos)
  have hmv_ne : amount.mValue ≠ 0 := fun h =>
    absurd ((STAmount.toRat_eq_zero_iff amount).mpr h) (ne_of_gt hpos)
  have hmv1 : 1 ≤ amount.mValue.toNat := by
    have : amount.mValue.toNat ≠ 0 := fun h => hmv_ne (by rw [← UInt64.toNat_inj]; simpa using h)
    omega
  -- mantissa and exponent bounds shared by the integral and fractional cases
  have hmax : amount.mValue.toNat ≤ maxRep.toNat := by
    by_cases hint : amount.integral = true
    · obtain ⟨hic, hmr⟩ := hc.1 hint
      exact le_trans hic.in_range hmr
    · have hf : amount.integral = false := by
        cases hb : amount.integral with | false => rfl | true => exact absurd hb hint
      have hiou := hc.2 hf
      have := hiou.mant_hi; rw [maxRep_val]; omega
  have hexp : (-96 : ℤ) ≤ amount.exponent ∧ amount.exponent ≤ 80 := by
    by_cases hint : amount.integral = true
    · obtain ⟨hic, _⟩ := hc.1 hint
      rw [show amount.exponent = amount.mOffset from rfl, hic.offset_zero]; omega
    · have hf : amount.integral = false := by
        cases hb : amount.integral with | false => rfl | true => exact absurd hb hint
      have hiou := hc.2 hf
      exact ⟨hiou.exp_lo, hiou.exp_hi⟩
  obtain ⟨hexp_lo, hexp_hi⟩ := hexp
  -- the normalize step is value-exact
  obtain ⟨M, e1, hdn, hMval, hMnorm⟩ :=
    doNormalize_largeRange_exact false amount.mantissa (amount.exponent + (v.scale.toNat : ℤ))
      .to_nearest hmv1 hmax
      (by show minExponent + 18 ≤ amount.exponent + (v.scale.toNat : ℤ)
          have hs : (0 : ℤ) ≤ (v.scale.toNat : ℤ) := by positivity
          unfold minExponent; omega)
      (by show amount.exponent + (v.scale.toNat : ℤ) ≤ maxExponent - 1
          have hs : (v.scale.toNat : ℤ) ≤ 18 := by exact_mod_cast hscale
          unfold maxExponent; omega)
  have hn1eq : n1 = ⟨false, M, e1⟩ := by
    have hdn' : Number.normalized false amount.mantissa (amount.exponent + (v.scale.toNat : ℤ))
        largeRange.min largeRange.max .to_nearest = .ok (⟨false, M, e1⟩ : Number) := hdn
    exact Except.ok.inj (hn1.symm.trans hdn')
  have hn1nn : (0 : ℚ) ≤ n1.toRat := by rw [hn1eq, Number.toRat_of_nonneg _ rfl]; positivity
  have hn2m : n2.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hshmv
  obtain ⟨hn2val, hn2normfn⟩ :=
    Number.truncate_floor n1 n2 (by rw [hn1eq]; exact hMnorm) (by rw [hn1eq]) hn2
  refine ⟨n1, n2, by rw [hn1eq]; exact hMnorm, by rw [hn1eq], ?_, hn2, hn2normfn hn2m,
    by rw [hn2val]; exact Rat.den_intCast _, hsh⟩
  rw [hn1eq, Number.toRat_of_nonneg _ rfl, hMval, STAmount.toRat_of_nonneg amount hposneg]
  show (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ))
     = (amount.mValue.toNat : ℚ) * 10 ^ amount.mOffset * 10 ^ (v.scale.toNat : ℤ)
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring

/-- **`assetsToSharesDeposit` is monotone in the amount** on an empty vault: the exact
`⌊amount · 10^scale⌋` map is monotone via truncation and integral conversion. -/
lemma assetsToSharesDeposit_empty_mono (v : Vault) (hscale : v.scale.toNat ≤ 18)
    (amount₁ amount₂ shares₁ shares₂ : STAmount)
    (hc₁ : amount₁.Canonical) (hpos₁ : 0 < amount₁.toRat)
    (hc₂ : amount₂.Canonical) (hpos₂ : 0 < amount₂.toRat)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hok₁ : assetsToSharesDeposit v amount₁ = .ok shares₁) (hnz₁ : shares₁.isZero = false)
    (hok₂ : assetsToSharesDeposit v amount₂ = .ok shares₂) (hnz₂ : shares₂.isZero = false)
    (hle : amount₁.toRat ≤ amount₂.toRat) : shares₁.toRat ≤ shares₂.toRat := by
  obtain ⟨n1₁, n2₁, hn1n₁, hn1neg₁, hn1v₁, htr₁, hn2n₁, hden₁, hsh₁⟩ :=
    deposit_empty_chain_facts v hscale amount₁ shares₁ hc₁ hpos₁ hmz hok₁ hnz₁
  obtain ⟨n1₂, n2₂, hn1n₂, hn1neg₂, hn1v₂, htr₂, hn2n₂, hden₂, hsh₂⟩ :=
    deposit_empty_chain_facts v hscale amount₂ shares₂ hc₂ hpos₂ hmz hok₂ hnz₂
  have hn1le : n1₁.toRat ≤ n1₂.toRat := by
    rw [hn1v₁, hn1v₂]; exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hn2le : n2₁.toRat ≤ n2₂.toRat :=
    Number.truncate_toRat_mono n1₁ n1₂ n2₁ n2₂ hn1n₁ hn1n₂ hn1neg₁ hn1neg₂ htr₁ htr₂ hn1le
  exact STAmount.ofNumber_integral_toRat_mono .int64 n2₁ n2₂ shares₁ shares₂ .to_nearest .to_nearest
    (by decide) hn2n₁ hn2n₂ hden₁ hden₂ hsh₁ hsh₂ hn2le

/-- **`assetsToSharesDeposit` is monotone in the amount**: the pricing chain,
truncation, and integral conversion are each monotone (empty vault: the exact
`⌊amount · 10^scale⌋` map). -/
lemma assetsToSharesDeposit_mono (v : Vault)
    (amount₁ amount₂ shares₁ shares₂ : STAmount)
    (hc₁ : amount₁.Canonical) (hpos₁ : 0 < amount₁.toRat)
    (hc₂ : amount₂.Canonical) (hpos₂ : 0 < amount₂.toRat)
    (hok₁ : assetsToSharesDeposit v amount₁ = .ok shares₁) (hnz₁ : shares₁.isZero = false)
    (hok₂ : assetsToSharesDeposit v amount₂ = .ok shares₂) (hnz₂ : shares₂.isZero = false)
    (hle : amount₁.toRat ≤ amount₂.toRat) : shares₁.toRat ≤ shares₂.toRat := by
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · exact assetsToSharesDeposit_empty_mono v v.wf.scale_le amount₁ amount₂ shares₁ shares₂
      hc₁ hpos₁ hc₂ hpos₂ hmz hok₁ hnz₁ hok₂ hnz₂ hle
  have hne : v.assetsTotal.mantissa_ ≠ 0 := hmz
  obtain ⟨aN₁, navN₁, P₁, T0₁, T₁, hav₁, haN₁, ham₁, hnav₁, hnavn₁, hnavm₁, hnavp₁, hSTm₁,
      hP₁, hPn₁, hPm₁, hT0₁, hT0n₁, hT0m₁, hT0p₁, hT₁, hTn₁, hTm₁, hTden₁, hsh₁⟩ :=
    deposit_nonempty_chain_facts v hne amount₁ shares₁ hc₁ hpos₁ hok₁ hnz₁
  obtain ⟨aN₂, navN₂, P₂, T0₂, T₂, hav₂, haN₂, ham₂, hnav₂, hnavn₂, hnavm₂, hnavp₂, hSTm₂,
      hP₂, hPn₂, hPm₂, hT0₂, hT0n₂, hT0m₂, hT0p₂, hT₂, hTn₂, hTm₂, hTden₂, hsh₂⟩ :=
    deposit_nonempty_chain_facts v hne amount₂ shares₂ hc₂ hpos₂ hok₂ hnz₂
  have hnaveq : navN₁ = navN₂ := hnav₁.trans hnav₂.symm
  subst hnaveq
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.sharesTotal hSTm₁))
  have hSTneg := Number.negative_false_of_pos v.sharesTotal hSTpos
  have hnavneg := Number.negative_false_of_pos navN₁ hnavp₁
  have haN₁neg := Number.negative_false_of_pos aN₁ (by rw [hav₁]; exact hpos₁)
  have haN₂neg := Number.negative_false_of_pos aN₂ (by rw [hav₂]; exact hpos₂)
  have haNle : aN₁.toRat ≤ aN₂.toRat := by rw [hav₁, hav₂]; exact hle
  have hT0le : T0₁.toRat ≤ T0₂.toRat :=
    Number.mul_div_num_mono v.sharesTotal navN₁ aN₁ aN₂ P₁ P₂ T0₁ T0₂
      v.wf.sharesTotal_norm hSTm₁ hSTneg hnavn₁ hnavm₁ hnavneg
      haN₁ ham₁ haN₁neg haN₂ ham₂ haN₂neg
      hP₁ hPm₁ hP₂ hPm₂ hT0₁ hT0m₁ hT0₂ hT0m₂ haNle
  have hTle : T₁.toRat ≤ T₂.toRat :=
    Number.truncate_toRat_mono T0₁ T0₂ T₁ T₂ hT0n₁ hT0n₂
      (Number.negative_false_of_pos T0₁ hT0p₁) (Number.negative_false_of_pos T0₂ hT0p₂)
      hT₁ hT₂ hT0le
  exact STAmount.ofNumber_integral_toRat_mono .int64 T₁ T₂ shares₁ shares₂ .to_nearest .to_nearest
    (by decide) hTn₁ hTn₂ hTden₁ hTden₂ hsh₁ hsh₂ hTle

end XRPL.Model.SingleAssetVault.DepAcc
