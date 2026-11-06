import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Deposit pricing

Facts about the deposit pricing: `Vault.depositNav`, `assetsToSharesDeposit`,
`sharesToAssetsDeposit` and the clamped charge. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On an integral vault a successful charge is a canonical integral amount of the vault's type. -/
lemma sharesToAssetsDeposit_integral_canonical (v : Vault) (shares c : STAmount)
    (hvint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.IntegralCanonical ∧ c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  obtain ⟨navN, hat, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hmz : navN.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : c' = c :=
      Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [heq] at hc
    rw [STAmount.checked] at hc
    exact STAmount.canonicalize_integral_canonical _ c .to_nearest
      (show (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hvint) hc
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n4, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : c' = c :=
      Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [heq] at hc
    exact STAmount.ofNumber_integral_canonical v.numericType n4 .to_nearest c hvint hc

/-- The charge is stored canonically for its kind. A nonzero charge is `IOUCanonical` on a fractional vault
and `IntegralCanonical` on an integral one. -/
private lemma sharesToAssetsDeposit_disj_canonical (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hok : sharesToAssetsDeposit v shares = .ok c) (hc0 : c.mValue ≠ 0) :
    c.IOUCanonical ∨ c.IntegralCanonical := by
  unfold sharesToAssetsDeposit at hok
  obtain ⟨navN, hat, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault: both branches pack through `canonicalize`/`ofNumber` integral
    by_cases hmz : navN.mantissa_ = 0
    · rw [if_pos hmz] at hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      rw [STAmount.checked] at hc
      exact Or.inr (STAmount.canonicalize_integral_canonical _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hc).1
    · rw [if_neg hmz] at hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      exact Or.inr (STAmount.ofNumber_integral_canonical v.numericType Q .to_nearest c hint hc).1
  · -- fractional vault: canonicalizes into `IOUCanonical`-or-zero
    have hfrac : v.numericType = .fractional := by
      cases hnt : v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
    by_cases hmz : navN.mantissa_ = 0
    · rw [if_pos hmz] at hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      rw [STAmount.checked] at hc
      have hcz := STAmount.canonicalize_fczr _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mNumericType = .fractional from hfrac) hc
      rcases hcz.2 with hio | hzero
      · exact Or.inl hio
      · exact absurd hzero hc0
    · rw [if_neg hmz] at hok
      obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨shN, hshN, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨Q, hQ, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hok
      have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
      rw [hceq] at hc
      have hcof : STAmount.ofNumber .fractional Q .to_nearest = .ok c := by rw [← hfrac]; exact hc
      -- nonzero chain: c ≠ 0 forces Q ≠ 0, walked back to the pipeline operands
      have hQm : Q.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero .fractional Q .to_nearest c rfl hcof hc0
      have hApos : 0 < v.toExact.assetsTotal :=
        lt_of_lt_of_le (Vault.assetsTotal_pos v navN hat hmz).2 (Vault.assetsTotal_le_exact v navN hat)
      have hSTne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
        absurd (Vault.exact_assetsTotal_eq_zero v h0) (ne_of_gt hApos)
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
        refine Number.mantissa_ne_zero_of_toRat_ne_zero ?_
        rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
        exact_mod_cast hSTne
      have hnavnorm : navN.isNormalized := (Vault.assetsTotal_ge_deployed v navN hat).1
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnnorm
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, hshNm⟩ := operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm v.wf.sharesTotal_norm
          hPm hSTm hQ hQm
      obtain ⟨hlo19, hhi19⟩ := hQnorm.mantissaBounds_nat hQm
      have hQexp_lo : minExponent ≤ Q.exponent_ := Number.exponent_ge_min Q hQnorm hQm
      rcases STAmount.ofNumber_iou_canonical_or_zero Q .to_nearest c hlo19 hhi19 hQexp_lo hcof with hio | hzero
      · exact Or.inl hio
      · exact absurd hzero hc0

/-- The charge type matches the vault's numeric type: both packings route through
`checked`/`ofNumber` on `vault.numericType`, which preserve the type. -/
lemma sharesToAssetsDeposit_mNumericType (v : Vault) (shares c : STAmount)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  obtain ⟨navN, hat, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hmz : navN.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq, STAmount.checked] at hcx
    exact STAmount.canonicalize_mNumericType _ c .to_nearest hcx
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hcx
    exact STAmount.ofNumber_mNumericType v.numericType Q .to_nearest c hcx

/-- The integral charge fits `maxRep`. On an integral vault the packing routes
through `checked`/`ofNumber`, whose stored magnitude never exceeds `maxRep`. -/
private lemma sharesToAssetsDeposit_le_maxRep (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mValue.toNat ≤ maxRep.toNat := by
  have hscale0 : v.scale = 0 := v.wf.scale_integral hint
  unfold sharesToAssetsDeposit at hok
  obtain ⟨navN, hat, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hmz : navN.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq, STAmount.checked] at hcx
    have hoff : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
      show shares.mOffset - (v.scale.toNat : ℤ) = 0
      rw [hshc.offset_zero, hscale0]; simp
    have hval : (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
      show shares.mValue.toNat ≤ maxRep.toNat
      have hr := hshc.in_range; rw [hshnt] at hr
      calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
        _ = maxRep.toNat := by decide
    obtain ⟨_, _, hle, _⟩ := STAmount.canonicalize_integral_facts _ c .to_nearest
      (show (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff hval hcx
    exact hle
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hcx
    obtain ⟨_, _, hle⟩ := STAmount.ofNumber_integral_facts v.numericType Q .to_nearest c hint hcx
    exact hle

/-- The charge is `ExactCanonical` or zero. A nonzero charge is canonical for its kind, and an integral one
also fits `Int64`. -/
lemma sharesToAssetsDeposit_exactCanonical_or_zero (v : Vault)
    (shares c : STAmount) (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.ExactCanonical ∨ c.mValue = 0 := by
  by_cases hc0 : c.mValue = 0
  · exact Or.inr hc0
  refine Or.inl ?_
  rcases sharesToAssetsDeposit_disj_canonical v shares c hshc hshnt hok hc0 with hio | hic
  · exact Or.inl hio
  · have htyeq : c.mNumericType = v.numericType :=
      sharesToAssetsDeposit_mNumericType v shares c hok
    have hint : v.numericType.isIntegral = true := by rw [← htyeq]; exact hic.is_integral
    refine Or.inr ⟨hic, ?_⟩
    have hle := sharesToAssetsDeposit_le_maxRep v shares c hshc hshnt hint hok
    calc c.mValue.toNat ≤ maxRep.toNat := hle
      _ ≤ 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num

/-- The charge is nonnegative. Both branches pack a nonnegative value. -/
lemma sharesToAssetsDeposit_nonneg (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ c.toRat := by
  unfold sharesToAssetsDeposit at hsad
  obtain ⟨navN, hat, hsad⟩ := bind_ok_peel _ _ _ hsad
  by_cases hmz : navN.mantissa_ = 0
  · -- empty vault
    rw [if_pos hmz] at hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hint : v.numericType.isIntegral = true
    · -- integral vault
      rw [STAmount.checked] at hc
      have hscale : v.scale = 0 := v.wf.scale_integral hint
      have hshexp : shares.exponent = 0 := hshc.offset_zero
      have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
        show shares.exponent - (v.scale.toNat : ℤ) = 0
        rw [hshexp, hscale]; rfl
      have hval0 : (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
        show shares.mantissa.toNat ≤ maxRep.toNat
        have hr := hshc.in_range; rw [hshnt] at hr
        calc shares.mantissa.toNat ≤ NumericType.int64.maxValue.toNat := hr
          _ = maxRep.toNat := by decide
      have hcval := STAmount.canonicalize_integral_toRat _ c .to_nearest
        (show (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
      rw [hcval, STAmount.toRat_of_nonneg _ rfl]; positivity
    · -- fractional vault
      have hnt_frac : v.numericType = .fractional := by
        cases hnt2 : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt2] at hint; exact absurd rfl hint
      have hsh_hi : shares.mValue.toNat < 2 ^ 63 := by
        have hr : shares.mValue.toNat ≤ maxRep.toNat := by
          have h := hshc.in_range; rw [hshnt] at h
          calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := h
            _ = maxRep.toNat := by decide
        have hmr : maxRep.toNat = 9223372036854775807 := by decide
        omega
      rw [STAmount.checked] at hc
      exact STAmount.canonicalize_signfalse_nonneg
        (STAmount.unchecked v.numericType shares.mantissa
          (shares.exponent - (v.scale.toNat : ℤ)) false)
        c .to_nearest hnt_frac rfl hsh_hi hc
  · -- nonempty vault: a positive total and positive shares give a positive quotient `Q`
    rw [if_neg hmz] at hsad
    obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hc0 : c.mValue = 0
    · rw [STAmount.toRat_signed, show c.mValue.toNat = 0 from by rw [hc0]; rfl]; simp
    · -- a positive normalized `Q` packs to a nonnegative amount
      have hApos : 0 < v.toExact.assetsTotal :=
        lt_of_lt_of_le (Vault.assetsTotal_pos v navN hat hmz).2 (Vault.assetsTotal_le_exact v navN hat)
      have hST_pos : 0 < v.sharesTotal.toRat := by
        have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
          absurd (Vault.exact_assetsTotal_eq_zero v h0) (ne_of_gt hApos)
        have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
        rw [← hcast]; exact_mod_cast Nat.pos_of_ne_zero hne
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hST_pos)
      have hQm : Q.mantissa_ ≠ 0 := by
        by_cases hint : v.numericType.isIntegral = true
        · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest c hint hc hc0
        · have hfrac : v.numericType = .fractional := by
            cases hnt : v.numericType with
            | fractional => rfl
            | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
          exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .to_nearest c hfrac hc hc0
      have hnavnorm : navN.isNormalized := (Vault.assetsTotal_ge_deployed v navN hat).1
      obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
        STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
      have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
      rw [hshNeq] at hsnval hsnnorm
      have hshN_pos : 0 < shN.toRat := by rw [hsnval]; exact hshpos
      have hshNm : shN.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hshN_pos)
      have hPm : P.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz P v.sharesTotal Q .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hQ hQm
      obtain ⟨hnavm, _⟩ := operator_mul_operands_ne_zero hnavnorm hsnnorm hP hPm
      have hnavN_pos := (Vault.assetsTotal_pos v navN hat hmz).2
      have hPnorm : P.isNormalized :=
        operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hnavm hshNm hP hPm
      have hQnorm : Q.isNormalized :=
        operator_div_result_isNormalized P v.sharesTotal Q .to_nearest hPnorm v.wf.sharesTotal_norm
          hPm hSTm hQ hQm
      have hmulb : |P.toRat - navN.toRat * shN.toRat|
          ≤ navN.toRat * shN.toRat * (5 / (2 ^ 63 + 7)) := by
        have h : |P.toRat - navN.toRat * shN.toRat|
            ≤ |navN.toRat * shN.toRat| * (5 / (2 ^ 63 + 7)) :=
          operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPm
        rwa [abs_of_nonneg (by positivity : (0 : ℚ) ≤ navN.toRat * shN.toRat)] at h
      have hPpos : 0 < P.toRat := by
        have := abs_le.mp hmulb
        nlinarith [mul_pos hnavN_pos hshN_pos]
      have hPN_pos : 0 < P.toRat / v.sharesTotal.toRat := div_pos hPpos hST_pos
      have hdivb : |Q.toRat - P.toRat / v.sharesTotal.toRat|
          ≤ P.toRat / v.sharesTotal.toRat * (6 / (2 ^ 63 - 3)) := by
        have h : |Q.toRat - P.toRat / v.sharesTotal.toRat|
            ≤ |P.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
          operator_div_rounds_to_nearest P v.sharesTotal Q hPnorm v.wf.sharesTotal_norm hQ hQm
        rwa [abs_of_pos hPN_pos] at h
      have hQpos : 0 < Q.toRat := by
        have := abs_le.mp hdivb
        nlinarith
      have hQneg : Q.negative_ = false := Number.negative_false_of_pos Q hQpos
      exact STAmount.ofNumber_nonneg v.numericType Q .to_nearest c hQnorm hQneg hc

/-- Priced at the vault's exact total, the ideal charge is the deposit ideal. -/
lemma RawVault.idealChargeDepositAt_depositNav (rv : RawVault) (shares : ℚ) :
    rv.idealChargeDepositAt rv.depositNav shares = rv.idealChargeDeposit shares := rfl

/-- Pricing at the computed total never charges more. The computed total sits at or below the
exact one, so a nonnegative share count costs at most the exact ideal charge. -/
lemma Vault.idealChargeDepositAt_le (v : Vault) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (shares : ℚ) (hs : 0 ≤ shares) :
    v.idealChargeDepositAt navN.toRat shares ≤ v.idealChargeDeposit shares := by
  unfold RawVault.idealChargeDeposit RawVault.idealChargeDepositAt RawVault.depositNav
  by_cases hm : navN.mantissa_ = 0
  · rw [if_pos ((Vault.assetsTotal_eq_zero_iff v navN hat).mp hm),
      if_pos (Number.toRat_eq_zero_of_mantissa_zero navN hm)]
  have hN := (Vault.assetsTotal_pos v navN hat hm).2
  have hle := Vault.assetsTotal_le_exact v navN hat
  rw [if_neg (ne_of_gt (lt_of_lt_of_le hN hle)), if_neg (ne_of_gt hN)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hs) (by positivity)

end XRPL.Model.SingleAssetVault
