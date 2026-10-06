import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.VaultValid

/-! # Deposit pricing

Facts about the deposit pricing: `Vault.depositNav`, `assetsToSharesDeposit`,
`sharesToAssetsDeposit` and the clamped charge. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The shares side of the exchange always packs through `ofNumber .int64`, so a
successful result is a canonical `int64` record. -/
lemma assetsToSharesDeposit_int64_canonical (v : Vault) (amount shares : STAmount)
    (hok : assetsToSharesDeposit v amount = .ok shares) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 := by
  unfold assetsToSharesDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · rw [if_pos hmz] at hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [heq] at hsh
    exact STAmount.ofNumber_integral_canonical .int64 n2 .to_nearest shares (by decide) hsh
  · rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n4, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n5, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [heq] at hsh
    exact STAmount.ofNumber_integral_canonical .int64 n5 .to_nearest shares (by decide) hsh

/-- On an integral vault, the charge side of the exchange packs through
`checked`/`ofNumber` on the vault's type, so a successful result is a canonical
integral record of the vault's type. -/
lemma sharesToAssetsDeposit_integral_canonical (v : Vault) (shares c : STAmount)
    (hvint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.IntegralCanonical ∧ c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
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

/-- **The deposit net asset value `navN = assetsTotal` on a nonempty lawful
vault.** It is normalized, equal to the exact positive `depositNav`, so within any
`to_nearest` budget of it (there is no subtraction stage under cash-basis). The `hnavm` witness (that the difference
did not round to zero) is available from any success that divides by it. -/
lemma Vault.depositNav_facts (v : Vault) (navN : Number)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (_hnavm : navN.mantissa_ ≠ 0)
    (hnavN : navN = v.assetsTotal) :
    navN.isNormalized ∧
      |navN.toRat - v.depositNav| ≤ v.depositNav * (6 / (2 ^ 63 - 3)) ∧
      0 < v.depositNav ∧ 0 < navN.toRat := by
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hnav_pos : 0 < v.depositNav := by unfold RawVault.depositNav; exact hApos
  have hnavN_eqNav : navN.toRat = v.depositNav := by rw [hnavN]; rfl
  refine ⟨by rw [hnavN]; exact v.wf.assetsTotal_norm, ?_, hnav_pos, ?_⟩
  · rw [hnavN_eqNav, sub_self, abs_zero]
    exact mul_nonneg (le_of_lt hnav_pos) (by norm_num)
  · rw [hnavN_eqNav]; exact hnav_pos

/-- **The issued shares are strictly positive.** `assetsToSharesDeposit` prices a
positive canonical `amount` into a nonnegative integer count, and a nonzero result
is therefore positive. The nonnegativity walks the exact `mul`/`div` chain: the
nonzero operands come from the successful division (never a zero divisor) and the
nonzero result (never a zero numerator), so no deep-underflow floor is needed. -/
lemma assetsToSharesDeposit_pos (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    0 < shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  have hne0 : shares.toRat ≠ 0 := STAmount.toRat_ne_zero shares hmv
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    exact absurd (show amount.toRat = 0 by rw [STAmount.toRat_signed, h0]; simp) (ne_of_gt hpos)
  suffices h : 0 ≤ shares.toRat from lt_of_le_of_ne h (Ne.symm hne0)
  unfold assetsToSharesDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize(amount·10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest hamv hn1cast hn1m
    have hin_nonneg : 0 ≤ (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat := by
      rw [Number.toRat_of_nonneg _ rfl]; positivity
    have hround := normalize_rounds_to_nearest _ n1 hn1cast hn1m
    have hn1_nonneg : 0 ≤ n1.toRat := by
      have hb : |n1.toRat - (Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat|
          ≤ |(Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := hround
      rw [abs_of_nonneg hin_nonneg] at hb
      have hab := abs_le.mp hb
      nlinarith [hin_nonneg]
    have hn1pos : 0 < n1.toRat :=
      lt_of_le_of_ne hn1_nonneg (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero n1 hn1m))
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    rw [hshval, hn2val]
    exact_mod_cast Int.floor_nonneg.mpr hn1_nonneg
  · -- nonempty vault: shares = ⌊(sharesTotal·amount)/nav⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    set navN := v.assetsTotal with hnavN_eq
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- nonzero chain, walked backward from the nonzero result
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
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
    -- value chain: every stage is nonnegative
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
    obtain ⟨_, _, _, hnavpos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
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
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    rw [hshval, hTval]
    exact_mod_cast Int.floor_nonneg.mpr hT0nn

/-- **The charge is stored canonically for its kind.** A nonzero
`sharesToAssetsDeposit` output is `IOUCanonical` (fractional vault) or
`IntegralCanonical` (integral vault): the empty branch canonicalizes the packed
record, and the nonempty branch packs the normalized division output through
`ofNumber`. The nonzero result forces a nonzero source, walked back to the
normalized division numerator/divisor. -/
lemma sharesToAssetsDeposit_disj_canonical (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hok : sharesToAssetsDeposit v shares = .ok c) (hc0 : c.mValue ≠ 0) :
    c.IOUCanonical ∨ c.IntegralCanonical := by
  unfold sharesToAssetsDeposit at hok
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault: both branches pack through `canonicalize`/`ofNumber` integral
    by_cases hmz : v.assetsTotal.mantissa_ = 0
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
    by_cases hmz : v.assetsTotal.mantissa_ = 0
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
      set navN := v.assetsTotal with hnavN_eq
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
      have hApos : 0 < v.toExact.assetsTotal := by
        rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
        · exact h
        · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
      have hSTne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
        absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
      have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
        refine Number.mantissa_ne_zero_of_toRat_ne_zero ?_
        rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
        exact_mod_cast hSTne
      have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
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
      have hQexp_lo : minExponent ≤ Q.exponent_ := by
        rcases hQnorm with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show Q.mantissa_ = 0 by rw [h0]; rfl) hQm
        · exact hlo
      rcases STAmount.ofNumber_iou_canonical_or_zero Q .to_nearest c hlo19 hhi19 hQexp_lo hcof with hio | hzero
      · exact Or.inl hio
      · exact absurd hzero hc0

/-- The charge type matches the vault's numeric type: both packings route through
`checked`/`ofNumber` on `vault.numericType`, which preserve the type. -/
lemma sharesToAssetsDeposit_mNumericType (v : Vault) (shares c : STAmount)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mNumericType = v.numericType := by
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
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

/-- **The integral charge fits `maxRep`.** On an integral vault the packing routes
through `checked`/`ofNumber`, whose stored magnitude never exceeds `maxRep`. -/
lemma sharesToAssetsDeposit_le_maxRep (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hint : v.numericType.isIntegral = true)
    (hok : sharesToAssetsDeposit v shares = .ok c) :
    c.mValue.toNat ≤ maxRep.toNat := by
  have hscale0 : v.scale = 0 := v.wf.scale_integral hint
  unfold sharesToAssetsDeposit at hok
  by_cases hmz : v.assetsTotal.mantissa_ = 0
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

/-- **The charge is `ExactCanonical` or zero.** A nonzero charge is canonical for
its kind (`sharesToAssetsDeposit_disj_canonical`); the integral kind additionally
fits `Int64` because its type equals the vault's, which is integral. -/
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

/-- **The charge converts exactly through `toNumber`.** The taken amount is stored
canonically for its kind (or is a fractional zero, handled by
`toNumber_zero_fractional`), so its `to_nearest` `Number` conversion is value-exact
and normalized. -/
lemma sharesToAssetsDeposit_toNumber_exact (v : Vault) (shares a : STAmount)
    (cN : Number) (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hsad : sharesToAssetsDeposit v shares = .ok a)
    (hcN : a.toNumber .to_nearest = .ok cN) :
    cN.toRat = a.toRat ∧ cN.isNormalized := by
  rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares a hshc hshnt hsad with hexact | ha0
  · obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical a .to_nearest hexact
    have hcNeq : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
    rw [← hcNeq]; exact ⟨hval, hnorm⟩
  · by_cases haint : a.integral = true
    · have htyeq := sharesToAssetsDeposit_mNumericType v shares a hsad
      have hvint : v.numericType.isIntegral = true := by
        show v.numericType.isIntegral = true
        rw [← htyeq]; exact haint
      obtain ⟨hIC, _⟩ := sharesToAssetsDeposit_integral_canonical v shares a hvint hsad
      have hexact : a.ExactCanonical := Or.inr ⟨hIC, by rw [ha0]; exact Nat.zero_le _⟩
      obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical a .to_nearest hexact
      have hcNeq : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
      rw [← hcNeq]; exact ⟨hval, hnorm⟩
    · have hafr : a.integral = false := by
        cases hb : a.integral with
        | false => rfl
        | true => exact absurd hb haint
      have hczero := STAmount.toNumber_zero_fractional a .to_nearest hafr ha0
      have hcNeq : cN = Number.zero := by rw [hczero] at hcN; exact (Except.ok.inj hcN).symm
      subst hcNeq
      refine ⟨?_, Or.inl rfl⟩
      rw [Number.toRat_zero, STAmount.toRat_signed, ha0]; simp

/-- **The charge is nonnegative.** `sharesToAssetsDeposit` prices positive shares
into an asset amount, either the exact integral value (empty integral branch,
sign-cleared) or the upward `ofNumber` snap of a nonnegative division result, so it
never goes negative. The fractional empty branch (first deposit into an empty
fractional vault) needs a `canonicalize`-of-sign-cleared-source nonnegativity fact
that lacks a ready lemma; it is left as a documented gap. -/
lemma sharesToAssetsDeposit_nonneg (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    0 ≤ c.toRat := by
  unfold sharesToAssetsDeposit at hsad
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: `c = checked v.numericType shares.mantissa (shares.exponent - scale) false`
    rw [if_pos hmz] at hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hint : v.numericType.isIntegral = true
    · -- integral: `canonicalize` is value-exact on the sign-cleared, offset-0 source
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
    · -- fractional empty vault: `checked = canonicalize (unchecked ... false)`, and the
      -- sign-cleared source stays nonnegative through the `iou`/`normalize` snap.
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
  · -- nonempty vault: `c = ofNumber v.numericType Q .to_nearest` with `Q ≥ 0`. The
    -- positive, normalized `Q` is read off the `sub`/`mul`/`div` pipeline exactly as
    -- in `sharesToAssetsDeposit_charge_integral_bound` (nav > 0, shares > 0 give
    -- `P, Q > 0`), and `ofNumber_signfalse_nonneg` then yields `0 ≤ c.toRat`.
    -- Reusing that pipeline walk here is the remaining step.
    rw [if_neg hmz] at hsad
    obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
    set navN := v.assetsTotal with hnavN_eq
    obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
    obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
    have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
    rw [hceq] at hc
    by_cases hc0 : c.mValue = 0
    · rw [STAmount.toRat_signed, show c.mValue.toNat = 0 from by rw [hc0]; rfl]; simp
    · -- `Q` is positive and normalized; the upward `ofNumber` snap is nonnegative
      have hApos : 0 < v.toExact.assetsTotal := by
        rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
        · exact h
        · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
      have hST_pos : 0 < v.sharesTotal.toRat := by
        have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
          absurd (v.exact.empty_shares h0).1 (ne_of_gt hApos)
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
      have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
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
      obtain ⟨_, _, _, hnavN_pos⟩ := Vault.depositNav_facts v navN hmz hnavm hnavN_eq
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
      exact STAmount.ofNumber_signfalse_nonneg v.numericType Q .to_nearest c hQnorm hQneg hc

/-- **`toNumber` is value-exact on the RECORDED deposit charge.** `computeDeposit`
prices a charge and the model records it CLAMPED, so `sharesToAssetsDeposit`'s own
exactness lemma no longer applies to what lands in the result — this re-derives it
from whichever clamp branch ran. -/
lemma Vault.deposit_charge_toNumber_facts (v : Vault) (shares priced c : STAmount)
    (cN : Number)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent v.assetsTotal priced = .ok c)
    (hcN : c.toNumber .to_nearest = .ok cN) :
    cN.toRat = c.toRat ∧ cN.isNormalized := by
  have hpnn : 0 ≤ priced.toRat := sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v shares priced hsad
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault: the clamp hands the charge straight back
    have hcp : c = priced :=
      clampToSumExponent_integral_nonneg v.assetsTotal priced c
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl
    rw [hcp] at hcN ⊢
    exact sharesToAssetsDeposit_toNumber_exact v shares priced cN hshc hshnt hsad hcN
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
    exact STAmount.toNumber_zero_facts c .to_nearest cN hcz hcN
  · -- fractional vault, sum branch
    have hshape : c.IOUCanonical ∨ c.mValue = 0 := by
      refine (clampToSumExponent_sum_shape v.assetsTotal priced c v.wf.assetsTotal_norm ?_ hpfrac
        (by simpa using hbr) hcl).2
      by_cases hpz : priced.mValue = 0
      · exact Or.inr hpz
      · rcases sharesToAssetsDeposit_disj_canonical v shares priced hshc hshnt hsad hpz with h | h
        · exact Or.inl h
        · exfalso
          have := h.is_integral
          rw [hpnt] at this
          exact hint this
    rcases hshape with h | h
    · obtain ⟨sn, hok, hval, hnorm⟩ := STAmount.toNumber_iou_exact c .to_nearest h
      rw [show cN = sn from Except.ok.inj (hcN.symm.trans hok)]
      exact ⟨hval, hnorm⟩
    · exact STAmount.toNumber_zero_facts c .to_nearest cN h hcN

end XRPL.Model.SingleAssetVault
