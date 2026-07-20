import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Vault.Common.DepositChargeProofs
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Protocol.Number.Div.Common.Decompose
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose

/-! # Wiring the `Vault.deposit` accuracy headlines

Proof bodies for the deposit accuracy headlines that derive the rounded amount's
canonicity from the raw input via the `roundToVaultExponent` keystone
(`RoundCanonical.lean`) and reuse the proven exchange cores. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **The issued shares are strictly positive.** `assetsToSharesDeposit` prices a
positive canonical `amount` into a nonnegative integer count, and a nonzero result
is therefore positive. The nonnegativity walks the exact `mul`/`div` chain: the
nonzero operands come from the successful division (never a zero divisor) and the
nonzero result (never a zero numerator), so no deep-underflow floor is needed. -/
lemma assetsToSharesDeposit_pos (v : Vault) (hv : v.Lawful) (amount shares : STAmount)
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
    obtain ⟨navN, hnavN, hok⟩ := bind_ok_peel _ _ _ hok
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
    have hnavnorm : navN.isNormalized :=
      operator_sub_isNormalized_to_nearest_sz _ _ _ hv.wf.assetsTotal_norm
        hv.wf.interestUnrealized_norm hnavN
    have hnavm : navN.mantissa_ ≠ 0 :=
      operator_div_divisor_ne_zero P navN T0 .to_nearest hnavnorm hT0
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hnavm) hT0 hT0m
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    obtain ⟨hSTm, hanm⟩ :=
      operator_mul_operands_ne_zero hv.wf.sharesTotal_norm hannorm hP hPm
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        hv.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
    have hT0norm : T0.isNormalized :=
      operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hnavm hT0 hT0m
    -- value chain: every stage is nonnegative
    have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact le_of_lt hpos
    have hSTnn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hPnn : 0 ≤ P.toRat := by
      have hb : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
        operator_mul_rounds_to_nearest v.sharesTotal amountN P
          hv.wf.sharesTotal_norm hannorm hP hPm
      rw [abs_of_nonneg (mul_nonneg hSTnn hann)] at hb
      have hab := abs_le.mp hb
      nlinarith [mul_nonneg hSTnn hann]
    obtain ⟨_, _, _, hnavpos⟩ := Vault.depositNav_facts v hv navN hmz hnavm hnavN
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
    have hcz : a.FracCanonZero := ⟨(hc.2 hfr).is_fractional, Or.inl (hc.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨rounded', hrx, hlast⟩ := bind_ok_peel _ _ _ hok
    have heq : rounded' = r := Except.ok.inj (show Except.ok rounded' = .ok r from hlast)
    rw [heq] at hrx
    rw [(STAmount.roundToExponent_fczr a r postScale .downward hcz hrx).1]
    exact hcz.1.symm

/-- Proof body of `Vault.deposit_charge_integral`. The rounded amount equals the
integral input (identity pass), the issued shares are a positive `int64` count,
and the proven `sharesToAssetsDeposit_charge_integral_bound` bounds the overcharge. -/
theorem Vault.deposit_charge_integral_proof (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult) (hv : v.Lawful) (hcanon : amountDeposit.Canonical)
    (hint : v.numericType.isIntegral = true) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε := by
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, hanz, _, _, _, hcd, _, _, _, _, _, _, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount c sh (hcd rfl)
  -- the charge is the vault's integral type, and it is comparable to `amount`
  have hcty : c.mNumericType = v.numericType :=
    (sharesToAssetsDeposit_integral_canonical v shares c hint hsad).2
  have hcmp : STAmount.areComparable amount c = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; simpa using hcond
  have hamt_int : amount.integral = true := by
    have htyeq : amount.mNumericType = c.mNumericType := by
      have := hcmp; unfold STAmount.areComparable at this
      exact beq_iff_eq.mp this
    unfold STAmount.integral; rw [htyeq, hcty]; exact hint
  -- so the input is integral, `roundToVaultExponent` was the identity
  have hameq : amount = amountDeposit := by
    have htype := roundToVaultExponent_mNumericType amountDeposit v.assetsTotal amount hcanon hround
    have hadint : amountDeposit.integral = true := by
      unfold STAmount.integral at hamt_int ⊢; rw [← htype]; exact hamt_int
    rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hadint] at hround
    exact (Except.ok.inj hround).symm
  rw [hameq] at hats
  -- issued shares: positive `int64` canonical count
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amountDeposit shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v hv amountDeposit shares hcanon hpos hats hsz
  -- apply the proven charge bound
  obtain ⟨_, hbound⟩ :=
    sharesToAssetsDeposit_charge_integral_bound v hv amountDeposit shares c hint hshc hshnt hshpos hsad
  have hcr : r.amountDeposit' = c := by rw [hr]
  have hsr : r.sharesIssued = shares := by rw [hr, hsheq]
  rw [hcr, hsr]
  exact hbound

end XRPL.Model.SingleAssetVault
