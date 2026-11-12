import XRPL.Properties.Vault.Proofs.Support.NoOverflow
import XRPL.Properties.Vault.Proofs.NoInternalErrors
import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Vault.Proofs.DepositAccuracy

/-! # No overflow within the Open limit

A deposit, a withdrawal and a clawback return `tecPATH_DRY` only when a step of their pricing overflows. On a
reachable vault every share is worth at least a base unit and the cash is at most `9·10^15` base units, so an amount
within the Open limit prices at most `9·10^15` shares, and every intermediate value stays far below the `int64` and
`Number` limits. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol



/-- The facts of a reachable vault the overflow bounds use: the cash and the share total are nonnegative, at most
`9·10^15` base units and shares, and each share is worth at least a base unit. -/
private lemma Vault.Reachable.size_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    0 ≤ v.assetsAvailable.toRat ∧ v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent ∧
      0 ≤ v.sharesTotal.toRat ∧ v.sharesTotal.toRat ≤ 9 * 10 ^ 15 ∧
      v.sharesTotal.toRat * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat ∧
      (v.sharesTotal.mantissa_ ≠ 0 → 1 ≤ v.sharesTotal.toRat) ∧
      (0 < v.assetsAvailable.toRat → 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat) ∧
      (-10 : ℤ) ≤ v.baseExponent ∧ v.baseExponent ≤ 0 := by
  have hz := Vault.Reachable.openZone v t0 hr
  have hinv := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf] at hinv
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hS0 := v.wf.sharesTotal_nonneg
  have hb := v.baseExponent_bounds
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA9 : v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    have := hz.assetsAvailable_le_openLimit
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at this
  refine ⟨hA0, hA9, hS0, ?_, hinv, fun hm => ?_, fun hp => (hz.cash_ge hp).1, hb.1, hb.2.1⟩
  · by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_right hc hbp]
  · have hpos : 0 < v.sharesTotal.toRat :=
      lt_of_le_of_ne hS0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hm))
    have hden := v.wf.sharesTotal_int
    have hnum : (v.sharesTotal.toRat.num : ℚ) = v.sharesTotal.toRat := Rat.coe_int_num_of_den_eq_one hden
    rw [← hnum] at hpos ⊢
    have : 0 < v.sharesTotal.toRat.num := by exact_mod_cast hpos
    exact_mod_cast (show (1 : ℤ) ≤ v.sharesTotal.toRat.num by omega)

/-- On a reachable vault the shares an amount within the Open limit names never overflow. -/
private lemma Vault.Reachable.assetsToSharesWithdraw_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (X : STAmount) (w : Bool) (hX : X.CanonicalOrZero) (hX0 : 0 ≤ X.toRat)
    (hXl : X.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) :
    assetsToSharesWithdraw v X true w ≠ .error .overflow := by
  have hz := Vault.Reachable.openZone v t0 hr
  intro h
  unfold assetsToSharesWithdraw at h
  rw [hz.assetsTotalForWithdrawal_eq w] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hXl' : X.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hXl
  split at h
  · cases h
  rename_i hAm
  have hAm' : v.assetsAvailable.mantissa_ ≠ 0 := by simpa using hAm
  have hApos : 0 < v.assetsAvailable.toRat :=
    lt_of_le_of_ne hA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm'))
  have hAb := hAge hApos
  obtain ⟨xn, hxn⟩ := hX.toNumber_ok
  obtain ⟨hxv, hxnn⟩ := hX.toNumber_exact xn hxn
  rw [hxn] at h
  simp only at h
  have h200 : (10 : ℚ) ^ 17 < 10 ^ (200 : ℤ) := by norm_num
  obtain ⟨P, hP⟩ := Number.operator_mul_ok_of_size v.sharesTotal xn .to_nearest v.wf.sharesTotal_norm hxnn
    (by rw [abs_of_nonneg hS0]; linarith) (by rw [hxv, abs_of_nonneg hX0]; nlinarith)
    (fun hm => by
      rw [abs_of_nonneg hS0]
      exact le_trans (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) (hS1 hm))
    (fun hm => by
      have hne : X.toRat ≠ 0 := by rw [← hxv]; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hm
      have hm' : X.mValue ≠ 0 := fun h0 => hne ((STAmount.toRat_eq_zero_iff _).mpr h0)
      rw [hxv]
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) (STAmount.CanonicalOrZero.abs_ge X hX hm'))
  rw [hP] at h
  simp only at h
  cases hQ : P.operator_div v.assetsAvailable .to_nearest with
  | error e => rw [hQ] at h; cases h; exact Number.operator_div_ne_overflow _ _ _ hQ
  | ok Q =>
    rw [hQ] at h
    simp only at h
    obtain ⟨hQn, hQ0, hQl⟩ := Number.mul_div_facts _ _ _ P Q v.wf.sharesTotal_norm hxnn v.wf.assetsAvailable_norm
      hS0 (by rw [hxv]; exact hX0) hApos hP hQ
    cases hT : Q.truncate with
    | error e => rw [hT] at h; cases h; exact Number.truncate_ne_overflow _ hT
    | ok T =>
      rw [hT] at h
      simp only at h
      obtain ⟨hTv, -⟩ := Number.truncate_floor Q T hQn (Number.negative_false_of_nonneg Q hQn hQ0) hT
      have hTn := Number.truncate_isNormalized hQn hT
      refine STAmount.ofNumber_ne_overflow .int64 T .to_nearest hTn ?_ h
      -- the quotient is at most `9·10^15` shares: a share is worth at least a base unit
      have hq : v.sharesTotal.toRat * xn.toRat / v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 := by
        rw [div_le_iff₀ hApos, hxv]
        calc v.sharesTotal.toRat * X.toRat ≤ v.sharesTotal.toRat * (9 * 10 ^ 15 * 10 ^ v.baseExponent) :=
              mul_le_mul_of_nonneg_left hXl' hS0
          _ = 9 * 10 ^ 15 * (v.sharesTotal.toRat * 10 ^ v.baseExponent) := by ring
          _ ≤ 9 * 10 ^ 15 * v.assetsAvailable.toRat := by nlinarith
      have hfl0 : (0 : ℚ) ≤ ⌊Q.toRat⌋ := by exact_mod_cast Int.floor_nonneg.mpr hQ0
      have hfl := Int.floor_le Q.toRat
      rw [hTv, abs_of_nonneg hfl0]
      have : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 2 := by norm_num
      nlinarith

/-- On a reachable vault the price of a share amount whose worth is at most `10^17` never overflows. -/
private lemma Vault.Reachable.sharesToAssetsWithdraw_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (sh : STAmount) (w : Bool) (hsh : sh.CanonicalOrZero) (hs0 : 0 ≤ sh.toRat) (hsl : sh.toRat ≤ 10 ^ 17)
    (hq : v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17) :
    v.sharesToAssetsWithdraw sh w ≠ .error .overflow := by
  have hz := Vault.Reachable.openZone v t0 hr
  intro h
  unfold Vault.sharesToAssetsWithdraw at h
  rw [hz.assetsTotalForWithdrawal_eq w] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hb10 : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) hblo
  split at h
  · cases h
  rename_i hAm
  have hAm' : v.assetsAvailable.mantissa_ ≠ 0 := by simpa using hAm
  have hApos : 0 < v.assetsAvailable.toRat :=
    lt_of_le_of_ne hA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm'))
  have hAb := hAge hApos
  -- a vault with cash has shares
  have hSm : v.sharesTotal.mantissa_ ≠ 0 := by
    intro h0
    have hz0 := Number.eq_zero_of_mantissa_zero _ v.wf.sharesTotal_norm h0
    exact hAm' (by rw [(v.valid.empty_shares hz0).1]; rfl)
  have hSpos : 0 < v.sharesTotal.toRat := lt_of_lt_of_le one_pos (hS1 hSm)
  obtain ⟨sn, hsn⟩ := hsh.toNumber_ok
  obtain ⟨hsv, hsnn⟩ := hsh.toNumber_exact sn hsn
  rw [hsn] at h
  simp only at h
  have h200 : (10 : ℚ) ^ 17 < 10 ^ (200 : ℤ) := by norm_num
  obtain ⟨P, hP⟩ := Number.operator_mul_ok_of_size v.assetsAvailable sn .to_nearest v.wf.assetsAvailable_norm hsnn
    (by rw [abs_of_nonneg hA0]; nlinarith) (by rw [hsv, abs_of_nonneg hs0]; linarith)
    (fun _ => by
      rw [abs_of_nonneg hA0]
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) (le_trans hb10 hAb))
    (fun hm => STAmount.CanonicalOrZero.number_ge sh hsh sn hsv hm)
  rw [hP] at h
  simp only at h
  cases hQ : P.operator_div v.sharesTotal .to_nearest with
  | error e => rw [hQ] at h; cases h; exact Number.operator_div_ne_overflow _ _ _ hQ
  | ok Q =>
    rw [hQ] at h
    simp only at h
    obtain ⟨hQn, hQ0, hQl⟩ := Number.mul_div_facts _ _ _ P Q v.wf.assetsAvailable_norm hsnn
      v.wf.sharesTotal_norm hA0 (by rw [hsv]; exact hs0) hSpos hP hQ
    have hne : STAmount.ofNumber v.numericType Q .to_nearest ≠ .error .overflow := by
      refine STAmount.ofNumber_ne_overflow _ Q .to_nearest hQn ?_
      rw [abs_of_nonneg hQ0]
      rw [hsv] at hQl
      have : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 2 := by norm_num
      nlinarith
    split at h
    · rename_i e he; cases h; exact hne he
    · cases h

/-- The base grid and the share scale cancel: an IOU base unit is `10^-scale`, an integral vault has scale `0`. -/
private lemma Vault.baseExponent_add_scale (v : Vault) : v.baseExponent + (v.scale.toNat : ℤ) = 0 := by
  unfold Vault.baseExponent NumericType.baseExponent
  split
  · rename_i hint; rw [v.wf.scale_integral hint]; rfl
  · ring

/-- On a reachable vault the shares a deposit within the Open limit prices never overflow. -/
private lemma Vault.Reachable.assetsToSharesDeposit_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (ra : STAmount) (hc : ra.Canonical) (hpos : 0 < ra.toRat)
    (hl : ra.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) :
    assetsToSharesDeposit v ra ≠ .error .overflow := by
  have hz := Vault.Reachable.openZone v t0 hr
  intro h
  unfold assetsToSharesDeposit at h
  rw [hz.assetsTotal_eq] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hl' : ra.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hl
  have hneg : ra.mIsNegative = false := STAmount.mIsNegative_false_of_pos ra hpos
  have hrm : ra.mValue ≠ 0 := fun h0 => by rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hpos; exact lt_irrefl _ hpos
  obtain ⟨hmax, helo, hehi⟩ := STAmount.Canonical.mantissa_exponent ra hc
  have hscale : (v.scale.toNat : ℤ) ≤ 10 := by have := v.baseExponent_add_scale; omega
  split at h
  · -- an empty vault issues `⌊ra·10^scale⌋` shares, at most `9·10^15`
    have hmv1 : 1 ≤ ra.mantissa.toNat := by
      have : ra.mValue.toNat ≠ 0 := fun h0 => hrm (by rw [← UInt64.toNat_inj]; simpa using h0)
      show 1 ≤ ra.mValue.toNat; omega
    obtain ⟨M, e1, hdn, hMval, hMnorm⟩ := doNormalize_largeRange_exact false ra.mantissa
      (ra.exponent + (v.scale.toNat : ℤ)) .to_nearest hmv1 hmax
      (by have : (0 : ℤ) ≤ (v.scale.toNat : ℤ) := by positivity
          unfold minExponent; omega)
      (by unfold maxExponent; omega)
    have hdn' : Number.normalized false ra.mantissa (ra.exponent + (v.scale.toNat : ℤ))
        largeRange.min largeRange.max .to_nearest = .ok (⟨false, M, e1⟩ : Number) := hdn
    rw [hdn'] at h
    simp only at h
    cases hn2 : (⟨false, M, e1⟩ : Number).truncate with
    | error e => rw [hn2] at h; cases h; exact Number.truncate_ne_overflow _ hn2
    | ok n2 =>
      rw [hn2] at h
      simp only at h
      have hn1v : (⟨false, M, e1⟩ : Number).toRat = ra.toRat * 10 ^ (v.scale.toNat : ℤ) := by
        rw [Number.toRat_of_nonneg _ rfl, hMval, STAmount.toRat_of_nonneg ra hneg]
        show (ra.mValue.toNat : ℚ) * 10 ^ (ra.mOffset + (v.scale.toNat : ℤ))
          = (ra.mValue.toNat : ℚ) * 10 ^ ra.mOffset * 10 ^ (v.scale.toNat : ℤ)
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
      obtain ⟨hn2v, -⟩ := Number.truncate_floor _ n2 hMnorm rfl hn2
      have hn2n := Number.truncate_isNormalized hMnorm hn2
      have hbound : |n2.toRat| < 9 * 10 ^ 18 := by
        have h1 : ra.toRat * 10 ^ (v.scale.toNat : ℤ) ≤ 9 * 10 ^ 15 := by
          have hc1 : (10 : ℚ) ^ v.baseExponent * 10 ^ (v.scale.toNat : ℤ) = 1 := by
            rw [← zpow_add₀ (by norm_num), v.baseExponent_add_scale, zpow_zero]
          have hsp : (0 : ℚ) < 10 ^ (v.scale.toNat : ℤ) := zpow_pos (by norm_num) _
          calc ra.toRat * 10 ^ (v.scale.toNat : ℤ)
              ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent * 10 ^ (v.scale.toNat : ℤ) :=
                mul_le_mul_of_nonneg_right hl' hsp.le
            _ = 9 * 10 ^ 15 := by rw [mul_assoc, hc1, mul_one]
        have h0 : (0 : ℚ) ≤ ra.toRat * 10 ^ (v.scale.toNat : ℤ) := by positivity
        have hfl := Int.floor_le (ra.toRat * 10 ^ (v.scale.toNat : ℤ))
        have hfl0 : (0 : ℚ) ≤ ⌊ra.toRat * 10 ^ (v.scale.toNat : ℤ)⌋ := by
          exact_mod_cast Int.floor_nonneg.mpr h0
        rw [hn2v, hn1v, abs_of_nonneg hfl0]
        linarith
      have hne := STAmount.ofNumber_ne_overflow .int64 n2 .to_nearest hn2n hbound
      split at h
      · rename_i e he; cases h; exact hne he
      · cases h
  · -- a nonempty vault prices `S·ra/AA` shares, at most `9·10^15`: a share is worth at least a base unit
    rename_i hAm
    have hApos : 0 < v.assetsAvailable.toRat :=
      lt_of_le_of_ne hA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))
    have hAb := hAge hApos
    have hX : ra.CanonicalOrZero := Or.inl hc
    obtain ⟨xn, hxn⟩ := hX.toNumber_ok
    obtain ⟨hxv, hxnn⟩ := hX.toNumber_exact xn hxn
    rw [hxn] at h
    simp only at h
    have h200 : (10 : ℚ) ^ 17 < 10 ^ (200 : ℤ) := by norm_num
    obtain ⟨P, hP⟩ := Number.operator_mul_ok_of_size v.sharesTotal xn .to_nearest v.wf.sharesTotal_norm hxnn
      (by rw [abs_of_nonneg hS0]; linarith) (by rw [hxv, abs_of_nonneg hpos.le]; nlinarith)
      (fun hm => by
        rw [abs_of_nonneg hS0]
        exact le_trans (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) (hS1 hm))
      (fun hm => STAmount.CanonicalOrZero.number_ge ra hX xn hxv hm)
    rw [hP] at h
    simp only at h
    cases hQ : P.operator_div v.assetsAvailable .to_nearest with
    | error e => rw [hQ] at h; cases h; exact Number.operator_div_ne_overflow _ _ _ hQ
    | ok Q =>
      rw [hQ] at h
      simp only at h
      obtain ⟨hQn, hQ0, hQl⟩ := Number.mul_div_facts _ _ _ P Q v.wf.sharesTotal_norm hxnn v.wf.assetsAvailable_norm
        hS0 (by rw [hxv]; exact hpos.le) hApos hP hQ
      cases hT : Q.truncate with
      | error e => rw [hT] at h; cases h; exact Number.truncate_ne_overflow _ hT
      | ok T =>
        rw [hT] at h
        simp only at h
        obtain ⟨hTv, -⟩ := Number.truncate_floor Q T hQn (Number.negative_false_of_nonneg Q hQn hQ0) hT
        have hTn := Number.truncate_isNormalized hQn hT
        have hq : v.sharesTotal.toRat * xn.toRat / v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 := by
          rw [div_le_iff₀ hApos, hxv]
          calc v.sharesTotal.toRat * ra.toRat ≤ v.sharesTotal.toRat * (9 * 10 ^ 15 * 10 ^ v.baseExponent) :=
                mul_le_mul_of_nonneg_left hl' hS0
            _ = 9 * 10 ^ 15 * (v.sharesTotal.toRat * 10 ^ v.baseExponent) := by ring
            _ ≤ 9 * 10 ^ 15 * v.assetsAvailable.toRat := by nlinarith
        have hbound : |T.toRat| < 9 * 10 ^ 18 := by
          have hfl0 : (0 : ℚ) ≤ ⌊Q.toRat⌋ := by exact_mod_cast Int.floor_nonneg.mpr hQ0
          have hfl := Int.floor_le Q.toRat
          rw [hTv, abs_of_nonneg hfl0]
          have : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 2 := by norm_num
          nlinarith
        have hne := STAmount.ofNumber_ne_overflow .int64 T .to_nearest hTn hbound
        split at h
        · rename_i e he; cases h; exact hne he
        · cases h

/-- On a reachable vault the price of the shares a deposit issues never overflows, while their worth is at most
`10^17`. -/
private lemma Vault.Reachable.sharesToAssetsDeposit_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (sh : STAmount) (hshc : sh.IntegralCanonical) (hsht : sh.mNumericType = .int64) (hs0 : 0 ≤ sh.toRat)
    (hsl : sh.toRat ≤ 10 ^ 17) (hq : v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17) :
    sharesToAssetsDeposit v sh ≠ .error .overflow := by
  have hz := Vault.Reachable.openZone v t0 hr
  intro h
  unfold sharesToAssetsDeposit at h
  rw [hz.assetsTotal_eq] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb10 : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) hblo
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hshm : sh.mValue.toNat ≤ maxRep.toNat := by
    have := hshc.in_range; rw [hsht] at this; exact le_trans this (by decide)
  split at h
  · -- an empty vault prices the shares at one base unit each, exactly
    have hscale : (v.scale.toNat : ℤ) ≤ 10 := by have := v.baseExponent_add_scale; omega
    have hne : STAmount.checked v.numericType sh.mantissa (sh.exponent - (v.scale.toNat : ℤ)) false .to_nearest
        ≠ .error .overflow := by
      have hexp : sh.exponent = 0 := hshc.offset_zero
      by_cases hint : v.numericType.isIntegral = true
      · rw [hexp, v.wf.scale_integral hint]
        exact STAmount.checked_integral_ne_overflow _ hint _ _ _ hshm
      · cases hnt : v.numericType with
        | integral => rw [hnt] at hint; exact absurd rfl hint
        | fractional =>
          refine STAmount.checked_fractional_ne_overflow _ _ _ _
            (show sh.mValue.toNat < 2 ^ 63 by rw [maxRep_val] at hshm; omega) (fun _ => ?_)
          rw [hexp]
          unfold minExponent
          constructor <;> omega
    split at h
    · rename_i e he; cases h; exact hne he
    · cases h
  · rename_i hAm
    have hApos : 0 < v.assetsAvailable.toRat :=
      lt_of_le_of_ne hA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))
    have hAb := hAge hApos
    have hSm : v.sharesTotal.mantissa_ ≠ 0 := by
      intro h0
      have hz0 := Number.eq_zero_of_mantissa_zero _ v.wf.sharesTotal_norm h0
      exact hAm (by rw [(v.valid.empty_shares hz0).1]; rfl)
    have hSpos : 0 < v.sharesTotal.toRat := lt_of_lt_of_le one_pos (hS1 hSm)
    have hsh : sh.CanonicalOrZero := Or.inl (hshc.canonical (by rw [hsht]; decide))
    obtain ⟨sn, hsn⟩ := hsh.toNumber_ok
    obtain ⟨hsv, hsnn⟩ := hsh.toNumber_exact sn hsn
    rw [hsn] at h
    simp only at h
    have h200 : (10 : ℚ) ^ 17 < 10 ^ (200 : ℤ) := by norm_num
    obtain ⟨P, hP⟩ := Number.operator_mul_ok_of_size v.assetsAvailable sn .to_nearest v.wf.assetsAvailable_norm
      hsnn (by rw [abs_of_nonneg hA0]; nlinarith) (by rw [hsv, abs_of_nonneg hs0]; linarith)
      (fun _ => by
        rw [abs_of_nonneg hA0]
        exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) (le_trans hb10 hAb))
      (fun hm => STAmount.CanonicalOrZero.number_ge sh hsh sn hsv hm)
    rw [hP] at h
    simp only at h
    cases hQ : P.operator_div v.sharesTotal .to_nearest with
    | error e => rw [hQ] at h; cases h; exact Number.operator_div_ne_overflow _ _ _ hQ
    | ok Q =>
      rw [hQ] at h
      simp only at h
      obtain ⟨hQn, hQ0, hQl⟩ := Number.mul_div_facts _ _ _ P Q v.wf.assetsAvailable_norm hsnn
        v.wf.sharesTotal_norm hA0 (by rw [hsv]; exact hs0) hSpos hP hQ
      have hne : STAmount.ofNumber v.numericType Q .to_nearest ≠ .error .overflow := by
        refine STAmount.ofNumber_ne_overflow _ Q .to_nearest hQn ?_
        rw [abs_of_nonneg hQ0]
        rw [hsv] at hQl
        have : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 2 := by norm_num
        nlinarith
      split at h
      · rename_i e he; cases h; exact hne he
      · cases h

/-- On a reachable vault the dust check of an amount at most `9·10^17` in size never reports an overflow. -/
private lemma Vault.Reachable.checkDebitNotDust_ne_path_dry (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : Number) (hn : amount.isNormalized) (hl : |amount.toRat| ≤ 9 * 10 ^ 17) :
    v.checkDebitNotDust amount ≠ .ok .tecPATH_DRY := by
  obtain ⟨hA0, hA9, -, -, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hA9' : |v.assetsAvailable.toRat| ≤ 9 * 10 ^ 15 := by rw [abs_of_nonneg hA0]; nlinarith
  obtain ⟨r, hrs⟩ := Number.operator_sub_ok_of_size v.assetsAvailable amount .to_nearest v.wf.assetsAvailable_norm hn
    (by linarith [show (9 : ℚ) * 10 ^ 15 < 10 ^ (200 : ℤ) by norm_num])
    (by linarith [show (9 : ℚ) * 10 ^ 17 < 10 ^ (200 : ℤ) by norm_num])
  have hrn : r.isNormalized := Number.operator_add_isNormalized_any _ _ r _ v.wf.assetsAvailable_norm
    (Number.operator_neg_isNormalized _ hn) hrs
  have hrl : |r.toRat| ≤ 10 ^ 18 := Number.abs_le_of_rounded r _
    (operator_add_rounded_to_nearest _ _ r v.wf.assetsAvailable_norm (Number.operator_neg_isNormalized _ hn) hrs)
    (by
      rw [Number.toRat_neg]
      calc |v.assetsAvailable.toRat + -amount.toRat| ≤ |v.assetsAvailable.toRat| + |-amount.toRat| :=
            abs_add_le _ _
        _ ≤ 10 ^ 18 := by rw [abs_neg]; linarith)
  have hcash := STAmount.ofNumber_ne_overflow v.numericType v.assetsAvailable .to_nearest
    v.wf.assetsAvailable_norm (by linarith)
  have hrest := STAmount.ofNumber_ne_overflow v.numericType r .to_nearest hrn (by linarith)
  intro h
  simp only [Vault.checkDebitNotDust, bind, Except.bind, pure, Except.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  walk_ok
  all_goals (obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›; simp_all)

/-- The shares a deposit within the Open limit issues on a reachable vault: a canonical count at most `10^17`, worth
at most `10^17`. -/
private lemma Vault.Reachable.deposit_shares_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (ra sh : STAmount) (hc : ra.Canonical) (hpos : 0 < ra.toRat) (hl : ra.toRat ≤ 9 * 10 ^ (15 + v.baseExponent))
    (hs : assetsToSharesDeposit v ra = .ok sh) (hsz : sh.isZero = false) :
    sh.IntegralCanonical ∧ sh.mNumericType = .int64 ∧ 0 ≤ sh.toRat ∧ sh.toRat ≤ 10 ^ 17 ∧
      v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17 := by
  have hz := Vault.Reachable.openZone v t0 hr
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hl' : ra.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hl
  obtain ⟨hshc, hsht⟩ := assetsToSharesDeposit_int64_canonical v ra sh hs
  have hsp := assetsToSharesDeposit_pos v ra sh hc hpos hs hsz
  obtain ⟨q, hqv, hqb, -⟩ := DepTight.shares_spec_exact v ra sh hc hpos _ hz.assetsTotal_eq hs hsz
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hεo : (0 : ℚ) ≤ sharesOverε ∧ sharesOverε ≤ 1 := by unfold sharesOverε; constructor <;> norm_num
  have hsq : sh.toRat ≤ v.idealSharesDepositAt v.assetsAvailable.toRat ra.toRat * (1 + sharesOverε) := by
    rw [hqv]
    have h1 := Int.floor_le q
    have h2 := (abs_le.mp hqb).2
    linarith
  refine ⟨hshc, hsht, hsp.le, ?_, ?_⟩
  · -- the ideal count is at most `9·10^15`
    have hI : v.idealSharesDepositAt v.assetsAvailable.toRat ra.toRat ≤ 9 * 10 ^ 15 := by
      unfold RawVault.idealSharesDepositAt
      split
      · have hc1 : (10 : ℚ) ^ v.baseExponent * 10 ^ (v.scale.toNat : ℤ) = 1 := by
          rw [← zpow_add₀ (by norm_num), v.baseExponent_add_scale, zpow_zero]
        have hsp' : (0 : ℚ) < 10 ^ (v.scale.toNat : ℤ) := zpow_pos (by norm_num) _
        rw [← zpow_natCast]
        calc ra.toRat * 10 ^ (v.scale.toNat : ℤ)
            ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent * 10 ^ (v.scale.toNat : ℤ) :=
              mul_le_mul_of_nonneg_right hl' hsp'.le
          _ = 9 * 10 ^ 15 := by rw [mul_assoc, hc1, mul_one]
      · rename_i hA
        have hApos : 0 < v.assetsAvailable.toRat := lt_of_le_of_ne hA0 (Ne.symm hA)
        rw [hST, div_le_iff₀ hApos]
        calc v.sharesTotal.toRat * ra.toRat ≤ v.sharesTotal.toRat * (9 * 10 ^ 15 * 10 ^ v.baseExponent) :=
              mul_le_mul_of_nonneg_left hl' hS0
          _ = 9 * 10 ^ 15 * (v.sharesTotal.toRat * 10 ^ v.baseExponent) := by ring
          _ ≤ 9 * 10 ^ 15 * v.assetsAvailable.toRat := by nlinarith
    nlinarith
  · -- their worth is at most the amount, up to `sharesOverε`
    by_cases hA : v.assetsAvailable.toRat = 0
    · rw [hA, zero_mul, zero_div]; norm_num
    by_cases hS : v.sharesTotal.toRat = 0
    · rw [hS, div_zero]; norm_num
    have hApos : 0 < v.assetsAvailable.toRat := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hSpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne hS0 (Ne.symm hS)
    unfold RawVault.idealSharesDepositAt at hsq
    rw [if_neg hA, hST] at hsq
    rw [div_le_iff₀ hSpos]
    have h1 : v.assetsAvailable.toRat * sh.toRat ≤
        v.assetsAvailable.toRat * (v.sharesTotal.toRat * ra.toRat / v.assetsAvailable.toRat * (1 + sharesOverε)) :=
      mul_le_mul_of_nonneg_left hsq hA0
    have h2 : v.assetsAvailable.toRat * (v.sharesTotal.toRat * ra.toRat / v.assetsAvailable.toRat * (1 + sharesOverε))
        = v.sharesTotal.toRat * (ra.toRat * (1 + sharesOverε)) := by field_simp
    have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
    have h3 : ra.toRat * (1 + sharesOverε) ≤ 10 ^ 17 := by nlinarith
    rw [h2] at h1
    nlinarith

/-- On a reachable vault the charge of a deposit within the Open limit, clamped onto the new total, never
overflows. -/
private lemma Vault.Reachable.deposit_charge_clamp_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (ra : STAmount) (hc : ra.Canonical) (hpos : 0 < ra.toRat) (hty : ra.mNumericType = v.numericType)
    (hl : ra.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (sh c : STAmount) (b : Bool) (A : Number)
    (hs : assetsToSharesDeposit v ra = .ok sh) (hsz' : ¬ sh.isZero = true)
    (hp : sharesToAssetsDeposit v sh = .ok c) (hgt : c.operator_gt ra = .ok b) (hb : ¬ b = true)
    (hat : v.assetsTotal = .ok A) : clampToSumExponent A c v.baseExponent ≠ .error .overflow := by
  have hz := Vault.Reachable.openZone v t0 hr
  have hmax := Vault.maxValue_fits_of_canonical v ra hc hty
  obtain ⟨hA0, hA9, -, -, -, -, -, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hA17 : |v.assetsAvailable.toRat| ≤ 10 ^ 17 := by rw [abs_of_nonneg hA0]; nlinarith
  have hl' : ra.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hl
  have hbr := v.baseExponent_range
  have hat' : v.assetsTotal = .ok v.assetsAvailable := hz.assetsTotal_eq
  rw [hat', Except.ok.injEq] at hat
  subst hat
  have hsz : sh.isZero = false := by simpa using hsz'
  obtain ⟨hshc, hsht⟩ := assetsToSharesDeposit_int64_canonical v ra sh hs
  have hshp := assetsToSharesDeposit_pos v ra sh hc hpos hs hsz
  have hgt' : c.operator_gt ra = .ok false := by rw [hgt]; simpa using hb
  have hcle := (DepAcc.Vault.deposit_priced_le v sh c ra hshc hsht hp hc hpos hgt').1
  have hc0 := sharesToAssetsDeposit_nonneg v sh c hshc hsht hshp hp
  have hct := sharesToAssetsDeposit_mNumericType v sh c hp
  have hcc : c.CanonicalOrZero := by
    rcases sharesToAssetsDeposit_exactCanonical_or_zero v sh c hshc hsht hp with hex | hz0
    · left
      rcases hex with hio | ⟨hic, -⟩
      · refine ⟨fun hi => ?_, fun _ => hio⟩
        exact absurd hi (by unfold STAmount.integral; rw [hio.is_fractional]; decide)
      · exact hic.canonical (by rw [hct]; exact hmax (by rw [← hct]; exact hic.is_integral))
    · right; simp [STAmount.isZero, hz0]
  exact clampToSumExponent_ne_overflow _ c _ v.wf.assetsAvailable_norm hA17 hcc
    (by rw [abs_of_nonneg hc0]; nlinarith) hbr.1 (by omega)

/-- On a reachable vault the share and charge computation of a deposit within the Open limit never overflows. -/
private lemma Vault.Reachable.computeDeposit_ne_path_dry (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (ra : STAmount) (isDonation : Bool) (hc : ra.Canonical) (hpos : 0 < ra.toRat)
    (hty : ra.mNumericType = v.numericType) (hl : ra.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) :
    (computeDeposit v ra isDonation).run ≠ .ok (.error .tecPATH_DRY) := by
  have hz := Vault.Reachable.openZone v t0 hr
  have hmax := Vault.maxValue_fits_of_canonical v ra hc hty
  obtain ⟨hA0, hA9, -, -, -, -, -, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hA17 : |v.assetsAvailable.toRat| ≤ 10 ^ 17 := by rw [abs_of_nonneg hA0]; nlinarith
  have hl' : ra.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hl
  have hra17 : |ra.toRat| ≤ 10 ^ 17 := by rw [abs_of_nonneg hpos.le]; nlinarith
  have hbr := v.baseExponent_range
  have hat' : v.assetsTotal = .ok v.assetsAvailable := hz.assetsTotal_eq
  intro h
  simp only [computeDeposit] at h
  unfold_ter at h
  walk_ok
  all_goals (obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›)
  all_goals first
    | exact Vault.Reachable.assetsToSharesDeposit_ne_overflow v t0 hr ra hc hpos hl ‹_›
    | exact STAmount.isFractionalNonPositive_ne_overflow _ ‹_›
    | exact STAmount.operator_lt_ne_overflow _ _ ‹_›
    | (rw [hat'] at *; contradiction)
    | skip
  · -- the price of the issued shares
    obtain ⟨hshc, hsht, hs0, hsl, hq⟩ := Vault.Reachable.deposit_shares_facts v t0 hr ra _ hc hpos hl
      ‹assetsToSharesDeposit v ra = .ok _› (by simpa using ‹¬ STAmount.isZero _ = true›)
    exact Vault.Reachable.sharesToAssetsDeposit_ne_overflow v t0 hr _ hshc hsht hs0 hsl hq ‹_›
  · -- the charge, at most the rounded amount, clamped onto the new total
    exact Vault.Reachable.deposit_charge_clamp_ne_overflow v t0 hr ra hc hpos hty hl _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›
      ‹_› ‹_›
  · -- a donation clamps the rounded amount onto the new total
    obtain ⟨A, hat, hcl⟩ : ∃ A, v.assetsTotal = .ok A ∧ clampToSumExponent A ra v.baseExponent = .error .overflow :=
      ⟨_, ‹_›, ‹_›⟩
    rw [hat', Except.ok.injEq] at hat
    subst hat
    exact clampToSumExponent_ne_overflow _ ra _ v.wf.assetsAvailable_norm hA17 (Or.inl hc)
      (le_trans hra17 (by norm_num)) hbr.1 (by omega) hcl

/-- Deposit on a reachable vault of a canonical amount of its asset within the Open limit -> never `tecPATH_DRY`. -/
lemma Vault.Reachable.deposit_no_path_dry_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amountDeposit.toRat)
    (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hl : amountDeposit.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) :
    (v.deposit amountDeposit isDonation t hpos).run ≠ .ok (.error .tecPATH_DRY) := by
  intro hok
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals try first
    | (rcases Vault.checkOpenLimit_codes _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
    | (rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
    | exact absurd (Vault.roundedDepositAmount_rejected_code_proof v amountDeposit _ ‹_›) (by decide)
  · -- the share cap: at most 9·10^15 shares are outstanding and the deposit mints at most 10^17
    obtain ⟨ra, amounts, hra, hcomp, hcap⟩ : ∃ ra amounts, (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra) ∧
        (computeDeposit v ra isDonation).run = .ok (.ok amounts) ∧
        v.sharesTotal.toRat + amounts.shares.toRat > (maxRep.toNat : ℚ) := ⟨_, _, ‹_›, ‹_›, ‹_›⟩
    obtain ⟨hrcz, -, hr0⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hra
    obtain ⟨A, -, hcl, hrz⟩ := roundedDepositAmount_rounded v amountDeposit ra hra
    have hrm : ra.mValue ≠ 0 := by simpa [STAmount.isZero] using hrz
    have hrc : ra.Canonical := hrcz.resolve_right (by simpa using hrz)
    have hrp : 0 < ra.toRat := lt_of_le_of_ne hr0 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
    have hle := clampToSumExponent_le_abs A amountDeposit ra v.baseExponent (Or.inl hc) v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [abs_of_pos hpos] at hle
    obtain ⟨-, -, -, hS9, -⟩ := Vault.Reachable.size_facts v t0 hr
    have hsh : amounts.shares.toRat ≤ 10 ^ 17 := by
      cases isDonation
      · obtain ⟨_, _, ha2s, hz, _⟩ := computeDeposit_success_reduces v ra amounts hcomp
        exact (Vault.Reachable.deposit_shares_facts v t0 hr ra _ hrc hrp (le_trans hle hl) ha2s hz).2.2.2.1
      · obtain ⟨_, hsh0, _⟩ := computeDeposit_donation_reduces v ra amounts hcomp
        rw [hsh0, STAmount.zero_toRat]; norm_num
    rw [show maxRep.toNat = 2 ^ 63 - 1 from rfl] at hcap
    push_cast at hcap
    linarith
  · -- the rounded amount is a positive canonical amount at most the request
    obtain ⟨ra, hra, hcomp⟩ : ∃ ra, (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra) ∧
        (computeDeposit v ra isDonation).run = .ok (.error .tecPATH_DRY) := ⟨_, ‹_›, ‹_›⟩
    obtain ⟨hrcz, hrt, hr0⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hra
    obtain ⟨A, -, hcl, hrz⟩ := roundedDepositAmount_rounded v amountDeposit ra hra
    have hrm : ra.mValue ≠ 0 := by simpa [STAmount.isZero] using hrz
    have hrc : ra.Canonical := hrcz.resolve_right (by simpa using hrz)
    have hrp : 0 < ra.toRat := lt_of_le_of_ne hr0 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
    have hle := clampToSumExponent_le_abs A amountDeposit ra v.baseExponent (Or.inl hc) v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [abs_of_pos hpos] at hle
    exact Vault.Reachable.computeDeposit_ne_path_dry v t0 hr ra isDonation hrc hrp hrt (le_trans hle hl) hcomp

/-- The withdrawal amount is within the Open limit when it names assets, and at most the share total when it
names shares. -/
private def WithdrawAmount.WithinLimit (amount : WithdrawAmount) (v : Vault) : Prop :=
  match amount with
  | .vaultAssets assets => assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)
  | .vaultShares shares => shares.toRat ≤ v.toExact.sharesTotal

/-- The shares an asset amount within the Open limit names on a reachable vault: a canonical count at most `10^17`,
worth at most `10^17`. -/
private lemma Vault.Reachable.withdraw_shares_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (X sh : STAmount) (w : Bool) (hc : X.Canonical) (hpos : 0 < X.toRat)
    (hl : X.toRat ≤ 9 * 10 ^ (15 + v.baseExponent))
    (hs : assetsToSharesWithdraw v X true w = .ok sh) (hsz : sh.isZero = false) :
    sh.CanonicalOrZero ∧ 0 ≤ sh.toRat ∧ sh.toRat ≤ 10 ^ 17 ∧
      v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17 := by
  have hz := Vault.Reachable.openZone v t0 hr
  obtain ⟨hA0, hA9, hS0, hS9, hinv, hS1, hAge, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hl' : X.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rwa [zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc] at hl
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  obtain ⟨hshc, hsht⟩ := assetsToSharesWithdraw_int64_canonical v X sh true w hs
  obtain ⟨-, hsp, hup, -⟩ := WdTight.shares_bounds v X sh w _ (hz.assetsTotalForWithdrawal_eq w) hpos hc hs hsz
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  unfold RawVault.idealSharesWithdrawAt at hup
  rw [hST] at hup
  have hε : (sharesε : ℚ) ≤ 1 := by unfold sharesε; norm_num
  have hε0 : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  refine ⟨Or.inl (hshc.canonical (by rw [hsht]; decide)), hsp.le, ?_, ?_⟩
  · by_cases hA : v.assetsAvailable.toRat = 0
    · rw [hA, div_zero, zero_mul] at hup; linarith
    have hApos : 0 < v.assetsAvailable.toRat := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hI : v.sharesTotal.toRat * X.toRat / v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 := by
      rw [div_le_iff₀ hApos]
      calc v.sharesTotal.toRat * X.toRat ≤ v.sharesTotal.toRat * (9 * 10 ^ 15 * 10 ^ v.baseExponent) :=
            mul_le_mul_of_nonneg_left hl' hS0
        _ = 9 * 10 ^ 15 * (v.sharesTotal.toRat * 10 ^ v.baseExponent) := by ring
        _ ≤ 9 * 10 ^ 15 * v.assetsAvailable.toRat := by nlinarith
    have hI0 : 0 ≤ v.sharesTotal.toRat * X.toRat / v.assetsAvailable.toRat := by positivity
    nlinarith
  · by_cases hA : v.assetsAvailable.toRat = 0
    · rw [hA, zero_mul, zero_div]; norm_num
    by_cases hS : v.sharesTotal.toRat = 0
    · rw [hS, div_zero]; norm_num
    have hApos : 0 < v.assetsAvailable.toRat := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hSpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne hS0 (Ne.symm hS)
    rw [div_le_iff₀ hSpos]
    have h1 : v.assetsAvailable.toRat * sh.toRat ≤
        v.assetsAvailable.toRat * (v.sharesTotal.toRat * X.toRat / v.assetsAvailable.toRat * (1 + sharesε)) :=
      mul_le_mul_of_nonneg_left hup hA0
    have h2 : v.assetsAvailable.toRat * (v.sharesTotal.toRat * X.toRat / v.assetsAvailable.toRat * (1 + sharesε))
        = v.sharesTotal.toRat * (X.toRat * (1 + sharesε)) := by field_simp
    have h3 : X.toRat * (1 + sharesε) ≤ 10 ^ 17 := by nlinarith
    rw [h2] at h1
    nlinarith

/-- On a reachable vault the share and price computation of a withdrawal within the limit never overflows. -/
private lemma Vault.Reachable.computeWithdraw_ne_path_dry (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (w : Bool) (hc : amount.amount.Canonical)
    (hpos : 0 < amount.amount.toRat) (hlim : amount.WithinLimit v) :
    (computeWithdraw v amount w).run ≠ .ok (.error .tecPATH_DRY) := by
  obtain ⟨hA0, hA9, hS0, hS9, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  cases amount with
  | vaultShares s =>
    have hsl : s.toRat ≤ v.sharesTotal.toRat := by rw [← hST]; exact hlim
    have hne := Vault.Reachable.sharesToAssetsWithdraw_ne_overflow v t0 hr s w (Or.inl hc) hpos.le
      (by linarith) (by
        by_cases hS : v.sharesTotal.toRat = 0
        · rw [hS, div_zero]; norm_num
        have hSpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne hS0 (Ne.symm hS)
        rw [div_le_iff₀ hSpos]
        have : v.assetsAvailable.toRat * s.toRat ≤ v.assetsAvailable.toRat * v.sharesTotal.toRat :=
          mul_le_mul_of_nonneg_left hsl hA0
        nlinarith)
    intro h
    simp only [computeWithdraw] at h
    unfold_ter at h
    walk_ok
    all_goals (obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›; exact hne ‹_›)
  | vaultAssets X =>
    have hne := Vault.Reachable.assetsToSharesWithdraw_ne_overflow v t0 hr X w (Or.inl hc) hpos.le hlim
    intro h
    simp only [computeWithdraw] at h
    unfold_ter at h
    walk_ok
    all_goals (obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›)
    · exact hne ‹_›
    · obtain ⟨hshc, hs0, hsl, hq⟩ := Vault.Reachable.withdraw_shares_facts v t0 hr X _ w hc hpos hlim ‹_›
        (by simpa using ‹¬ STAmount.isZero _ = true›)
      exact Vault.Reachable.sharesToAssetsWithdraw_ne_overflow v t0 hr _ w hshc hs0 hsl hq ‹_›

/-- On a reachable vault the price of a canonical share amount whose worth is at most `10^17` is a canonical amount
between zero and `3·10^17`. -/
private lemma Vault.Reachable.price_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (sh : STAmount)
    (w : Bool)
    (hsh : sh.Canonical) (hs0 : 0 ≤ sh.toRat)
    (hq : v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17) (p : STAmount)
    (hp : v.sharesToAssetsWithdraw sh w = .ok p) :
    p.CanonicalOrZero ∧ 0 ≤ p.toRat ∧ p.toRat ≤ 3 * 10 ^ 17 := by
  have hz := Vault.Reachable.openZone v t0 hr
  have hnav := hz.assetsTotalForWithdrawal_eq w
  obtain ⟨hA0, -, hS0, -, -, -, -, -, -⟩ := Vault.Reachable.size_facts v t0 hr
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  rcases (Nat.cast_nonneg v.toExact.sharesTotal : (0 : ℚ) ≤ _).lt_or_eq with hS | hS
  swap
  · -- no shares: the vault holds nothing and the price is zero
    have hz0 : v.sharesTotal = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp (by rw [← hST, ← hS])
    obtain ⟨hAA, -⟩ := v.valid.empty_shares hz0
    obtain ⟨nav, hnav', -, hcase⟩ := WdPrice.price_cases v sh p w hp
    rw [hnav, Except.ok.injEq] at hnav'
    subst hnav'
    rcases hcase with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact ⟨(STAmount.zero_canonicalOrZero _).1, by rw [STAmount.zero_toRat], by rw [STAmount.zero_toRat]; norm_num⟩
    · exact absurd (by rw [hAA]; rfl) hm
  have hmax := Vault.Reachable.maxValue_fits v t0 hr hS
  have hpc := (Vault.sharesToAssetsWithdraw_form v sh p w hmax hp).1
  obtain ⟨hp0, hpu, -⟩ := Vault.sharesToAssetsWithdraw_total_proof v sh p w _ hnav hs0 hsh hp
  refine ⟨hpc, hp0, ?_⟩
  have hI : v.idealAssetsWithdrawAt v.assetsAvailable.toRat sh.toRat ≤ 10 ^ 17 := by
    unfold RawVault.idealAssetsWithdrawAt; rw [hST]; exact hq
  have hε : (sharesε : ℚ) ≤ 1 := by unfold sharesε; norm_num
  have hε0 : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hI0 : 0 ≤ v.idealAssetsWithdrawAt v.assetsAvailable.toRat sh.toRat := by
    unfold RawVault.idealAssetsWithdrawAt; positivity
  by_cases hpm : p.mValue = 0
  · rw [(STAmount.toRat_eq_zero_iff _).mpr hpm]; norm_num
  have hpc' : p.Canonical := hpc.resolve_right (by simpa [STAmount.isZero] using hpm)
  by_cases hint : p.integral = true
  · have he : p.exponent = 0 := (hpc'.1 hint).1.offset_zero
    rw [he, zpow_zero] at hpu
    nlinarith
  · have hio := hpc'.2 (by simpa using hint)
    have hppos : 0 < p.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
    have hpv := STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
    have hm15 : (10 : ℚ) ^ 15 ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
    have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
    have hulp : (10 : ℚ) ^ 15 * 10 ^ p.exponent ≤ p.toRat := by
      rw [hpv]; exact mul_le_mul_of_nonneg_right hm15 hg.le
    nlinarith

/-- A withdrawal computation within the limit on a reachable vault prices a canonical amount between zero and
`3·10^17`. -/
private lemma Vault.Reachable.computeWithdraw_assets_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (w : Bool) (hc : amount.amount.Canonical) (hpos : 0 < amount.amount.toRat)
    (hlim : amount.WithinLimit v) (amounts : VaultAmounts)
    (hcw : (computeWithdraw v amount w).run = .ok (.ok amounts)) :
    amounts.assets.CanonicalOrZero ∧ 0 ≤ amounts.assets.toRat ∧ amounts.assets.toRat ≤ 3 * 10 ^ 17 := by
  have hp := computeWithdraw_ok_priced v amount w amounts hcw
  obtain ⟨hA0, hA9, hS0, hS9, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  cases amount with
  | vaultShares s =>
    have hsh : amounts.shares = s := by
      simp only [computeWithdraw] at hcw
      unfold_ter at hcw
      walk_ok
      rfl
    rw [hsh] at hp
    have hsl : s.toRat ≤ v.sharesTotal.toRat := by rw [← hST]; exact hlim
    exact Vault.Reachable.price_facts v t0 hr s w hc hpos.le (by
      by_cases hS : v.sharesTotal.toRat = 0
      · rw [hS, div_zero]; norm_num
      have hSpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne hS0 (Ne.symm hS)
      rw [div_le_iff₀ hSpos]
      have : v.assetsAvailable.toRat * s.toRat ≤ v.assetsAvailable.toRat * v.sharesTotal.toRat :=
        mul_le_mul_of_nonneg_left hsl hA0
      nlinarith) _ hp
  | vaultAssets X =>
    have hsh : assetsToSharesWithdraw v X true w = .ok amounts.shares ∧ amounts.shares.isZero = false := by
      simp only [computeWithdraw] at hcw
      unfold_ter at hcw
      walk_ok
      exact ⟨‹_›, by simpa using ‹¬ STAmount.isZero _ = true›⟩
    obtain ⟨hshc, hs0, -, hq⟩ := Vault.Reachable.withdraw_shares_facts v t0 hr X _ w hc hpos hlim hsh.1 hsh.2
    exact Vault.Reachable.price_facts v t0 hr _ w (hshc.resolve_right (by simp [hsh.2])) hs0 hq _ hp

/-- A nonzero withdrawal price on a reachable vault means the vault has shares, so its asset's maximum fits an
`int64` amount. -/
private lemma Vault.Reachable.maxValue_fits_of_price (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (sh p : STAmount) (w : Bool) (hp : v.sharesToAssetsWithdraw sh w = .ok p) (hpz : p.isZero = false) :
    v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t0 hr with hmax | hS
  · exact hmax
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hz0 : v.sharesTotal = Number.zero :=
    (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp (by rw [← hST, hS])
  obtain ⟨hAA, -⟩ := v.valid.empty_shares hz0
  have hz := Vault.Reachable.openZone v t0 hr
  obtain ⟨nav, hnav, -, hcase⟩ := WdPrice.price_cases v sh p w hp
  rw [hz.assetsTotalForWithdrawal_eq w, Except.ok.injEq] at hnav
  subst hnav
  rcases hcase with ⟨-, rfl⟩ | ⟨hm, -⟩
  · exact absurd hpz (by simp [STAmount.isZero, STAmount.zero_mValue])
  · exact absurd (by rw [hAA]; rfl) hm

/-- The early-exit fee step of a withdrawal on a reachable vault never overflows, for a canonical priced amount
between zero and `3·10^17`. -/
private lemma Vault.Reachable.withdraw_fee_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (t : UInt32)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (assets : STAmount) (hac : assets.CanonicalOrZero) (ha0 : 0 ≤ assets.toRat) (hal : assets.toRat ≤ 3 * 10 ^ 17)
    (aN : Number) (haN : assets.toNumber .to_nearest = .ok aN)
    (hrate : ¬ (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = true) :
    tenthBipsOfValue aN (v.earlyExitFeeRateAt t) .upward ≠ .error .overflow ∧
    ∀ fee, tenthBipsOfValue aN (v.earlyExitFeeRateAt t) .upward = .ok fee →
      aN.operator_sub fee .downward ≠ .error .overflow ∧
      ∀ pN, aN.operator_sub fee .downward = .ok pN →
        STAmount.ofNumber v.numericType pN .downward ≠ .error .overflow ∧
        ∀ payout, STAmount.ofNumber v.numericType pN .downward = .ok payout → payout.isZero = false →
          clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent ≠ .error .overflow := by
  obtain ⟨hav, han⟩ := hac.toNumber_exact aN haN
  obtain ⟨hA0, hA9, -, -, -, -, -, hblo, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hA17 : |v.assetsAvailable.toRat| ≤ 10 ^ 17 := by rw [abs_of_nonneg hA0]; nlinarith
  have hbr := v.baseExponent_range
  have hrle := Vault.earlyExitFeeRateAt_le v t
  have hrlt : (v.earlyExitFeeRateAt t).toNat < 100000 := by
    have hne : v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate := by simpa using hrate
    have : (v.earlyExitFeeRateAt t).toNat ≠ 100000 := fun h => hne (by
      apply UInt32.toNat_inj.mp; rw [h]; rfl)
    omega
  have hsmall : aN.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ aN.toRat := by
    by_cases hm : assets.mValue = 0
    · left; rw [hav]; exact (STAmount.toRat_eq_zero_iff _).mpr hm
    · right
      have := STAmount.CanonicalOrZero.abs_ge assets hac hm
      rw [abs_of_nonneg ha0] at this
      rw [hav]
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) this
  obtain ⟨fee, hfee, hfn, hf0, hfle, -⟩ := tenthBipsOfValue_upward_ok aN (v.earlyExitFeeRateAt t) (-100) han
    (by rw [hav]; exact ha0) (by rw [hav]; linarith) le_rfl (fun hm => by
      have hne : assets.toRat ≠ 0 := by rw [← hav]; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hm
      have hm' : assets.mValue ≠ 0 := fun h0 => hne ((STAmount.toRat_eq_zero_iff _).mpr h0)
      have := STAmount.CanonicalOrZero.abs_ge assets hac hm'
      rw [abs_of_nonneg ha0] at this
      rw [hav]
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) this) hrle
  refine ⟨by rw [hfee]; simp, fun fee' hfee' => ?_⟩
  obtain rfl : fee = fee' := Except.ok.inj (hfee.symm.trans hfee')
  have h200 : (3 : ℚ) * 10 ^ 17 < 10 ^ (200 : ℤ) := by norm_num
  obtain ⟨pN, hsub⟩ := Number.operator_sub_ok_of_size aN fee .downward han hfn
    (by rw [hav, abs_of_nonneg ha0]; linarith) (by rw [abs_of_nonneg hf0]; linarith)
  refine ⟨by rw [hsub]; simp, fun pN' hsub' => ?_⟩
  obtain rfl : pN = pN' := Except.ok.inj (hsub.symm.trans hsub')
  obtain ⟨hpN0, hpNle, -⟩ := payoutNumber_bounds aN fee pN _ han (by rw [hav]; exact ha0) hsmall hrlt hfee hsub
  have hpNn : pN.isNormalized := Number.operator_add_isNormalized_any _ _ pN _ han
    (Number.operator_neg_isNormalized _ hfn) hsub
  have hr1 : aN.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) ≤ aN.toRat := by
    have : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
    nlinarith [show 0 ≤ aN.toRat by rw [hav]; exact ha0]
  rw [hav] at hr1 hpNle
  refine ⟨STAmount.ofNumber_ne_overflow _ pN _ hpNn (by rw [abs_of_nonneg hpN0]; linarith),
    fun payout hpo hpz => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hple, hpay0⟩ :=
    Vault.feePayout_shape v assets payout aN fee pN _ hac ha0 (by rw [← hav]; exact hsmall) hrlt haN hfee hsub hpo hpz
  have hpc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo).1
  exact clampToSumExponent_ne_overflow _ _ _ v.wf.assetsAvailable_norm hA17 hpc.operator_neg
    (by rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0]; linarith) hbr.1 (by omega)

/-- The dust check of a withdrawal within the limit on a reachable vault never reports an overflow. -/
private lemma Vault.Reachable.withdraw_dust_ne_path_dry (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (hc : amount.amount.Canonical) (hpos : 0 < amount.amount.toRat)
    (hlim : amount.WithinLimit v) (am : VaultAmounts) (aN : Number)
    (hcw : (computeWithdraw v amount waive).run = .ok (.ok am)) (haN : am.assets.toNumber .to_nearest = .ok aN) :
    v.checkDebitNotDust aN ≠ .ok .tecPATH_DRY := by
  obtain ⟨hac, ha0, hal⟩ := Vault.Reachable.computeWithdraw_assets_facts v t0 hr amount waive hc hpos hlim am hcw
  obtain ⟨hav, han⟩ := hac.toNumber_exact aN haN
  exact Vault.Reachable.checkDebitNotDust_ne_path_dry v t0 hr aN han (by rw [hav, abs_of_nonneg ha0]; linarith)

/-- The early-exit fee step of a nonzero withdrawal within the limit on a reachable vault never overflows. -/
private lemma Vault.Reachable.withdraw_fee_steps_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hc : amount.amount.Canonical)
    (hpos : 0 < amount.amount.toRat) (hlim : amount.WithinLimit v) (am : VaultAmounts) (aN : Number) (b : Bool)
    (hcw : (computeWithdraw v amount waive).run = .ok (.ok am)) (haN : am.assets.toNumber .to_nearest = .ok aN)
    (hfin : (b && !am.assets.isZero) = true) (hrate : ¬ (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = true) :
    tenthBipsOfValue aN (v.earlyExitFeeRateAt t) .upward ≠ .error .overflow ∧
    ∀ fee, tenthBipsOfValue aN (v.earlyExitFeeRateAt t) .upward = .ok fee →
      aN.operator_sub fee .downward ≠ .error .overflow ∧
      ∀ pN, aN.operator_sub fee .downward = .ok pN →
        STAmount.ofNumber v.numericType pN .downward ≠ .error .overflow ∧
        ∀ payout, STAmount.ofNumber v.numericType pN .downward = .ok payout → payout.isZero = false →
          clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent ≠ .error .overflow := by
  obtain ⟨hac, ha0, hal⟩ := Vault.Reachable.computeWithdraw_assets_facts v t0 hr amount waive hc hpos hlim am hcw
  have hnz : am.assets.isZero = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
    exact hfin.2
  have hmax := Vault.Reachable.maxValue_fits_of_price v t0 hr _ _ waive
    (computeWithdraw_ok_priced v amount waive am hcw) hnz
  exact Vault.Reachable.withdraw_fee_ne_overflow v t0 hr t hmax am.assets hac ha0 hal aN haN hrate

/-- Withdrawal on a reachable vault of an asset amount within the Open limit, or of at most the share total ->
never `tecPATH_DRY`. -/
lemma Vault.Reachable.withdraw_no_path_dry_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical)
    (hassets : ∀ assets, amount = .vaultAssets assets → assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent))
    (hshares : ∀ shares, amount = .vaultShares shares → shares.toRat ≤ v.toExact.sharesTotal) :
    (v.withdraw amount waive t hpos).run ≠ .ok (.error .tecPATH_DRY) := by
  have hlim : amount.WithinLimit v := by
    cases amount with
    | vaultAssets a => exact hassets a rfl
    | vaultShares s => exact hshares s rfl
  intro hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (exact Vault.Reachable.computeWithdraw_ne_path_dry v t0 hr amount waive hc hpos hlim ‹_›)
  all_goals try (rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
  · exact Vault.Reachable.withdraw_dust_ne_path_dry v t0 hr amount waive hc hpos hlim _ _ ‹_› ‹_› ‹_›
  all_goals (
    obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›
    first
      | exact STAmount.isFractionalNonPositive_ne_overflow _ ‹_›
      | exact (Vault.Reachable.withdraw_fee_steps_ne_overflow v t0 hr amount waive t hc hpos hlim _ _ _ ‹_› ‹_› ‹_›
          ‹_›).1 ‹_›
      | exact ((Vault.Reachable.withdraw_fee_steps_ne_overflow v t0 hr amount waive t hc hpos hlim _ _ _ ‹_› ‹_› ‹_›
          ‹_›).2 _ ‹_›).1 ‹_›
      | exact (((Vault.Reachable.withdraw_fee_steps_ne_overflow v t0 hr amount waive t hc hpos hlim _ _ _ ‹_› ‹_›
          ‹_› ‹_›).2 _ ‹_›).2 _ ‹_›).1 ‹_›
      | exact (((Vault.Reachable.withdraw_fee_steps_ne_overflow v t0 hr amount waive t hc hpos hlim _ _ _ ‹_› ‹_›
          ‹_› ‹_›).2 _ ‹_›).2 _ ‹_›).2 _ ‹_› (by simpa using ‹¬ STAmount.isZero _ = true›) ‹_›)

/-- On a reachable vault the cash converted to the asset is a canonical amount, or zero, of the cash's value. -/
private lemma Vault.Reachable.cash_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash) :
    cash.CanonicalOrZero ∧ cash.toRat = v.assetsAvailable.toRat := by
  have hcv := Vault.cash_ofNumber_toRat v cash hcash
  refine ⟨?_, hcv⟩
  by_cases hA : v.assetsAvailable.toRat = 0
  · right
    have : cash.mValue = 0 := (STAmount.toRat_eq_zero_iff _).mp (by rw [hcv, hA])
    simp [STAmount.isZero, this]
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t0 hr with hmax | hS
  · exact (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
  · exfalso
    have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hz0 : v.sharesTotal = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp (by rw [← hST, hS])
    exact hA (by rw [(v.valid.empty_shares hz0).1]; exact Number.toRat_zero)

/-- The shares a clawback names on a reachable vault, for an amount within the Open limit and a holder with at most
the share total: a canonical count at most `10^17`, worth at most `10^17`. -/
private lemma Vault.Reachable.clawback_shares_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares sh : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (hhs : holderShares.ShareBalance)
    (hhl : holderShares.toRat ≤ v.toExact.sharesTotal)
    (hs : assetsToSharesClawback v assets holderShares waive = .ok sh) :
    sh.Canonical ∧ 0 ≤ sh.toRat ∧ sh.toRat ≤ 10 ^ 17 ∧
      v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17 := by
  obtain ⟨hA0, hA9, hS0, hS9, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  -- a count at most the share total is worth at most the cash
  have hworth : ∀ x : ℚ, 0 ≤ x → x ≤ v.sharesTotal.toRat →
      v.assetsAvailable.toRat * x / v.sharesTotal.toRat ≤ 10 ^ 17 := by
    intro x hx0 hx
    by_cases hS : v.sharesTotal.toRat = 0
    · rw [hS, div_zero]; norm_num
    have hSpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne hS0 (Ne.symm hS)
    rw [div_le_iff₀ hSpos]
    have : v.assetsAvailable.toRat * x ≤ v.assetsAvailable.toRat * v.sharesTotal.toRat :=
      mul_le_mul_of_nonneg_left hx hA0
    nlinarith
  unfold assetsToSharesClawback at hs
  split at hs
  · split at hs
    · -- the sole holder's waived clawback names the share total
      simp only [bind, Except.bind, pure, Except.pure] at hs
      cases hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest with
      | error e => rw [hst] at hs; cases hs
      | ok st =>
        rw [hst] at hs
        obtain rfl : st = sh := Except.ok.inj hs
        have hstv : st.toRat = v.sharesTotal.toRat :=
          STAmount.ofNumber_integral_exact .int64 _ _ _ (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hst
        obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) hst
        exact ⟨hic.canonical (by rw [hty]; decide), by rw [hstv]; exact hS0, by rw [hstv]; linarith,
          hworth _ (by rw [hstv]; exact hS0) (by rw [hstv])⟩
    · -- a zero amount names the holder's balance
      obtain rfl : holderShares = sh := Except.ok.inj hs
      have hle : holderShares.toRat ≤ v.sharesTotal.toRat := by rw [← hST]; exact hhl
      have h0 : 0 ≤ holderShares.toRat := by
        rw [STAmount.toRat_of_nonneg holderShares hhs.nonneg]; positivity
      exact ⟨hhs.canonical, h0, by linarith, hworth _ h0 hle⟩
  · -- a nonzero amount names the shares it prices to
    rename_i hz
    have hz' : assets.isZero = false := by simpa using hz
    by_cases hsz : sh.isZero = true
    · have hm : sh.mValue = 0 := by simpa [STAmount.isZero] using hsz
      have h0 : sh.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr hm
      obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive hs
      refine ⟨hic.canonical (by rw [hty]; decide), by rw [h0], by rw [h0]; norm_num, ?_⟩
      rw [h0, mul_zero, zero_div]; norm_num
    have hac : assets.Canonical := hc.resolve_right (by simp [hz'])
    have hpos : 0 < assets.toRat := lt_of_le_of_ne hnn (Ne.symm (fun h0 => by
      have := (STAmount.toRat_eq_zero_iff _).mp h0
      simp [STAmount.isZero, this] at hz'))
    obtain ⟨hshc, hs0, hsl, hq⟩ := Vault.Reachable.withdraw_shares_facts v t0 hr assets sh waive hac hpos hl hs
      (by simpa using hsz)
    exact ⟨hshc.resolve_right (by simpa using hsz), hs0, hsl, hq⟩

/-- The shares the cash names on a reachable vault: a canonical count at most `10^17`, worth at most `10^17`. -/
private lemma Vault.Reachable.cash_shares_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (cash sh : STAmount)
    (w : Bool) (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hs : assetsToSharesWithdraw v cash true w = .ok sh) :
    sh.Canonical ∧ 0 ≤ sh.toRat ∧ sh.toRat ≤ 10 ^ 17 ∧
      v.assetsAvailable.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17 := by
  obtain ⟨hcc, hcv⟩ := Vault.Reachable.cash_facts v t0 hr cash hcash
  obtain ⟨hA0, hA9, -, -, -, -, -, -, -⟩ := Vault.Reachable.size_facts v t0 hr
  obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true w hs
  have hshc : sh.Canonical := hic.canonical (by rw [hty]; decide)
  by_cases hsz : sh.isZero = true
  · have h0 : sh.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hsz)
    refine ⟨hshc, by rw [h0], by rw [h0]; norm_num, ?_⟩
    rw [h0, mul_zero, zero_div]; norm_num
  have hcpos : 0 < cash.toRat := by
    rcases (show (0 : ℚ) ≤ cash.toRat by rw [hcv]; exact hA0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hm : cash.mValue = 0 := (STAmount.toRat_eq_zero_iff _).mp h.symm
      have := assetsToSharesWithdraw_amount_ne_zero v cash sh w hcc hs (by simpa using hsz)
      exact this h.symm
  have hcC : cash.Canonical := hcc.resolve_right (fun hz => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)] at hcpos
    exact lt_irrefl _ hcpos)
  obtain ⟨-, hs0, hsl, hq⟩ := Vault.Reachable.withdraw_shares_facts v t0 hr cash sh w hcC hcpos
    (by rw [hcv, zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc]; exact hA9)
    hs (by simpa using hsz)
  exact ⟨hshc, hs0, hsl, hq⟩

/-- On a reachable vault the price of the shares a clawback names, and its clamp, never overflow. -/
private lemma Vault.Reachable.clawback_direct_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (hhs : holderShares.ShareBalance)
    (hhl : holderShares.toRat ≤ v.toExact.sharesTotal) (sh : STAmount)
    (hs : assetsToSharesClawback v assets holderShares waive = .ok sh) :
    v.sharesToAssetsWithdraw sh waive ≠ .error .overflow ∧
    ∀ rec, v.sharesToAssetsWithdraw sh waive = .ok rec →
      rec.toNumber .to_nearest ≠ .error .overflow ∧
      clampToSumExponent v.assetsAvailable rec.operator_neg v.baseExponent ≠ .error .overflow := by
  obtain ⟨hshc, hs0, hsl, hq⟩ :=
    Vault.Reachable.clawback_shares_facts v t0 hr assets holderShares sh waive hc hnn hl hhs hhl hs
  refine ⟨Vault.Reachable.sharesToAssetsWithdraw_ne_overflow v t0 hr sh waive (Or.inl hshc) hs0 hsl hq,
    fun rec hp => ?_⟩
  obtain ⟨hrc, hr0, hrl⟩ := Vault.Reachable.price_facts v t0 hr sh waive hshc hs0 hq rec hp
  obtain ⟨hA0, hA9, -, -, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  refine ⟨STAmount.CanonicalOrZero.toNumber_ne_overflow hrc,
    clampToSumExponent_ne_overflow _ _ _ v.wf.assetsAvailable_norm
    (by rw [abs_of_nonneg hA0]; nlinarith) hrc.operator_neg ?_ v.baseExponent_range.1
    (by have := v.baseExponent_bounds; omega)⟩
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0]; linarith

/-- On a reachable vault the shares the cash names, their price and its clamp never overflow. -/
private lemma Vault.Reachable.clawback_capped_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (waive : Bool) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash) :
    assetsToSharesWithdraw v cash true waive ≠ .error .overflow ∧
    ∀ sh, assetsToSharesWithdraw v cash true waive = .ok sh →
      v.sharesToAssetsWithdraw sh waive ≠ .error .overflow ∧
      ∀ rec, v.sharesToAssetsWithdraw sh waive = .ok rec →
        rec.toNumber .to_nearest ≠ .error .overflow ∧
        clampToSumExponent v.assetsAvailable rec.operator_neg v.baseExponent ≠ .error .overflow := by
  obtain ⟨hcc, hcv⟩ := Vault.Reachable.cash_facts v t0 hr cash hcash
  obtain ⟨hA0, hA9, -, -, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  refine ⟨Vault.Reachable.assetsToSharesWithdraw_ne_overflow v t0 hr cash waive hcc (by rw [hcv]; exact hA0)
    (by rw [hcv, zpow_add₀ (by norm_num), show ((10 : ℚ) ^ (15 : ℤ)) = 10 ^ 15 by norm_num, ← mul_assoc]; exact hA9),
    fun sh hs => ?_⟩
  obtain ⟨hshc, hs0, hsl, hq⟩ := Vault.Reachable.cash_shares_facts v t0 hr cash sh waive hcash hs
  refine ⟨Vault.Reachable.sharesToAssetsWithdraw_ne_overflow v t0 hr sh waive (Or.inl hshc) hs0 hsl hq,
    fun rec hp => ?_⟩
  obtain ⟨hrc, hr0, hrl⟩ := Vault.Reachable.price_facts v t0 hr sh waive hshc hs0 hq rec hp
  refine ⟨STAmount.CanonicalOrZero.toNumber_ne_overflow hrc,
    clampToSumExponent_ne_overflow _ _ _ v.wf.assetsAvailable_norm
    (by rw [abs_of_nonneg hA0]; nlinarith) hrc.operator_neg ?_ v.baseExponent_range.1
    (by have := v.baseExponent_bounds; omega)⟩
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0]; linarith

/-- On a reachable vault the shares a clawback within the Open limit names never overflow. -/
private lemma Vault.Reachable.assetsToSharesClawback_ne_overflow (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) :
    assetsToSharesClawback v assets holderShares waive ≠ .error .overflow := by
  obtain ⟨-, -, hS0, hS9, -, -, -, -, -⟩ := Vault.Reachable.size_facts v t0 hr
  unfold assetsToSharesClawback
  split
  · split
    · simp only [bind, Except.bind, pure, Except.pure]
      have hne := STAmount.ofNumber_ne_overflow .int64 v.sharesTotal .to_nearest v.wf.sharesTotal_norm
        (by rw [abs_of_nonneg hS0]; linarith)
      split
      · rename_i e he; intro h; cases h; exact hne he
      · simp
    · intro h; cases h
  · exact Vault.Reachable.assetsToSharesWithdraw_ne_overflow v t0 hr assets waive hc hnn hl

/-- On a reachable vault the pricing of a clawback within the limits never overflows. -/
private lemma Vault.Reachable.computeClawback_ne_path_dry (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (hhs : holderShares.ShareBalance)
    (hhl : holderShares.toRat ≤ v.toExact.sharesTotal) :
    (computeClawback v assets holderShares waive).run ≠ .ok (.error .tecPATH_DRY) := by
  have hS0 := v.wf.sharesTotal_nonneg
  obtain ⟨hA0, hA9, -, hS9, -, -, -, -, hbhi⟩ := Vault.Reachable.size_facts v t0 hr
  intro h
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals (obtain rfl := isOverflow_eq_true ‹isOverflow _ = true›)
  all_goals first
    | exact Vault.Reachable.assetsToSharesClawback_ne_overflow v t0 hr assets holderShares waive hc hnn hl ‹_›
    | exact (Vault.Reachable.clawback_direct_ne_overflow v t0 hr assets holderShares waive hc hnn hl hhs hhl _
        ‹_›).1 ‹_›
    | exact ((Vault.Reachable.clawback_direct_ne_overflow v t0 hr assets holderShares waive hc hnn hl hhs hhl _
        ‹_›).2 _ ‹_›).1 ‹_›
    | exact ((Vault.Reachable.clawback_direct_ne_overflow v t0 hr assets holderShares waive hc hnn hl hhs hhl _
        ‹_›).2 _ ‹_›).2 ‹_›
    | exact STAmount.ofNumber_ne_overflow v.numericType v.assetsAvailable .to_nearest v.wf.assetsAvailable_norm (by
        rw [abs_of_nonneg hA0]
        have hb1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
        nlinarith) ‹_›
    | exact STAmount.ofNumber_ne_overflow .int64 v.sharesTotal .to_nearest v.wf.sharesTotal_norm
        (by rw [abs_of_nonneg hS0]; linarith) ‹_›
    | exact (Vault.Reachable.clawback_capped_ne_overflow v t0 hr waive _ ‹_›).1 ‹_›
    | exact ((Vault.Reachable.clawback_capped_ne_overflow v t0 hr waive _ ‹_›).2 _ ‹_›).1 ‹_›
    | exact (((Vault.Reachable.clawback_capped_ne_overflow v t0 hr waive _ ‹_›).2 _ ‹_›).2 _ ‹_›).1 ‹_›
    | exact (((Vault.Reachable.clawback_capped_ne_overflow v t0 hr waive _ ‹_›).2 _ ‹_›).2 _ ‹_›).2 ‹_›
    | exact STAmount.isFractionalNonPositive_ne_overflow _ ‹_›

/-- A clawback computation within the limits on a reachable vault records a canonical amount between zero and
`3·10^17`. -/
private lemma Vault.Reachable.computeClawback_assets_facts (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (hhs : holderShares.ShareBalance)
    (hhl : holderShares.toRat ≤ v.toExact.sharesTotal) (amounts : VaultAmounts)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts)) :
    amounts.assets.CanonicalOrZero ∧ 0 ≤ amounts.assets.toRat ∧ amounts.assets.toRat ≤ 3 * 10 ^ 17 := by
  obtain ⟨rec, -, hpr, -, -, hcase⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  have hrec : rec.CanonicalOrZero ∧ 0 ≤ rec.toRat ∧ rec.toRat ≤ 3 * 10 ^ 17 := by
    cases hpr with
    | direct _ _ _ hs hp _ _ =>
      obtain ⟨hshc, hs0, -, hq⟩ :=
        Vault.Reachable.clawback_shares_facts v t0 hr assets holderShares _ waive hc hnn hl hhs hhl hs
      exact Vault.Reachable.price_facts v t0 hr _ waive hshc hs0 hq rec hp
    | capped _ _ cash _ _ _ _ _ _ _ _ hcash hs hp _ _ =>
      obtain ⟨hshc, hs0, -, hq⟩ := Vault.Reachable.cash_shares_facts v t0 hr cash _ waive hcash hs
      exact Vault.Reachable.price_facts v t0 hr _ waive hshc hs0 hq rec hp
  obtain ⟨hrc, hr0, hrl⟩ := hrec
  rcases hcase with ⟨-, heq⟩ | ⟨-, hcl, -⟩
  · rw [heq]; exact ⟨hrc, hr0, hrl⟩
  · obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    have hle := clampToSumExponent_le_abs _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0] at hle
    exact ⟨hcc, hc0, by linarith⟩

/-- Clawback on a reachable vault of an amount within the Open limit from a holder of at most the share total ->
never `tecPATH_DRY`. -/
lemma Vault.Reachable.clawback_no_path_dry_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero)
    (hl : assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) (hhs : holderShares.ShareBalance)
    (hhl : holderShares.toRat ≤ v.toExact.sharesTotal) :
    (v.clawback assets holderShares waive hnn).run ≠ .ok (.error .tecPATH_DRY) := by
  intro hok
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  · obtain ⟨am, aN, hcw, haN, hd⟩ : ∃ (am : VaultAmounts) (aN : Number),
        (computeClawback v assets holderShares waive).run = .ok (.ok am) ∧
        am.assets.toNumber .to_nearest = .ok aN ∧ v.checkDebitNotDust aN = .ok .tecPATH_DRY :=
      ⟨_, _, ‹_›, ‹_›, ‹_›⟩
    obtain ⟨hac, ha0, hal⟩ := Vault.Reachable.computeClawback_assets_facts v t0 hr assets holderShares waive hc hnn
      hl hhs hhl am hcw
    obtain ⟨hav, han⟩ := hac.toNumber_exact aN haN
    exact Vault.Reachable.checkDebitNotDust_ne_path_dry v t0 hr aN han (by rw [hav, abs_of_nonneg ha0]; linarith) hd
  all_goals try (rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
  all_goals exact Vault.Reachable.computeClawback_ne_path_dry v t0 hr assets holderShares waive hc hnn hl hhs hhl ‹_›

end XRPL.Model.SingleAssetVault
