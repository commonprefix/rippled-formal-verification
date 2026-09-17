import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.DivQuotient
import XRPL.Properties.Protocol.Number.Totality

/-! # Forward totality for the withdraw pricing prefix

The withdraw accuracy suite reasons *backward* (from `run = .ok r`). Emptying a
vault needs the opposite: that the one-share run *reaches* a success. This file
supplies the reusable forward facts that do not touch the well-founded `Number`
rounding pipeline:

* subtracting a mantissa-zero `Number` (the reachable vault's zero loss) is the
  identity and total, so the pricing subtraction of
  `sharesToAssetsWithdraw` collapses to `nav = assetsTotal`, and
* the try/catch wrapper `computeWithdrawByShares` forwards a successful
  `sharesToAssetsWithdraw` to a no-error record.

What remains open is the arithmetic core (`operator_mul` / `operator_div` /
`ofNumber` / `to_rep` totality on symbolic bounded operands). -/

namespace XRPL.Model.Protocol

/-! ## Forward totality of the integral `STAmount.ofNumber` (`to_rep`) path

`STAmount.ofNumber` on an integral numeric type funnels a sign-cleared operand
through `Number.to_rep`, then repacks with `STAmount.checked`, which runs a second
`to_rep` inside `canonicalize`. For a bounded operand both `to_rep` calls are total:
the `grow` overflow is unreachable (the adjusted exponent is nonpositive, so `grow`
is never entered with a positive offset), and the final rounding-overflow is
unreachable (an `offset = 0` operand keeps the empty start guard so it never rounds
up, while an `offset < 0` operand floor-divides by at least ten, landing strictly
below `maxRep`, so the round-up bump stays in range). A sub-floor operand rounds to
the canonical zero (an `.ok`, not a throw). This is the `ofNumber` front the
emptying run needs for the share-total (`.to_nearest`) and payout (`.downward`)
integral conversions. -/

/-- **Cap bounds the adjusted `Number.exponent`.** A normalized nonnegative
`Number` whose value fits `2 ^ 63 - 1` has a nonpositive `Number.exponent`. When
the mantissa exceeds `maxRep` (so the accessor bumps the exponent by one), a
nonnegative raw exponent would already push the value above `maxRep = 2 ^ 63 - 1`,
so the raw exponent is at most `-1` and the bumped exponent stays nonpositive. -/
theorem Number.exponent_fn_le_zero_of_cap (n : Number) (hnorm : n.isNormalized)
    (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    n.exponent ≤ 0 := by
  have htoRat : n.toRat = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
    Number.toRat_of_nonneg n hneg
  rcases hnorm with hz | ⟨hmlo, _hmhi, _, _hexp_lo, _hexp_hi⟩
  · rw [hz]; decide
  · unfold Number.exponent
    by_cases hgt : n.mantissa_ > maxRep
    · rw [if_pos hgt]
      by_contra hcon
      push_neg at hcon
      have hexp_nn : (0 : ℤ) ≤ n.exponent_ := by omega
      have hpow_ge1 : (1 : ℚ) ≤ (10 : ℚ) ^ n.exponent_ := by
        rw [show n.exponent_ = ((n.exponent_.toNat : ℤ)) from by omega, zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      have hm_ge : (9223372036854775808 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by
        have hlt := UInt64.lt_iff_toNat_lt.mp hgt
        rw [maxRep_val] at hlt
        have h2 : (9223372036854775808 : ℕ) ≤ n.mantissa_.toNat := by omega
        exact_mod_cast h2
      have hge : (9223372036854775808 : ℚ) ≤ n.toRat := by
        rw [htoRat]
        calc (9223372036854775808 : ℚ) = 9223372036854775808 * 1 := by ring
          _ ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
              mul_le_mul hm_ge hpow_ge1 (by norm_num) (by positivity)
      have : (9223372036854775808 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this
    · rw [if_neg hgt]
      by_contra hcon
      push_neg at hcon
      have hm_nat : (1000000000000000000 : ℕ) ≤ n.mantissa_.toNat := by
        have := UInt64.le_iff_toNat_le.mp hmlo; rwa [largeRange_min_val] at this
      have hm_q : (1000000000000000000 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_nat
      have hexp1 : 1 ≤ n.exponent_.toNat := by omega
      have hpow : (10 : ℚ) ≤ 10 ^ n.exponent_.toNat := by
        calc (10 : ℚ) = 10 ^ 1 := (pow_one 10).symm
          _ ≤ 10 ^ n.exponent_.toNat := pow_le_pow_right₀ (by norm_num) hexp1
      have hge : (10000000000000000000 : ℚ) ≤ n.toRat := by
        rw [htoRat, show n.exponent_ = (n.exponent_.toNat : ℤ) from by omega, zpow_natCast]
        calc (10000000000000000000 : ℚ) = 1000000000000000000 * 10 := by norm_num
          _ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_.toNat :=
              mul_le_mul hm_q hpow (by norm_num) (by positivity)
      have : (10000000000000000000 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this

/-- **Forward totality of `Number.to_rep` on a nonnegative, small-exponent operand.**
A nonnegative `Number` with nonpositive adjusted `Number.exponent` converts to a
signed `Int64` without error. The `grow` overflow is unreachable (`offset ≤ 0`, so
`grow` is entered only at `offset = 0`, returning its input); the final
rounding-overflow is unreachable too (at `offset = 0` the empty start guard never
rounds up, and at `offset < 0` the floor-divide by at least ten lands strictly below
`maxRep`, so the round-up bump stays in range). -/
theorem Number.to_rep_ok_of_nonneg_exp_nonpos (n : Number) (mode : rounding_mode)
    (hneg : n.negative_ = false) (hexp : n.exponent ≤ 0) :
    ∃ r : Int64, n.to_rep mode = .ok r := by
  unfold Number.to_rep
  simp only
  by_cases hz : (n.mantissa == 0) = true
  · exact ⟨0, by rw [if_pos hz]⟩
  · rw [if_neg hz]
    have hD0_range : 0 ≤ n.mantissa.toInt ∧ n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by
      unfold Number.mantissa
      rw [if_neg (by rw [hneg]; decide)]
      by_cases hgt : n.mantissa_ > maxRep
      · rw [if_pos hgt]
        have hlt : (n.mantissa_ / 10).toNat < 2 ^ 63 := by
          rw [UInt64.toNat_div, uint64_ten_toNat]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        refine ⟨Int.natCast_nonneg _, ?_⟩
        rw [UInt64.toNat_div, uint64_ten_toNat, maxRep_val]
        have := UInt64.toNat_lt_size n.mantissa_
        rw [uint64_size_val] at this; omega
      · rw [if_neg hgt]
        have hle : n.mantissa_.toNat ≤ maxRep.toNat :=
          UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hgt)
        have hlt : n.mantissa_.toNat < 2 ^ 63 := by rw [maxRep_val] at hle; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        exact ⟨Int.natCast_nonneg _, by exact_mod_cast hle⟩
    rw [hneg]
    simp only [Bool.false_eq_true, if_false]
    by_cases hexplt : n.exponent < 0
    · have hge : ¬ n.exponent ≥ 0 := by omega
      rw [if_pos hexplt, if_neg hge]
      simp only
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ (-n.exponent).toNat := by
        have := shift_fst_eq n.mantissa n.exponent Guard.new hD0_range.1
        rwa [← hspdef] at this
      have hsp_nn : 0 ≤ sp.1.toInt := by
        rw [hDf]; exact Int.ediv_nonneg hD0_range.1 (by positivity)
      have hsp_lt : sp.1.toInt < (maxRep.toNat : ℤ) := by
        have hk_ne : (10 : ℤ) ^ (-n.exponent).toNat ≠ 0 := by positivity
        have hmul : sp.1.toInt * 10 ^ (-n.exponent).toNat ≤ n.mantissa.toInt := by
          rw [hDf]; exact Int.ediv_mul_le _ hk_ne
        have h10le : (10 : ℤ) ≤ 10 ^ (-n.exponent).toNat := by
          calc (10 : ℤ) = 10 ^ 1 := by ring
            _ ≤ 10 ^ (-n.exponent).toNat := pow_le_pow_right₀ (by norm_num) (by omega)
        have hmul10 : sp.1.toInt * 10 ≤ n.mantissa.toInt :=
          le_trans (mul_le_mul_of_nonneg_left h10le hsp_nn) hmul
        have hle := hD0_range.2
        rw [maxRep_val] at hle ⊢
        omega
      have hsp_lt_u64 : sp.1.toUInt64.toNat < maxRep.toNat := by
        have hnat := toUInt64_toNat_of_nonneg sp.1 hsp_nn; omega
      rw [pushOverflow_noop_of_lt_maxRep hsp_lt_u64 sp.2 mode]
      by_cases hb : (sp.2.round mode == 1 || sp.2.round mode == 0 && sp.1 % 2 == 1) = true
      · rw [if_pos hb, if_neg (show ¬ sp.1 ≥ maxRep.toInt64 from fun hc => by
          have := Int64.le_iff_toInt_le.mp hc
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          omega)]
        exact ⟨_, rfl⟩
      · rw [if_neg hb, if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from
          fun hc => by
            have := Int64.lt_iff_toInt_lt.mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
            omega)]
        exact ⟨_, rfl⟩
    · have hexpge : n.exponent ≥ 0 := not_lt.mp hexplt
      rw [if_neg hexplt, if_pos hexpge]
      have hgrow0 : Number.to_rep.grow n.mantissa n.exponent = .ok n.mantissa := by
        rw [Number.to_rep.grow, if_neg (show ¬ n.exponent > 0 from by omega)]
      rw [hgrow0]
      simp only
      have h_u64 : n.mantissa.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep n.mantissa hD0_range.1 hD0_range.2
      rw [pushOverflow_noop_of_le_maxRep_of_empty h_u64 Guard.new mode (by decide)]
      rw [show Guard.new.round mode = -2 from by
        have := start_guard_round mode false; simpa using this]
      rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && n.mantissa % 2 == 1) = true
        from by simp)]
      rw [if_neg (show ¬ (maxRep.toInt64 < n.mantissa ∧ n.mantissa < maxRepUp.toInt64) from
        fun hc => by
          have := Int64.lt_iff_toInt_lt.mp hc.1
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          omega)]
      exact ⟨_, rfl⟩

/-- **Forward totality of the integral `STAmount.canonicalize`.** An offset-`0`,
sign-cleared integral record whose magnitude fits both `maxRep` and the numeric
type's carried bound canonicalizes without error: the nested `to_rep` succeeds by
`Number.to_rep_ok_of_nonneg_exp_nonpos` (offset `0`, so its own adjusted exponent is
nonpositive), and the resulting magnitude, still within `maxRep`, clears the
type's `maxValue` check. -/
theorem STAmount.canonicalize_integral_ok (s : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0) (hsneg : s.mIsNegative = false)
    (hv : s.mValue.toNat ≤ maxRep.toNat) (hvmax : maxRep.toNat ≤ s.mNumericType.maxValue.toNat)
    (hmaxoff : (0 : Int) ≤ s.mNumericType.maxOffset) :
    ∃ result, s.canonicalize mode = .ok result := by
  rw [STAmount.canonicalize, if_pos hint]
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · exact ⟨_, by rw [if_pos hz]⟩
  · rw [if_neg hz,
        if_neg (show ¬ s.mOffset > s.mNumericType.maxOffset from by rw [hoff]; omega)]
    simp only [IntAmount.ofNumber]
    obtain ⟨r2, hr2⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos
      (Number.unchecked s.mIsNegative s.mValue s.mOffset) mode
      (show (Number.unchecked s.mIsNegative s.mValue s.mOffset).negative_ = false from hsneg)
      (show (Number.unchecked s.mIsNegative s.mValue s.mOffset).exponent ≤ 0 from by
        unfold Number.exponent
        rw [if_neg (show ¬ (Number.unchecked s.mIsNegative s.mValue s.mOffset).mantissa_ > maxRep
          from by show ¬ s.mValue > maxRep; rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; omega)]
        exact le_of_eq hoff)
    rw [hr2]
    simp only []
    have hr2rng := XRPL.Model.SingleAssetVault.Number.to_rep_nonneg_range
      (Number.unchecked s.mIsNegative s.mValue s.mOffset) mode r2 hsneg hr2
    rw [if_neg (show ¬ r2.toInt.natAbs.toUInt64 > s.mNumericType.maxValue from by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
      have habs : (r2.toInt.natAbs : ℤ) = r2.toInt := Int.natAbs_of_nonneg hr2rng.1
      have habs_le : r2.toInt.natAbs ≤ maxRep.toNat := by
        have : (r2.toInt.natAbs : ℤ) ≤ (maxRep.toNat : ℤ) := by rw [habs]; exact hr2rng.2
        exact_mod_cast this
      have hlt64 : r2.toInt.natAbs < 2 ^ 64 := by
        have : maxRep.toNat < 2 ^ 64 := by rw [maxRep_val]; norm_num
        omega
      rw [UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hlt64)]
      omega)]
    exact ⟨_, rfl⟩

/-- **Forward totality of the integral `STAmount.ofNumber`.** A normalized,
nonnegative `Number` whose value fits `2 ^ 63 - 1` converts into any integral
numeric type whose carried `maxValue` covers `maxRep` and whose `maxOffset` is
nonnegative. The sign flag resolves to `false`, `to_rep` succeeds (its adjusted
exponent is nonpositive by `Number.exponent_fn_le_zero_of_cap`), and the repack
`checked` canonicalizes without error. -/
theorem STAmount.ofNumber_integral_ok_of_cap (nt : NumericType) (n : Number)
    (mode : rounding_mode) (hnt : nt.isIntegral = true)
    (hmaxval : maxRep.toNat ≤ nt.maxValue.toNat) (hmaxoff : (0 : Int) ≤ nt.maxOffset)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber nt n mode = .ok result := by
  unfold STAmount.ofNumber
  rw [if_pos hnt]
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hnegf : neg = false := by
    rw [hneg_def]
    apply decide_eq_false
    unfold Number.signum
    rw [hneg]; simp only [Bool.false_eq_true, if_false]
    split <;> norm_num
  have hwn : working = n := by rw [hw_def, hnegf]; simp only [Bool.false_eq_true, if_false]
  rw [hwn]
  have hexp0 : n.exponent ≤ 0 := Number.exponent_fn_le_zero_of_cap n hnorm hneg hcap
  obtain ⟨r, hr⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos n mode hneg hexp0
  rw [hr]
  simp only []
  rw [hnegf]
  have hrrng := XRPL.Model.SingleAssetVault.Number.to_rep_nonneg_range n mode r hneg hr
  have hru64 : r.toUInt64.toNat ≤ maxRep.toNat := toUInt64_toNat_le_maxRep r hrrng.1 hrrng.2
  obtain ⟨result, hres⟩ := STAmount.canonicalize_integral_ok
    (STAmount.unchecked nt r.toUInt64 0 false) mode hnt rfl rfl hru64 hmaxval hmaxoff
  exact ⟨result, by rw [STAmount.checked]; exact hres⟩

/-- **Share-total / payout `ofNumber .int64` totality (both caller modes).** The
emptying run's two integral conversions -- the stored share total (`.to_nearest`)
and the priced payout (`.downward`) -- succeed for any normalized nonnegative
`Number` bounded by `2 ^ 63 - 1`. `NumericType.int64` carries `maxValue = maxRep`
and `maxOffset = 18`, so the general cap totality applies directly. -/
theorem STAmount.ofNumber_int64_ok (n : Number) (mode : rounding_mode)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber .int64 n mode = .ok result :=
  STAmount.ofNumber_integral_ok_of_cap .int64 n mode (by decide) (by decide) (by decide)
    hnorm hneg hcap

/-- **Forward totality of `operator_sub` for two normalized capped operands.** Both
stored-total decrements of the withdraw run, `assetsTotal - payout` and
`sharesTotal - sharesBurned`, share this shape: `x` and `y` are normalized
nonnegative `Number`s bounded by `2 ^ 63 - 1`, so each succeeds in every mode. A
zero subtrahend is the identity (`Number.operator_sub_of_mantissa_zero`). Otherwise
the negated subtrahend has the opposite sign to `x`, so the internal add takes its
different-sign branch, discharged by `Number.operator_add_diffSign_ok` with the
cap-derived exponent bounds. No ordering (`y ≤ x`) is needed for totality. -/
theorem Number.operator_sub_ok_of_normalized_cap (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hxcap : x.toRat ≤ 2 ^ 63 - 1) (hycap : y.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, x.operator_sub y mode = .ok result := by
  by_cases hy0 : y.mantissa_ = 0
  · exact ⟨x, Number.operator_sub_of_mantissa_zero x y mode hy0⟩
  · have hxe : x.exponent_ ≤ 0 := by
      have h := Number.exponent_fn_le_zero_of_cap x hx hxneg hxcap
      unfold Number.exponent at h; split at h <;> omega
    have hye : y.exponent_ ≤ 0 := by
      have h := Number.exponent_fn_le_zero_of_cap y hy hyneg hycap
      unfold Number.exponent at h; split at h <;> omega
    exact Number.operator_sub_ok_of_normalized_exp x y mode hx hy hxneg hyneg
      (by unfold maxExponent; omega) (by unfold maxExponent; omega)

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Pricing prefix collapse on a zero-loss vault.** When the loss `Number`
carries a zero mantissa (the reachable, loss-free case), the net-asset-value
subtraction of `sharesToAssetsWithdraw` is an identity, so the exchange reduces
to the raw `assetsTotal` guard and the mul/div/ofNumber pricing chain. -/
theorem Vault.sharesToAssetsWithdraw_zeroLoss_reduces (v : Vault) (shares : STAmount)
    (hL : v.lossUnrealized.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares false =
      (if v.assetsTotal.mantissa_ == 0 then
        (pure (STAmount.zero v.numericType) : Except Error STAmount)
       else do
        let sharesNumber ← shares.toNumber .to_nearest
        let NAVShares ← v.assetsTotal.operator_mul sharesNumber .to_nearest
        let assetsNumber ← NAVShares.operator_div v.sharesTotal .to_nearest
        let assets ← STAmount.ofNumber v.numericType assetsNumber .downward
        return assets) := by
  unfold Vault.sharesToAssetsWithdraw
  simp only []
  rw [Number.operator_sub_of_mantissa_zero v.assetsTotal v.lossUnrealized _ hL, ok_bind]
  rfl

/-- **`computeWithdrawByShares` forwards a successful exchange.** If the exchange
`sharesToAssetsWithdraw` returns `.ok assets`, the try/catch wrapper produces the
no-error record echoing the named shares. -/
theorem computeWithdrawByShares_of_exchange_ok (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (assets : STAmount)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    computeWithdrawByShares v shares waiveUnrealizedLoss
      = .ok ⟨none, assets, shares⟩ := by
  unfold computeWithdrawByShares
  rw [hok]
  simp only [ok_bind, epure]
  rw [tryCatch_ok]
  rfl

end XRPL.Model.SingleAssetVault
