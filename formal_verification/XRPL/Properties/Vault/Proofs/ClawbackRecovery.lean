import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # What a clawback destroys and recovers

A clawback destroys the shares the amount prices to, truncated, or the holder's whole balance for a zero amount. When
the price of those shares exceeds the cash, it destroys the shares the cash prices to instead. It recovers their price,
floored onto the grid of the cash it leaves, which on a reachable vault is the base grid. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful clawback, read off the code: it prices the destroyed shares, which are not zero,
and records the priced recovery, clamped onto the grid of the cash it leaves unless it is zero. -/
lemma Vault.clawback_recovery_cases (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ recovered : STAmount, v.ClawbackPriced assets holderShares waive r.shares recovered ∧
      r.shares.isZero = false ∧
      ((recovered.isZero = true ∧ r.assets = recovered) ∨
        (recovered.isZero = false ∧
          clampToSumExponent v.assetsAvailable recovered.operator_neg v.baseExponent = .ok r.assets ∧
          r.assets.isFractionalNonPositive = .ok false)) := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  have hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok _) := ‹_›
  obtain ⟨rec, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v _ _ waive _ hcomp
  exact ⟨rec, hpr, by simpa using ‹¬ STAmount.isZero _ = true›, hrec⟩

/-- The recovery a clawback prices is the price of the destroyed shares, and the cash covers it. -/
lemma Vault.ClawbackPriced.recovered {v : Vault} {assets holderShares : STAmount} {waive : Bool}
    {shares recovered : STAmount}
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered) :
    v.sharesToAssetsWithdraw shares waive = .ok recovered ∧ recovered.CanonicalOrZero ∧
      recovered.toRat ≤ v.assetsAvailable.toRat := by
  have hcap : ∀ n : Number, v.sharesToAssetsWithdraw shares waive = .ok recovered →
      recovered.toNumber .to_nearest = .ok n → n.operator_gt v.assetsAvailable = false →
      v.sharesToAssetsWithdraw shares waive = .ok recovered ∧ recovered.CanonicalOrZero ∧
        recovered.toRat ≤ v.assetsAvailable.toRat := by
    intro n hs2a hn hgt
    have har := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
    obtain ⟨hv, hnorm⟩ := har.toNumber_exact n hn
    have hle : ¬ v.assetsAvailable.toRat < n.toRat := by
      rw [← operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm]
      simpa [Number.operator_gt] using hgt
    exact ⟨hs2a, har, by rw [← hv]; linarith⟩
  cases hpr with
  | direct _ _ n _ hs2a hn hgt => exact hcap n hs2a hn hgt
  | capped _ _ _ _ _ _ n _ _ _ _ _ _ hs2a hn hgt => exact hcap n hs2a hn hgt

/-- The shares a clawback of a nonzero amount destroys are a nonnegative canonical MPT amount. -/
private lemma Vault.ClawbackPriced.shares_of_nonzero {v : Vault} {assets holderShares : STAmount} {waive : Bool}
    {shares recovered : STAmount}
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hc : assets.Canonical) (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 ∧ 0 ≤ shares.toRat := by
  cases hpr with
  | direct _ _ _ ha2s _ _ _ =>
    simp only [assetsToSharesClawback, hznz, Bool.false_eq_true, ↓reduceIte] at ha2s
    obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ha2s
    exact ⟨hic, hty, assetsToSharesWithdraw_nonneg v _ _ waive (Or.inl hc) hnn ha2s⟩
  | capped _ _ cash _ _ _ _ _ _ _ _ hcash ha2s _ _ _ =>
    have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
    have hc0 := STAmount.ofNumber_nonneg _ _ _ _ v.wf.assetsAvailable_norm
      (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg) hcash
    obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ha2s
    exact ⟨hic, hty, assetsToSharesWithdraw_nonneg v _ _ waive hcc hc0 ha2s⟩

/-- A successful clawback recovers the price of the destroyed shares, clamped onto the grid of the cash it leaves
unless it is zero. The cash covers that price. -/
lemma Vault.clawback_priced (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧ priced.CanonicalOrZero ∧
      priced.toRat ≤ v.assetsAvailable.toRat ∧
      ((priced.isZero = true ∧ r.assets = priced) ∨
        (priced.isZero = false ∧
          clampToSumExponent v.assetsAvailable priced.operator_neg v.baseExponent = .ok r.assets ∧
          r.assets.isFractionalNonPositive = .ok false)) := by
  obtain ⟨rec, hpr, -, hcase⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hs2a, hrc, hrle⟩ := hpr.recovered hmax
  exact ⟨rec, hs2a, hrc, hrle, hcase⟩

/-- The recovery is the priced worth, or that worth floored onto the grid of the cash it leaves.
A zero recovery is the priced worth. -/
lemma Vault.clawback_recovery_le (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hsc : r.shares.CanonicalOrZero) (hs0 : 0 ≤ r.shares.toRat) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧ priced.CanonicalOrZero ∧
      0 ≤ priced.toRat ∧ priced.toRat ≤ v.assetsAvailable.toRat ∧ 0 ≤ r.assets.toRat ∧
      r.assets.toRat ≤ priced.toRat ∧
      r.assets.toRat + 1 / 2 * (10 : ℚ) ^ priced.exponent ≤ priced.toRat + 1 / 2 * (10 : ℚ) ^ r.assets.exponent ∧
      (r.assets.isZero = true → r.assets = priced) ∧
      (priced.isZero = false → v.numericType.isIntegral = false →
        r.assets.IOUCanonical ∧ priced.IOUCanonical ∧ 0 < r.assets.toRat ∧
          clampToSumExponent v.assetsAvailable priced.operator_neg v.baseExponent = .ok r.assets) ∧
      (priced.isZero = false → v.numericType.isIntegral = true →
        r.assets.toRat = priced.toRat ∧ r.assets.exponent = priced.exponent) := by
  obtain ⟨priced, hpr, hpc, hple, hcase⟩ := Vault.clawback_priced v assets holderShares waive hnn hmax r hok
  have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).2
  have hp0 := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive hsc hs0 hpr
  refine ⟨priced, hpr, hpc, hp0, hple, ?_⟩
  rcases hcase with ⟨hz, heq⟩ | ⟨hnz, hcl, hfnp⟩
  · -- a zero priced worth is recorded as it is
    rw [heq]
    refine ⟨hp0, le_refl _, le_refl _, fun _ => rfl, fun h => absurd hz (by simp [h]),
      fun h => absurd hz (by simp [h])⟩
  have hpm : priced.mValue ≠ 0 := by simpa [STAmount.isZero] using hnz
  have hpos : 0 < priced.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
  have hrc := clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hrle := clampToSumExponent_le_abs _ _ _ _ hpc.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hp0] at hrle
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral clamp keeps the priced worth and its exponent
    have hni : priced.operator_neg.integral = true := by
      unfold STAmount.integral
      rw [(STAmount.operator_neg_fields priced).1, hpt]
      exact hint
    rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
    obtain ⟨-, hoff, -, hrat⟩ := clamp_magnitude priced.operator_neg
    rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hp0] at hrat
    have hexp : r.assets.exponent = priced.exponent := by
      show r.assets.mOffset = priced.mOffset
      rw [← hcl, hoff, (STAmount.operator_neg_fields priced).2.1]
    refine ⟨hrc.2.2, hrle, by rw [hrat, hexp], fun hz => ?_, fun _ h => absurd hint (by simp [h]),
      fun _ _ => ⟨hrat, hexp⟩⟩
    have : r.assets.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)
    linarith
  -- a fractional recovery is not zero, so it is the floor of the priced worth on the post-sum grid
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hrt : r.assets.mNumericType = .fractional := by
    rw [hrc.2.1, (STAmount.operator_neg_fields priced).1, hpt, hvfr]
  have hrm : r.assets.mValue ≠ 0 := fun h0 => by
    rw [STAmount.isFractionalNonPositive_zero _ hrt h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hrc.2.2 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
  have hfrR : r.assets.integral = false := by unfold STAmount.integral; rw [hrt]; rfl
  have hfrP : priced.integral = false := by unfold STAmount.integral; rw [hpt, hvfr]; rfl
  have hRc : r.assets.IOUCanonical :=
    (hrc.1.resolve_right (by simpa [STAmount.isZero] using hrm)).2 hfrR
  have hPc : priced.IOUCanonical := (hpc.resolve_right (by simpa [STAmount.isZero] using hpm)).2 hfrP
  obtain ⟨-, e, -, -, -, hfl⟩ := Vault.clamp_floor v priced r.assets hpc (by rw [hpt, hvfr]) hp0 hrm hcl
  obtain ⟨hU, -⟩ := STAmount.IOUCanonical.floor_bounds priced r.assets e hPc hRc hrpos hfl
  exact ⟨hrc.2.2, hrle, hU, fun hz => absurd (by simpa [STAmount.isZero] using hz) hrm,
    fun _ _ => ⟨hRc, hPc, hrpos, hcl⟩, fun _ h => absurd h hint⟩

/-- A successful clawback of a nonzero amount prices at a nonzero value. At a zero value the
amount is worth no shares, and the shares the holder names are worth nothing, which the cash covers. -/
private lemma Vault.clawback_nav_ne_zero (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ nav : Number, v.assetsTotalForWithdrawal waive = .ok nav ∧ nav.mantissa_ ≠ 0 := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  cases hcp with
  | direct _ _ _ ha2s _ _ _ =>
    simp only [assetsToSharesClawback, hznz, Bool.false_eq_true, ↓reduceIte] at ha2s
    obtain ⟨nav, hnav, hcase⟩ := WdTight.shares_reduces v _ _ waive ha2s
    refine ⟨nav, hnav, fun h0 => ?_⟩
    rcases hcase with ⟨-, hz⟩ | ⟨hm, -⟩
    · rw [hz] at hsnz
      exact absurd hsnz (by simp [STAmount.isZero, STAmount.zero_mValue])
    · exact hm h0
  | capped _ rec0 _ _ _ n0 _ _ hs2a0 hn0 hgt0 _ _ _ _ _ =>
    obtain ⟨nav, hnav, -, hcase⟩ := WdPrice.price_cases v _ _ waive hs2a0
    refine ⟨nav, hnav, fun h0 => ?_⟩
    rcases hcase with ⟨-, hz⟩ | ⟨hm, -⟩
    · -- shares worth nothing are not above the cash
      have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
      rw [hz] at hn0
      obtain ⟨hv, hnorm⟩ := (STAmount.zero_canonicalOrZero _).1.toNumber_exact n0 hn0
      rw [STAmount.zero_toRat _] at hv
      have hlt : v.assetsAvailable.toRat < n0.toRat := by
        rw [← operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm]
        simpa [Number.operator_gt] using hgt0
      linarith
    · exact hm h0

/-- `10⁻¹⁰⁰` is far above the `Number` underflow threshold. -/
private lemma underflow_tiny : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-100 : ℤ) := by
  have h : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-118 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
  calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (18 : ℕ) * 10 ^ (-118 : ℤ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 10 ^ (-100 : ℤ) := by rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; norm_num

/-- A two-stage `Number` quotient of at least `10⁻⁵⁰` does not underflow, and stays within
`sharesε` of the exact quotient. -/
lemma pipe_large (x y p q z : Number) (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hzpos : 0 < z.toRat) (hz1 : 1 ≤ z.toRat)
    (hlarge : (10 : ℚ) ^ (-50 : ℤ) ≤ x.toRat * y.toRat / z.toRat)
    (hmul : x.operator_mul y .to_nearest = .ok p) (hdiv : p.operator_div z .to_nearest = .ok q) :
    q.isNormalized ∧ 0 < q.toRat ∧
      |q.toRat - x.toRat * y.toRat / z.toRat| ≤ x.toRat * y.toRat / z.toRat * sharesε := by
  have ht := underflow_tiny
  have h50 : (10 : ℚ) ^ (-100 : ℤ) < 10 ^ (-50 : ℤ) / 2 := by
    rw [lt_div_iff₀ (by norm_num), show (-50 : ℤ) = -100 + 50 by norm_num, zpow_add₀ (by norm_num)]
    have : (0 : ℚ) < 10 ^ (-100 : ℤ) := zpow_pos (by norm_num) _
    have : (2 : ℚ) < 10 ^ (50 : ℤ) := by norm_num
    nlinarith
  have h50p : (0 : ℚ) < 10 ^ (-50 : ℤ) := zpow_pos (by norm_num) _
  have hxy0 := mul_nonneg hx0 hy0
  have hxy : x.toRat * y.toRat / z.toRat ≤ x.toRat * y.toRat := div_le_self hxy0 hz1
  have hxm : x.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero x h] at hlarge; simp at hlarge
    linarith [zpow_pos (by norm_num : (0 : ℚ) < 10) (-50 : ℤ)]
  have hym : y.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero y h] at hlarge; simp at hlarge
    linarith [zpow_pos (by norm_num : (0 : ℚ) < 10) (-50 : ℤ)]
  have hpm : p.mantissa_ ≠ 0 := fun h => by
    have h1 := operator_mul_underflow_truth_small x y p _ hx hy hxm hym hmul h
    rw [abs_of_nonneg hxy0] at h1
    exact lt_irrefl _ (lt_of_le_of_lt (hlarge.trans hxy)
      ((lt_of_lt_of_le h1 ht).trans (h50.trans (half_lt_self h50p))))
  have hpn := operator_mul_result_isNormalized _ _ _ _ hx hy hxm hym hmul hpm
  have hzm := operator_div_divisor_ne_zero _ _ _ _ hz hdiv
  have hqm : q.mantissa_ ≠ 0 := fun h => by
    have hu := operator_div_underflow_truth_small p z q _ hpn hz hpm hzm hdiv h
    have hw1 := operator_mul_rounds_to_nearest x y p hx hy hmul hpm
    simp only [RoundsWithin, RatValued.toRat] at hw1
    change |p.toRat - x.toRat * y.toRat| ≤ |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7)) at hw1
    rw [abs_of_nonneg hxy0] at hw1
    have ha : x.toRat * y.toRat * (5 / (2 ^ 63 + 7)) ≤ x.toRat * y.toRat * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by norm_num) hxy0
    have hp : x.toRat * y.toRat / 2 ≤ |p.toRat| := by
      have := (abs_le.mp hw1).1
      have := le_abs_self p.toRat
      linarith
    rw [abs_div, abs_of_pos hzpos, div_lt_iff₀ hzpos] at hu
    have h2 : |p.toRat| < 10 ^ (-100 : ℤ) * z.toRat := lt_of_lt_of_le hu (mul_le_mul_of_nonneg_right ht hzpos.le)
    have h3 : 10 ^ (-100 : ℤ) * z.toRat < 10 ^ (-50 : ℤ) / 2 * z.toRat :=
      mul_lt_mul_of_pos_right h50 hzpos
    have h4 : 10 ^ (-50 : ℤ) * z.toRat ≤ x.toRat * y.toRat := by
      have := mul_le_mul_of_nonneg_right hlarge hzpos.le
      rwa [div_mul_cancel₀ _ hzpos.ne'] at this
    have h5 : 10 ^ (-50 : ℤ) / 2 * z.toRat ≤ |p.toRat| := by
      rw [div_mul_eq_mul_div]
      exact le_trans (div_le_div_of_nonneg_right h4 (by norm_num)) hp
    exact lt_irrefl _ (lt_of_le_of_lt h5 (h2.trans h3))
  exact WdPrice.pipe x y p q z hx hx0 hy hy0 hz hzpos hmul hdiv hqm

/-- A clawback of a nonzero amount from a reachable vault recovers nothing only on an integral
vault, when the destroyed shares are worth at most half a unit. -/
private lemma Vault.Reachable.clawback_zero_recovery (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hz : r.assets.isZero = true) :
    v.numericType.isIntegral = true ∧
      v.idealAssetsClawback waive r.shares.toRat * (1 - sharesε) ≤ 1 / 2 ∧ r.assets.exponent = 0 := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0⟩ := hcp.shares_of_nonzero hmax hc hznz hnn
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, -, -, -, -, -, hzero, -, -⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  have hrp := hzero hz
  have hpz : priced.mValue = 0 := by rw [← hrp]; simpa [STAmount.isZero] using hz
  -- the vault prices at its cash, which is not zero
  obtain ⟨nav, hnav, hnm⟩ := Vault.clawback_nav_ne_zero v assets holderShares waive hznz hnn r hok
  have hnavv := Vault.Reachable.nav_eq_cash v t0 hr waive nav hnav
  obtain ⟨nav', hnav', hnavn, hcase⟩ := WdPrice.price_cases v _ _ waive hpr
  rw [hnav, Except.ok.injEq] at hnav'
  subst hnav'
  rcases hcase with ⟨h0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · exact absurd h0 hnm
  have hAApos : 0 < v.assetsAvailable.toRat := lt_of_le_of_ne v.exact.assetsAvailable_nonneg
    (fun h => Number.toRat_ne_zero_of_mantissa_ne_zero _ hnm (hnavv.trans h.symm))
  have hAA : (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat :=
    ((Vault.Reachable.openZone_proof v t0 hr hmax).cash_ge hAApos).2
  -- the shares are a whole positive number, and the share total is below `10¹⁹`
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical r.shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hsc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hspos : 0 < r.shares.toRat := lt_of_le_of_ne hs0 (Ne.symm (STAmount.toRat_ne_zero _
    (by simpa [STAmount.isZero] using hsnz)))
  have hs1 : (1 : ℚ) ≤ r.shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hST := Vault.sharesTotal_le_maxRep v
  obtain ⟨hSTpos, hST1, -⟩ := Vault.sharesTotal_bounds_of_cash v hAApos
  -- the priced worth is at least `10⁻²⁹`, so its `Number` stages do not underflow
  set T := nav.toRat * sn0.toRat / v.sharesTotal.toRat with hT
  have hT29 : (10 : ℚ) ^ (-29 : ℤ) ≤ T := by
    rw [hT, hnavv, hsnv, le_div_iff₀ hSTpos]
    have h19 : (10 : ℚ) ^ (-29 : ℤ) * (2 ^ 63 - 1) ≤ 10 ^ (-10 : ℤ) := by norm_num
    calc (10 : ℚ) ^ (-29 : ℤ) * v.sharesTotal.toRat ≤ 10 ^ (-29 : ℤ) * (2 ^ 63 - 1) :=
          mul_le_mul_of_nonneg_left hST (by positivity)
      _ ≤ 10 ^ (-10 : ℤ) * 1 := by rw [mul_one]; exact h19
      _ ≤ v.assetsAvailable.toRat * r.shares.toRat :=
          mul_le_mul hAA hs1 zero_le_one (le_trans (by positivity) hAA)
  obtain ⟨hann, hanpos, hb⟩ := pipe_large nav sn0 NS an v.sharesTotal hnavn hsnn v.wf.sharesTotal_norm
    (by rw [hnavv]; exact v.exact.assetsAvailable_nonneg) (by rw [hsnv]; exact hs0) hSTpos hST1
    (le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hT29) hmul hdiv
  rw [← hT] at hb
  obtain ⟨hb1, -⟩ := abs_le.mp hb
  have hT0 : 0 ≤ T := le_trans (zpow_pos (by norm_num) _).le hT29
  have hη : (sharesε : ℚ) ≤ 1 / 2 := by unfold sharesε; norm_num
  -- the ideal is the priced worth's exact quotient
  have hI : v.idealAssetsClawback waive r.shares.toRat = T := by
    have h := WdPrice.nav_exact v waive nav (Vault.Reachable.withdrawNavExact_proof v t0 hr waive) hnav
    unfold RawVault.idealAssetsClawback RawVault.idealAssetsWithdraw
    rw [hT, hsnv, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf,
      show (if waive = true then v.depositNav else v.withdrawNav) = nav.toRat from h.symm]
  rw [hI]
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral worth rounds to zero only below one half
    have hhalf := STAmount.ofNumber_integral_within_half _ an priced hint hann
      (Number.negative_false_of_pos an hanpos) hof
    rw [(STAmount.toRat_eq_zero_iff _).mpr hpz, zero_sub, abs_neg, abs_of_pos hanpos] at hhalf
    have hoff := (STAmount.ofNumber_integral_canonical _ an .to_nearest priced hint hof).1.offset_zero
    refine ⟨hint, ?_, by rw [hrp]; exact hoff⟩
    nlinarith
  -- a fractional worth of at least `10⁻⁸¹` converts to a nonzero amount
  exfalso
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ an.toRat := by
    have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-29 : ℤ) / 2 := by norm_num
    have h1 : T / 2 ≤ T * (1 - sharesε) := by nlinarith
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-29 : ℤ) / 2 := h81
      _ ≤ T / 2 := div_le_div_of_nonneg_right hT29 (by norm_num)
      _ ≤ T * (1 - sharesε) := h1
      _ ≤ an.toRat := by linarith
  exact STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest priced hann hge (hvfr ▸ hof) hpz

/-- The recovery of a clawback from a reachable vault, within `sharesε` and a rounding step of the destroyed
shares' worth. It is their priced worth, floored onto the base grid when it is fractional. -/
lemma Vault.clawback_assetsRecovered_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (t0 : UInt32) (hr : Vault.Reachable v t0) (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.assets.toRat ≤ v.toExact.assetsAvailable ∧ 0 ≤ r.assets.toRat ∧
    r.assets.toRat ≤ v.idealAssetsClawback waive r.shares.toRat * (1 + sharesε) +
      1 / 2 * (10 : ℚ) ^ r.assets.exponent ∧
    v.idealAssetsClawback waive r.shares.toRat - r.assets.toRat ≤
      v.idealAssetsClawback waive r.shares.toRat * sharesε +
        max (1 / 2 * (10 : ℚ) ^ r.assets.exponent)
          ((10 : ℚ) ^ v.baseExponent - 1 / 2 * (10 : ℚ) ^ r.assets.exponent) ∧
    (r.assets.isZero = true → v.numericType.isIntegral = true ∧
      v.idealAssetsClawback waive r.shares.toRat * (1 - sharesε) ≤ 1 / 2) := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0⟩ := hcp.shares_of_nonzero hmax hc hznz hnn
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, hpc, hp0, hple, hr0, hrle, hU, -, hfrac, hintg⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  obtain ⟨-, hbU, hbL⟩ := Vault.sharesToAssetsWithdraw_bounds_proof v r.shares priced waive hs0 hsc
    (Vault.Reachable.withdrawNavExact_proof v t0 hr waive) hpr
  have hI : v.idealAssetsWithdraw waive r.shares.toRat = v.idealAssetsClawback waive r.shares.toRat := rfl
  rw [hI] at hbU hbL
  have hzr := Vault.Reachable.clawback_zero_recovery v t0 hr assets holderShares waive hc hznz hnn hmax r hok
  set I := v.idealAssetsClawback waive r.shares.toRat with hIdef
  have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; positivity
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    unfold RawVault.idealAssetsClawback RawVault.idealAssetsWithdraw
    have hnq : 0 ≤ WdPrice.navQ v waive := WdPrice.navQ_nonneg v waive
    exact div_nonneg (mul_nonneg hnq hs0) (by positivity)
  have hrp : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
  refine ⟨le_trans hrle hple, hr0, by linarith, ?_, fun hz => ⟨(hzr hz).1, (hzr hz).2.1⟩⟩
  by_cases hpz : priced.isZero = true
  · -- nothing is recovered: the vault holds an integral asset and the shares are worth at most half
    have hp00 : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hpz)
    have hz : r.assets.isZero = true := by
      have : r.assets.toRat = 0 := le_antisymm (by linarith) hr0
      simpa [STAmount.isZero] using (STAmount.toRat_eq_zero_iff _).mp this
    obtain ⟨-, hhalf, hexp⟩ := hzr hz
    have h0 : r.assets.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)
    rw [hexp, zpow_zero, h0]
    have hm := le_max_left (1 / 2 * (1 : ℚ)) ((10 : ℚ) ^ v.baseExponent - 1 / 2 * 1)
    linarith
  have hpnz : priced.isZero = false := by simpa using hpz
  have hlow := hbL hpnz
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral recovery is the priced worth
    obtain ⟨hval, hexp⟩ := hintg hpnz hint
    rw [hval, hexp]
    have hm := le_max_left (1 / 2 * (10 : ℚ) ^ priced.exponent)
      ((10 : ℚ) ^ v.baseExponent - 1 / 2 * (10 : ℚ) ^ priced.exponent)
    linarith
  -- a fractional recovery is the priced worth floored onto the base grid
  obtain ⟨hRc, hPc, hrpos, hcl⟩ := hfrac hpnz (by simpa using hint)
  have hfl := Vault.Reachable.clamp_base v t0 hr hmax priced r.assets hpc hPc.is_fractional hp0 hple
    (by intro h0; rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hrpos; exact lt_irrefl _ hrpos) hcl
  obtain ⟨-, hL⟩ := STAmount.IOUCanonical.floor_bounds priced r.assets v.baseExponent hPc hRc hrpos hfl
  linarith

/-- A truncating `assetsToSharesWithdraw` that burns shares prices a nonzero amount. -/
lemma assetsToSharesWithdraw_amount_ne_zero (v : Vault) (amount shares : STAmount) (waive : Bool)
    (hc : amount.CanonicalOrZero)
    (hok : assetsToSharesWithdraw v amount true waive = .ok shares) (hnz : shares.isZero = false) :
    amount.toRat ≠ 0 := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  unfold assetsToSharesWithdraw at hok
  obtain ⟨navN, -, hok⟩ := bind_ok_peel _ _ _ hok
  dsimp only at hok
  by_cases hmz : navN.mantissa_ = 0
  · rw [if_pos (by simp [hmz])] at hok
    obtain rfl := Except.ok.inj hok
    exact absurd hnz (by decide)
  rw [if_neg (by simp [hmz])] at hok
  obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T, hT, hsh⟩ := bind_ok_peel _ _ _ hok
  have hTm := STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
  have hT0m := Number.truncate_source_ne_zero T0 T hT hTm
  have hPm := operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
    (Number.not_operator_eq_zero_of_mantissa_ne hmz) hT0 hT0m
  obtain ⟨hanval, hannorm⟩ := hc.toNumber_exact amountN hamN
  obtain ⟨-, hanm⟩ := operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
  rw [← hanval]
  exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hanm

/-- A clawback of a nonzero amount whose price the cash covers destroys the shares that amount prices to: the
pricing does not reprice from the cash. -/
private lemma Vault.clawback_direct_shares (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (waive : Bool) (assetsRecoveredNumber : Number)
    (hshares : assetsToSharesWithdraw v assets true waive = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.shares = sharesDestroyed ∧ r.shares.isZero = false := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  refine ⟨?_, hsnz⟩
  cases hcp with
  | direct _ _ _ ha2s _ _ _ =>
    simp only [assetsToSharesClawback, hznz, Bool.false_eq_true, ↓reduceIte] at ha2s
    exact Except.ok.inj (ha2s.symm.trans hshares)
  | capped _ _ _ _ _ _ _ ha2s0 hs2a0 hn0 hgt0 _ _ _ _ _ =>
    simp only [assetsToSharesClawback, hznz, Bool.false_eq_true, ↓reduceIte] at ha2s0
    obtain rfl := Except.ok.inj (ha2s0.symm.trans hshares)
    obtain rfl := Except.ok.inj (hs2a0.symm.trans hassets)
    obtain rfl := Except.ok.inj (hn0.symm.trans hnum)
    rw [hle] at hgt0
    exact absurd hgt0 (by decide)

/-- A clawback whose first price exceeds the cash destroys the shares the cash prices to. -/
private lemma Vault.clawback_capped_shares (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount) (waive : Bool)
    (assetsRecoveredNumber : Number)
    (hshares : assetsToSharesWithdraw v assets true waive = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    assetsToSharesWithdraw v assetsRecovered' true waive = .ok r.shares ∧ r.shares.isZero = false := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  refine ⟨?_, hsnz⟩
  cases hcp with
  | direct _ _ _ ha2s hs2a hn hgt' =>
    simp only [assetsToSharesClawback, hznz, Bool.false_eq_true, ↓reduceIte] at ha2s
    obtain rfl := Except.ok.inj (ha2s.symm.trans hshares)
    obtain rfl := Except.ok.inj (hs2a.symm.trans hassets)
    obtain rfl := Except.ok.inj (hn.symm.trans hnum)
    rw [hgt] at hgt'
    exact absurd hgt' (by decide)
  | capped _ _ _ _ _ _ _ _ _ _ _ hcash ha2s _ _ _ =>
    obtain rfl := Except.ok.inj (hcash.symm.trans hclamped)
    exact ha2s

/-- The shares destroyed by assets, priced at a net asset value: a whole count within `sharesε`
of the ideal at that value above, and less than one share plus `sharesε` below. -/
private lemma clawback_shares_bounds (v : Vault) (X shares : STAmount) (waive : Bool) (nav : Number)
    (hnav : v.assetsTotalForWithdrawal waive = .ok nav) (hX : X.CanonicalOrZero) (hX0 : 0 ≤ X.toRat)
    (hok : assetsToSharesWithdraw v X true waive = .ok shares) (hnz : shares.isZero = false) :
    shares.toRat.den = 1 ∧ 0 ≤ shares.toRat ∧
    v.idealSharesWithdrawAt nav.toRat X.toRat * (1 - sharesε) - 1 < shares.toRat ∧
    shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat X.toRat * (1 + sharesε) := by
  have hX0' := assetsToSharesWithdraw_amount_ne_zero v X shares waive hX hok hnz
  have hpos : 0 < X.toRat := lt_of_le_of_ne hX0 (Ne.symm hX0')
  have hXc : X.Canonical := hX.resolve_right (fun hz => hX0' ((STAmount.toRat_eq_zero_iff _).mpr
    (by simpa [STAmount.isZero] using hz)))
  obtain ⟨hden, hspos, hup, hlo⟩ := WdTight.shares_bounds v X shares waive nav hnav hpos hXc hok hnz
  exact ⟨hden, hspos.le, hlo, hup⟩

/-- Proof of the valid-vault line of `Vault.clawback_sharesDestroyed`. -/
lemma Vault.clawback_sharesDestroyed_total_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount) (waive : Bool)
    (assetsRecoveredNumber nav : Number) (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets true waive = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 - sharesε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 + sharesε) := by
  obtain ⟨heq, hsnz⟩ := Vault.clawback_direct_shares v assets holderShares sharesDestroyed assetsRecovered
    waive assetsRecoveredNumber hshares hassets hnum hle hznz hnn r hok
  rw [heq] at hsnz ⊢
  exact clawback_shares_bounds v assets sharesDestroyed waive nav hnav (Or.inl hc) hnn hshares hsnz

/-- The shares a capped clawback destroys, priced at a net asset value: within `sharesε` of the
ideal of the cash above, and less than one share plus `sharesε` below. -/
private lemma clawback_capped_bounds (v : Vault) (cash shares : STAmount) (waive : Bool) (nav : Number)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hok : assetsToSharesWithdraw v cash true waive = .ok shares) (hnz : shares.isZero = false) :
    shares.toRat.den = 1 ∧ 0 ≤ shares.toRat ∧
    v.idealSharesWithdrawAt nav.toRat cash.toRat * (1 - sharesε) - 1 < shares.toRat ∧
    shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat cash.toRat * (1 + sharesε) := by
  have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
  have hc0 := STAmount.ofNumber_nonneg _ _ _ _ v.wf.assetsAvailable_norm
    (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg) hcash
  exact clawback_shares_bounds v cash shares waive nav hnav hcc hc0 hok hnz

/-- Proof of the capped line of `Vault.clawback_sharesDestroyed`. -/
lemma Vault.clawback_sharesDestroyed_clamped_total_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount) (waive : Bool)
    (assetsRecoveredNumber nav : Number) (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hshares : assetsToSharesWithdraw v assets true waive = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesWithdrawAt nav.toRat assetsRecovered'.toRat * (1 - sharesε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat assetsRecovered'.toRat * (1 + sharesε) := by
  obtain ⟨ha2s, hsnz⟩ := Vault.clawback_capped_shares v assets holderShares sharesDestroyed assetsRecovered
    assetsRecovered' waive assetsRecoveredNumber hshares hassets hnum hgt hclamped hznz hnn r hok
  exact clawback_capped_bounds v assetsRecovered' r.shares waive nav hmax hnav hclamped ha2s hsnz

/-- A zero clawback amount names the holder's balance: the sole holder's balance is the share
total, so the share total the waived pricing names is that balance. -/
private lemma assetsToSharesClawback_zero (v : Vault) (assets holderShares shares : STAmount) (waive : Bool)
    (hhs : holderShares.ShareBalance) (hsole : waive = true ↔ v.IsSoleShareholder holderShares)
    (hz : assets.isZero = true)
    (hok : assetsToSharesClawback v assets holderShares waive = .ok shares) : shares = holderShares := by
  simp only [assetsToSharesClawback, hz, ↓reduceIte] at hok
  cases hw : waive
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at hok
    exact (Except.ok.inj hok).symm
  simp only [hw, ↓reduceIte, bind, Except.bind] at hok
  cases hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest with
  | error e => rw [hst] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hst] at hok
    obtain rfl : st = shares := Except.ok.inj hok
    obtain ⟨hSTpos, hhv⟩ := hsole.mp hw
    have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hstv : st.toRat = v.sharesTotal.toRat :=
      STAmount.ofNumber_integral_exact .int64 _ _ _ (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hst
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) hst
    have hm : st.mValue ≠ 0 := fun h0 => by
      rw [(STAmount.toRat_eq_zero_iff _).mpr h0, ← hcast] at hstv
      linarith
    refine STAmount.eq_of_exactCanonical st holderShares (Or.inr ⟨hic, ?_⟩)
      (STAmount.Canonical.exactCanonical _ hhs.canonical) (by rw [hty, hhs.int64]) hm
      (by rw [hstv, hhv, hcast])
    have h := hic.in_range
    rw [hty] at h
    exact le_trans h (by decide)

/-- Proof of `Vault.clawback_zero_all_shares`. A zero amount names the holder's balance, so the run
destroys that balance and records its price clamped onto the grid of the cash it leaves. -/
lemma Vault.clawback_zero_all_shares_proof (v : Vault)
    (assets holderShares assetsRecovered reported : STAmount) (waive : Bool) (assetsRecoveredNumber : Number)
    (hhs : holderShares.ShareBalance) (hsole : waive = true ↔ v.IsSoleShareholder holderShares)
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsAvailable assetsRecovered.operator_neg v.baseExponent = .ok reported)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.shares = holderShares ∧ r.assets.toRat = reported.toRat ∧ holderShares.isZero = false := by
  obtain ⟨rec, hcp, hsnz, hcase⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  -- the pricing does not reprice from the cash, which covers the holder's balance
  have hdirect : r.shares = holderShares ∧ rec = assetsRecovered := by
    cases hcp with
    | direct _ _ _ ha2s hs2a _ _ =>
      obtain rfl := assetsToSharesClawback_zero v assets holderShares _ waive hhs hsole hz ha2s
      exact ⟨rfl, Except.ok.inj (hs2a.symm.trans hassets)⟩
    | capped _ _ _ _ _ _ _ ha2s0 hs2a0 hn0 hgt0 _ _ _ _ _ =>
      obtain rfl := assetsToSharesClawback_zero v assets holderShares _ waive hhs hsole hz ha2s0
      obtain rfl := Except.ok.inj (hs2a0.symm.trans hassets)
      obtain rfl := Except.ok.inj (hn0.symm.trans hnum)
      rw [hle] at hgt0
      exact absurd hgt0 (by decide)
  obtain ⟨hsh, rfl⟩ := hdirect
  refine ⟨hsh, ?_, by rw [← hsh]; exact hsnz⟩
  rcases hcase with ⟨hrz, heq⟩ | ⟨-, hcl, -⟩
  · -- a zero worth is recorded as it is, and clamps to zero
    have hm : rec.operator_neg.mValue = 0 := by
      rw [(STAmount.operator_neg_fields rec).2.2]; simpa [STAmount.isZero] using hrz
    rw [heq, (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hrz),
      (STAmount.toRat_eq_zero_iff _).mpr (clampToSumExponent_zero _ _ _ _ hm hclamp)]
  · rw [Except.ok.inj (hcl.symm.trans hclamp)]

/-- An integral amount the model prices is a whole number of units: its exponent is zero. -/
lemma Vault.sharesToAssetsWithdraw_integral_exponent (v : Vault) (shares priced : STAmount) (waive : Bool)
    (hint : v.numericType.isIntegral = true) (hpr : v.sharesToAssetsWithdraw shares waive = .ok priced)
    (hnz : priced.mValue ≠ 0) : priced.exponent = 0 := by
  obtain ⟨_, -, -, hcase⟩ := WdPrice.price_cases v _ _ waive hpr
  rcases hcase with ⟨-, rfl⟩ | ⟨-, _, _, an, -, -, -, hof⟩
  · exact absurd (STAmount.zero_mValue _) hnz
  · exact (STAmount.ofNumber_integral_canonical _ an .to_nearest priced hint hof).1.offset_zero

end XRPL.Model.SingleAssetVault
