import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.DepositExits

/-! # Depositing and redeeming at the same close time

A deposit runs only outside the investment and redemption phases, so redeeming the issued shares at
the same close time pays no early-exit fee. On a reachable vault the charge and the payout are both
whole steps of the base grid, each within a step of the issued shares' worth. So they are less than two
steps apart, which makes them at most one step apart. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit runs only outside the investment and redemption phases. -/
private lemma Vault.deposit_phase_open (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    (v.phase t == .investment || v.phase t == .redemption) = false := by
  cases hb : (v.phase t == .investment || v.phase t == .redemption)
  · rfl
  · rw [Vault.deposit_expired_proof v amountDeposit t hpos hb] at hok
    exact absurd hok (by simp)

/-- A deposit runs outside the investment phase, so the vault it leaves charges no early-exit fee
at the same close time. -/
private lemma Vault.deposit_fee_free (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    r.vault'.earlyExitFeeRateAt t = 0 := by
  have hph := Vault.deposit_phase_open v amountDeposit t hpos r hok
  obtain ⟨_, _, hv⟩ := Vault.deposit_frame v _ _ _ _ r hok
  have hsch : r.vault'.schedule = v.schedule := (congrArg RawVault.schedule hv).trans rfl
  have hfee : r.vault'.earlyExitFeeRate = v.earlyExitFeeRate := (congrArg RawVault.earlyExitFeeRate hv).trans rfl
  have hphase : r.vault'.phase t = v.phase t := by unfold Vault.phase; rw [hsch]
  unfold Vault.earlyExitFeeRateAt
  rw [hfee, hphase]
  have hinv : (v.phase t == .investment) = false := by
    cases h : (v.phase t == .investment) <;> simp_all
  split <;> simp [hinv]

/-- A deposit into a vault with shares finds cash or deployed assets: an insolvent vault refuses
the deposit. -/
private lemma Vault.deposit_solvent (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) : v.isInsolvent = false := by
  have hph := Vault.deposit_phase_open v amountDeposit t hpos r hok
  by_contra h
  rw [Vault.deposit_insolvent_proof v amountDeposit t hpos hph (by simpa using h)] at hok
  exact absurd hok (by simp)

/-- A vault with shares that takes a deposit has cash. Nothing is deployed in the Open zone, and an
insolvent vault refuses the deposit. -/
private lemma Vault.OpenZone.deposit_cash_pos {v : Vault} (hz : v.OpenZone) (amountDeposit : STAmount)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hSpos : 0 < (v.toExact.sharesTotal : ℚ)) : 0 < v.assetsAvailable.toRat := by
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hsol := Vault.deposit_solvent v amountDeposit t hpos r hok
  have hSm : v.sharesTotal.mantissa_ ≠ 0 := fun h0 => by
    rw [hcast, Number.toRat_eq_zero_of_mantissa_zero _ h0] at hSpos; exact lt_irrefl _ hSpos
  have hSneg := Number.negative_false_of_pos v.sharesTotal (by rw [← hcast]; exact hSpos)
  have hsig : v.sharesTotal.signum = 1 := by simp [Number.signum, hSneg, hSm]
  have hAm : v.assetsAvailable.mantissa_ ≠ 0 := by
    intro h0
    unfold Vault.isInsolvent at hsol
    rw [hz.assetsDeployed] at hsol
    simp [h0, hsig, Number.zero] at hsol
  exact lt_of_le_of_ne v.exact.assetsAvailable_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))

/-- `1/8` is far above the `Number` underflow threshold. -/
private lemma underflow_small : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 1 / 8 := by
  have h : (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-19 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
  calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (18 : ℕ) * 10 ^ (-19 : ℤ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / 10 := by norm_num
    _ ≤ 1 / 8 := by norm_num

/-- A two-stage `Number` quotient that underflows to zero has an exact value below `1/4`. -/
private lemma pipe_underflow (x y z p q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hz : z.isNormalized) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hz1 : 1 ≤ z.toRat)
    (hmul : x.operator_mul y .to_nearest = .ok p) (hdiv : p.operator_div z .to_nearest = .ok q)
    (hq : q.mantissa_ = 0) : x.toRat * y.toRat / z.toRat ≤ 1 / 4 := by
  have hxy0 := mul_nonneg hx0 hy0
  have hz0 : 0 < z.toRat := by linarith
  have hle : x.toRat * y.toRat / z.toRat ≤ x.toRat * y.toRat := div_le_self hxy0 hz1
  by_cases hxm : x.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero x hxm]; norm_num
  by_cases hym : y.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero y hym]; norm_num
  have ht := underflow_small
  by_cases hpm : p.mantissa_ = 0
  · have h1 := operator_mul_underflow_truth_small x y p _ hx hy hxm hym hmul hpm
    rw [abs_of_nonneg hxy0] at h1
    linarith
  · have hpn := operator_mul_result_isNormalized _ _ _ _ hx hy hxm hym hmul hpm
    have hzm := operator_div_divisor_ne_zero _ _ _ _ hz hdiv
    have hu := operator_div_underflow_truth_small p z q _ hpn hz hpm hzm hdiv hq
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
    rw [abs_div, abs_of_pos hz0, div_lt_iff₀ hz0] at hu
    rw [div_le_iff₀ hz0]
    nlinarith

/-- On an integral vault the shares' price is within `sharesε` and half a unit of their worth at
the computed net asset value, zero or not. -/
private lemma Vault.sharesToAssetsWithdraw_integral_near (v : Vault) (shares priced : STAmount) (w : Bool)
    (nav : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav) (hint : v.numericType.isIntegral = true)
    (hsc : shares.Canonical) (hs0 : 0 ≤ shares.toRat)
    (hpr : v.sharesToAssetsWithdraw shares w = .ok priced) :
    |priced.toRat - v.idealAssetsWithdrawAt nav.toRat shares.toRat| ≤
      v.idealAssetsWithdrawAt nav.toRat shares.toRat * sharesε + 1 / 2 := by
  have hI : v.idealAssetsWithdrawAt nav.toRat shares.toRat =
      nav.toRat * shares.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rw [hI]
  have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  obtain ⟨nav', hsub, hnavn, hcase⟩ := WdPrice.price_cases v _ _ w hpr
  rw [hnav, Except.ok.injEq] at hsub
  subst hsub
  have hN0 := (Vault.assetsTotalForWithdrawal_nonneg v w nav hnav).2
  rcases hcase with ⟨h0, rfl⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [STAmount.zero_toRat _, Number.toRat_eq_zero_of_mantissa_zero _ h0]
    norm_num
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hsc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hSTm := operator_div_divisor_ne_zero _ _ _ _ v.wf.sharesTotal_norm hdiv
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := rat_one_le_of_den_one_pos _ v.wf.sharesTotal_int hSTpos
  rw [← hsnv]
  have hT0 : 0 ≤ nav.toRat * sn0.toRat / v.sharesTotal.toRat :=
    div_nonneg (mul_nonneg hN0 (by rw [hsnv]; exact hs0)) hSTpos.le
  by_cases ham : an.mantissa_ = 0
  · -- the quotient underflowed: the worth is below a quarter and nothing is paid
    have hT := pipe_underflow nav sn0 v.sharesTotal NS an hnavn hsnn v.wf.sharesTotal_norm hN0
      (by rw [hsnv]; exact hs0) hST1 hmul hdiv ham
    have hp0 : priced.mValue = 0 := by
      by_contra hpm
      exact STAmount.ofNumber_integral_source_ne_zero _ an .to_nearest priced hint hof hpm ham
    rw [(STAmount.toRat_eq_zero_iff _).mpr hp0, zero_sub, abs_neg, abs_of_nonneg hT0]
    nlinarith [mul_nonneg hT0 hε]
  obtain ⟨hann, hanpos, hb⟩ := WdPrice.pipe nav sn0 NS an v.sharesTotal hnavn hN0 hsnn (by rw [hsnv]; exact hs0)
    v.wf.sharesTotal_norm hSTpos hmul hdiv ham
  have hh := STAmount.ofNumber_integral_within_half _ an priced hint hann (Number.negative_false_of_pos an hanpos) hof
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  rw [abs_le]
  constructor <;> linarith

/-- An amount of the vault's asset at most one unit of its own last digit above a value below the
Open-zone limit plus three base steps has a unit no coarser than a base step. -/
private lemma Vault.exponent_le_base (v : Vault) (x : STAmount) (hx : x.CanonicalOrZero)
    (hxt : x.mNumericType = v.numericType) (hxm : x.mValue ≠ 0) (hpos : 0 < x.toRat) (y : ℚ)
    (hle : x.toRat ≤ y + 10 ^ x.exponent)
    (hy : y < 9 * 10 ^ 15 * 10 ^ v.baseExponent + 3 * 10 ^ v.baseExponent) :
    x.exponent ≤ v.baseExponent := by
  have hxc : x.Canonical := hx.resolve_right (by simpa [STAmount.isZero] using hxm)
  by_cases hint : v.numericType.isIntegral = true
  · have hoff := (hxc.1 (by unfold STAmount.integral; rw [hxt]; exact hint)).1.offset_zero
    rw [show x.exponent = 0 from hoff, (Vault.baseExponent_bounds v).2.2 hint]
  have hiou := hxc.2 (by unfold STAmount.integral; rw [hxt]; simpa using hint)
  by_contra hgt
  push Not at hgt
  obtain ⟨hcb, -⟩ := STAmount.IOUCanonical.toRat_bounds x hiou hpos
  have h10 : 10 * (10 : ℚ) ^ v.baseExponent ≤ 10 ^ x.exponent := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10) (show v.baseExponent + 1 ≤ x.exponent by omega)
    rw [zpow_add_one₀ (by norm_num)] at this; linarith
  rw [zpow_add₀ (by norm_num)] at hcb
  norm_num at hcb
  have : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  nlinarith

/-- A fractional Open-zone vault with cash prices a positive share count above zero. The worth is
at least `10⁻²⁹`, far above the smallest IOU amount. -/
private lemma Vault.OpenZone.sharesToAssetsWithdraw_ne_zero {v : Vault} (hz : v.OpenZone)
    (hfr : v.numericType.isIntegral = false) (hA : 0 < v.assetsAvailable.toRat)
    (shares priced : STAmount) (w : Bool) (hsic : shares.IntegralCanonical)
    (hs64 : shares.mNumericType = .int64) (hspos : 0 < shares.toRat)
    (hpr : v.sharesToAssetsWithdraw shares w = .ok priced) : priced.mValue ≠ 0 := by
  intro hpz
  have hsc : shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨nav, hnav, hnavn, hcase⟩ := WdPrice.price_cases v _ _ w hpr
  rw [hz.assetsTotalForWithdrawal_eq w, Except.ok.injEq] at hnav
  subst hnav
  rcases hcase with ⟨h0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hA; exact lt_irrefl _ hA
  obtain ⟨-, hA10⟩ := hz.cash_ge hA
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hsc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hs1 : (1 : ℚ) ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  obtain ⟨hSTpos, hST1, hST⟩ := Vault.sharesTotal_bounds_of_cash v hA
  set T := v.assetsAvailable.toRat * sn0.toRat / v.sharesTotal.toRat with hT
  have hT29 : (10 : ℚ) ^ (-29 : ℤ) ≤ T := by
    rw [hT, hsnv, le_div_iff₀ hSTpos]
    have h19 : (10 : ℚ) ^ (-29 : ℤ) * (2 ^ 63 - 1) ≤ 10 ^ (-10 : ℤ) := by norm_num
    calc (10 : ℚ) ^ (-29 : ℤ) * v.sharesTotal.toRat ≤ 10 ^ (-29 : ℤ) * (2 ^ 63 - 1) :=
          mul_le_mul_of_nonneg_left hST (by positivity)
      _ ≤ 10 ^ (-10 : ℤ) * 1 := by rw [mul_one]; exact h19
      _ ≤ v.assetsAvailable.toRat * shares.toRat :=
          mul_le_mul hA10 hs1 zero_le_one (le_trans (by positivity) hA10)
  obtain ⟨hann, -, hb⟩ := pipe_large v.assetsAvailable sn0 NS an v.sharesTotal hnavn hsnn v.wf.sharesTotal_norm
    hA.le (by rw [hsnv]; exact hspos.le) hSTpos hST1
    (le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hT29) hmul hdiv
  rw [← hT] at hb
  obtain ⟨hb1, -⟩ := abs_le.mp hb
  have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ an.toRat := by
    have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-29 : ℤ) / 2 := by norm_num
    have hT0 : 0 ≤ T := le_trans (zpow_pos (by norm_num) _).le hT29
    have h1 : T / 2 ≤ T * (1 - sharesε) := by unfold sharesε; nlinarith
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-29 : ℤ) / 2 := h81
      _ ≤ T / 2 := div_le_div_of_nonneg_right hT29 (by norm_num)
      _ ≤ T * (1 - sharesε) := h1
      _ ≤ an.toRat := by linarith
  exact STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest priced hann hge
    (NumericType.eq_fractional_of_not_integral hfr ▸ hof) hpz

/-- A non-final withdrawal with no fee from a reachable vault pays at least the burned shares' worth less
`sharesε` of it and one step of the base grid. The payout is the priced amount floored onto the base grid. -/
private lemma Vault.Reachable.withdraw_payout_ge_nofee (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfee : v.earlyExitFeeRateAt t = 0) (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    v.idealAssetsWithdraw waive r.shares.toRat * (1 - sharesε) - (10 : ℚ) ^ v.baseExponent ≤
      r.assets.toRat := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hnavN := hz.assetsTotalForWithdrawal_eq waive
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hIat : v.idealAssetsWithdrawAt v.assetsAvailable.toRat r.shares.toRat =
      v.assetsAvailable.toRat * r.shares.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt; rw [hST]
  rw [hz.idealAssetsWithdraw_eq]
  have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hSpos : 0 < v.sharesTotal.toRat := by rw [← hST]; linarith
  have hI0 : 0 ≤ v.assetsAvailable.toRat * r.shares.toRat / v.sharesTotal.toRat :=
    div_nonneg (mul_nonneg hA0 hspos.le) hSpos.le
  obtain ⟨priced, hpr, hcase⟩ := Vault.withdraw_payout_cases v amount waive t hpos hc hty r hok hlt
  have hple := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax _ _ waive hspos.le hsc hlt.le hpr
  have hopen := (Vault.Reachable.openZone_proof v t0 hr hmax).assetsAvailable_le_openLimit
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral payout is the priced amount, within `sharesε` and half a unit of the worth
    have hb0 := (Vault.baseExponent_bounds v).2.2 hint
    have hnear := Vault.sharesToAssetsWithdraw_integral_near v _ _ waive v.assetsAvailable hnavN hint hsc
      hspos.le hpr
    rw [hIat] at hnear
    obtain ⟨hn1, -⟩ := abs_le.mp hnear
    rw [hb0, zpow_zero]
    -- the payout is the priced amount, or nothing when the price is zero
    have hpay : r.assets.toRat = priced.toRat := by
      rcases hcase with ⟨h0, hz0⟩ | ⟨aN, fee, pN, -, payout, hlow, haN, hfeeE, hsub, hpo, hpz, hcl, -, -, -⟩
      · rcases hz0 with hmaxr | hp0
        · exact absurd (hfee.symm.trans hmaxr) (by decide)
        · rw [h0, hp0]
      · obtain ⟨hpc, hp0, hsmall⟩ := Vault.withdraw_priced_facts v _ _ waive hmax hsc hspos hpr
        obtain ⟨hav, han⟩ := hpc.toNumber_exact aN haN
        obtain ⟨hflo, hfhi⟩ := tenthBipsOfValue_upward_bounds aN _ fee han (hav ▸ hp0) (hav ▸ hsmall) hfeeE
        rw [hfee] at hflo hfhi
        have hfn := (tenthBipsOfValue_upward_facts aN _ fee han (hav ▸ hp0) hfeeE).1
        have hf0 : fee.toRat = 0 := le_antisymm (by simpa using hfhi) (by simpa using hflo)
        have hfm : fee.mantissa_ = 0 := by
          by_contra h; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h hf0
        rw [Number.operator_sub_zero_right aN fee .downward hfn hfm, Except.ok.injEq] at hsub
        subst hsub
        have hpm : payout.mValue ≠ 0 := by simpa [STAmount.isZero] using hpz
        have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).2
        have hPd : priced.toRat.den = 1 := by
          rcases hpc with hcan | hz'
          · exact (hcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1.den_eq_one
          · rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz')]; rfl
        have hYv : payout.toRat = priced.toRat := by
          rw [STAmount.ofNumber_integral_exact _ aN .downward payout hint han (by rw [hav]; exact hPd) hpo, hav]
        have hni : payout.operator_neg.integral = true := by
          unfold STAmount.integral
          rw [(STAmount.operator_neg_fields payout).1, STAmount.ofNumber_mNumericType _ _ _ _ hpo]
          exact hint
        rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
        obtain ⟨-, -, -, hrat⟩ := clamp_magnitude payout.operator_neg
        have hpay0 := STAmount.ofNumber_nonneg _ _ _ _ han
          (Number.negative_false_of_nonneg aN han (by rw [hav]; exact hp0)) hpo
        rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0] at hrat
        rw [hrat, hYv]
    rw [hpay]
    linarith
  -- a fractional payout is the priced amount floored onto the base grid
  have hfr : v.numericType.isIntegral = false := by simpa using hint
  have hvfr := NumericType.eq_fractional_of_not_integral hfr
  rcases eq_or_lt_of_le hA0 with hAz | hApos
  · rw [← hAz, zero_mul, zero_div, zero_mul, zero_sub]
    have := (Vault.withdraw_payout_units v amount waive t hpos hz hmax r hok).2.1
    obtain ⟨j, hj⟩ := this
    have : (0 : ℚ) ≤ (j : ℚ) * 10 ^ v.baseExponent := by positivity
    linarith
  have hpm := hz.sharesToAssetsWithdraw_ne_zero hfr hApos _ _ waive hsic hs64 hspos hpr
  obtain ⟨-, -, hbL⟩ := Vault.sharesToAssetsWithdraw_bounds_proof v r.shares priced waive hspos.le hsc
    (hz.withdrawNavExact waive) hpr
  rw [hz.idealAssetsWithdraw_eq] at hbL
  have hlow := hbL (by simpa [STAmount.isZero] using hpm)
  rcases hcase with ⟨-, hz0⟩ | ⟨aN, fee, pN, -, payout, -, haN, hfeeE, hsub, hpo, hpz, hcl, hfnp, -, -⟩
  · rcases hz0 with hmaxr | hp0
    · exact absurd (hfee.symm.trans hmaxr) (by decide)
    · exact absurd ((STAmount.toRat_eq_zero_iff _).mp hp0) hpm
  obtain ⟨hpc, hp0, hsmall⟩ := Vault.withdraw_priced_facts v _ _ waive hmax hsc hspos hpr
  obtain ⟨hav, han⟩ := hpc.toNumber_exact aN haN
  obtain ⟨hflo, hfhi⟩ := tenthBipsOfValue_upward_bounds aN _ fee han (hav ▸ hp0) (hav ▸ hsmall) hfeeE
  rw [hfee] at hflo hfhi
  have hfn := (tenthBipsOfValue_upward_facts aN _ fee han (hav ▸ hp0) hfeeE).1
  have hf0 : fee.toRat = 0 := le_antisymm (by simpa using hfhi) (by simpa using hflo)
  have hfm : fee.mantissa_ = 0 := by
    by_contra h; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h hf0
  rw [Number.operator_sub_zero_right aN fee .downward hfn hfm, Except.ok.injEq] at hsub
  subst hsub
  have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).2
  have hppos : 0 < priced.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
  have hPc : priced.Canonical := hpc.resolve_right (by simpa [STAmount.isZero] using hpm)
  have hPiou : priced.IOUCanonical := hPc.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  have hpaym : payout.mValue ≠ 0 := by simpa [STAmount.isZero] using hpz
  have hY : payout = priced := STAmount.ofNumber_downward_self _ priced (Or.inl hPiou) hpt hppos aN han hav
    payout hpo hpaym
  subst hY
  have hrc := clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hrt : r.assets.mNumericType = .fractional := by
    rw [hrc.2.1, (STAmount.operator_neg_fields _).1, hpt, hvfr]
  have hrm : r.assets.mValue ≠ 0 := fun h0 => by
    rw [STAmount.isFractionalNonPositive_zero _ hrt h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hrc.2.2 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
  have hRiou : r.assets.IOUCanonical :=
    (hrc.1.resolve_right (by simpa [STAmount.isZero] using hrm)).2 (by unfold STAmount.integral; rw [hrt]; rfl)
  have hfl := Vault.Reachable.clamp_base v t0 hr hmax payout r.assets hpc (by rw [hpt, hvfr]) hp0 hple hrm hcl
  obtain ⟨-, hL⟩ := STAmount.IOUCanonical.floor_bounds payout r.assets _ hPiou hRiou hrpos hfl
  have hrle : r.assets.toRat ≤ payout.toRat := by
    have h := clampToSumExponent_le_abs _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rwa [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hp0] at h
  have hpp : (0 : ℚ) < 10 ^ payout.exponent := zpow_pos (by norm_num) _
  have hRe : r.assets.exponent ≤ v.baseExponent :=
    le_trans (STAmount.IOUCanonical.exponent_le _ _ hRiou hPiou hrpos hrle)
      (Vault.exponent_le_base v payout hpc hpt hpaym hppos payout.toRat (by linarith)
        (by rw [zpow_add₀ (by norm_num)] at hopen; linarith))
  have hre : (10 : ℚ) ^ r.assets.exponent ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) hRe
  have hrp : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
  have hm : max (1 / 2 * (10 : ℚ) ^ r.assets.exponent)
      ((10 : ℚ) ^ v.baseExponent - 1 / 2 * (10 : ℚ) ^ r.assets.exponent) ≤ 10 ^ v.baseExponent :=
    max_le (by linarith) (by linarith)
  linarith

/-- Two whole numbers of base steps less than two steps apart are at most one step apart. -/
private lemma grid_steps_le_one (x y : ℚ) (b jx jy : ℤ) (hx : x = (jx : ℚ) * 10 ^ b)
    (hy : y = (jy : ℚ) * 10 ^ b) (h : x - y < 2 * 10 ^ b) : x - y ≤ 10 ^ b := by
  by_contra hgt
  push Not at hgt
  have := grid_diff_ge x (y + 10 ^ b) b b jx (jy + 1) hx (by rw [hy]; push_cast; ring) (by linarith)
  rw [min_self] at this
  linarith

/-- The round-trip arithmetic. A charge `c` within `I·sharesε` plus a step `u` of the shares' worth `I`, and
a payout within `sharesε` plus a step of the worth `c + (I - c)·λ` after the deposit, are less than two steps apart. -/
private lemma roundtrip_steps (I c lam π u : ℚ) (hu : 0 < u) (hI0 : 0 ≤ I) (hc0 : 0 ≤ c)
    (hcle : c ≤ 9 * 10 ^ 15 * u) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hc1 : I * (1 - sharesε) - u ≤ c) (hc2 : c - I ≤ I * sharesε + 1 / 2 * u)
    (hup : π ≤ (c + (I - c) * lam) * (1 + sharesε) + 1 / 2 * u)
    (hlo : (c + (I - c) * lam) * (1 - sharesε) - u ≤ π) :
    π - c < 2 * u ∧ c - π < 2 * u := by
  unfold sharesε at hc1 hc2 hup hlo
  have hd1 : (I - c) * lam ≤ I * (11 / 10 ^ 19) + u := by
    have h1 : I - c ≤ I * (11 / 10 ^ 19) + u := by linarith
    calc (I - c) * lam ≤ (I * (11 / 10 ^ 19) + u) * lam := mul_le_mul_of_nonneg_right h1 hlam0
      _ ≤ I * (11 / 10 ^ 19) + u := mul_le_of_le_one_right (by positivity) hlam1
  have hd2 : (c - I) * lam ≤ I * (11 / 10 ^ 19) + 1 / 2 * u := by
    calc (c - I) * lam ≤ (I * (11 / 10 ^ 19) + 1 / 2 * u) * lam := mul_le_mul_of_nonneg_right hc2 hlam0
      _ ≤ I * (11 / 10 ^ 19) + 1 / 2 * u := mul_le_of_le_one_right (by positivity) hlam1
  -- the worth is at most twice the charge plus two steps, so its relative error is tiny
  have hIle : I ≤ 2 * c + 2 * u := by
    have h1 : I / 2 ≤ I * (1 - 11 / 10 ^ 19) := by nlinarith
    linarith
  have hI'0 : 0 ≤ c + (I - c) * lam := by
    have : c + (I - c) * lam = c * (1 - lam) + I * lam := by ring
    rw [this]; exact add_nonneg (mul_nonneg hc0 (by linarith)) (mul_nonneg hI0 hlam0)
  have hI'le : c + (I - c) * lam ≤ 3 * c + 3 * u := by nlinarith
  have hs1 : I * (11 / 10 ^ 19) ≤ 1 / 10 * u := by nlinarith
  have hs2 : (c + (I - c) * lam) * (11 / 10 ^ 19) ≤ 1 / 10 * u := by nlinarith
  constructor
  · have e : (c + (I - c) * lam) * (1 + 11 / 10 ^ 19) =
        c + (I - c) * lam + (c + (I - c) * lam) * (11 / 10 ^ 19) := by ring
    linarith
  · have e : (c + (I - c) * lam) * (1 - 11 / 10 ^ 19) =
        c + (I - c) * lam - (c + (I - c) * lam) * (11 / 10 ^ 19) := by ring
    have e2 : (c - I) * lam = -((I - c) * lam) := by ring
    linarith

/-- The round-trip gain arithmetic. A redemption half a step above the charge cannot reach the value the
charge was priced from: the worth drops by `I·(W - c)/A` across the deposit, more than the pricing errors. -/
private lemma roundtrip_no_gain_arith (A I c W B q an δ : ℚ) (hA : 0 < A) (hI : 0 ≤ I)
    (hc0 : 0 ≤ c) (hB : 0 < B) (hopen : A + c ≤ 9 * 10 ^ 15 * B)
    (hW : W * (A + I) = (A + c) * I)
    (hq : I * (1 - sharesε) ≤ q) (hqan : q ≤ an + δ) (han : an ≤ W * (1 + sharesε))
    (hδ : 2 * 10 ^ 16 * δ ≤ W * (1 + 1 / 10 ^ 15))
    (hWc : c + B / 2 ≤ W * (1 + sharesε)) : False := by
  unfold sharesε at hq han hWc
  have hAI : 0 < A + I := by linarith
  -- the worth after the deposit is a weighted mean of the cash plus charge and the worth before it
  have hWle : W ≤ A + c := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hAI
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ A + c) hA.le]
  have hcW : c < W := by linarith
  have hkey : A * (I - W) = I * (W - c) := by linear_combination (-1 : ℚ) * hW
  have hIW : W ≤ I := by
    by_contra h
    push Not at h
    have h1 : A * (I - W) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
    have h2 : 0 ≤ I * (W - c) := mul_nonneg hI (by linarith)
    linarith
  have hIpos : 0 < I := by linarith
  -- the pricing errors bound the gap between the two worths
  have h1 : I - W ≤ 11 / 10 ^ 19 * (I + W) + δ := by linarith
  have h2 : I * (W - c) ≤ A * (11 / 10 ^ 19 * (I + W) + δ) := by
    rw [← hkey]; exact mul_le_mul_of_nonneg_left h1 hA.le
  have h3 : I * (B / 2 - 11 / 10 ^ 19 * W) ≤ I * (W - c) := mul_le_mul_of_nonneg_left (by linarith) hI
  have h4 : A * δ ≤ A * (I * (1 + 1 / 10 ^ 15) / (2 * 10 ^ 16)) :=
    mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ (by norm_num)]; nlinarith) hA.le
  have h5 : A * (11 / 10 ^ 19 * (I + W)) ≤ A * (11 / 10 ^ 19 * (2 * I)) :=
    mul_le_mul_of_nonneg_left (by linarith) hA.le
  have h6 : I * (B / 2 - 11 / 10 ^ 19 * W) ≤
      I * (2 * A * (11 / 10 ^ 19) + A * (1 + 1 / 10 ^ 15) / (2 * 10 ^ 16)) := by
    have : A * (11 / 10 ^ 19 * (2 * I)) + A * (I * (1 + 1 / 10 ^ 15) / (2 * 10 ^ 16)) =
        I * (2 * A * (11 / 10 ^ 19) + A * (1 + 1 / 10 ^ 15) / (2 * 10 ^ 16)) := by ring
    nlinarith
  have h7 := le_of_mul_le_mul_left h6 hIpos
  linarith

/-- A redemption priced at or above a grid point `g` reaches the charge's pricing. Its source value `an` is
at least the value `q` half a unit `10^e` below `g`, less half that unit when the priced amount enters a new decade. -/
private lemma redemption_reaches_charge_price (nt : NumericType) (priced : STAmount) (an : Number) (q W g : ℚ)
    (e : ℤ) (hpc : priced.CanonicalOrZero) (hpt : priced.mNumericType = nt) (hpm : priced.mValue ≠ 0)
    (hp0 : 0 < priced.toRat) (hof : STAmount.ofNumber nt an .to_nearest = .ok priced)
    (hann : an.isNormalized) (hanpos : 0 < an.toRat)
    (hphi : priced.toRat - an.toRat ≤ 1 / 2 * 10 ^ priced.exponent) (han : an.toRat ≤ W * (1 + sharesε))
    (hWnn : 0 ≤ W) (hge : g ≤ priced.toRat) (helo : -96 ≤ e) (hehi : e ≤ 80)
    (hqg : q + 1 / 2 * 10 ^ e ≤ g) (hg16 : g ≤ 10 ^ (e + 16)) (heint : nt.isIntegral = true → e = 0) :
    ∃ δ : ℚ, q ≤ an.toRat + δ ∧ 2 * 10 ^ 16 * δ ≤ W * (1 + 1 / 10 ^ 15) := by
  by_cases hle₁ : priced.exponent ≤ e
  · -- the priced amount keeps the charge's unit or a finer one
    have : (10 : ℚ) ^ priced.exponent ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) hle₁
    exact ⟨0, by linarith, by nlinarith⟩
  push Not at hle₁
  have hpc' : priced.Canonical := hpc.resolve_right (by simpa [STAmount.isZero] using hpm)
  by_cases hint : nt.isIntegral = true
  · have hoff := (hpc'.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1.offset_zero
    have he0 := heint hint
    exact absurd hle₁ (by rw [show priced.exponent = 0 from hoff, he0]; exact lt_irrefl 0)
  have hvfr : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral _ _ _ _ => exact absurd rfl hint
  have hpiou := hpc'.2 (by unfold STAmount.integral; rw [hpt]; simpa using hint)
  -- the largest sixteen-digit amount of the charge's unit lies below the priced amount
  let a : STAmount := ⟨.fractional, 9999999999999999, e, false⟩
  have ha : a.ExactCanonical := Or.inl ⟨rfl, show 10 ^ 15 ≤ (9999999999999999 : UInt64).toNat by decide,
    show (9999999999999999 : UInt64).toNat < 10 ^ 16 by decide, by exact helo, by exact hehi⟩
  have haval : a.toRat = 9999999999999999 * 10 ^ e := by
    rw [STAmount.toRat_of_nonneg a rfl]
    show ((9999999999999999 : UInt64).toNat : ℚ) * 10 ^ e = _
    rw [show (9999999999999999 : UInt64).toNat = 9999999999999999 by decide]
    push_cast; ring
  have h16 : (10 : ℚ) ^ (e + 16) = 10 ^ 16 * 10 ^ e := by rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have hpbig : (10 : ℚ) ^ (e + 16) ≤ priced.toRat :=
    le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) (STAmount.IOUCanonical.toRat_bounds priced hpiou hp0).1
  -- so the value the redemption is priced from lies above it too
  have hana : a.toRat < an.toRat := by
    by_contra h
    push Not at h
    have := STAmount.ofNumber_to_nearest_le_of_canonical nt an priced a hann hanpos.le ha
      (show NumericType.fractional = nt by rw [hvfr]) h hof hpm
    rw [haval] at this
    rw [h16] at hpbig
    linarith
  rw [haval] at hana
  rw [h16] at hg16
  refine ⟨1 / 2 * 10 ^ e, by linarith, ?_⟩
  unfold sharesε at han
  linarith

/-- A round trip on a reachable vault with shares never pays back more than it took. A gain needs the
redemption to round up to the base step above the charge, past the value the charge was priced from. -/
private lemma Vault.roundtrip_payout_le_charge (v : Vault) (amountDeposit : STAmount) (waive : Bool)
    (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0) (ht : t0 ≤ t)
    (hcanon : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r₁ : VaultWithAmounts) (hok₁ : (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.shares.toRat ≤ 2 ^ 63 - 1)
    (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts)
    (hok₂ : (r₁.vault'.withdraw (.vaultShares r₁.shares) waive t hpos₂).run = .ok (.ok r₂))
    (hSpos : 0 < (v.toExact.sharesTotal : ℚ)) :
    r₂.assets.toRat ≤ r₁.assets.toRat := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hr' : Vault.Reachable r₁.vault' t :=
    Vault.Reachable.deposit v t0 t amountDeposit false r₁ hr ht hcanon hty hpos hok₁ hSsz
  have hnt := Vault.deposit_numericType v amountDeposit false t hpos r₁ hok₁
  have hbe := Vault.deposit_baseExponent v amountDeposit false t hpos r₁ hok₁
  have hmax' : r₁.vault'.numericType.isIntegral = true → r₁.vault'.numericType.maxValue.toNat ≤ maxRep.toNat :=
    hnt ▸ hmax
  have hz' := Vault.Reachable.openZone_proof r₁.vault' t hr' hmax'
  obtain ⟨hAA', -⟩ := Vault.deposit_openZone v amountDeposit false t hpos hcanon hty hz r₁ hok₁
  have hST' := Vault.deposit_exact_sharesTotal v amountDeposit false t hpos hcanon hty r₁ hok₁ hSsz
  obtain ⟨-, priced₁, navN, -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, -, hcl, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r₁ hok₁
  have hshc' : r₁.shares.Canonical := hshc.canonical (by rw [hshnt]; decide)
  have hrs := Vault.withdraw_sharesRedeemed_exact_proof r₁.vault' r₁.shares waive t hpos₂ r₂ hok₂
  have hwc : (WithdrawAmount.vaultShares r₁.shares).amount.Canonical := hshc'
  have hwt : (WithdrawAmount.vaultShares r₁.shares).InAsset r₁.vault'.numericType := hshnt
  have hu : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hcast' := RawVault.WF.toExact_sharesTotal r₁.vault'.toRawVault r₁.vault'.wf
  -- the charge and the payout are whole steps of the base grid
  obtain ⟨kA, -, hkA⟩ := hz.cash
  obtain ⟨kA', -, hkA'⟩ := hz'.cash
  rw [hbe] at hkA'
  have hcgrid : r₁.assets.toRat = ((kA' - kA : ℤ) : ℚ) * 10 ^ v.baseExponent := by
    push_cast; rw [sub_mul, ← hkA', ← hkA]; linarith
  obtain ⟨-, ⟨jπ, hjπ⟩, -, -⟩ := Vault.withdraw_payout_units r₁.vault' _ waive t hpos₂ hz' hmax' r₂ hok₂
  rw [hbe] at hjπ
  have hπgrid : r₂.assets.toRat = ((jπ : ℤ) : ℚ) * 10 ^ v.baseExponent := by rw [hjπ]; push_cast; rfl
  have hc0 := (DepRnd.Vault.deposit_charge_bounds v r₁.shares priced₁ r₁.assets navN hshc hshnt hshpos hsad hcl).1
  have hApos := hz.deposit_cash_pos amountDeposit t hpos r₁ hok₁ hSpos
  have hlt' : r₂.shares.toRat < r₁.vault'.toExact.sharesTotal := by
    rw [hrs, hST']; linarith
  have hfee := Vault.deposit_fee_free v amountDeposit t hpos r₁ hok₁
  have hIc : v.idealChargeDeposit r₁.shares.toRat =
      v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealChargeDeposit
    have hAT : v.toExact.assetsTotal ≠ 0 := by
      show v.assetsAvailable.toRat + v.assetsDeployed.toRat ≠ 0
      rw [hz.assetsDeployed, Number.toRat_zero, add_zero]; exact ne_of_gt hApos
    rw [if_neg hAT, hz.depositNav_eq]
  have hI0 : 0 ≤ v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) :=
    div_nonneg (mul_nonneg hA0 hshpos.le) hSpos.le
  by_contra hgt
  push Not at hgt
  -- both are whole steps of the base grid, so the payout is a whole step above the charge
  have hstep : r₁.assets.toRat + 10 ^ v.baseExponent ≤ r₂.assets.toRat := by
    have := grid_diff_ge _ _ _ _ jπ (kA' - kA) hπgrid hcgrid hgt
    rw [min_self] at this
    linarith
  -- with no fee the payout is at most the priced amount
  obtain ⟨priced, hpr, hle⟩ :=
    Vault.withdraw_payout_le_proof r₁.vault' _ waive t hpos₂ hwc hwt hmax' r₂ hok₂ hlt'
  rw [hrs] at hpr
  rw [hfee, show ((0 : TenthBips32).toNat : ℚ) = 0 by rfl, zero_div, sub_zero, mul_one] at hle
  obtain ⟨hpc, hpt⟩ := Vault.sharesToAssetsWithdraw_form r₁.vault' _ _ waive hmax' hpr
  obtain ⟨nav, hnav, -, -, hcase⟩ := WdPrice.price_spec r₁.vault' r₁.shares priced waive hshpos.le hshc' hpr
  have hnavc : nav = r₁.vault'.assetsAvailable :=
    Except.ok.inj (hnav.symm.trans (hz'.assetsTotalForWithdrawal_eq waive))
  rcases hcase with hpm | ⟨-, -, an, hanpos, hanb, hpan, hann, hof⟩
  · have : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr hpm
    linarith
  have hpm : priced.mValue ≠ 0 := fun h => by
    have : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr h
    linarith
  have hp0 : 0 < priced.toRat := by linarith
  -- the priced amount's own unit is at most a base step
  have hple := Vault.Reachable.sharesToAssetsWithdraw_le_cash r₁.vault' t hr' hmax' _ _ waive hshpos.le hshc'
    (by rw [← hrs]; exact hlt'.le) hpr
  have hop := hz.deposit_open amountDeposit false t hpos hcanon hty r₁ hok₁
  have hpe : (10 : ℚ) ^ priced.exponent ≤ 10 ^ v.baseExponent := by
    have hpp : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
    have h9 : 9 * (10 : ℚ) ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; ring
    have := Vault.exponent_le_base r₁.vault' priced hpc hpt hpm hp0 priced.toRat (by linarith)
      (by rw [hbe]; linarith)
    rw [hbe] at this
    exact zpow_le_zpow_right₀ (by norm_num) this
  -- the charge was priced from a value half a unit below the next base step above it
  have hmz : v.assetsAvailable.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hApos; exact lt_irrefl _ hApos
  obtain ⟨q, e₁, he₁lo, he₁b, hq, hqg, hg16, he₁int⟩ := Vault.deposit_charge_open_grid v amountDeposit t hcanon
    hpos v.assetsAvailable hz.assetsTotal_eq hmz r₁ hok₁
  have hIat : v.idealChargeDepositAt v.assetsAvailable.toRat r₁.shares.toRat =
      v.idealChargeDeposit r₁.shares.toRat := by
    rw [← hz.depositNav_eq, RawVault.idealChargeDepositAt_depositNav]
  rw [hIat, hIc] at hq
  -- the redemption's priced value against the worth after the deposit
  obtain ⟨-, hanhi⟩ := abs_le.mp hanb
  obtain ⟨-, hphi⟩ := abs_le.mp hpan
  rw [hnavc, ← hcast', hST', hAA'] at hanhi
  set W := (v.assetsAvailable.toRat + r₁.assets.toRat) * r₁.shares.toRat /
    ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) with hWdef
  have hWnn : 0 ≤ W := div_nonneg (mul_nonneg (by linarith) hshpos.le) (by linarith)
  have han : an.toRat ≤ W * (1 + sharesε) := by linarith
  have hWc : r₁.assets.toRat + 10 ^ v.baseExponent / 2 ≤ W * (1 + sharesε) := by linarith
  have hbb := v.baseExponent_range.2
  obtain ⟨δ, hqan, hδ⟩ := redemption_reaches_charge_price r₁.vault'.numericType priced an q W
    (r₁.assets.toRat + 10 ^ v.baseExponent) e₁ hpc hpt hpm hp0 hof hann hanpos hphi han hWnn (by linarith)
    he₁lo (by omega) hqg hg16 (fun h => he₁int (hnt ▸ h))
  exact roundtrip_no_gain_arith v.assetsAvailable.toRat
    (v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ)) r₁.assets.toRat W
    (10 ^ v.baseExponent) q an.toRat δ hApos hI0 hc0 hu
    (by rw [zpow_add₀ (by norm_num)] at hop; linarith)
    (by rw [hWdef]; field_simp) hq hqan han hδ hWc

/-- Proof of `Vault.deposit_withdraw_roundtrip`. The charge and the payout are whole base steps, each within the
pricing errors and a step of the shares' worth, so they are less than two steps apart, and a gain is ruled out. -/
lemma Vault.deposit_withdraw_roundtrip_proof (v : Vault) (amountDeposit : STAmount) (waive : Bool)
    (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0) (ht : t0 ≤ t)
    (hcanon : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r₁ : VaultWithAmounts) (hok₁ : (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.shares.toRat ≤ 2 ^ 63 - 1)
    (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts)
    (hok₂ : (r₁.vault'.withdraw (.vaultShares r₁.shares) waive t hpos₂).run = .ok (.ok r₂)) :
    r₂.assets.toRat ≤ r₁.assets.toRat ∧
      r₁.assets.toRat - r₂.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hr' : Vault.Reachable r₁.vault' t :=
    Vault.Reachable.deposit v t0 t amountDeposit false r₁ hr ht hcanon hty hpos hok₁ hSsz
  have hnt := Vault.deposit_numericType v amountDeposit false t hpos r₁ hok₁
  have hbe := Vault.deposit_baseExponent v amountDeposit false t hpos r₁ hok₁
  have hmax' : r₁.vault'.numericType.isIntegral = true → r₁.vault'.numericType.maxValue.toNat ≤ maxRep.toNat :=
    hnt ▸ hmax
  have hz' := Vault.Reachable.openZone_proof r₁.vault' t hr' hmax'
  obtain ⟨hAA', -⟩ := Vault.deposit_openZone v amountDeposit false t hpos hcanon hty hz r₁ hok₁
  have hST' := Vault.deposit_exact_sharesTotal v amountDeposit false t hpos hcanon hty r₁ hok₁ hSsz
  obtain ⟨-, priced₁, navN, -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, -, hcl, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r₁ hok₁
  have hshc' : r₁.shares.Canonical := hshc.canonical (by rw [hshnt]; decide)
  have hrs := Vault.withdraw_sharesRedeemed_exact_proof r₁.vault' r₁.shares waive t hpos₂ r₂ hok₂
  have hwc : (WithdrawAmount.vaultShares r₁.shares).amount.Canonical := hshc'
  have hwt : (WithdrawAmount.vaultShares r₁.shares).InAsset r₁.vault'.numericType := hshnt
  have hu : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hcast' := RawVault.WF.toExact_sharesTotal r₁.vault'.toRawVault r₁.vault'.wf
  -- the charge and the payout are whole steps of the base grid
  obtain ⟨kA, -, hkA⟩ := hz.cash
  obtain ⟨kA', hkA'le, hkA'⟩ := hz'.cash
  rw [hbe] at hkA'
  have hcgrid : r₁.assets.toRat = ((kA' - kA : ℤ) : ℚ) * 10 ^ v.baseExponent := by
    push_cast; rw [sub_mul, ← hkA', ← hkA]; linarith
  obtain ⟨-, ⟨jπ, hjπ⟩, -, -⟩ := Vault.withdraw_payout_units r₁.vault' _ waive t hpos₂ hz' hmax' r₂ hok₂
  rw [hbe] at hjπ
  have hπgrid : r₂.assets.toRat = ((jπ : ℤ) : ℚ) * 10 ^ v.baseExponent := by rw [hjπ]; push_cast; rfl
  have hc0 := (DepRnd.Vault.deposit_charge_bounds v r₁.shares priced₁ r₁.assets navN hshc hshnt hshpos hsad hcl).1
  have hopen' : r₁.vault'.assetsAvailable.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
    rw [hkA']
    have : (kA' : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hkA'le
    nlinarith
  have hcle : r₁.assets.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by linarith
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hS0 with hSz | hSpos
  · -- from an empty vault the redemption is the final withdrawal, which pays all the cash
    have hz0 : v.toExact.sharesTotal = 0 := by exact_mod_cast hSz.symm
    obtain ⟨hAAz, -⟩ := v.exact.empty_shares hz0
    change v.assetsAvailable.toRat = 0 at hAAz
    have hfinal : r₂.shares.toRat = r₁.vault'.toExact.sharesTotal := by
      rw [hrs, hST', ← hSz, zero_add]
    obtain ⟨hπ, -, -⟩ := Vault.withdraw_final_proof r₁.vault' (.vaultShares r₁.shares) waive t t hpos₂ hr' hwc hwt
      hmax' r₂ hok₂ hfinal
    refine ⟨by rw [hπ, hAA', hAAz, zero_add], ?_⟩
    rw [hπ, hAA', hAAz, zero_add, sub_self]
    exact hu.le
  have hApos := hz.deposit_cash_pos amountDeposit t hpos r₁ hok₁ hSpos
  have hlt' : r₂.shares.toRat < r₁.vault'.toExact.sharesTotal := by
    rw [hrs, hST']; linarith
  have hfee := Vault.deposit_fee_free v amountDeposit t hpos r₁ hok₁
  -- the charge against the issued shares' worth
  obtain ⟨-, hc1, -, hc2⟩ := Vault.Reachable.deposit_charge_proof v amountDeposit t t0 hpos hr hcanon r₁ hok₁
  have hIc : v.idealChargeDeposit r₁.shares.toRat =
      v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealChargeDeposit
    have hAT : v.toExact.assetsTotal ≠ 0 := by
      show v.assetsAvailable.toRat + v.assetsDeployed.toRat ≠ 0
      rw [hz.assetsDeployed, Number.toRat_zero, add_zero]; exact ne_of_gt hApos
    rw [if_neg hAT, hz.depositNav_eq]
  rw [hIc] at hc1 hc2
  -- the payout against the redeemed shares' worth after the deposit
  obtain ⟨priced, hpr, hU⟩ := Vault.withdraw_payout_le_priced r₁.vault' _ waive t hpos₂ hwc hwt hmax' r₂ hok₂ hlt'
  rw [hrs] at hpr
  obtain ⟨-, hbU, -⟩ := Vault.sharesToAssetsWithdraw_bounds_proof r₁.vault' r₁.shares priced waive hshpos.le
    hshc' (hz'.withdrawNavExact waive) hpr
  rw [hz'.idealAssetsWithdraw_eq] at hbU
  have hlow := Vault.Reachable.withdraw_payout_ge_nofee r₁.vault' t hr' hmax' _ waive t hpos₂ hwc hwt r₂ hok₂
    hfee hlt'
  rw [hz'.idealAssetsWithdraw_eq, hbe, hrs] at hlow
  rw [← hcast', hST'] at hbU hlow
  -- the half steps of the charge and the payout are at most half a base step
  obtain ⟨hcf, hct, -⟩ := Vault.deposit_charge_form v amountDeposit false t hpos hcanon hty r₁ hok₁
  have hce : 1 / 2 * (10 : ℚ) ^ r₁.assets.exponent ≤ 1 / 2 * 10 ^ v.baseExponent ∨ r₁.assets.toRat = 0 := by
    by_cases hcm : r₁.assets.mValue = 0
    · exact Or.inr ((STAmount.toRat_eq_zero_iff _).mpr hcm)
    · left
      have hcpos : 0 < r₁.assets.toRat := lt_of_le_of_ne hc0 (Ne.symm (STAmount.toRat_ne_zero _ hcm))
      have hce0 : (0 : ℚ) < 10 ^ r₁.assets.exponent := zpow_pos (by norm_num) _
      have := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10)
        (Vault.exponent_le_base v r₁.assets hcf hct hcm hcpos r₁.assets.toRat (by linarith) (by linarith))
      linarith
  have hπup : r₂.assets.toRat ≤
      r₁.vault'.assetsAvailable.toRat * r₁.shares.toRat / ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) *
        (1 + sharesε) + 1 / 2 * 10 ^ v.baseExponent := by
    -- with no fee the payout is at most the priced amount
    obtain ⟨p₂, hp₂, hle⟩ :=
      Vault.withdraw_payout_le_proof r₁.vault' _ waive t hpos₂ hwc hwt hmax' r₂ hok₂ hlt'
    rw [hrs, hpr, Except.ok.injEq] at hp₂
    subst hp₂
    rw [hfee, show ((0 : TenthBips32).toNat : ℚ) = 0 by rfl, zero_div, sub_zero, mul_one] at hle
    obtain ⟨hpc, hpt⟩ := Vault.sharesToAssetsWithdraw_form r₁.vault' _ _ waive hmax' hpr
    have hple := Vault.Reachable.sharesToAssetsWithdraw_le_cash r₁.vault' t hr' hmax' _ _ waive hshpos.le hshc'
      (by rw [← hrs]; exact hlt'.le) hpr
    have hp0 := Vault.sharesToAssetsWithdraw_nonneg r₁.vault' _ _ waive (Or.inl hshc') hshpos.le hpr
    by_cases hpm : priced.mValue = 0
    · have : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr hpm
      have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
      have hA'0 : 0 ≤ r₁.vault'.assetsAvailable.toRat := r₁.vault'.exact.assetsAvailable_nonneg
      have : 0 ≤ r₁.vault'.assetsAvailable.toRat * r₁.shares.toRat /
          ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) * (1 + sharesε) :=
        mul_nonneg (div_nonneg (mul_nonneg hA'0 hshpos.le) (by linarith)) (by linarith)
      linarith
    have hppos : 0 < priced.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
    have hpp : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
    have hpe := Vault.exponent_le_base r₁.vault' priced hpc hpt hpm hppos priced.toRat (by linarith)
      (by rw [hbe]; linarith)
    rw [hbe] at hpe
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10) hpe
    linarith
  -- the shares' worth after the deposit is the charge plus the deposit's rounding, scaled down
  have hSs : 0 < (v.toExact.sharesTotal : ℚ) + r₁.shares.toRat := by linarith
  have hI'eq : r₁.vault'.assetsAvailable.toRat * r₁.shares.toRat /
        ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) =
      r₁.assets.toRat +
        (v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) - r₁.assets.toRat) *
          ((v.toExact.sharesTotal : ℚ) / ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat)) := by
    rw [hAA']; field_simp; ring
  rw [hI'eq] at hπup hlow
  have hlam0 : 0 ≤ (v.toExact.sharesTotal : ℚ) / ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) :=
    div_nonneg hS0 hSs.le
  have hlam1 : (v.toExact.sharesTotal : ℚ) / ((v.toExact.sharesTotal : ℚ) + r₁.shares.toRat) ≤ 1 := by
    rw [div_le_one hSs]; linarith
  have hI0 : 0 ≤ v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) :=
    div_nonneg (mul_nonneg hA0 hshpos.le) hS0
  have hc2' : r₁.assets.toRat - v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) ≤
      v.assetsAvailable.toRat * r₁.shares.toRat / (v.toExact.sharesTotal : ℚ) * sharesε +
        1 / 2 * 10 ^ v.baseExponent := by
    have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
    rcases hce with h | h
    · linarith
    · rw [h]
      have := mul_nonneg hI0 hε
      linarith
  have hgain := Vault.roundtrip_payout_le_charge v amountDeposit waive t t0 hpos hr ht hcanon hty hmax r₁ hok₁ hSsz
    hpos₂ r₂ hok₂ hSpos
  obtain ⟨-, hL⟩ := roundtrip_steps _ _ _ _ _ hu hI0 hc0 hcle hlam0 hlam1
    (by have := mul_nonneg hI0 (show (0 : ℚ) ≤ sharesε by unfold sharesε; norm_num); linarith) hc2' hπup hlow
  exact ⟨hgain, grid_steps_le_one _ _ _ (kA' - kA) jπ hcgrid hπgrid hL⟩

end XRPL.Model.SingleAssetVault
