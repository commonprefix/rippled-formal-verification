import XRPL.Properties.Vault.Proofs.ClawbackRecovery
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable

/-! # The payout of a withdrawal from a reachable vault

On a reachable vault, a withdrawal that leaves shares pays exactly the priced amount less the exact
early-exit fee, floored onto the base grid. More shares price at least as high, so they never pay less. -/

namespace XRPL.Model.Protocol

/-- The early-exit fee never passes a representable amount at or above the exact fee whose
`100000`-fold is representable too. Each upward step stops at the first representable value. -/
lemma tenthBipsOfValue_upward_tight (d : Number) (rate : TenthBips32) (fee c c5 : Number)
    (hd : d.isNormalized) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hc5 : c5.isNormalized) (hc5v : c5.toRat = c.toRat * 100000)
    (hge : d.toRat * rate.toNat / 100000 ≤ c.toRat)
    (hok : tenthBipsOfValue d rate .upward = .ok fee) : fee.toRat ≤ c.toRat := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu : ((kTenthBipsPerUnity.toNat : ℕ) : ℚ) = 100000 := by rfl
  rw [hu] at huv
  have hun0 : ¬ kTenthBipsPerUnity.toNumber.operator_eq Number.zero = true := by
    intro h
    have := (operator_eq_iff _ _ hun Number.zero_isNormalized).mp h
    rw [huv, Number.toRat_zero] at this
    norm_num at this
  unfold tenthBipsOfValue at hok
  dsimp only at hok
  obtain ⟨p, hp, hok⟩ := bind_ok_peel _ _ _ hok
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hp
  by_cases hfm : fee.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero fee hfm]; exact hc0
  have hpm : p.mantissa_ ≠ 0 := operator_div_numerator_ne_zero_sz _ _ _ _ hun0 hok hfm
  -- the product rounds up to at most the representable `100000·c`
  obtain ⟨n, hn, hpv⟩ := operator_mul_rounded_upward d rate.toNumber p hd hrn hp hpm
  have hple : p.toRat ≤ c5.toRat := by
    rw [hpv]
    refine Number.upper_tight _ n hn c5 hc5 ?_
    rw [hrv, hc5v]
    rw [div_le_iff₀ (by norm_num)] at hge
    linarith
  -- and the quotient by unity rounds up to at most `c`
  obtain ⟨n', hn', hfv⟩ := operator_div_rounded_upward p _ fee hpn hun hok hfm
  rw [hfv]
  refine Number.upper_tight _ n' hn' c hc ?_
  rw [huv, div_le_iff₀ (by norm_num)]
  linarith

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- What is left of an amount on a fine grid after whole steps of a coarser grid is representable,
and so is its `100000`-fold. -/
private lemma gap_representable (x : ℚ) (z : ℕ) (q b k : ℤ) (hx : x = z * 10 ^ q) (hz : z < 10 ^ 16)
    (hqb : q ≤ b) (hq : -96 ≤ q) (hb : b ≤ 70) (hk : 0 ≤ k) (hc : 0 < x - k * 10 ^ b) :
    ∃ c c5 : Number, c.isNormalized ∧ c.toRat = x - k * 10 ^ b ∧ c5.isNormalized ∧
      c5.toRat = (x - k * 10 ^ b) * 100000 := by
  have hstep : (10 : ℚ) ^ b = 10 ^ (b - q).toNat * 10 ^ q := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ (by norm_num), sub_add_cancel]
  set K : ℤ := z - k * 10 ^ (b - q).toNat with hK
  have hKv : x - k * 10 ^ b = (K : ℚ) * 10 ^ q := by
    rw [hx, hstep, hK]; push_cast; ring
  have hqpos : (0 : ℚ) < 10 ^ q := zpow_pos (by norm_num) _
  have hK1 : 1 ≤ K := by
    have : (0 : ℚ) < K := by
      rw [hKv] at hc
      exact pos_of_mul_pos_left hc hqpos.le
    exact_mod_cast this
  have hKz : K ≤ z := by
    have : 0 ≤ k * 10 ^ (b - q).toNat := mul_nonneg hk (by positivity)
    omega
  have hK63 : K.toNat < 2 ^ 63 := by omega
  have hKcast : ((K.toNat : ℕ) : ℚ) = K := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  obtain ⟨c, hcn, hcv⟩ := Exact.exists_normalized_grid K.toNat q (by omega) hK63
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  obtain ⟨c5, hc5n, hc5v⟩ := Exact.exists_normalized_grid K.toNat (q + 5) (by omega) hK63
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  refine ⟨c, c5, hcn, by rw [hcv, hKcast, hKv], hc5n, ?_⟩
  rw [hc5v, hKcast, hKv, zpow_add₀ (by norm_num)]
  norm_num
  ring

/-- A positive priced amount of a reachable vault sits on a grid no coarser than the base grid,
fewer than `10^16` steps of it. -/
private lemma Vault.priced_grid (v : Vault) (p : STAmount) (hpc : p.CanonicalOrZero)
    (hpt : p.mNumericType = v.numericType) (hp : 0 < p.toRat)
    (hle : p.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent)) :
    ∃ (z : ℕ) (q : ℤ), p.toRat = z * 10 ^ q ∧ z < 10 ^ 16 ∧ -96 ≤ q ∧ q ≤ v.baseExponent := by
  have hneg := STAmount.mIsNegative_false_of_pos p hp
  have hpv := STAmount.toRat_of_nonneg p hneg
  have hcan : p.Canonical := by
    rcases hpc with h | hz
    · exact h
    · exfalso
      have : p.mValue = 0 := by simpa [STAmount.isZero] using hz
      rw [(STAmount.toRat_eq_zero_iff _).mpr this] at hp
      exact lt_irrefl _ hp
  by_cases hint : v.numericType.isIntegral = true
  · have hic : p.IntegralCanonical := (hcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have hb0 := (Vault.baseExponent_bounds v).2.2 hint
    rw [hic.offset_zero, zpow_zero, mul_one] at hpv
    refine ⟨p.mValue.toNat, 0, by rw [hpv, zpow_zero, mul_one], ?_, by norm_num, by rw [hb0]⟩
    rw [hb0] at hle
    have : (p.mValue.toNat : ℚ) < 10 ^ 16 := by rw [← hpv]; norm_num at hle ⊢; linarith
    exact_mod_cast this
  · have hiou : p.IOUCanonical := hcan.2 (by unfold STAmount.integral; rw [hpt]; simpa using hint)
    refine ⟨p.mValue.toNat, p.mOffset, hpv, hiou.mant_hi, hiou.exp_lo, ?_⟩
    -- a 16-digit amount at most `9·10^(15 + base)` has its exponent at most the base
    obtain ⟨h1, -⟩ := STAmount.IOUCanonical.toRat_bounds p hiou hp
    by_contra h
    push Not at h
    have h2 : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 10 ^ (p.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by show 16 + v.baseExponent ≤ p.mOffset + 15; omega)
    have h3 : 9 * (10 : ℚ) ^ (15 + v.baseExponent) < 10 ^ (16 + v.baseExponent) := by
      rw [show (16 : ℤ) + v.baseExponent = (15 + v.baseExponent) + 1 by ring, zpow_add_one₀ (by norm_num)]
      have : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
      linarith
    linarith

/-- On a reachable vault a withdrawal that leaves shares pays the priced amount less the exact
early-exit fee, floored onto the base grid. -/
lemma Vault.Reachable.withdraw_payout_floor_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      r.assets.toRat = (⌊priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) /
        10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, hcase⟩ := Vault.withdraw_payout_cases v amount waive t hpos hc hty r hok hlt
  obtain ⟨hpc, hp0, hsmall⟩ := Vault.withdraw_priced_facts v _ _ waive hmax hsc hspos hpr
  have hρ : ((v.earlyExitFeeRateAt t).toNat : ℚ) ≤ 100000 := by exact_mod_cast v.earlyExitFeeRateAt_le t
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  refine ⟨priced, hpr, ?_⟩
  rcases hcase with ⟨h0, hz⟩ | ⟨aN, fee, pN, -, payout, hlow, haN, hfee, hsub, hpo, hpz, hcl, hfnp, -, -⟩
  · -- nothing is paid: the fee takes everything, or the shares are worth nothing
    rw [h0]
    rcases hz with hfull | hpz0
    · rw [hfull, show ((maxEarlyExitFeeRate.toNat : ℕ) : ℚ) = 100000 by rfl]; simp
    · rw [hpz0]; simp
  have hrate : (v.earlyExitFeeRateAt t).toNat < 100000 :=
    lt_of_le_of_ne (v.earlyExitFeeRateAt_le t) (fun h => hlow (UInt32.toNat_inj.mp h))
  obtain ⟨hav, han, hfn, hpN0, hpNle, hpNn, hpm, hpayle, hpay0⟩ :=
    Vault.feePayout_shape v priced payout aN fee pN _ hpc hp0 hsmall hrate haN hfee hsub hpo hpz
  have hpNm := STAmount.ofNumber_source_ne_zero _ _ _ _ hpo hpm
  have hpNneg := Number.negative_false_of_nonneg _ hpNn hpN0
  have hcash := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax _ _ waive hspos.le hsc hlt.le hpr
  have hopen := (Vault.Reachable.openZone_proof v t0 hr hmax).assetsAvailable_le_openLimit
  set y : ℚ := priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) with hy
  have hρ1 : (v.earlyExitFeeRateAt t).toNat / (100000 : ℚ) ≤ 1 := by rw [div_le_one (by norm_num)]; exact hρ
  have hρ0 : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
  have hy0 : 0 ≤ y := mul_nonneg hp0 (by linarith)
  have hyle : y ≤ priced.toRat := by rw [hy]; nlinarith
  -- what is left after the fee floors onto the base grid like the exact post-fee value
  have hkey : ⌊pN.toRat / 10 ^ v.baseExponent⌋ = ⌊y / 10 ^ v.baseExponent⌋ := by
    apply le_antisymm (Int.floor_mono (div_le_div_of_nonneg_right hpNle hbpos.le))
    set k := ⌊y / 10 ^ v.baseExponent⌋ with hk
    have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (div_nonneg hy0 hbpos.le)
    have hky : (k : ℚ) * 10 ^ v.baseExponent ≤ y := by
      have := Int.floor_le (y / 10 ^ v.baseExponent)
      rwa [le_div_iff₀ hbpos] at this
    apply Int.le_floor.mpr
    rw [le_div_iff₀ hbpos]
    rcases eq_or_lt_of_le hk0 with hk0' | hkpos
    · rw [← hk0']; simpa using hpN0
    -- the fee leaves at least `k` base steps of the priced amount
    have hfeec : fee.toRat ≤ priced.toRat - k * 10 ^ v.baseExponent := by
      have hyv : y = priced.toRat - priced.toRat * (v.earlyExitFeeRateAt t).toNat / 100000 := by
        rw [hy]; ring
      rcases eq_or_lt_of_le (show 0 ≤ priced.toRat - k * 10 ^ v.baseExponent by linarith) with hc0 | hcpos
      · -- nothing is left over, so nothing is charged
        have hf := (tenthBipsOfValue_upward_bounds aN _ fee han (hav ▸ hp0) (hav ▸ hsmall) hfee).2
        rw [hav] at hf
        have hz : priced.toRat * (v.earlyExitFeeRateAt t).toNat / 100000 = 0 := by
          have h1 : 0 ≤ priced.toRat * (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
          linarith
        rw [hz, zero_mul] at hf
        rw [← hc0]; exact hf
      have hkB : 0 ≤ (k : ℚ) * 10 ^ v.baseExponent := mul_nonneg (by exact_mod_cast hk0) hbpos.le
      have hppos : 0 < priced.toRat := by linarith
      obtain ⟨z, q, hzq, hz16, hq, hqb⟩ := Vault.priced_grid v priced hpc
        (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).2 hppos (by linarith)
      obtain ⟨c, c5, hcn, hcv, hc5n, hc5v⟩ := gap_representable priced.toRat z q v.baseExponent k hzq hz16 hqb hq
        (by have := (Vault.baseExponent_bounds v).2.1; omega) hk0 hcpos
      rw [← hcv]
      refine tenthBipsOfValue_upward_tight aN _ fee c c5 han hcn (by rw [hcv]; linarith) hc5n
        (by rw [hc5v, hcv]) ?_ hfee
      rw [hcv, hav]
      linarith
    -- `k` base steps are representable, so the downward subtraction keeps them
    have hk9 : (k : ℚ) ≤ 9 * 10 ^ 15 := by
      have h15 : (10 : ℚ) ^ (15 + v.baseExponent) = 10 ^ 15 * 10 ^ v.baseExponent := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      have h1 : (k : ℚ) * 10 ^ v.baseExponent ≤ (9 * 10 ^ 15) * 10 ^ v.baseExponent := by
        rw [h15] at hopen; nlinarith
      exact le_of_mul_le_mul_right h1 hbpos
    have hk63 : k.toNat < 2 ^ 63 := by
      have : k ≤ 9 * 10 ^ 15 := by exact_mod_cast hk9
      omega
    obtain ⟨w, hwn, hwv⟩ := Exact.exists_normalized_grid k.toNat v.baseExponent (by omega) hk63
      (by have := (Vault.baseExponent_bounds v).1; unfold minExponent; omega)
      (by have := (Vault.baseExponent_bounds v).2.1; unfold maxExponent; omega)
    have hkcast : ((k.toNat : ℕ) : ℚ) = k := by exact_mod_cast Int.toNat_of_nonneg hk0
    rw [hkcast] at hwv
    obtain ⟨n, hn, hpNv⟩ := operator_sub_rounded_downward aN fee pN han hfn hsub hpNm
    rw [hpNv, ← hwv]
    exact Number.lower_tight _ n hn w hwn (by rw [hwv, hav]; linarith)
  -- the payout and the clamp floor onto grids no coarser than the base grid
  have hpt : payout.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hpo
  have hmag : |payout.operator_neg.toRat| = payout.toRat := by
    rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0]
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral payout is the whole part of what is left, and the clamp keeps it
    have hb0 := v.baseExponent_bounds.2.2 hint
    obtain ⟨iv, hrep, hval⟩ := STAmount.ofNumber_integral_toRat _ _ _ _ hint hpNneg hpo
    obtain ⟨hfl1, hfl2⟩ := Number.to_rep_downward_floor _ iv hpNn hpNneg hrep
    have hivf : iv.toInt = ⌊pN.toRat⌋ := by rw [eq_comm, Int.floor_eq_iff]; exact ⟨hfl1, hfl2⟩
    have hni : payout.operator_neg.integral = true := by
      unfold STAmount.integral
      rw [(STAmount.operator_neg_fields payout).1, hpt]
      exact hint
    rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
    have hra := (clamp_magnitude payout.operator_neg).2.2.2
    rw [hcl, hmag] at hra
    rw [hb0, zpow_zero, div_one, div_one] at hkey
    rw [hb0, zpow_zero, div_one, mul_one, hra, hval, hivf, hkey]
  -- a fractional payout floors onto the 16-digit grid of what is left
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hfloor : payout.toRat = (⌊pN.toRat / 10 ^ (pN.exponent_ + 3)⌋ : ℚ) * 10 ^ (pN.exponent_ + 3) :=
    STAmount.ofNumber_iou_downward_floor pN payout hpNn hpNm hpN0 (hvfr ▸ hpo) hpm
  have hpe : pN.exponent_ + 3 ≤ v.baseExponent := by
    by_contra h
    push Not at h
    obtain ⟨hm_lo, -⟩ := hpNn.mantissaBounds_nat hpNm
    have hm : (10 : ℚ) ^ 18 ≤ (pN.mantissa_.toNat : ℚ) := by exact_mod_cast hm_lo
    have hbig : 9 * (10 : ℚ) ^ (15 + v.baseExponent) < 10 ^ (16 + v.baseExponent) := by
      rw [show (16 : ℤ) + v.baseExponent = (15 + v.baseExponent) + 1 by ring, zpow_add_one₀ (by norm_num)]
      have : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
      linarith
    have hge : (10 : ℚ) ^ (16 + v.baseExponent) ≤ pN.toRat := by
      rw [Number.toRat_of_nonneg pN hpNneg]
      calc (10 : ℚ) ^ (16 + v.baseExponent) ≤ 10 ^ (pN.exponent_ + (18 : ℕ)) :=
            zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
        _ = 10 ^ 18 * 10 ^ pN.exponent_ := by rw [zpow_add₀ (by norm_num), zpow_natCast]; ring
        _ ≤ (pN.mantissa_.toNat : ℚ) * 10 ^ pN.exponent_ :=
            mul_le_mul_of_nonneg_right hm (zpow_pos (by norm_num) _).le
    linarith
  have hpf : payout.operator_neg.FracCanonZero :=
    STAmount.operator_neg_fczr _ (STAmount.ofNumber_fractional_fczr _ _ _ (hvfr ▸ hpo))
  have hrnz : r.assets.mValue ≠ 0 := by
    intro h0
    have hrt := (clampToSumExponent_frac_shape _ _ _ _ hpf hcl).1
    rw [STAmount.isFractionalNonPositive_zero _ hrt h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  have hfl := Vault.Reachable.clamp_base v t0 hr hmax payout r.assets
    (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo).1 (by rw [hpt, hvfr]) hpay0 (by linarith) hrnz hcl
  rw [hfl, hfloor, floor_grid_floor_of_le _ _ _ hpe, hkey]

/-- A payout that leaves shares is at most the priced amount less the fee, and less than one base step below it: the
floor onto the base grid loses less than one step. -/
lemma Vault.withdraw_payout_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      r.assets.toRat ≤ priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) ∧
      priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) - (10 : ℚ) ^ v.baseExponent <
        r.assets.toRat := by
  obtain ⟨priced, hpr, hfl⟩ :=
    Vault.Reachable.withdraw_payout_floor_proof v amount waive t t0 hpos hr hc hty hmax r hok hlt
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  set y := priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) with hy
  have h1 := Int.floor_le (y / 10 ^ v.baseExponent)
  have h2 := Int.lt_floor_add_one (y / 10 ^ v.baseExponent)
  rw [le_div_iff₀ hbpos] at h1
  rw [div_lt_iff₀ hbpos, add_mul, one_mul] at h2
  refine ⟨priced, hpr, by rw [hfl, ← hy]; exact h1, by rw [hfl, ← hy]; linarith⟩

/-- On a reachable vault more shares price at least as high. The vault prices at its cash, well
clear of underflow, and every step of the pricing rounds monotonically. -/
lemma Vault.Reachable.sharesToAssetsWithdraw_mono (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (waive : Bool) (s₁ s₂ p₁ p₂ : STAmount) (hc₁ : s₁.Canonical) (hc₂ : s₂.Canonical)
    (hs₁ : 1 ≤ s₁.toRat) (hle : s₁.toRat ≤ s₂.toRat)
    (hok₁ : v.sharesToAssetsWithdraw s₁ waive = .ok p₁)
    (hok₂ : v.sharesToAssetsWithdraw s₂ waive = .ok p₂) :
    p₁.toRat ≤ p₂.toRat := by
  have hp₂0 := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive (Or.inl hc₂) (by linarith) hok₂
  obtain ⟨nav, hsub, hnavn, hcase₁⟩ := WdPrice.price_cases v _ _ waive hok₁
  obtain ⟨nav', hsub', -, hcase₂⟩ := WdPrice.price_cases v _ _ waive hok₂
  obtain rfl : nav = nav' := Except.ok.inj (hsub.symm.trans hsub')
  rcases hcase₁ with ⟨-, rfl⟩ | ⟨hnavm, sn₁, NS₁, an₁, hsn₁, hmul₁, hdiv₁, hof₁⟩
  · rw [STAmount.zero_toRat _]; exact hp₂0
  rcases hcase₂ with ⟨h0, -⟩ | ⟨-, sn₂, NS₂, an₂, hsn₂, hmul₂, hdiv₂, hof₂⟩
  · exact absurd h0 hnavm
  -- the vault prices at its cash, at least `10⁻¹⁰`
  have hnavv := Vault.Reachable.nav_eq_cash v t0 hr waive nav hsub
  have hnavpos : 0 < nav.toRat := lt_of_le_of_ne (by rw [hnavv]; exact v.exact.assetsAvailable_nonneg)
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hnavm))
  have hAA10 : (10 : ℚ) ^ (-10 : ℤ) ≤ nav.toRat := by
    rw [hnavv]; exact ((Vault.Reachable.openZone_proof v t0 hr hmax).cash_ge (by rw [← hnavv]; exact hnavpos)).2
  have hnavneg := Number.negative_false_of_pos nav hnavpos
  -- the shares as `Number`s, at least one
  obtain ⟨sn₁', h1', hsnv₁, hsnn₁⟩ := STAmount.toNumber_exact_canonical s₁ .to_nearest
    (STAmount.Canonical.exactCanonical s₁ hc₁)
  obtain rfl : sn₁ = sn₁' := Except.ok.inj (hsn₁.symm.trans h1')
  obtain ⟨sn₂', h2', hsnv₂, hsnn₂⟩ := STAmount.toNumber_exact_canonical s₂ .to_nearest
    (STAmount.Canonical.exactCanonical s₂ hc₂)
  obtain rfl : sn₂ = sn₂' := Except.ok.inj (hsn₂.symm.trans h2')
  have hsn₁pos : 0 < sn₁.toRat := by rw [hsnv₁]; linarith
  have hsn₂pos : 0 < sn₂.toRat := by rw [hsnv₂]; linarith
  -- the share total is at least one and at most `2^63 - 1`
  have hSTm := operator_div_divisor_ne_zero _ _ _ _ v.wf.sharesTotal_norm hdiv₁
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := rat_one_le_of_den_one_pos _ v.wf.sharesTotal_int hSTpos
  have hSTle := Vault.sharesTotal_le_maxRep v
  have hlarge : ∀ sn : Number, 1 ≤ sn.toRat →
      (10 : ℚ) ^ (-50 : ℤ) ≤ nav.toRat * sn.toRat / v.sharesTotal.toRat := by
    intro sn hsn
    rw [le_div_iff₀ hSTpos]
    have h1 : (10 : ℚ) ^ (-50 : ℤ) * v.sharesTotal.toRat ≤ 10 ^ (-50 : ℤ) * 2 ^ 63 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (10 : ℚ) ^ (-50 : ℤ) * 2 ^ 63 ≤ 10 ^ (-10 : ℤ) := by norm_num
    nlinarith
  -- both quotients stay clear of underflow
  obtain ⟨han₁, han₁pos, -⟩ := pipe_large nav sn₁ NS₁ an₁ v.sharesTotal hnavn hsnn₁
    v.wf.sharesTotal_norm hnavpos.le hsn₁pos.le hSTpos hST1 (hlarge sn₁ (by rw [hsnv₁]; exact hs₁))
    hmul₁ hdiv₁
  obtain ⟨han₂, han₂pos, -⟩ := pipe_large nav sn₂ NS₂ an₂ v.sharesTotal hnavn hsnn₂
    v.wf.sharesTotal_norm hnavpos.le hsn₂pos.le hSTpos hST1 (hlarge sn₂ (by rw [hsnv₂]; linarith))
    hmul₂ hdiv₂
  have han₁m : an₁.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero han₁pos.ne'
  have han₂m : an₂.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero han₂pos.ne'
  have hNS₁m := (operator_div_operands_ne_zero (Number.operator_mul_isNormalized _ _ _ _ hnavn hsnn₁ hmul₁)
    v.wf.sharesTotal_norm hdiv₁ han₁m).1
  have hNS₂m := (operator_div_operands_ne_zero (Number.operator_mul_isNormalized _ _ _ _ hnavn hsnn₂ hmul₂)
    v.wf.sharesTotal_norm hdiv₂ han₂m).1
  have hanle : an₁.toRat ≤ an₂.toRat :=
    Number.mul_div_num_mono nav v.sharesTotal sn₁ sn₂ NS₁ NS₂ an₁ an₂ hnavn hnavm hnavneg
      v.wf.sharesTotal_norm hSTm (Number.negative_false_of_pos _ hSTpos)
      hsnn₁ (Number.mantissa_ne_zero_of_toRat_ne_zero hsn₁pos.ne') (Number.negative_false_of_pos _ hsn₁pos)
      hsnn₂ (Number.mantissa_ne_zero_of_toRat_ne_zero hsn₂pos.ne') (Number.negative_false_of_pos _ hsn₂pos)
      hmul₁ hNS₁m hmul₂ hNS₂m hdiv₁ han₁m hdiv₂ han₂m (by rw [hsnv₁, hsnv₂]; exact hle)
  exact WdMono.ofNumber_mono v.numericType an₁ an₂ p₁ p₂ han₁ han₂ han₁pos.le hanle hof₁ hof₂

/-- Proof of `Vault.withdraw_payout_monotone`. A final withdrawal pays all the cash, and otherwise both payouts
are the base-grid floor of their post-fee priced amounts, and more shares price at least as high. -/
lemma Vault.withdraw_payout_monotone_proof (v : Vault) (amount₁ amount₂ : WithdrawAmount) (waive : Bool)
    (t t0 : UInt32) (hpos₁ : 0 < amount₁.amount.toRat) (hpos₂ : 0 < amount₂.amount.toRat)
    (hr : Vault.Reachable v t0)
    (hc₁ : amount₁.amount.Canonical) (hc₂ : amount₂.amount.Canonical)
    (hty₁ : amount₁.InAsset v.numericType) (hty₂ : amount₂.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r₁ r₂ : VaultWithAmounts)
    (hok₁ : (v.withdraw amount₁ waive t hpos₁).run = .ok (.ok r₁))
    (hok₂ : (v.withdraw amount₂ waive t hpos₂).run = .ok (.ok r₂))
    (hle : r₁.shares.toRat ≤ r₂.shares.toRat) :
    r₁.assets.toRat ≤ r₂.assets.toRat := by
  by_cases hlt₂ : r₂.shares.toRat < v.toExact.sharesTotal
  swap
  · -- the second withdrawal burns every share and pays all the cash, and no payout exceeds the cash
    have h₂ := Vault.withdraw_vault_updates_exact_proof v amount₂ waive t t0 hpos₂ hr hc₂ hty₂ hmax r₂ hok₂
    have hS' : (0 : ℚ) ≤ (r₂.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
    have hfin : r₂.shares.toRat = v.toExact.sharesTotal := by linarith [h₂.2, not_lt.mp hlt₂]
    have hall := (Vault.withdraw_final_proof v amount₂ waive t t0 hpos₂ hr hc₂ hty₂ hmax r₂ hok₂ hfin).1
    have h₁ := Vault.withdraw_vault_updates_exact_proof v amount₁ waive t t0 hpos₁ hr hc₁ hty₁ hmax r₁ hok₁
    have hA' : 0 ≤ r₁.vault'.assetsAvailable.toRat := r₁.vault'.exact.assetsAvailable_nonneg
    linarith [h₁.1]
  obtain ⟨hsic₁, hs64₁, hspos₁⟩ :=
    Vault.withdraw_shares_form v amount₁ waive t hpos₁ hc₁ hty₁ r₁ hok₁
  obtain ⟨hsic₂, hs64₂, -⟩ := Vault.withdraw_shares_form v amount₂ waive t hpos₂ hc₂ hty₂ r₂ hok₂
  obtain ⟨p₁, hpr₁, hfl₁⟩ := Vault.Reachable.withdraw_payout_floor_proof v amount₁ waive t t0 hpos₁ hr
    hc₁ hty₁ hmax r₁ hok₁ (lt_of_le_of_lt hle hlt₂)
  obtain ⟨p₂, hpr₂, hfl₂⟩ := Vault.Reachable.withdraw_payout_floor_proof v amount₂ waive t t0 hpos₂ hr
    hc₂ hty₂ hmax r₂ hok₂ hlt₂
  -- a positive whole number of shares is at least one
  have hs₁ : (1 : ℚ) ≤ r₁.shares.toRat := by
    have hv := STAmount.toRat_of_nonneg r₁.shares (STAmount.mIsNegative_false_of_pos _ hspos₁)
    rw [hsic₁.offset_zero, zpow_zero, mul_one] at hv
    rw [hv] at hspos₁ ⊢
    have : 0 < r₁.shares.mValue.toNat := by exact_mod_cast hspos₁
    exact_mod_cast this
  have hp := Vault.Reachable.sharesToAssetsWithdraw_mono v t0 hr hmax waive _ _ p₁ p₂
    (hsic₁.canonical (by rw [hs64₁]; decide)) (hsic₂.canonical (by rw [hs64₂]; decide)) hs₁ hle hpr₁ hpr₂
  have hρ : ((v.earlyExitFeeRateAt t).toNat : ℚ) ≤ 100000 := by exact_mod_cast v.earlyExitFeeRateAt_le t
  have hρ1 : (0 : ℚ) ≤ 1 - (v.earlyExitFeeRateAt t).toNat / 100000 := by
    rw [sub_nonneg, div_le_one (by norm_num)]; exact hρ
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  rw [hfl₁, hfl₂]
  apply mul_le_mul_of_nonneg_right _ hbpos.le
  exact_mod_cast Int.floor_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hρ1) hbpos.le)

end XRPL.Model.SingleAssetVault
