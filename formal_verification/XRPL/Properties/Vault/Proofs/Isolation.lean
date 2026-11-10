import XRPL.Properties.Vault.Proofs.IsolationRun
import XRPL.Properties.Vault.Proofs.PerShareFloor
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Common.GuardProofs

/-! # Isolation of a withdrawal by shares

Proof bodies behind `Isolation.lean`. Without a partial early-exit fee a reachable vault pays any withdrawal by shares
it covers. Under one, the withdrawal needs the price of its shares not to fall: a donation and an update keep it, and a
fee-paying withdrawal or a clawback keep it when the withdrawn shares are worth a whole number of base units. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A withdrawal that succeeded passed the timing check. -/
private lemma Vault.withdraw_open_of_ok (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false := by
  cases h : (v.earlyExitFeeRate.isNone && v.phase t == .investment)
  · rfl
  · rw [Vault.withdraw_too_soon_proof v amount waive t hpos h] at hok
    exact absurd hok (by simp)

/-- A withdrawal by shares that succeeded redeemed at most the share total. -/
private lemma Vault.withdraw_shares_le_total (v : Vault) (shares : STAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (hc : shares.Canonical)
    (hty : shares.mNumericType = .int64) (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r)) :
    shares.toRat ≤ v.toExact.sharesTotal := by
  have h := Vault.withdraw_exact_sharesTotal v (.vaultShares shares) waive t hpos hc hty r hok
  rw [Vault.withdraw_sharesRedeemed_exact_proof v shares waive t hpos r hok] at h
  have : (0 : ℚ) ≤ r.vault'.toExact.sharesTotal := Nat.cast_nonneg _
  linarith

/-- A deposit that is not a donation succeeds only outside the investment phase, where no early-exit fee applies. -/
private lemma Vault.deposit_fee_zero (v : Vault) (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat)
    (r : VaultWithAmounts) (hok : (v.deposit amount false t hpos).run = .ok (.ok r)) :
    v.earlyExitFeeRateAt t = 0 := by
  have hph : v.phase t ≠ .investment := by
    intro hph
    simp only [Vault.deposit] at hok
    unfold_ter at hok
    simp [hph] at hok
  unfold Vault.earlyExitFeeRateAt
  split
  · simp [hph]
  · rfl

/-- Two vaults with the same dates, fee rate, asset and scale withdraw on the same terms. -/
private lemma Vault.terms_congr {v v' : Vault} (hs : v'.schedule = v.schedule)
    (hf : v'.earlyExitFeeRate = v.earlyExitFeeRate) (hnt : v'.numericType = v.numericType)
    (hsc : v'.scale = v.scale) (t : UInt32) :
    (v'.earlyExitFeeRate.isNone && v'.phase t == .investment) =
      (v.earlyExitFeeRate.isNone && v.phase t == .investment) ∧
      v'.earlyExitFeeRateAt t = v.earlyExitFeeRateAt t ∧ v'.baseExponent = v.baseExponent := by
  have hph : v'.phase t = v.phase t := by unfold Vault.phase; rw [hs]
  exact ⟨by rw [hf, hph], by unfold Vault.earlyExitFeeRateAt; rw [hf, hph],
    by unfold Vault.baseExponent; rw [hnt, hsc]⟩

/-- On a reachable vault a withdrawal by shares that leaves shares and keeps some of its price after the early-exit
fee pays at least one base unit, so the price of its shares less the exact fee is at least one base unit. -/
private lemma Vault.Reachable.withdraw_fee_floor (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r))
    (hlt : shares.toRat < v.toExact.sharesTotal) (hM : v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate)
    (p : STAmount) (hpr : v.sharesToAssetsWithdraw shares waive = .ok p) :
    (10 : ℚ) ^ v.baseExponent ≤ p.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hrs := Vault.withdraw_sharesRedeemed_exact_proof v shares waive t hpos r hok
  have hty' : (WithdrawAmount.vaultShares shares).InAsset v.numericType := hty
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v _ waive t hpos hc hty' r hok)
  obtain ⟨priced, hpr', hfl⟩ :=
    Vault.Reachable.withdraw_payout_floor_proof v _ waive t t0 hpos hr hc hty' hmax r hok (by rw [hrs]; exact hlt)
  rw [hrs, hpr] at hpr'
  obtain rfl := Except.ok.inj hpr'
  obtain ⟨priced2, hpr2, hcase⟩ := Vault.withdraw_payout_cases v _ waive t hpos hc hty' r hok (by rw [hrs]; exact hlt)
  rw [hrs, hpr] at hpr2
  obtain rfl := Except.ok.inj hpr2
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  -- the withdrawal paid something
  have hra : r.assets.toRat ≠ 0 := by
    rcases hcase with ⟨-, hfm | hp0⟩ | ⟨aN, fee, pN, -, payout, -, -, -, -, hpo, hpz, hcl, hfnp, -, -⟩
    · exact absurd hfm hM
    · exfalso
      obtain ⟨p0, hp0r, hp0lo, -⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hlt.le
      rw [hpr] at hp0r
      obtain rfl := Except.ok.inj hp0r
      linarith
    · have hpm : payout.mValue ≠ 0 := by simpa [STAmount.isZero] using hpz
      have hpt := STAmount.ofNumber_mNumericType _ _ _ _ hpo
      by_cases hint : v.numericType.isIntegral = true
      · have hni : payout.operator_neg.integral = true := by
          unfold STAmount.integral
          rw [(STAmount.operator_neg_fields payout).1, hpt]
          exact hint
        rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
        have hm := (clamp_magnitude payout.operator_neg).2.2.2
        rw [hcl, STAmount.operator_neg_toRat, abs_neg] at hm
        rw [hm]
        exact abs_ne_zero.mpr (STAmount.toRat_ne_zero payout hpm)
      · have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
        have hpf : payout.operator_neg.FracCanonZero :=
          STAmount.operator_neg_fczr _ (STAmount.ofNumber_fractional_fczr _ _ _ (hvfr ▸ hpo))
        intro h0'
        have hm0 : r.assets.mValue = 0 := (STAmount.toRat_eq_zero_iff _).mp h0'
        have hrt := (clampToSumExponent_frac_shape _ _ _ _ hpf hcl).1
        rw [STAmount.isFractionalNonPositive_zero _ hrt hm0] at hfnp
        exact absurd (Except.ok.inj hfnp) (by decide)
  -- so the floor of the priced amount less the fee is at least one base unit
  have hp0 : 0 ≤ p.toRat := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive (Or.inl hc) hspos.le hpr
  have hρ1 : (0 : ℚ) ≤ 1 - (v.earlyExitFeeRateAt t).toNat / 100000 := by
    rw [sub_nonneg, div_le_one (by norm_num)]; exact_mod_cast v.earlyExitFeeRateAt_le t
  set y := p.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) with hy
  have hy0 : 0 ≤ y := mul_nonneg hp0 hρ1
  have hk0 : 0 ≤ ⌊y / 10 ^ v.baseExponent⌋ := Int.floor_nonneg.mpr (div_nonneg hy0 hbpos.le)
  have hk1 : 1 ≤ ⌊y / 10 ^ v.baseExponent⌋ := by
    rcases eq_or_lt_of_le hk0 with h | h
    · exfalso
      apply hra
      rw [hfl, ← h]
      simp
    · omega
  have h1 := Int.le_floor.mp hk1
  rw [Int.cast_one, le_div_iff₀ hbpos, one_mul] at h1
  exact h1

/-- On a reachable vault the price of shares up to the share total is at least every whole number of base units at
or below their worth. -/
private lemma Vault.Reachable.price_ge_grid (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (shares : STAmount)
    (waive : Bool) (hc : shares.Canonical) (hs1 : 1 ≤ shares.toRat) (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (p : STAmount) (hpr : v.sharesToAssetsWithdraw shares waive = .ok p) (k : ℤ)
    (hk : (k : ℚ) * 10 ^ v.baseExponent ≤ v.idealAssetsWithdraw waive shares.toRat) :
    (k : ℚ) * 10 ^ v.baseExponent ≤ p.toRat := by
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨p0, hp0, hplo, hphi⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hle
  rw [hpr] at hp0
  obtain rfl := Except.ok.inj hp0
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hpv, heb, -, hpl, hrel⟩ := hz.priced_grid hmax shares p waive (by linarith) hc hpr hphi (by linarith)
  have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  exact ge_of_grid_lt _ k _ _ heb _ _ hpv rfl (by linarith)

/-- Two reachable vaults of one asset -> the same shares price at least as high in the second when its per-share
value is higher by a factor of at least `1 + 10⁻¹⁷`, more than the 19-digit error of either price. -/
private lemma Vault.Reachable.price_mono_of_gain (u u' : Vault) (t0 t0' : UInt32) (hr : Vault.Reachable u t0)
    (hr' : Vault.Reachable u' t0') (hnt : u'.numericType = u.numericType) (shares : STAmount) (w w' : Bool)
    (hc : shares.Canonical) (hs1 : 1 ≤ shares.toRat) (hle : shares.toRat ≤ u.toExact.sharesTotal)
    (hle' : shares.toRat ≤ u'.toExact.sharesTotal)
    (hgain : u.assetsAvailable.toRat * u'.toExact.sharesTotal * (1 + 1 / 10 ^ 17) ≤
      u'.assetsAvailable.toRat * u.toExact.sharesTotal)
    (p p' : STAmount) (hpr : u.sharesToAssetsWithdraw shares w = .ok p)
    (hpr' : u'.sharesToAssetsWithdraw shares w' = .ok p') : p.toRat ≤ p'.toRat := by
  have hmax := Vault.Reachable.maxValue_fits u t0 hr (by linarith)
  -- both vaults price at their cash, at least one base unit per share
  have hS := RawVault.WF.toExact_sharesTotal u.toRawVault u.wf
  have hS' := RawVault.WF.toExact_sharesTotal u'.toRawVault u'.wf
  have hcashS := Vault.Reachable.sharesTotal_le_cash_proof u t0 hr
  have hcashS' := Vault.Reachable.sharesTotal_le_cash_proof u' t0' hr'
  have hb10 : ∀ x : Vault, (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ x.baseExponent :=
    fun x => zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds x).1
  have hA : (10 : ℚ) ^ (-10 : ℤ) ≤ u.assetsAvailable.toRat := by
    have := hb10 u
    have : (1 : ℚ) * 10 ^ u.baseExponent ≤ (u.toExact.sharesTotal : ℚ) * 10 ^ u.baseExponent :=
      mul_le_mul_of_nonneg_right (by linarith) (zpow_pos (by norm_num) _).le
    linarith
  have hA' : (10 : ℚ) ^ (-10 : ℤ) ≤ u'.assetsAvailable.toRat := by
    have := hb10 u'
    have : (1 : ℚ) * 10 ^ u'.baseExponent ≤ (u'.toExact.sharesTotal : ℚ) * 10 ^ u'.baseExponent :=
      mul_le_mul_of_nonneg_right (by linarith) (zpow_pos (by norm_num) _).le
    linarith
  have h10 : (0 : ℚ) < 10 ^ (-10 : ℤ) := zpow_pos (by norm_num) _
  obtain ⟨nav, hsub, hnavn, hcase⟩ := WdPrice.price_cases u _ _ w hpr
  obtain ⟨nav', hsub', hnavn', hcase'⟩ := WdPrice.price_cases u' _ _ w' hpr'
  have hnavv := Vault.Reachable.nav_eq_cash u t0 hr w nav hsub
  have hnavv' := Vault.Reachable.nav_eq_cash u' t0' hr' w' nav' hsub'
  rcases hcase with ⟨h0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hnavv; linarith
  rcases hcase' with ⟨h0, -⟩ | ⟨-, sn', NS', an', hsn', hmul', hdiv', hof'⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hnavv'; linarith
  -- the shares as a `Number`, at least one
  obtain ⟨sn₀, h0', hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical shares hc)
  rw [Except.ok.inj (hsn.symm.trans h0')] at hmul
  rw [Except.ok.inj (hsn'.symm.trans h0')] at hmul'
  -- each share total is at least one, and each quotient within `sharesε` of the worth
  have hST1 : (1 : ℚ) ≤ u.sharesTotal.toRat := by rw [← hS]; linarith
  have hST1' : (1 : ℚ) ≤ u'.sharesTotal.toRat := by rw [← hS']; linarith
  have hT : (10 : ℚ) ^ (-50 : ℤ) ≤ nav.toRat * sn₀.toRat / u.sharesTotal.toRat := by
    rw [hnavv, hsnv, le_div_iff₀ (by linarith)]
    have h63 : u.sharesTotal.toRat ≤ 2 ^ 63 - 1 := Vault.sharesTotal_le_maxRep u
    have h1 : (10 : ℚ) ^ (-50 : ℤ) * u.sharesTotal.toRat ≤ 10 ^ (-50 : ℤ) * 2 ^ 63 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (10 : ℚ) ^ (-50 : ℤ) * 2 ^ 63 ≤ 10 ^ (-10 : ℤ) := by norm_num
    nlinarith
  have hT' : (10 : ℚ) ^ (-50 : ℤ) ≤ nav'.toRat * sn₀.toRat / u'.sharesTotal.toRat := by
    rw [hnavv', hsnv, le_div_iff₀ (by linarith)]
    have h63 : u'.sharesTotal.toRat ≤ 2 ^ 63 - 1 := Vault.sharesTotal_le_maxRep u'
    have h1 : (10 : ℚ) ^ (-50 : ℤ) * u'.sharesTotal.toRat ≤ 10 ^ (-50 : ℤ) * 2 ^ 63 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (10 : ℚ) ^ (-50 : ℤ) * 2 ^ 63 ≤ 10 ^ (-10 : ℤ) := by norm_num
    nlinarith
  obtain ⟨han, hanpos, hb⟩ := pipe_large nav sn₀ NS an u.sharesTotal hnavn hsnn u.wf.sharesTotal_norm
    (by rw [hnavv]; linarith) (by rw [hsnv]; linarith) (by linarith) hST1 hT hmul hdiv
  obtain ⟨han', -, hb'⟩ := pipe_large nav' sn₀ NS' an' u'.sharesTotal hnavn' hsnn u'.wf.sharesTotal_norm
    (by rw [hnavv']; linarith) (by rw [hsnv]; linarith) (by linarith) hST1' hT' hmul' hdiv'
  -- the gain is far more than both errors
  set T := nav.toRat * sn₀.toRat / u.sharesTotal.toRat with hTdef
  set T' := nav'.toRat * sn₀.toRat / u'.sharesTotal.toRat with hT'def
  have hgT : T * (1 + 1 / 10 ^ 17) ≤ T' := by
    rw [hTdef, hT'def, hnavv, hnavv', div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by linarith)]
    rw [← hS, ← hS']
    have hs0 : 0 ≤ sn₀.toRat := by rw [hsnv]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hgain hs0]
  have hε : (sharesε : ℚ) = 11 / 10 ^ 19 := rfl
  rw [hε] at hb hb'
  obtain ⟨-, hb2⟩ := abs_le.mp hb
  obtain ⟨hb1', -⟩ := abs_le.mp hb'
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hanle : an.toRat ≤ an'.toRat := by nlinarith
  exact WdMono.ofNumber_mono u.numericType an an' p p' han han' hanpos.le hanle hof (hnt ▸ hof')

/-- Two Open-zone vaults with the same cash, share total and asset price shares the same, whatever the loss flag. -/
private lemma Vault.price_congr {v v' : Vault} (hz : v.OpenZone) (hz' : v'.OpenZone)
    (hA : v'.assetsAvailable = v.assetsAvailable) (hS : v'.sharesTotal = v.sharesTotal)
    (hnt : v'.numericType = v.numericType) (shares : STAmount) (w w' : Bool) :
    v'.sharesToAssetsWithdraw shares w' = v.sharesToAssetsWithdraw shares w := by
  simp only [Vault.sharesToAssetsWithdraw, hz.assetsTotalForWithdrawal_eq, hz'.assetsTotalForWithdrawal_eq, hA, hS,
    hnt]

/-- On a reachable vault a withdrawal that leaves shares and pays a nonzero early-exit fee pays at most the worth of the
redeemed shares, and on an XRP or MPT vault at least `49/100` of a unit less. -/
private lemma Vault.Reachable.withdraw_fee_payout_le (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) (h0 : v.earlyExitFeeRateAt t ≠ 0) :
    r.assets.toRat ≤ v.idealAssetsWithdraw waive r.shares.toRat ∧
      (v.numericType.isIntegral = true → r.assets.toRat + 49 / 100 ≤ v.idealAssetsWithdraw waive r.shares.toRat) := by
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := lt_trans hspos hlt
  obtain ⟨priced, hpr, hfl⟩ :=
    Vault.Reachable.withdraw_payout_floor_proof v amount waive t t0 hpos hr hc hty hmax r hok hlt
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hI := hz.idealAssetsWithdraw_eq waive r.shares.toRat
  rw [← hcast] at hI
  set I := v.idealAssetsWithdraw waive r.shares.toRat with hIdef
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hI0 : 0 ≤ I := by rw [hI]; positivity
  have hIA : I ≤ v.assetsAvailable.toRat := by
    rw [hI, div_le_iff₀ hSpos]; exact mul_le_mul_of_nonneg_left hlt.le hA0
  have hcash9 := hz.cash_le
  have hp0 : 0 ≤ priced.toRat := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive (Or.inl hsc) hspos.le hpr
  have hρ1 : (1 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat := by
    have : (v.earlyExitFeeRateAt t).toNat ≠ 0 := fun h => h0 (UInt32.toNat_inj.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  set y := priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) with hy
  have hyle : y ≤ priced.toRat - priced.toRat / 100000 := by
    rw [hy]
    have : priced.toRat * ((v.earlyExitFeeRateAt t).toNat / 100000) ≥ priced.toRat * (1 / 100000) :=
      mul_le_mul_of_nonneg_left (by rw [div_le_div_iff_of_pos_right (by norm_num)]; exact hρ1) hp0
    linarith
  have hfle : r.assets.toRat ≤ y := by
    have h := Int.floor_le (y / 10 ^ v.baseExponent)
    rw [le_div_iff₀ hbpos] at h
    rw [hfl]; exact h
  by_cases hpz : priced.toRat = 0
  · -- nothing priced, nothing paid
    have hy0 : y = 0 := by rw [hy, hpz, zero_mul]
    have hr0 : r.assets.toRat = 0 := by
      rw [hfl, hy0, zero_div, Int.floor_zero, Int.cast_zero, zero_mul]
    refine ⟨by linarith, fun hint => ?_⟩
    -- an XRP or MPT share is worth at least one unit
    have hcashS := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
    rw [(Vault.baseExponent_bounds v).2.2 hint, zpow_zero, mul_one] at hcashS
    have hs1 : 1 ≤ r.shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
    have : (1 : ℚ) ≤ I := by
      rw [hI, le_div_iff₀ hSpos, one_mul]
      nlinarith
    linarith
  have hpc := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax r.shares priced waive hspos.le hsc hlt.le hpr
  obtain ⟨hpv, heb, hpu, -, hrel⟩ := hz.priced_grid hmax r.shares priced waive hspos.le hsc hpr hpc hpz
  have hge : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
  have hε : (sharesε : ℚ) = 11 / 10 ^ 19 := rfl
  rw [hε] at hpu hrel
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr
  have hpcan : priced.Canonical := hpcz.resolve_right (by
    simpa [STAmount.isZero] using fun h => hpz ((STAmount.toRat_eq_zero_iff _).mpr h))
  by_cases hint : v.numericType.isIntegral = true
  · -- integral: the payout is a whole number below the whole price, so one unit below it
    have hb0 : v.baseExponent = 0 := (Vault.baseExponent_bounds v).2.2 hint
    have hic : priced.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have he : priced.exponent = 0 := hic.offset_zero
    rw [he, zpow_zero, mul_one] at hpv hpu hrel
    rw [hb0, zpow_zero, div_one, mul_one] at hfl
    have hppos : 0 < priced.toRat := lt_of_le_of_ne hp0 (Ne.symm hpz)
    have hylt : y < priced.toRat := by
      have : 0 < priced.toRat / 100000 := by positivity
      linarith
    have hfloor : ⌊y⌋ < (priced.mValue.toNat : ℤ) := by
      rw [Int.floor_lt]; push_cast; rw [← hpv]; exact hylt
    have hfl' : (⌊y⌋ : ℚ) ≤ priced.toRat - 1 := by
      rw [hpv]
      have : ⌊y⌋ ≤ (priced.mValue.toNat : ℤ) - 1 := by omega
      exact_mod_cast this
    have hIε : I * (11 / 10 ^ 19) ≤ 1 / 100 := by nlinarith
    rw [hfl]
    exact ⟨by linarith, fun _ => by linarith⟩
  · -- fractional: the fee takes at least `10⁻⁵` of a 16-digit price, far more than its rounding
    have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    have hio : priced.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
    have hmlo : (10 ^ 15 : ℚ) ≤ priced.mValue.toNat := by exact_mod_cast hio.mant_lo
    have hbig : 10 ^ 15 * (10 : ℚ) ^ priced.exponent ≤ priced.toRat := by
      rw [hpv]; exact mul_le_mul_of_nonneg_right hmlo hge.le
    exact ⟨by linarith, fun h => absurd h hint⟩

/-- On a reachable vault a withdrawal that leaves shares and pays a nonzero early-exit fee keeps the per-share value. -/
private lemma Vault.Reachable.withdraw_fee_no_dilution (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) (h0 : v.earlyExitFeeRateAt t ≠ 0) :
    r.vault'.assetsAvailable.toRat * v.toExact.sharesTotal ≥
      v.assetsAvailable.toRat * r.vault'.toExact.sharesTotal := by
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨hAA', hS'⟩ := Vault.withdraw_vault_updates_exact_proof v amount waive t t0 hpos hr hc hty hmax r hok
  have hpay := (Vault.Reachable.withdraw_fee_payout_le v t0 t hr amount waive hpos hc hty r hok hlt h0).1
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := lt_of_le_of_lt (by
    have := (Vault.withdraw_shares_form v amount waive t hpos hc hty r hok).2.2; linarith) hlt
  rw [hz.idealAssetsWithdraw_eq, ← hcast] at hpay
  rw [hAA', hS']
  have hIS : v.assetsAvailable.toRat * r.shares.toRat / v.toExact.sharesTotal * v.toExact.sharesTotal =
      v.assetsAvailable.toRat * r.shares.toRat := by field_simp
  nlinarith

/-- On a reachable XRP or MPT vault a withdrawal that leaves shares and pays a nonzero early-exit fee raises the cash
per share by a factor of at least `1 + 10⁻¹⁷`: it pays at least `49/100` of a unit below the worth. -/
private lemma Vault.Reachable.withdraw_fee_gain_integral (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) (h0 : v.earlyExitFeeRateAt t ≠ 0)
    (hint : v.numericType.isIntegral = true) :
    v.assetsAvailable.toRat * r.vault'.toExact.sharesTotal * (1 + 1 / 10 ^ 17) ≤
      r.vault'.assetsAvailable.toRat * v.toExact.sharesTotal := by
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨hAA', hS'⟩ := Vault.withdraw_vault_updates_exact_proof v amount waive t t0 hpos hr hc hty hmax r hok
  have hpay := (Vault.Reachable.withdraw_fee_payout_le v t0 t hr amount waive hpos hc hty r hok hlt h0).2 hint
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hrpos := (Vault.withdraw_shares_form v amount waive t hpos hc hty r hok).2.2
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := lt_trans hrpos hlt
  rw [hz.idealAssetsWithdraw_eq, ← hcast] at hpay
  rw [hAA', hS']
  have hIS : v.assetsAvailable.toRat * r.shares.toRat / v.toExact.sharesTotal * v.toExact.sharesTotal =
      v.assetsAvailable.toRat * r.shares.toRat := by field_simp
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hcash9 := hz.cash_le
  have hS'0 : 0 ≤ (v.toExact.sharesTotal : ℚ) - r.shares.toRat := by linarith
  -- the cash per share gains at least `49/100` over the share total, far more than `10⁻¹⁷` of it
  have hsmall : v.assetsAvailable.toRat * ((v.toExact.sharesTotal : ℚ) - r.shares.toRat) * (1 / 10 ^ 17) ≤
      49 / 100 * v.toExact.sharesTotal := by
    have h1 : v.assetsAvailable.toRat * ((v.toExact.sharesTotal : ℚ) - r.shares.toRat) ≤
        9 * 10 ^ 15 * v.toExact.sharesTotal := by nlinarith
    nlinarith
  nlinarith

/-- A withdrawal by shares that succeeded on a reachable vault still succeeds on a reachable vault with the same
dates, fee rate, asset and scale, enough shares, and under a partial fee a price for its shares at least as high. -/
private lemma Vault.Reachable.withdraw_transfer (v v' : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (hr' : Vault.Reachable v' t) (hsched : v'.schedule = v.schedule)
    (hrate : v'.earlyExitFeeRate = v.earlyExitFeeRate) (hnt : v'.numericType = v.numericType)
    (hsc : v'.scale = v.scale) (shares : STAmount) (waive waive' : Bool) (hc : shares.Canonical)
    (hty : shares.mNumericType = .int64) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (rW : VaultWithAmounts) (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (hle' : shares.toRat ≤ v'.toExact.sharesTotal)
    (hprice : shares.toRat < v'.toExact.sharesTotal → v.earlyExitFeeRateAt t ≠ 0 →
      v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate → ∀ p', v'.sharesToAssetsWithdraw shares waive' = .ok p' →
      shares.toRat < v.toExact.sharesTotal ∧ ∃ p, v.sharesToAssetsWithdraw shares waive = .ok p ∧ p.toRat ≤ p'.toRat) :
    ∃ r', (v'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') := by
  obtain ⟨hgate, hfee, hbase⟩ := Vault.terms_congr hsched hrate hnt hsc t
  have hopen := Vault.withdraw_open_of_ok v _ waive t hpos rW hW
  refine Vault.Reachable.withdraw_shares_ok v' t t hr' waive' (by rw [hgate]; exact hopen) shares hc hty hpos hle' ?_
  intro hlt' h0 hM p' hp'
  rw [hfee] at h0 hM ⊢
  rw [hbase]
  obtain ⟨hlt, p, hp, hpp⟩ := hprice hlt' h0 hM p' hp'
  have hfloor := Vault.Reachable.withdraw_fee_floor v t0 t hr waive shares hc hty hpos rW hW hlt hM p hp
  have hρ1 : (0 : ℚ) ≤ 1 - (v.earlyExitFeeRateAt t).toNat / 100000 := by
    rw [sub_nonneg, div_le_one (by norm_num)]; exact_mod_cast v.earlyExitFeeRateAt_le t
  exact le_trans hfloor (mul_le_mul_of_nonneg_right hpp hρ1)

/-- A vault written only in its cash and share total keeps its dates, fee rate, asset and scale. -/
private lemma Vault.cash_frame_terms {v v' : Vault} {a s : Number}
    (hv : v'.toRawVault = { v.toRawVault with assetsAvailable := a, sharesTotal := s }) :
    v'.schedule = v.schedule ∧ v'.earlyExitFeeRate = v.earlyExitFeeRate ∧ v'.numericType = v.numericType ∧
      v'.scale = v.scale :=
  ⟨(congrArg RawVault.schedule hv).trans rfl, (congrArg RawVault.earlyExitFeeRate hv).trans rfl,
    (congrArg RawVault.numericType hv).trans rfl, (congrArg RawVault.scale hv).trans rfl⟩

/-- Proof of the deposit line of `Vault.Reachable.isolation`. A deposit runs outside the investment phase, where no
fee applies, and a donation raises the cash by at least one base unit, more than the price's 19-digit error. -/
lemma Vault.Reachable.isolation_deposit_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) (hty : shares.mNumericType = .int64) (rW : VaultWithAmounts)
    (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (amount : STAmount) (isDonation : Bool) (hposX : 0 < amount.toRat) (hcX : amount.Canonical)
    (htyX : amount.mNumericType = v.numericType) (r : VaultWithAmounts)
    (hok : (v.deposit amount isDonation t hposX).run = .ok (.ok r)) (waive' : Bool) :
    ∃ r' : VaultWithAmounts, (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hsle := Vault.withdraw_shares_le_total v shares waive t hpos hc hty rW hW
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hmint := Vault.Reachable.deposit_mint_fits_proof v t0 hr amount isDonation t hposX hcX htyX r hok
  have hr' := Vault.Reachable.deposit v t0 t amount isDonation r hr ht hcX htyX hposX hok hmint
  obtain ⟨a, s, hv⟩ := Vault.deposit_frame v amount isDonation t hposX r hok
  obtain ⟨hsch, hfr, hnt, hscl⟩ := Vault.cash_frame_terms hv
  have hmaxX := Vault.maxValue_fits_of_canonical v amount hcX htyX
  obtain ⟨-, hS'⟩ :=
    Vault.deposit_vault_updates_exact_proof v amount isDonation t t0 hposX hr hcX htyX hmaxX r hok hmint
  have htr := Vault.Reachable.withdraw_transfer v r.vault' t0 t hr hr' hsch hfr hnt hscl shares
    waive waive' hc hty hpos rW hW
  cases isDonation with
  | false =>
    -- a deposit: more shares, and no fee at a time deposits are open
    have hs0 : 0 ≤ r.shares.toRat := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hshpos, -⟩ :=
        DepAcc.Vault.deposit_success_reduces v amount t hposX hcX r hok
      exact hshpos.le
    exact htr (by rw [hS']; linarith) (fun _ h0 => absurd (Vault.deposit_fee_zero v amount t hposX r hok) h0)
  | true =>
    -- a donation: the same shares, and at least one more base unit of cash
    obtain ⟨hnav, hSeq⟩ := Vault.deposit_donation_no_dilution_proof v amount t t0 hposX hr hcX htyX hmaxX r hok
    have hSeq' : (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal := by rw [hSeq]
    refine htr (by rw [hSeq']; exact hsle) ?_
    intro hlt' _ _ p' hp'
    have hlt : shares.toRat < v.toExact.sharesTotal := by rw [← hSeq']; exact hlt'
    obtain ⟨p, hp, -, -⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hsle
    refine ⟨hlt, p, hp, ?_⟩
    have hz' := Vault.Reachable.openZone r.vault' t hr'
    have hb' : r.vault'.baseExponent = v.baseExponent := Vault.deposit_baseExponent v amount true t hposX r hok
    rw [hz.withdrawNav_eq, hz'.withdrawNav_eq] at hnav
    obtain ⟨k, -, hk⟩ := hz.cash
    obtain ⟨k', -, hk'⟩ := hz'.cash
    rw [hb'] at hk'
    have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    have hkk : (k : ℚ) + 1 ≤ k' := by
      rw [hk, hk'] at hnav
      have hlt : k < k' := by exact_mod_cast lt_of_mul_lt_mul_right hnav hbpos.le
      exact_mod_cast hlt
    have hgrow : v.assetsAvailable.toRat + 10 ^ v.baseExponent ≤ r.vault'.assetsAvailable.toRat := by
      rw [hk, hk']; nlinarith
    have hopen := hz.assetsAvailable_le_openLimit
    have h15 : (10 : ℚ) ^ (15 + v.baseExponent) = 10 ^ 15 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [h15] at hopen
    refine Vault.Reachable.price_mono_of_gain v r.vault' t0 t hr hr' hnt shares waive
      waive' hc hs1 hsle (by rw [hSeq']; exact hsle) ?_ p p' hp hp'
    rw [hSeq']
    have hS0 : (0 : ℚ) ≤ v.toExact.sharesTotal := Nat.cast_nonneg _
    have hfac : v.assetsAvailable.toRat * (1 + 1 / 10 ^ 17) ≤ r.vault'.assetsAvailable.toRat := by nlinarith
    nlinarith

/-- Proof of the withdrawal line of `Vault.Reachable.isolation`. A withdrawal with a fee raises the per-share value
of an XRP or MPT vault past the price's error, and keeps it on an IOU vault, where a whole-unit price stays. -/
lemma Vault.Reachable.isolation_withdraw_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) (hty : shares.mNumericType = .int64) (rW : VaultWithAmounts)
    (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (amount : WithdrawAmount) (holderShares : STAmount) (waiveX : Bool) (hposX : 0 < amount.amount.toRat)
    (hcX : amount.amount.Canonical) (htyX : amount.InAsset v.numericType) (hhs : holderShares.ShareBalance)
    (hsole : waiveX = true ↔ v.IsSoleShareholder holderShares) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waiveX t hposX).run = .ok (.ok r)) (hheld : r.shares.toRat ≤ holderShares.toRat)
    (hother : r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal)
    (hwhole : v.earlyExitFeeRateAt t ≠ 0 → v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate →
      v.numericType.isIntegral = false →
      ∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) (waive' : Bool) :
    ∃ r' : VaultWithAmounts, (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hsle := Vault.withdraw_shares_le_total v shares waive t hpos hc hty rW hW
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hr' := Vault.Reachable.withdraw v t0 t amount holderShares waiveX r hr ht hcX htyX hhs hsole hposX hok hheld
  obtain ⟨a, s, hv⟩ := Vault.withdraw_frame v amount waiveX t hposX r hok
  obtain ⟨hsch, hfr, hnt, hscl⟩ := Vault.cash_frame_terms hv
  obtain ⟨-, hS'⟩ := Vault.withdraw_vault_updates_exact_proof v amount waiveX t t0 hposX hr hcX htyX hmax r hok
  obtain ⟨-, -, hrpos⟩ := Vault.withdraw_shares_form v amount waiveX t hposX hcX htyX r hok
  have hle' : shares.toRat ≤ r.vault'.toExact.sharesTotal := by rw [hS']; linarith
  refine Vault.Reachable.withdraw_transfer v r.vault' t0 t hr hr' hsch hfr hnt hscl shares
    waive waive' hc hty hpos rW hW hle' ?_
  intro hlt' h0 hM p' hp'
  have hlt : shares.toRat < v.toExact.sharesTotal := by linarith
  obtain ⟨p, hp, -, hphi⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hsle
  refine ⟨hlt, p, hp, ?_⟩
  by_cases hint : v.numericType.isIntegral = true
  · -- an XRP or MPT vault: the fee raises the per-share value by more than the price's 19-digit error
    exact Vault.Reachable.price_mono_of_gain v r.vault' t0 t hr hr' hnt
      shares waive waive' hc hs1 hsle hle'
      (Vault.Reachable.withdraw_fee_gain_integral v t0 t hr amount waiveX hposX hcX htyX r hok (by linarith) h0 hint)
      p p' hp hp'
  obtain ⟨k, hk⟩ := hwhole h0 hM (by simpa using hint)
  -- the price is at most the worth, a whole number of base units
  have hple := hz.priced_le_worth hmax shares p waive hspos.le hc hp hphi ⟨k, hk⟩
  -- the fee keeps the per-share value, so the shares are worth at least as much after
  have hgain := Vault.Reachable.withdraw_fee_no_dilution v t0 t hr amount waiveX hposX hcX htyX r hok (by linarith) h0
  have hz' := Vault.Reachable.openZone r.vault' t hr'
  have hb' : r.vault'.baseExponent = v.baseExponent := (Vault.terms_congr hsch hfr hnt hscl t).2.2
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hcast' := RawVault.WF.toExact_sharesTotal r.vault'.toRawVault r.vault'.wf
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  have hS'pos : (0 : ℚ) < r.vault'.toExact.sharesTotal := by linarith
  have hk' : (k : ℚ) * 10 ^ r.vault'.baseExponent ≤ r.vault'.idealAssetsWithdraw waive' shares.toRat := by
    rw [hb', ← hk, hz.idealAssetsWithdraw_eq, hz'.idealAssetsWithdraw_eq, ← hcast, ← hcast',
      div_le_div_iff₀ hSpos hS'pos]
    nlinarith
  have hge := Vault.Reachable.price_ge_grid r.vault' t hr' shares waive' hc hs1 hle' p' hp' k hk'
  rw [hb'] at hge
  linarith

/-- Proof of the clawback line of `Vault.Reachable.isolation`. A clawback worth a whole number of base units keeps the
per-share value, so a price on a whole number of base units stays. -/
lemma Vault.Reachable.isolation_clawback_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) (hty : shares.mNumericType = .int64) (rW : VaultWithAmounts)
    (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (hcX : assets.CanonicalOrZero)
    (htyX : assets.mNumericType = v.numericType) (hhs : holderShares.ShareBalance)
    (hsole : waiveX = true ↔ v.IsSoleShareholder holderShares) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r))
    (hheld : r.shares.toRat ≤ holderShares.toRat) (hother : r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal)
    (hwhole : v.earlyExitFeeRateAt t ≠ 0 → v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate →
      (∃ k : ℤ, v.idealAssetsWithdraw waiveX r.shares.toRat = k * 10 ^ v.baseExponent) ∧
      ∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) (waive' : Bool) :
    ∃ r' : VaultWithAmounts, (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hsle := Vault.withdraw_shares_le_total v shares waive t hpos hc hty rW hW
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hr' := Vault.Reachable.clawback v t0 t assets holderShares waiveX r hr ht hcX htyX hhs hsole hnn hok hheld
  obtain ⟨a, s, hv⟩ := Vault.clawback_frame v assets holderShares waiveX hnn r hok
  obtain ⟨hsch, hfr, hnt, hscl⟩ := Vault.cash_frame_terms hv
  obtain ⟨-, hS'⟩ := Vault.clawback_vault_updates_exact_proof v assets holderShares waiveX t0 hnn hr hcX hhs hmax r hok
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waiveX hnn r hok
  obtain ⟨-, -, hrs0, -⟩ := hcp.form hcX hnn hhs hmax
  have hrpos : 0 < r.shares.toRat := lt_of_le_of_ne hrs0 (Ne.symm (STAmount.toRat_ne_zero _
    (by simpa [STAmount.isZero] using hsnz)))
  have hle' : shares.toRat ≤ r.vault'.toExact.sharesTotal := by rw [hS']; linarith
  refine Vault.Reachable.withdraw_transfer v r.vault' t0 t hr hr' hsch hfr hnt hscl shares
    waive waive' hc hty hpos rW hW hle' ?_
  intro hlt' h0 hM p' hp'
  have hlt : shares.toRat < v.toExact.sharesTotal := by linarith
  obtain ⟨hwX, k, hk⟩ := hwhole h0 hM
  obtain ⟨p, hp, -, hphi⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hsle
  refine ⟨hlt, p, hp, ?_⟩
  -- the price is at most the worth, a whole number of base units
  have hple := hz.priced_le_worth hmax shares p waive hspos.le hc hp hphi ⟨k, hk⟩
  -- a clawback worth whole base units keeps the per-share value, so the shares are worth at least as much after
  have hgain := Vault.Reachable.clawback_no_dilution_intended_proof v assets holderShares waiveX t0 hnn hr hcX hhs
    hmax r hok hwX
  have hz' := Vault.Reachable.openZone r.vault' t hr'
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq] at hgain
  have hb' : r.vault'.baseExponent = v.baseExponent := (Vault.terms_congr hsch hfr hnt hscl t).2.2
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hcast' := RawVault.WF.toExact_sharesTotal r.vault'.toRawVault r.vault'.wf
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  have hS'pos : (0 : ℚ) < r.vault'.toExact.sharesTotal := by linarith
  have hk' : (k : ℚ) * 10 ^ r.vault'.baseExponent ≤ r.vault'.idealAssetsWithdraw waive' shares.toRat := by
    rw [hb', ← hk, hz.idealAssetsWithdraw_eq, hz'.idealAssetsWithdraw_eq, ← hcast, ← hcast',
      div_le_div_iff₀ hSpos hS'pos]
    nlinarith
  have hge := Vault.Reachable.price_ge_grid r.vault' t hr' shares waive' hc hs1 hle' p' hp' k hk'
  rw [hb'] at hge
  linarith

/-- Proof of the update line of `Vault.Reachable.isolation`. An update moves no cash and no shares, so the shares price
the same. -/
lemma Vault.Reachable.isolation_update_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) (hty : shares.mNumericType = .int64) (rW : VaultWithAmounts)
    (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool) (v' : Vault)
    (hcan : v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tesSUCCESS)
    (hok : v.update assetsMaximum blockDeposit unblockDeposit = .ok v') (waive' : Bool) :
    ∃ r' : VaultWithAmounts, (v'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') := by
  have hspos : 0 < shares.toRat := hpos
  have hsle := Vault.withdraw_shares_le_total v shares waive t hpos hc hty rW hW
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hr' := Vault.Reachable.update v t0 t assetsMaximum blockDeposit unblockDeposit v' hr ht hcan hok
  have hz' := Vault.Reachable.openZone v' t hr'
  obtain ⟨m, d, hv⟩ := Vault.update_frame v assetsMaximum blockDeposit unblockDeposit v' hok
  have hSn : v'.sharesTotal = v.sharesTotal := (congrArg RawVault.sharesTotal hv).trans rfl
  have hsch : v'.schedule = v.schedule := (congrArg RawVault.schedule hv).trans rfl
  have hfr : v'.earlyExitFeeRate = v.earlyExitFeeRate := (congrArg RawVault.earlyExitFeeRate hv).trans rfl
  have hnt : v'.numericType = v.numericType := (congrArg RawVault.numericType hv).trans rfl
  have hscl : v'.scale = v.scale := (congrArg RawVault.scale hv).trans rfl
  have hSeq : (v'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal := by
    show ((v'.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ)
    rw [hSn]
  refine Vault.Reachable.withdraw_transfer v v' t0 t hr hr' hsch hfr hnt hscl shares
    waive waive' hc hty hpos rW hW (by rw [hSeq]; exact hsle) ?_
  intro hlt' _ _ p' hp'
  rw [Vault.price_congr hz hz' ((congrArg RawVault.assetsAvailable hv).trans rfl) hSn hnt shares
    waive waive'] at hp'
  exact ⟨by rw [← hSeq]; exact hlt', p', hp', le_rfl⟩

/-- Proof of the burn line of `Vault.Reachable.isolation`. A vault where a withdrawal by shares succeeded has shares
and cash, so it is not insolvent and the owner cannot burn shares. -/
lemma Vault.Reachable.isolation_burn_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) (hty : shares.mNumericType = .int64) (rW : VaultWithAmounts)
    (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW))
    (amount holderShares sharesTotalAmount : STAmount)
    (hcan : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) : False := by
  have hspos : 0 < shares.toRat := hpos
  have hsle := Vault.withdraw_shares_le_total v shares waive t hpos hc hty rW hW
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by linarith)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hcashS := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hins : v.isInsolvent = false := by
    cases h : v.isInsolvent
    · rfl
    · obtain ⟨h1, -⟩ := (Vault.isInsolvent_iff_proof v).mp h
      change v.assetsAvailable.toRat + v.assetsDeployed.toRat = 0 at h1
      rw [hz.assetsDeployed, Number.toRat_zero, add_zero] at h1
      nlinarith
  simp only [Vault.canBurnShares] at hcan
  unfold_ter at hcan
  simp [hins] at hcan

end XRPL.Model.SingleAssetVault
