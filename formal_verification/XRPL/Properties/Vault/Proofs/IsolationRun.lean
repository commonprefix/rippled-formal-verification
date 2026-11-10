import XRPL.Properties.Vault.Proofs.Support.ExactCash
import XRPL.Properties.Vault.Proofs.CanEmpty
import XRPL.Properties.Vault.Proofs.WithdrawPayoutFloor
import XRPL.Properties.Vault.Proofs.PricedWorth
import XRPL.Properties.Vault.Proofs.ShareWorth
import XRPL.Properties.Protocol.Common.TenthBipsTotality

/-! # A withdrawal by shares on a reachable vault

On a reachable vault a withdrawal by shares, of at most the share total and at a time withdrawals are open,
succeeds unless a partial early-exit fee leaves less than one base unit of its priced amount. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On an Open-zone vault the cash, as an amount of the asset, sits on the base grid or finer. -/
private lemma Vault.OpenZone.cash_exponent_le {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash) :
    max v.baseExponent cash.exponent = v.baseExponent := by
  have hcv := Vault.final_payout_exact v cash hz.cashExact hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hct : cash.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  rcases STAmount.ofNumber_exactCanonical _ _ _ _ v.wf.assetsAvailable_norm hA.le hcash hcm with hiou | ⟨hic, -⟩
  · -- an IOU cash below `10^(16 + base)` has its last digit at the base exponent or below
    obtain ⟨hlo, -⟩ := STAmount.IOUCanonical.toRat_bounds cash hiou (by rw [hcv]; exact hA)
    have hopen := hz.assetsAvailable_le_openLimit
    refine max_eq_left ?_
    by_contra h
    push Not at h
    have h1 : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 10 ^ (cash.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : 9 * (10 : ℚ) ^ (15 + v.baseExponent) < 10 ^ (16 + v.baseExponent) := by
      rw [show (16 : ℤ) + v.baseExponent = (15 + v.baseExponent) + 1 by ring, zpow_add_one₀ (by norm_num)]
      have : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
      linarith
    rw [hcv] at hlo
    linarith
  · -- an integral cash has exponent zero, the base exponent of an integral asset
    have hint : v.numericType.isIntegral = true := by rw [← hct]; exact hic.is_integral
    have he : cash.exponent = 0 := hic.offset_zero
    rw [he, (Vault.baseExponent_bounds v).2.2 hint]
    rfl

/-- On a reachable vault shares up to the share total are worth at least one base unit each. -/
private lemma Vault.Reachable.worth_ge_base (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (shares : ℚ)
    (hs1 : 1 ≤ shares) (hle : shares ≤ v.toExact.sharesTotal) :
    (10 : ℚ) ^ v.baseExponent ≤ shares * v.assetsAvailable.toRat / v.toExact.sharesTotal := by
  have hcash := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := le_trans (by positivity) hcash
  rw [le_div_iff₀ hSpos]
  calc (10 : ℚ) ^ v.baseExponent * v.toExact.sharesTotal ≤ v.assetsAvailable.toRat := by linarith
    _ = 1 * v.assetsAvailable.toRat := (one_mul _).symm
    _ ≤ shares * v.assetsAvailable.toRat := mul_le_mul_of_nonneg_right hs1 hA0

/-- On a reachable vault a positive whole number of shares up to the share total prices between one base unit and
the cash. The 19-digit price sits within `2·10⁻¹⁸` times their worth, too close to cross either bound. -/
lemma Vault.Reachable.price_part (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical) (hs1 : 1 ≤ shares.toRat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal) :
    ∃ p, v.sharesToAssetsWithdraw shares waive = .ok p ∧
      (10 : ℚ) ^ v.baseExponent ≤ p.toRat ∧ p.toRat ≤ v.assetsAvailable.toRat := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hworth := Vault.Reachable.worth_ge_base v t0 hr _ hs1 hle
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hb10 : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ v.baseExponent :=
    zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).1
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  set V := shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal with hV
  have hA : 0 < v.assetsAvailable.toRat := by
    have : 0 < V := lt_of_lt_of_le hbpos hworth
    rw [hV, lt_div_iff₀ hSpos, zero_mul] at this
    nlinarith
  have hcash9 := hz.cash_le
  have hVle : V ≤ v.assetsAvailable.toRat := by
    rw [hV, div_le_iff₀ hSpos]; nlinarith [mul_le_mul_of_nonneg_right hle hA.le]
  -- the 19-digit worth, and the price it converts to
  obtain ⟨an, hann, hanpos, hb2, hprice⟩ := Vault.price_quotient v shares waive hc
    (hz.assetsTotalForWithdrawal_eq waive) hs1 hle (hz.cash_ge hA).2 (by linarith)
    (le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) (le_trans hb10 hworth))
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb2
  rw [← hV] at hb3 hb4
  obtain ⟨p, hp, hpz⟩ : ∃ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p ∧ p.toRat ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · rw [(Vault.baseExponent_bounds v).2.2 hint, zpow_zero] at hworth
      obtain ⟨p, hp, hp1, -⟩ := Vault.integral_price_ok v hz.cashExact hint an hann (by nlinarith) (by nlinarith)
        (by nlinarith)
      exact ⟨p, hp, by linarith⟩
    · have hfr := NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)
      rw [hfr]
      obtain ⟨p, hp⟩ := STAmount.ofNumber_fractional_ok_below an hann hanpos (by nlinarith)
      refine ⟨p, hp, STAmount.toRat_ne_zero p (STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest p hann ?_ hp)⟩
      have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2 := by norm_num
      have hVh : (10 : ℚ) ^ (-10 : ℤ) ≤ V := le_trans hb10 hworth
      have h10 : (0 : ℚ) < 10 ^ (-10 : ℤ) := zpow_pos (by norm_num) _
      have hhalf : V / 2 ≤ an.toRat := by linarith
      exact le_trans h81 (le_trans (div_le_div_of_nonneg_right hVh (by norm_num)) hhalf)
  have hpr := hprice p hp
  have hphi := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax shares p waive (by linarith) hc hle hpr
  refine ⟨p, hpr, ?_, hphi⟩
  -- the price is a whole number of its last digit, no coarser than the base grid, less than one digit off the worth
  obtain ⟨hpv, heb, -, hpl, hrel⟩ := hz.priced_grid hmax shares p waive (by linarith) hc hpr hphi hpz
  have hI : v.idealAssetsWithdraw waive shares.toRat = V := by
    rw [hz.idealAssetsWithdraw_eq, hV, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; ring
  rw [hI] at hpl hrel
  have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  have h := ge_of_grid_lt _ 1 _ _ heb _ _ hpv rfl (by push_cast; linarith)
  push_cast at h
  linarith

/-- On an XRP or MPT vault whose cash is stored exactly, a value between one unit and the cash rounds down to a
whole amount of at least one unit. -/
private lemma Vault.integral_payout_ok (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hint : v.numericType.isIntegral = true) (n : Number) (hn : n.isNormalized) (hlo : 1 ≤ n.toRat)
    (hhi : n.toRat ≤ v.assetsAvailable.toRat) :
    ∃ payout, STAmount.ofNumber v.numericType n .downward = .ok payout ∧ 1 ≤ payout.toRat := by
  have hneg := Number.negative_false_of_pos n (by linarith)
  obtain ⟨hmo, k, hkmax, hk63, hkv⟩ := Vault.cash_integral_of_exact hexact hint (by linarith)
  have hkq := cast_le_maxRep hk63
  obtain ⟨r, hr, hr0, hru64, heq⟩ := STAmount.ofNumber_integral_reduce v.numericType n .downward hint hn hneg
    (by rw [hkv] at hhi; linarith)
  obtain ⟨hfl1, hfl2⟩ := Number.to_rep_downward_floor n r hn hneg hr
  have hrlo : 1 ≤ r.toInt := by
    have : (0 : ℚ) < r.toInt := by linarith
    have : 0 < r.toInt := by exact_mod_cast this
    omega
  have hrhi : r.toInt ≤ k := by
    have : (r.toInt : ℚ) ≤ k := by rw [hkv] at hhi; linarith
    exact_mod_cast this
  have hrnat : (r.toUInt64.toNat : ℤ) = r.toInt := toUInt64_toNat_of_nonneg r hr0
  obtain ⟨p, hp⟩ : ∃ p, STAmount.ofNumber v.numericType n .downward = .ok p := by
    rw [heq]
    obtain ⟨res, hres⟩ := STAmount.canonicalize_integral_ok_of_le
      (STAmount.unchecked v.numericType r.toUInt64 0 false) .downward hint rfl rfl hru64
      (by show r.toUInt64.toNat ≤ v.numericType.maxValue.toNat; omega) hmo
    exact ⟨res, by rw [STAmount.checked]; exact hres⟩
  obtain ⟨iv, hiv, hpv⟩ := STAmount.ofNumber_integral_toRat _ n .downward p hint hneg hp
  obtain rfl : iv = r := Except.ok.inj (hiv.symm.trans hr)
  exact ⟨p, hp, by rw [hpv]; exact_mod_cast hrlo⟩

/-- A downward IOU conversion of a value at least one base unit keeps at least one base unit. -/
private lemma Vault.frac_payout_ge (b : ℤ) (hb : -10 ≤ b) (n : Number) (payout : STAmount) (hn : n.isNormalized)
    (hlo : (10 : ℚ) ^ b ≤ n.toRat) (h : STAmount.ofNumber .fractional n .downward = .ok payout) :
    (10 : ℚ) ^ b ≤ payout.toRat := by
  have hbpos : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have h0 : 0 ≤ n.toRat := by linarith
  have hm : n.mantissa_ ≠ 0 := fun h' => by rw [Number.toRat_eq_zero_of_mantissa_zero n h'] at hlo; linarith
  have hneg := Number.negative_false_of_nonneg n hn h0
  have hsz : payout.mValue ≠ 0 := by
    intro hz
    have := STAmount.ofNumber_fractional_zero_below_min .fractional n payout .downward rfl hn hneg hm h hz
    have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hR := STAmount.ofNumber_iou_downward_floor n payout hn hm h0 h hsz
  unfold RoundsToRepresentableAt at hR
  change payout.toRat = _ at hR
  rw [hR]
  set g : ℤ := n.exponent_ + 3 with hg
  have hgpos : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  obtain ⟨hmlo, -⟩ := hn.mantissaBounds_nat hm
  have hnv : (10 : ℚ) ^ (18 : ℕ) * 10 ^ n.exponent_ ≤ n.toRat := by
    rw [Number.toRat_of_nonneg n hneg]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmlo) (zpow_pos (by norm_num) _).le
  by_cases hgb : g ≤ b
  · -- one base unit is a whole number of the value's 16-digit steps
    obtain ⟨K, hK⟩ := grid_coarse_steps 1 g b hgb
    rw [Int.cast_one, one_mul] at hK
    have hKx : (K : ℚ) ≤ n.toRat / 10 ^ g := by rw [le_div_iff₀ hgpos, ← hK]; exact hlo
    have : K ≤ ⌊n.toRat / 10 ^ g⌋ := Int.le_floor.mpr hKx
    rw [hK]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hgpos.le
  · -- a 16-digit step coarser than the base unit, and the value holds at least `10^15` of them
    push Not at hgb
    have h15 : (10 ^ 15 : ℚ) ≤ n.toRat / 10 ^ g := by
      rw [le_div_iff₀ hgpos, hg, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      have : (10 : ℚ) ^ (15 : ℕ) * (10 ^ n.exponent_ * 10 ^ (3 : ℤ)) = 10 ^ (18 : ℕ) * 10 ^ n.exponent_ := by
        norm_num; ring
      norm_num at this ⊢
      linarith
    have hfl : (10 ^ 15 : ℤ) ≤ ⌊n.toRat / 10 ^ g⌋ := Int.le_floor.mpr (by exact_mod_cast h15)
    have hbg : (10 : ℚ) ^ b ≤ 10 ^ g := zpow_le_zpow_right₀ (by norm_num) hgb.le
    calc (10 : ℚ) ^ b ≤ 1 * 10 ^ g := by rw [one_mul]; exact hbg
      _ ≤ (⌊n.toRat / 10 ^ g⌋ : ℚ) * 10 ^ g := by
          apply mul_le_mul_of_nonneg_right _ hgpos.le
          have : (1 : ℤ) ≤ ⌊n.toRat / 10 ^ g⌋ := le_trans (by norm_num) hfl
          exact_mod_cast this

/-- A 100% early-exit fee pays nothing: a redemption of some but not all shares, priced between one unit at the scale
of the cash and the cash, succeeds on a vault with nothing lent and its cash stored exactly. -/
private lemma Vault.withdraw_part_ok_full_fee (v : Vault) (t : UInt32)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero)
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hfee : v.earlyExitFeeRateAt t = maxEarlyExitFeeRate)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal) (hApos : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (p : STAmount) (hpr : v.sharesToAssetsWithdraw shares waive = .ok p)
    (hplo : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ p.toRat) (hphi : p.toRat ≤ v.assetsAvailable.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hnav := Vault.assetsTotalForWithdrawal_of_noLending v hAD waive
  -- the share total as an amount, which the shares fall short of: the withdrawal is not final
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hnf : shares.operator_eq S = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact absurd ((Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS).mp h) (ne_of_lt hlt)
  have hsz : shares.isZero = false := by
    simp only [STAmount.isZero, beq_eq_false_iff_ne]
    intro h0
    rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hspos
    exact lt_irrefl _ hspos
  obtain ⟨hblo, -, -⟩ := Vault.baseExponent_bounds v
  have hp10 : (10 : ℚ) ^ (-10 : ℤ) ≤ p.toRat :=
    le_trans (zpow_le_zpow_right₀ (by norm_num) (le_trans hblo (le_max_left _ _))) hplo
  have hp0 : 0 < p.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) hp10
  have hcomp := computeWithdraw_shares_ok_of_price v shares p waive hsz hpr
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr
  have hpm : p.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hp0; exact lt_irrefl _ hp0
  have hpz : p.isZero = false := by simpa [STAmount.isZero] using hpm
  obtain ⟨pN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hpcz
  obtain ⟨hpNv, hpNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hpcz pN haN
  have hdust := Vault.dust_ok_of_exact v hexact hmax hApos cash hcash pN hpNn (by rw [hpNv]; exact hplo)
    (by rw [hpNv]; exact hphi)
    (fun hint => by rw [hpNv]; exact STAmount.CanonicalOrZero.den_one hpcz (by rw [hpt]; exact hint))
  -- the fee takes everything: the payout is zero and the shares are burned
  obtain ⟨hzc, hzt⟩ := STAmount.zero_canonicalOrZero v.numericType
  have hz0 : (STAmount.zero v.numericType).toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)
  obtain ⟨zN, hzN⟩ := STAmount.CanonicalOrZero.toNumber_ok hzc
  have hge : v.assetsAvailable.operator_lt zN = false :=
    Vault.lt_cash_false v _ zN hzc hzN (by rw [hz0]; exact hApos.le)
  obtain ⟨raw, hadj⟩ := Vault.adjust_ok_of_exact v hexact hmax _ shares hzc hzt (by rw [hz0])
    (by rw [hz0]; exact hApos.le) hsic hty hspos.le hlt.le
  have hlaw := Vault.withdraw_update_lawful v _ shares raw hmax ⟨0, by rw [hz0]; simp⟩ hzc
    (by rw [STAmount.operator_neg_toRat, hz0]; linarith) hsic hty hspos.le hlt.le
    (fun h => absurd h (ne_of_lt hlt)) hadj
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  refine ⟨{ vault' := v', assets := STAmount.zero v.numericType, shares := shares }, ?_⟩
  simp only [ExceptT.run] at hcomp hadj
  simp only [Vault.withdraw]
  unfold_ter
  simp [hopen, hcomp, hS, hnf, haN, hnav, hpz, hdust, hfee, hzN, hge, hadj, hv',
    show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide,
    show (maxEarlyExitFeeRate == 0) = false by decide]

/-- A partial early-exit fee: a redemption of some but not all shares, priced between one base unit and the cash,
succeeds on an Open-zone vault when the priced amount less the exact fee is at least one base unit. -/
private lemma Vault.withdraw_part_ok_partial_fee (v : Vault) (t : UInt32) (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hfee0 : v.earlyExitFeeRateAt t ≠ 0) (hfeeM : v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal) (hApos : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hE : max v.baseExponent cash.exponent = v.baseExponent)
    (p : STAmount) (hpr : v.sharesToAssetsWithdraw shares waive = .ok p)
    (hplo : (10 : ℚ) ^ v.baseExponent ≤ p.toRat) (hphi : p.toRat ≤ v.assetsAvailable.toRat)
    (hpay : (10 : ℚ) ^ v.baseExponent ≤ p.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000)) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) := by
  have hexact := hz.cashExact
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hnav := Vault.assetsTotalForWithdrawal_of_noLending v hz.assetsDeployed waive
  -- the share total as an amount, which the shares fall short of: the withdrawal is not final
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hnf : shares.operator_eq S = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact absurd ((Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS).mp h) (ne_of_lt hlt)
  have hsz : shares.isZero = false := by
    simp only [STAmount.isZero, beq_eq_false_iff_ne]
    intro h0
    rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hspos
    exact lt_irrefl _ hspos
  obtain ⟨hblo, -, -⟩ := Vault.baseExponent_bounds v
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp10 : (10 : ℚ) ^ (-10 : ℤ) ≤ p.toRat := le_trans (zpow_le_zpow_right₀ (by norm_num) hblo) hplo
  have hp0 : 0 < p.toRat := lt_of_lt_of_le hbpos hplo
  have hcomp := computeWithdraw_shares_ok_of_price v shares p waive hsz hpr
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr
  have hpm : p.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hp0; exact lt_irrefl _ hp0
  have hpz : p.isZero = false := by simpa [STAmount.isZero] using hpm
  obtain ⟨pN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hpcz
  obtain ⟨hpNv, hpNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hpcz pN haN
  have hdust := Vault.dust_ok_of_exact v hexact hmax hApos cash hcash pN hpNn (by rw [hpNv, hE]; exact hplo)
    (by rw [hpNv]; exact hphi)
    (fun hint => by rw [hpNv]; exact STAmount.CanonicalOrZero.den_one hpcz (by rw [hpt]; exact hint))
  -- the fee rate is strictly between 0 and 100%
  have hρle : (v.earlyExitFeeRateAt t).toNat ≤ 100000 := v.earlyExitFeeRateAt_le t
  have hρlt : (v.earlyExitFeeRateAt t).toNat < 100000 :=
    lt_of_le_of_ne hρle (fun h => hfeeM (UInt32.toNat_inj.mp h))
  have hρ0 : (0 : ℚ) < (v.earlyExitFeeRateAt t).toNat := by
    have : (v.earlyExitFeeRateAt t).toNat ≠ 0 := fun h => hfee0 (UInt32.toNat_inj.mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrz : (v.earlyExitFeeRateAt t == 0) = false := by simpa using hfee0
  have hrm : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false := by simpa using hfeeM
  -- the cash and every price stay within the Open limit
  have hopenl := hz.assetsAvailable_le_openLimit
  have h15 : (10 : ℚ) ^ (15 + v.baseExponent) = 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  rw [h15] at hopenl
  have hcash9 := hz.cash_le
  -- the fee rounds up to at most the priced amount less one base unit
  obtain ⟨fee, hfee, hfn, hf0, hfle, -⟩ := tenthBipsOfValue_upward_ok pN (v.earlyExitFeeRateAt t) (-10) hpNn
    (by rw [hpNv]; exact hp0.le) (by rw [hpNv]; linarith) (by norm_num) (fun _ => by rw [hpNv]; exact hp10) hρle
  have hgt : (10 : ℚ) ^ v.baseExponent < p.toRat := by
    by_contra h
    push Not at h
    have hpb : p.toRat = 10 ^ v.baseExponent := le_antisymm h hplo
    rw [hpb] at hpay
    have : (0 : ℚ) < 10 ^ v.baseExponent * ((v.earlyExitFeeRateAt t).toNat / 100000) := by positivity
    nlinarith
  obtain ⟨z, q, hzq, hz16, hq, hqb⟩ := Vault.priced_grid v p hpcz hpt hp0 (by linarith)
  obtain ⟨c, c5, hcn, hcv, hc5n, hc5v⟩ := gap_representable p.toRat z q v.baseExponent 1 hzq hz16 hqb hq
    (by have := (Vault.baseExponent_bounds v).2.1; omega) (by norm_num) (by push_cast; linarith)
  push_cast at hcv hc5v
  rw [one_mul] at hcv hc5v
  have hfc : fee.toRat ≤ c.toRat := tenthBipsOfValue_upward_tight pN _ fee c c5 hpNn hcn (by rw [hcv]; linarith)
    hc5n (by rw [hc5v, hcv]) (by
      rw [hcv, hpNv]
      have : p.toRat * (v.earlyExitFeeRateAt t).toNat / 100000 =
          p.toRat - p.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) := by ring
      linarith) hfee
  rw [hcv] at hfc
  -- what is left after the fee rounds down to at least one base unit
  obtain ⟨pn, hsub⟩ := Number.operator_sub_ok_of_normalized_cap pN fee .downward hpNn hfn
    (Number.negative_false_of_pos _ (by rw [hpNv]; exact hp0)) (Number.negative_false_of_nonneg _ hfn hf0)
    (by rw [hpNv]; linarith) (by rw [hpNv] at hfle; linarith)
  obtain ⟨hpn0, hpnup, hpnlo⟩ := payoutNumber_bounds pN fee pn _ hpNn (by rw [hpNv]; exact hp0.le)
    (Or.inr (by rw [hpNv]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hp10)) hρlt hfee hsub
  rw [hpNv] at hpnup hpnlo
  have hpnpos : 0 < pn.toRat := by
    have : p.toRat * (5 / 10 ^ 18) < 10 ^ v.baseExponent := by nlinarith
    linarith
  have hpnm : pn.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpnpos.ne'
  have hpnn : pn.isNormalized := operator_sub_isNormalized _ _ _ _ hpNn hfn hsub hpnm
  obtain ⟨w, hwn, hwv⟩ := Exact.exists_normalized_grid 1 v.baseExponent le_rfl (by norm_num)
    (by unfold minExponent; omega) (by have := (Vault.baseExponent_bounds v).2.1; unfold maxExponent; omega)
  rw [Nat.cast_one, one_mul] at hwv
  obtain ⟨n, hn, hpnv⟩ := operator_sub_rounded_downward pN fee pn hpNn hfn hsub hpnm
  have hpnge : (10 : ℚ) ^ v.baseExponent ≤ pn.toRat := by
    rw [hpnv, ← hwv]
    exact Number.lower_tight _ n hn w hwn (by rw [hwv, hpNv]; linarith)
  have hρ1 : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
  have hpnle : pn.toRat ≤ p.toRat := by nlinarith
  -- the rest converts into the asset, keeping at least one base unit
  obtain ⟨payout, hpo, hpayge⟩ : ∃ payout, STAmount.ofNumber v.numericType pn .downward = .ok payout ∧
      (10 : ℚ) ^ v.baseExponent ≤ payout.toRat := by
    by_cases hint : v.numericType.isIntegral = true
    · have hb0 := (Vault.baseExponent_bounds v).2.2 hint
      rw [hb0, zpow_zero] at hpnge ⊢
      obtain ⟨payout, hpo, h1⟩ := Vault.integral_payout_ok v hexact hint pn hpnn hpnge (by linarith)
      exact ⟨payout, hpo, h1⟩
    · have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
      obtain ⟨payout, hpo⟩ := STAmount.ofNumber_fractional_downward_ok pn hpnn hpnpos (by linarith)
      exact ⟨payout, by rw [hvfr]; exact hpo, Vault.frac_payout_ge _ hblo pn payout hpnn hpnge hpo⟩
  obtain ⟨hpoc, hpot⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo
  have hpom : payout.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hpayge; linarith
  have hpoz : payout.isZero = false := by simpa [STAmount.isZero] using hpom
  have hpocan : payout.Canonical := hpoc.resolve_right (by simp [hpoz])
  have hpole : payout.toRat ≤ pn.toRat :=
    (STAmount.ofNumber_downward_floor_bounds _ _ _ hpnn (Number.negative_false_of_pos _ hpnpos) hpo hpom).1
  -- the clamp keeps it on the grid of the cash it leaves, and the cash covers it
  obtain ⟨cl, hcl, hnp, hcc, hct, hc0, hcle⟩ := Vault.clamp_ok_of_exact v hexact hmax hApos cash hcash payout
    hpocan hpot (by rw [hE]; exact hpayge) (by linarith)
  obtain ⟨cN, hcN⟩ := STAmount.CanonicalOrZero.toNumber_ok hcc
  have hlt' : v.assetsAvailable.operator_lt cN = false := Vault.lt_cash_false v cl cN hcc hcN (by linarith)
  obtain ⟨raw, hadj⟩ := Vault.adjust_ok_of_exact v hexact hmax cl shares hcc hct hc0 (by linarith) hsic hty
    hspos.le hlt.le
  have hlaw := Vault.withdraw_update_lawful v cl shares raw hmax
    (Vault.clamp_grid v _ _ _ (STAmount.CanonicalOrZero.operator_neg hpoc) hcl)
    hcc (by rw [STAmount.operator_neg_toRat]; linarith) hsic hty hspos.le hlt.le
    (fun h => absurd h (ne_of_lt hlt)) hadj
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  refine ⟨{ vault' := v', assets := cl, shares := shares }, ?_⟩
  simp only [ExceptT.run] at hcomp hadj
  simp only [Vault.withdraw]
  unfold_ter
  simp [hopen, hcomp, hS, hnf, haN, hnav, hpz, hdust, hrz, hrm, hfee, hsub, hpo, hpoz, hcl, hnp, hcN, hlt', hadj,
    hv', show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]

/-- On a reachable vault a withdrawal by shares, of at most the share total and at a time withdrawals are open,
succeeds unless a partial early-exit fee leaves less than one base unit of what the shares price at. -/
lemma Vault.Reachable.withdraw_shares_ok (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (hfee : shares.toRat < v.toExact.sharesTotal → v.earlyExitFeeRateAt t ≠ 0 →
      v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate → ∀ p, v.sharesToAssetsWithdraw shares waive = .ok p →
      (10 : ℚ) ^ v.baseExponent ≤ p.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000)) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (lt_of_lt_of_le hspos hle)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  rcases lt_or_eq_of_le hle with hlt | hall
  swap
  · -- every share: the final withdrawal pays all the cash, with no fee
    obtain ⟨r, hrun, -⟩ := Vault.withdraw_all_proof v t0 t hr waive hopen shares hc hty hall hpos
    exact ⟨r, hrun⟩
  obtain ⟨p, hpr, hplo, hphi⟩ := Vault.Reachable.price_part v t0 hr hmax shares waive hc hs1 hle
  have hApos : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) (hplo.trans hphi)
  obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hz.cashExact
  have hE := hz.cash_exponent_le hmax hApos cash hcash
  by_cases h0 : v.earlyExitFeeRateAt t = 0
  · obtain ⟨r, hrun, -⟩ := Vault.withdraw_part_ok_of_price v t hmax hz.assetsDeployed hz.lossUnrealized hz.cashExact
      waive hopen h0 shares hc hty hpos hlt hApos cash hcash p hpr (by rw [hE]; exact hplo) hphi
    exact ⟨r, hrun⟩
  by_cases hM : v.earlyExitFeeRateAt t = maxEarlyExitFeeRate
  · exact Vault.withdraw_part_ok_full_fee v t hmax hz.assetsDeployed hz.cashExact waive hopen hM shares hc hty hpos
      hlt hApos cash hcash p hpr (by rw [hE]; exact hplo) hphi
  exact Vault.withdraw_part_ok_partial_fee v t hz hmax waive hopen h0 hM shares hc hty hpos hlt hApos cash hcash hE p
    hpr hplo hphi (hfee hlt h0 hM p hpr)

end XRPL.Model.SingleAssetVault
