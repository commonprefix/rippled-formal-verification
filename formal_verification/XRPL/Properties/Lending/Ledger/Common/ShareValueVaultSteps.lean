import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Vault.Proofs.PricedWorth
import XRPL.Properties.Vault.Proofs.PerShareFloor

/-! # Vault transactions that keep shareValue on a lending vault

A lending vault has assets lent out and can carry an unrealized loss, so the vault-only proofs do not cover it.
While its balances are whole base units below `10^16` of them, a VaultWithdraw or VaultClawback that does not waive
the loss pays at most the worth of the shares it removes, when that worth is a whole number of base units. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A count of base units with 16 digits is an amount of an IOU. -/
private lemma STAmount.exists_iou_units (k : ℤ) (b : ℤ) (hlo : 10 ^ 15 ≤ k) (hhi : k < 10 ^ 16)
    (hb : -96 ≤ b ∧ b ≤ 80) :
    ∃ a : STAmount, a.IOUCanonical ∧ a.toRat = (k : ℚ) * 10 ^ b ∧ a.exponent = b := by
  have hkn : k.toNat < 2 ^ 64 := by omega
  have hm : (UInt64.ofNat k.toNat).toNat = k.toNat := UInt64.toNat_ofNat_of_lt' hkn
  refine ⟨⟨.fractional, UInt64.ofNat k.toNat, b, false⟩, ⟨rfl, ?_, ?_, hb.1, hb.2⟩, ?_, rfl⟩
  · show 10 ^ 15 ≤ (UInt64.ofNat k.toNat).toNat
    rw [hm]; omega
  · show (UInt64.ofNat k.toNat).toNat < 10 ^ 16
    rw [hm]; omega
  · rw [STAmount.toRat_of_nonneg _ rfl]
    show (((UInt64.ofNat k.toNat).toNat : ℕ) : ℚ) * 10 ^ b = _
    rw [hm]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ k)

/-- A withdrawal price never exceeds the worth of the shares at the computed net asset value, when that worth is a
whole number of base units below `10^16` of them. The price rounds to nearest and the worth is an amount. -/
private lemma Vault.priced_le_whole_worth (v : Vault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares p : STAmount) (w : Bool) (nav : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav)
    (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical) (hpr : v.sharesToAssetsWithdraw shares w = .ok p)
    (k : ℤ) (hk : v.idealAssetsWithdrawAt nav.toRat shares.toRat = k * 10 ^ v.baseExponent)
    (hk16 : k < 10 ^ 16) :
    p.toRat ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat := by
  obtain ⟨nav', hsub, hN0, hp0, hcase⟩ := WdPrice.price_spec v shares p w hnn hsc hpr
  rw [hnav, Except.ok.injEq] at hsub
  subst hsub
  have hAt : v.idealAssetsWithdrawAt nav.toRat shares.toRat = nav.toRat * shares.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hI0 : 0 ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat := by
    rw [hAt]; exact div_nonneg (mul_nonneg hN0 hnn) v.wf.sharesTotal_nonneg
  rcases hcase with hpz | ⟨-, -, an, hanpos, hb, hh, hann, hof⟩
  · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hpz]; exact hI0
  rw [← hAt] at hb
  set I := v.idealAssetsWithdrawAt nav.toRat shares.toRat with hIdef
  by_cases hpm : p.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hpm]; exact hI0
  have hppos : 0 < p.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v shares p w hmax hpr
  have hpcan : p.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  have hpv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent :=
    STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
  have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  have hε : (sharesε : ℚ) = 11 / 10 ^ 19 := rfl
  have hIle : I ≤ (10 ^ 16 - 1) * 10 ^ v.baseExponent := by
    rw [hk]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k ≤ 10 ^ 16 - 1)) hbp.le
  rw [hε] at hb1 hb2
  -- on a grid no coarser than the base grid the price is less than one step above the worth, so at most it
  suffices hgrid : p.exponent ≤ v.baseExponent ∧ I * (11 / 10 ^ 19) < 1 / 2 * 10 ^ p.exponent from
    le_of_grid_lt _ k _ _ hgrid.1 _ _ hpv hk (by linarith [hgrid.2])
  by_cases hint : v.numericType.isIntegral = true
  · have hic : p.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have he : p.exponent = 0 := hic.offset_zero
    have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
    rw [hb0, zpow_zero, mul_one] at hIle
    rw [he, hb0, zpow_zero]
    exact ⟨le_refl _, by linarith⟩
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : p.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  have hmlo : (10 ^ 15 : ℚ) ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
  have hmhi : (p.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hio.mant_hi
  have hsm : p.toRat < 10 ^ 16 * (10 : ℚ) ^ p.exponent := by
    rw [hpv]; exact mul_lt_mul_of_pos_right hmhi hg
  have hbig : 10 ^ 15 * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right hmlo hg.le
  refine ⟨?_, by linarith⟩
  -- a price on a coarser grid is `10^16` base units or more, above the worth, which the rounding can't pass
  by_contra hgt
  push Not at hgt
  have h1 : (10 : ℚ) ^ (v.baseExponent + 1) ≤ 10 ^ p.exponent := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (10 : ℚ) ^ (v.baseExponent + 1) = 10 * 10 ^ v.baseExponent := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  have hk15 : 10 ^ 15 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hI' : I ≤ (10 ^ 15 - 1) * 10 ^ v.baseExponent := by
      rw [hk]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k ≤ 10 ^ 15 - 1)) hbp.le
    linarith
  obtain ⟨W, hW, hWv, hWe⟩ := STAmount.exists_iou_units k v.baseExponent hk15 hk16 v.baseExponent_range
  have hWI : W.toRat = I := by rw [hWv, hk]
  have hWt : W.mNumericType = v.numericType := by rw [hW.is_fractional, hvfr]
  have hple : p.toRat ≤ W.toRat := by
    by_cases hanle : an.toRat ≤ W.toRat
    · exact STAmount.ofNumber_to_nearest_le_of_canonical _ an p W hann hanpos.le (Or.inl hW) hWt hanle hof hpm
    · push Not at hanle
      have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (W.exponent - 1) = (10 : ℚ) ^ v.baseExponent / 20 := by
        rw [hWe, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
      refine le_of_eq (STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an p W hann hanpos.le (Or.inl hW) hWt
        (by rw [hWI]; linarith) ?_ hof hpm)
      rw [hWI, abs_of_pos (by rw [← hWI]; linarith), hu]
      linarith
  rw [hWI] at hple
  linarith

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

open private Vault.withdraw_payout_units' Vault.clawback_payout_units' Vault.debit_total_eq
  from XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
open private Vault.assetsTotal_eq_of_grid Vault.assetsTotal_bounds
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs

/-- The net asset value a withdrawal prices at is exactly AssetsTotal − LossUnrealized, while the balances are
whole base units and AssetsTotal is below `10^16` of them. -/
private lemma Vault.withdrawNav_exact (v : Vault) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hLU : ∃ n : ℕ, n ≤ 10 ^ 16 ∧ v.lossUnrealized.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (nav : Number) (hnav : v.assetsTotalForWithdrawal false = .ok nav) :
    nav.toRat = v.withdrawNav := by
  unfold XRPL.Model.SingleAssetVault.Vault.assetsTotalForWithdrawal at hnav
  obtain ⟨atot, hat, hsub⟩ := bind_ok_peel _ _ _ hnav
  dsimp only at hsub
  have hatv := Vault.assetsTotal_eq_of_grid v atot hv hS hat
  obtain ⟨hatn, -, -⟩ := Vault.assetsTotal_bounds v atot hat
  obtain ⟨⟨-, a, ha⟩, ⟨-, c, hc⟩⟩ := hv
  obtain ⟨n, hn, hnv⟩ := hLU
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hsum : v.assetsAvailable.toRat + v.assetsDeployed.toRat = ((a + c : ℤ) : ℚ) * 10 ^ v.baseExponent := by
    rw [ha, hc]; push_cast; ring
  have h0 : 0 ≤ a + c := by
    have : (0 : ℚ) ≤ ((a + c : ℤ) : ℚ) * 10 ^ v.baseExponent := by rw [← hsum]; linarith
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have h16 : a + c < 10 ^ 16 := by
    rw [open_line_eq, hsum] at hS
    have : ((a + c : ℤ) : ℚ) < 10 ^ 16 := lt_of_mul_lt_mul_right hS hp.le
    exact_mod_cast this
  obtain ⟨hlo, hhi, -⟩ := Vault.baseExponent_bounds v
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (a + c - n) v.baseExponent (by omega)
    (by unfold minExponent maxExponent; omega)
  have hex := Number.operator_sub_exact_of_fits hatn v.wf.lossUnrealized_norm hsub
    ⟨w, hw, by rw [hwv, hatv, hsum, hnv]; push_cast; ring⟩
  show nav.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat
  rw [hex, hatv]

/-- A debit of at most the removed shares' worth keeps the net asset value per share. -/
private lemma debit_keeps_perShare (A S x π : ℚ) (hS : 0 < S) (hπ : π ≤ A * x / S) :
    (A - π) * S ≥ A * (S - x) := by
  have h1 : π * S ≤ A * x := by
    have := mul_le_mul_of_nonneg_right hπ hS.le
    rwa [div_mul_cancel₀ _ hS.ne'] at this
  nlinarith

variable (v : Vault) (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
  (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
  (hLU : ∃ n : ℕ, n ≤ 10 ^ 16 ∧ v.lossUnrealized.toRat = (n : ℚ) * 10 ^ v.baseExponent)
include hasset hv hS

/-- Shares within SharesTotal, worth a whole number of base units, are priced at most at that worth when the loss
is not waived. -/
private lemma Vault.priced_le_worth_of_grid (hLU : ∃ n : ℕ, n ≤ 10 ^ 16 ∧
      v.lossUnrealized.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (shares p : STAmount) (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical)
    (hle : shares.toRat ≤ (v.toExact.sharesTotal : ℚ)) (hpr : v.sharesToAssetsWithdraw shares false = .ok p)
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw false shares.toRat = k * 10 ^ v.baseExponent) :
    p.toRat ≤ v.withdrawNav * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨nav, hnav, hN0, -⟩ := XRPL.Model.SingleAssetVault.WdPrice.price_spec v shares p false hnn hsc hpr
  have hnavv := Vault.withdrawNav_exact v hv hS hLU nav hnav
  have hI : v.idealAssetsWithdraw false shares.toRat =
      v.withdrawNav * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealAssetsWithdraw
    rw [if_neg Bool.false_ne_true]
  have hIat : v.idealAssetsWithdrawAt nav.toRat shares.toRat =
      v.withdrawNav * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealAssetsWithdrawAt
    rw [hnavv]
  obtain ⟨k, hk⟩ := hworth
  rw [hI] at hk
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hLU0 : 0 ≤ v.lossUnrealized.toRat := by
    obtain ⟨n, -, hnv⟩ := hLU
    rw [hnv]; positivity
  have hnavlt : v.withdrawNav < 10 ^ 16 * 10 ^ v.baseExponent := by
    rw [← open_line_eq]
    show v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat < _
    linarith
  -- the worth of shares within SharesTotal is at most the net asset value
  have hworthle : v.withdrawNav * shares.toRat / (v.toExact.sharesTotal : ℚ) ≤ v.withdrawNav := by
    rw [hnavv] at hN0
    rcases (Nat.cast_nonneg (α := ℚ) v.toExact.sharesTotal).lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hle hN0
    · rw [← hzero, div_zero]; exact hN0
  have hk16 : k < 10 ^ 16 := by
    have : (k : ℚ) * 10 ^ v.baseExponent < 10 ^ 16 * 10 ^ v.baseExponent := by rw [← hk]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have h := v.priced_le_whole_worth hasset.maxValue_le shares p false nav hnav hnn hsc hpr k
    (by rw [hIat]; exact hk) hk16
  rwa [hIat] at h

/-- A debit of whole base units that AssetsAvailable covers lowers AssetsTotal − LossUnrealized by exactly that
amount. -/
private lemma Vault.debit_withdrawNav (v' : Vault) (assets shares : STAmount) (raw : RawVault)
    (hc : assets.CanonicalOrZero) (hj : ∃ j : ℕ, assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hle : assets.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares assets.operator_neg shares).run = .ok (.ok raw))
    (hraw : v'.toRawVault = raw) : v'.withdrawNav = v.withdrawNav - assets.toRat := by
  have htot := Vault.debit_total_eq v assets shares raw hasset hv hS hc hj hle hadj
  obtain ⟨aa', st', hfr⟩ := Vault.adjustAssetsAndShares_frame v _ _ raw hadj
  subst hraw
  have hLU' : v'.lossUnrealized = v.lossUnrealized := (congrArg RawVault.lossUnrealized hfr :)
  have htot' : v'.assetsAvailable.toRat + v'.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat - assets.toRat := htot
  show v'.assetsAvailable.toRat + v'.assetsDeployed.toRat - v'.lossUnrealized.toRat =
    v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat - assets.toRat
  rw [hLU', htot']
  ring

/-- A VaultWithdraw that leaves shares and does not waive the loss keeps shareValue, cross-multiplied, when the
shares it redeems are worth a whole number of base units. -/
lemma Vault.withdraw_keeps_shareValue (hLU : ∃ n : ℕ, n ≤ 10 ^ 16 ∧
      v.lossUnrealized.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (haa : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (amount : WithdrawAmount) (t : UInt32) (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (r : VaultWithAmounts)
    (hok : (v.withdraw amount false t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < (v.toExact.sharesTotal : ℚ))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw false r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  have hmax := hasset.maxValue_le
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount false t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨hac, hj, hle, raw, hadj, hraw⟩ := Vault.withdraw_payout_units' v amount false t hpos hst haa hmax r hok
  have hNav' := Vault.debit_withdrawNav v hasset hv hS r.vault' r.assets _ raw hac hj hle hadj hraw
  have hST' := Vault.withdraw_exact_sharesTotal v amount false t hpos hc hty r hok
  obtain ⟨priced, hpr, hpay⟩ := Vault.withdraw_payout_le_proof v amount false t hpos hc hty hmax r hok hlt
  have hple := Vault.priced_le_worth_of_grid v hasset hv hS hLU r.shares priced hspos.le hsc hlt.le hpr hworth
  have hp0 := Vault.sharesToAssetsWithdraw_nonneg v _ _ false (Or.inl hsc) hspos.le hpr
  have hρ' : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
  rw [hNav', hST']
  refine debit_keeps_perShare _ _ _ _ (by linarith) ?_
  nlinarith

/-- A VaultClawback that does not waive the loss keeps shareValue, cross-multiplied, when the shares it destroys
are worth a whole number of base units. -/
lemma Vault.clawback_keeps_shareValue (hLU : ∃ n : ℕ, n ≤ 10 ^ 16 ∧
      v.lossUnrealized.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.ShareBalance) (hhs0 : 0 ≤ holderShares.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares false hnn).run = .ok (.ok r))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw false r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  have hmax := hasset.maxValue_le
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares false hnn r hok
  obtain ⟨hsic, hs64, hs0, -⟩ := hcp.form hc hnn hhs hmax
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, -, -, -, hrle, -⟩ :=
    Vault.clawback_recovery_le v assets holderShares false hnn hmax r hok (Or.inl hsc) hs0
  obtain ⟨hac, hj, hle, raw, hadj, hraw⟩ :=
    Vault.clawback_payout_units' v assets holderShares false hnn hc ⟨Or.inl hhs.canonical, hhs0⟩ hmax r hok
  have hNav' := Vault.debit_withdrawNav v hasset hv hS r.vault' r.assets _ raw hac hj hle hadj hraw
  have hST' := Vault.clawback_exact_sharesTotal v assets holderShares false hnn hc hhs hmax r hok
  have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rw [hST'] at hS'0
  have hple := Vault.priced_le_worth_of_grid v hasset hv hS hLU r.shares priced hs0 hsc (by linarith) hpr hworth
  have hspos : 0 < r.shares.toRat :=
    lt_of_le_of_ne hs0 (Ne.symm (STAmount.toRat_ne_zero _ (by simpa [STAmount.isZero] using hsnz)))
  rw [hNav', hST']
  exact debit_keeps_perShare _ _ _ _ (by linarith) (le_trans hrle hple)

omit hv hS in
open XRPL.Model.SingleAssetVault in
/-- A VaultDeposit that issues shares keeps shareValue, cross-multiplied, on a vault with nothing lent out, when
the shares are worth a whole number of base units. Its Open-limit check puts the vault in the Open zone. -/
lemma Vault.deposit_keeps_shareValue (hat : v.assetsTotal = .ok v.assetsAvailable)
    (hAD : v.assetsDeployed = Number.zero) (hLU0 : v.lossUnrealized = Number.zero)
    (hYU : v.yieldUnrealized = Number.zero)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (haa : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat) (hc : amount.Canonical)
    (hty : amount.mNumericType = v.numericType) (r : VaultWithAmounts)
    (hok : (v.deposit amount false t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1)
    (hworth : ∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  have hmax := hasset.maxValue_le
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, -, -, -, -⟩ := Vault.deposit_ok_reduces v amount false t hpos r hok
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra false amounts hrac hraty hmax hcomp
  obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
  obtain ⟨j, hj⟩ := Vault.clamp_grid v _ _ _ (sharesToAssetsDeposit_form v amounts.shares assets hmax hsta).1 hcl
  obtain ⟨amountNum, hnum, hex⟩ := Vault.checkOpenLimit_ok_inv v _ hin
  obtain ⟨hnv, hnn⟩ := hcf.toNumber_exact amountNum hnum
  obtain ⟨kA, hkA⟩ := haa
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hb := Vault.exceedsOpenLimit_false_total v amountNum v.assetsAvailable hnn (by rw [hnv]; exact hc0) hat
    v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg ⟨kA, by rw [hkA]; push_cast; rfl⟩
    ⟨0, by rw [hYU, Number.toRat_zero]; simp⟩ ⟨j, by rw [hnv, hj]⟩ hex
  rw [hYU, Number.toRat_zero, hnv, hkA] at hb
  have hk9 : kA ≤ 9 * 10 ^ 15 := by
    have : (kA : ℚ) * 10 ^ v.baseExponent ≤ ((9 * 10 ^ 15 : ℕ) : ℚ) * 10 ^ v.baseExponent := by
      push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hp
  have hz : v.OpenZone := ⟨hAD, hLU0, hYU, ⟨kA, hk9, hkA⟩, hst⟩
  exact hz.deposit_keeps_perShare amount t hpos hc hty r hok hSsz hworth

end XRPL.Model.Lending
