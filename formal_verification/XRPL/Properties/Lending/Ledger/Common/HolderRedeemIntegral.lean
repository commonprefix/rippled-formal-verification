import XRPL.Properties.Lending.Ledger.Common.HolderRedeem

/-! # A holder redeems part of an XRP or MPT vault of any size

Whole-number cash below `2^63` keeps the redemption price within 20 units of the worth of the shares, so a redemption
that leaves at least 20 units succeeds without the cash bound of a settled vault. A last single share takes all the
cash. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On an XRP or MPT vault paying out a whole amount the cash covers leaves exactly the cash less the payout.
Both are whole numbers below `2^63`, so the 19-digit difference and its rounding into the asset are exact. -/
private lemma Vault.debit_exact_integral (v : Vault)
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) (hint : v.numericType.isIntegral = true)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (c shares : STAmount) (raw : RawVault) (hc : c.CanonicalOrZero) (hct : c.mNumericType = v.numericType)
    (hc0 : 0 < c.toRat) (hcA : c.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares c.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat = v.assetsAvailable.toRat - c.toRat := by
  have hAAn := v.wf.assetsAvailable_norm
  obtain ⟨-, k, -, hk63, hkv⟩ := Vault.cash_integral_of_exact hexact hint (by linarith)
  have hkq := cast_le_maxRep hk63
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ :=
    STAmount.CanonicalOrZero.toNumber_exact (STAmount.CanonicalOrZero.operator_neg hc) assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hv
  have hr := operator_add_rounded_to_nearest _ _ _ hAAn hnorm hs
  rw [hv, ← sub_eq_add_neg] at hr
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hnorm hs
  -- the difference of two whole numbers below `2^63` is a `Number`, so the 19-digit sum is exact
  obtain ⟨q, hq⟩ : ∃ q : ℤ, c.toRat = q :=
    ⟨_, (Rat.coe_int_num_of_den_eq_one (STAmount.CanonicalOrZero.den_one hc (by rw [hct]; exact hint))).symm⟩
  have hdiff : (((k : ℤ) - q : ℤ) : ℚ) = v.assetsAvailable.toRat - c.toRat := by push_cast; rw [hkv, hq]
  have hnum0 : (0 : ℤ) ≤ (k : ℤ) - q := by
    have : (0 : ℚ) ≤ (((k : ℤ) - q : ℤ) : ℚ) := by rw [hdiff]; linarith
    exact_mod_cast this
  have hnum63 : (k : ℤ) - q < 2 ^ 63 := by
    have : (((k : ℤ) - q : ℤ) : ℚ) < 2 ^ 63 := by rw [hdiff]; linarith
    exact_mod_cast this
  obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow ((k : ℤ) - q) 0 ⟨by omega, hnum63⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  rw [zpow_zero, mul_one, hdiff] at hwv
  have hsv : s.toRat = v.assetsAvailable.toRat - c.toRat :=
    Number.RoundsToRepresentable.eq_of_representable _ _ hr w hwn hwv
  show aa'.toRat = _
  unfold STAmount.roundToNumericType at haa
  cases hof : STAmount.ofNumber v.numericType s .to_nearest with
  | error e => rw [hof] at haa; exact absurd haa (by simp)
  | ok st =>
    rw [hof] at haa
    simp only at haa
    rw [(STAmount.CanonicalOrZero.toNumber_exact (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hof).1 aa' haa).1,
      STAmount.ofNumber_integral_exact _ _ _ _ hint hsn (by rw [hsv, ← hdiff]; exact Rat.den_intCast _) hof, hsv]

/-- On an XRP or MPT vault with nothing lent or lost, a redemption of some but not all shares succeeds without an
early-exit fee when the shares are worth at least a unit and leave at least 20, paying their worth within 20 units. -/
lemma Vault.withdraw_part_ok_integral (v : Vault) (t : UInt32) (hint : v.numericType.isIntegral = true)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero) (hLU : v.lossUnrealized = Number.zero)
    (hcash : STAmount.isRounded v.numericType v.assetsAvailable = false) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false) (hfee : v.earlyExitFeeRateAt t = 0)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (hlt : shares.toRat < v.toExact.sharesTotal)
    (hworth : 1 ≤ shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal)
    (hkeep : 20 ≤ (v.toExact.sharesTotal - shares.toRat) * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧ r.shares = shares ∧
      r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
      |r.assets.toRat - shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal| ≤ 20 := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  set V := shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal with hV
  have hrest : (v.toExact.sharesTotal - shares.toRat) * v.assetsAvailable.toRat / v.toExact.sharesTotal =
      v.assetsAvailable.toRat - V := by
    rw [hV]; field_simp
  have hVA : V + 20 ≤ v.assetsAvailable.toRat := by linarith
  have hApos : 0 < v.assetsAvailable.toRat := by linarith
  obtain ⟨-, k, -, hk63, hkv⟩ := Vault.cash_integral_of_exact hcash hint hApos
  have hkq := cast_le_maxRep hk63
  have hA10 : (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat :=
    le_trans (le_trans (by norm_num) hworth) (by linarith)
  -- the 19-digit worth is within `2·10⁻¹⁸·V` of `V`, at most `18.5` units for a cash below `2^63`
  obtain ⟨an, hann, -, hb, hprice⟩ := Vault.price_quotient v shares waive hc
    (Vault.assetsTotalForWithdrawal_of_noLending v hAD waive) hs1 hlt.le hA10 (Vault.cash_lt_of_exact hcash)
    (le_trans (by norm_num) hworth)
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb
  have herr : V * (2 / 10 ^ 18) ≤ 37 / 2 := by
    have : V ≤ 2 ^ 63 - 1 := by linarith
    nlinarith
  obtain ⟨p, hp, hp1, hpA, hph⟩ := Vault.integral_price_ok v hcash hint an hann (by linarith) (by linarith)
    (by linarith)
  have hp0 : 0 < p.toRat := by linarith
  obtain ⟨cash, hcashok⟩ := Vault.cash_ok_of_exact hcash
  have hE0 : max v.baseExponent cash.exponent = 0 := by
    rw [(Vault.baseExponent_bounds v).2.2 hint,
      show cash.exponent = 0 from (STAmount.ofNumber_integral_canonical _ _ _ _ hint hcashok).1.offset_zero]
    rfl
  have hpr := hprice p hp
  obtain ⟨r, hrun, hrs, hcl, hadj⟩ := Vault.withdraw_part_ok_of_price v t hmax hAD hLU hcash waive hopen hfee
    shares hc hty hpos hlt hApos cash hcashok p hpr (by rw [hE0, zpow_zero]; exact hp1) hpA
  -- an XRP or MPT clamp pays the price itself
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr
  have hni : p.operator_neg.integral = true := by
    unfold STAmount.integral; rw [STAmount.operator_neg_mNumericType, hpt]; exact hint
  rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
  obtain ⟨hmt, -, -, hrat⟩ := clamp_magnitude p.operator_neg
  have hra : r.assets.toRat = p.toRat := by
    rw [← hcl, hrat, STAmount.operator_neg_toRat, abs_neg, abs_of_pos hp0]
  have hrc : r.assets.CanonicalOrZero := by
    rw [← hcl]
    exact (clampToSumExponent_canonicalOrZero v.assetsAvailable _ _ v.baseExponent
      (STAmount.CanonicalOrZero.operator_neg hpcz) (v.baseExponent_range).1 (v.baseExponent_range).2
      (clampToSumExponent_integral v.assetsAvailable _ v.baseExponent hni)).1
  have hrt : r.assets.mNumericType = v.numericType := by
    rw [← hcl, hmt, STAmount.operator_neg_mNumericType, hpt]
  refine ⟨r, hrun, hrs, ?_, ?_⟩
  · -- the cash update is exact
    exact Vault.debit_exact_integral v hcash hint hmax _ _ _ hrc hrt (by rw [hra]; exact hp0)
      (by rw [hra]; exact hpA) hadj
  · rw [hra]
    have h1 : |p.toRat - V| ≤ |p.toRat - an.toRat| + |an.toRat - V| := abs_sub_le _ _ _
    linarith

/-- With a single share in the vault, one share prices exactly at the cash: multiplying by one and dividing by
one are exact, and the cash is stored exactly. -/
private lemma Vault.price_one_share (v : Vault)
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero) (_hLU : v.lossUnrealized = Number.zero)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical) (hall : shares.toRat = 1)
    (hS : v.toExact.sharesTotal = 1) :
    ∃ a, v.sharesToAssetsWithdraw shares waive = .ok a ∧ a.toRat = v.assetsAvailable.toRat := by
  have hnav := Vault.assetsTotalForWithdrawal_of_noLending v hAD waive
  have hAAn := v.wf.assetsAvailable_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  by_cases hAm : v.assetsAvailable.mantissa_ = 0
  · refine ⟨_, Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ hnav hAm, ?_⟩
    rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _), Number.toRat_eq_zero_of_mantissa_zero _ hAm]
  have hA : 0 < v.assetsAvailable.toRat :=
    lt_of_le_of_ne hAA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))
  have hA81 := Vault.cash_floor_of_exact hexact hA
  have hA96 := Vault.cash_lt_of_exact hexact
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hST : v.sharesTotal.toRat = 1 := by rw [← hcast, hS]; norm_num
  have hsn1 : sn.toRat = 1 := by rw [hsnv, hall]
  have hsnm : sn.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsn1]; norm_num)
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hST]; norm_num)
  have hSTn := v.wf.sharesTotal_norm
  -- exponents: the cash sits in `[-99, 77]`, one in `[-18, 0]`
  have hAAe_lo : (-100 : ℤ) < v.assetsAvailable.exponent_ := exponent_gt_of_le _ _ hAAn hA (by
    calc (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-100 : ℤ) = 10 ^ (-81 : ℤ) := by norm_num
      _ ≤ _ := hA81)
  have hAAe_hi : v.assetsAvailable.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt _ _ hAAn (Number.negative_false_of_pos _ hA)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  have hsne_lo : (-19 : ℤ) < sn.exponent_ :=
    exponent_gt_of_le _ _ hsnn (by rw [hsn1]; norm_num) (by rw [hsn1]; norm_num)
  have hsne_hi : sn.exponent_ ≤ 0 :=
    Number.exponent_le_of_toRat_lt _ _ hsnn (Number.negative_false_of_pos _ (by rw [hsn1]; norm_num))
      (by unfold minExponent; norm_num) (by rw [hsn1]; norm_num)
  have hSTe_lo : (-19 : ℤ) < v.sharesTotal.exponent_ :=
    exponent_gt_of_le _ _ hSTn (by rw [hST]; norm_num) (by rw [hST]; norm_num)
  obtain ⟨NS, hmul⟩ := Number.operator_mul_ok_of_normalized v.assetsAvailable sn .to_nearest hAAn hsnn hAm hsnm
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hNSv : NS.toRat = v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.eq_of_representable _ _ (operator_mul_rounded_to_nearest _ _ _ hAAn hsnn hmul)
      _ hAAn (by rw [hsn1, mul_one]) |>.trans (by rw [hsn1, mul_one])
  have hNSm : NS.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hNSv]; exact hA.ne')
  have hNSn := operator_mul_result_isNormalized _ _ _ _ hAAn hsnn hAm hsnm hmul hNSm
  have hNS : NS = v.assetsAvailable := Number.isNormalized.toRat_inj hNSn hAAn hNSv
  subst hNS
  obtain ⟨an, hdiv⟩ := Number.operator_div_ok_of_normalized _ v.sharesTotal .to_nearest hNSn hSTn hNSm hSTm
    (by unfold maxExponent; omega)
  have hanv : an.toRat = v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.eq_of_representable _ _ (operator_div_rounded_to_nearest _ _ _ hNSn hSTn hdiv)
      _ hAAn (by rw [hST, div_one]) |>.trans (by rw [hST, div_one])
  have hanm : an.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hanv]; exact hA.ne')
  have hann := operator_div_result_isNormalized _ _ _ _ hNSn hSTn hNSm hSTm hdiv hanm
  have han : an = v.assetsAvailable := Number.isNormalized.toRat_inj hann hAAn hanv
  subst han
  obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hexact
  refine ⟨cash, ?_, Vault.final_payout_exact v cash hexact hmax hcash⟩
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure, hnav, hsn, hmul, hdiv, hcash]
  simp [hAm]

/-- On an XRP or MPT vault with nothing lent or lost and a single share, redeeming that share succeeds at a time
withdrawals are open. It pays out all the cash and leaves no cash and no shares. -/
lemma Vault.withdraw_one_share_ok (v : Vault) (t : UInt32) (_hint : v.numericType.isIntegral = true)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero) (hLU : v.lossUnrealized = Number.zero)
    (hcash : STAmount.isRounded v.numericType v.assetsAvailable = false) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hS : v.toExact.sharesTotal = 1) (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hall : shares.toRat = 1) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧ r.shares = shares ∧
      r.vault'.assetsAvailable = Number.zero ∧ r.vault'.sharesTotal = Number.zero := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hall' : shares.toRat = v.toExact.sharesTotal := by rw [hall, hS]; norm_num
  -- the share total as an amount, which the shares equal: the withdrawal is final
  obtain ⟨S, hS'⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hfinal : shares.operator_eq S = true := (Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS').mpr hall'
  obtain ⟨a, hpr, hav⟩ := Vault.price_one_share v hcash hmax hAD hLU shares waive hc hall hS
  have hsz : shares.isZero = false := by
    simp only [STAmount.isZero, beq_eq_false_iff_ne]
    intro h0
    rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hspos
    exact lt_irrefl _ hspos
  have hcomp := computeWithdraw_shares_ok_of_price v shares a waive hsz hpr
  have hac := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).1
  obtain ⟨aN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hac
  obtain ⟨haNv, haNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hac aN haN
  have hge : v.assetsAvailable.operator_lt aN = false := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff _ _ v.wf.assetsAvailable_norm haNn, haNv, hav]
    exact lt_irrefl _
  have hAD' : v.assetsDeployed.operator_ne Number.zero = false := by rw [hAD]; decide
  have hLU' : v.lossUnrealized.operator_ne Number.zero = false := by rw [hLU]; decide
  obtain ⟨cash, hcashok⟩ := Vault.cash_ok_of_exact hcash
  have hcashv := Vault.final_payout_exact v cash hcash hmax hcashok
  have hcashc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcashok).1
  obtain ⟨raw, hadj⟩ := Vault.adjustAssetsAndShares_burn_all_ok' v cash shares hcashc hcashv
    (Vault.cash_lt_of_exact hcash) hsic hty hall'
  have hzero : v.assetsAvailable.toRat + cash.operator_neg.toRat = 0 := by
    rw [STAmount.operator_neg_toRat, hcashv]; ring
  obtain ⟨k, hk⟩ := v.exact.assetsAvailable_onGrid
  have hlaw := Vault.withdraw_update_lawful v cash shares raw hmax ⟨k, by rw [hcashv]; exact hk⟩ hcashc
    (le_of_eq hzero.symm) hsic hty hspos.le hall'.le (fun _ => ⟨hzero, hAD⟩) hadj
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  have hrun : (v.withdraw (.vaultShares shares) waive t hpos).run =
      .ok (.ok { vault' := v', assets := cash, shares := shares }) := by
    simp only [ExceptT.run] at hcomp hadj
    simp only [Vault.withdraw]
    unfold_ter
    simp [hopen, hcomp, hS', hfinal, hAD', haN, hge, hLU', hcashok, hadj, hv']
  obtain ⟨-, h1, h2⟩ := Vault.withdraw_final_empties v (.vaultShares shares) waive t hpos hc hty hmax hcash _ hrun hall'
  exact ⟨_, hrun, rfl, h1, h2⟩

end XRPL.Model.SingleAssetVault
