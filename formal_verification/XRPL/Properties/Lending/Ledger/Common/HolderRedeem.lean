import XRPL.Properties.Lending.Ledger.Common.SettledVault
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalExponent
import XRPL.Properties.Lending.Loan.Common.RoundTotal
import XRPL.Properties.Lending.Loan.Common.ManageRoundToExponent
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.PerShareValue

/-! # A holder redeems part of a settled vault

With no early-exit fee, shares worth at least one unit at the scale of the cash price between that unit and the cash,
so the dust check, the clamp and the cash update of a redemption that leaves other shares all succeed. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

open private STAmount.ofNumber_integral_reduce from XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality
open private exponent_headroom_of_neg from XRPL.Properties.Lending.Ledger.Common.SettledVault

/-- A cash the asset stores exactly converts into the asset. -/
lemma Vault.cash_ok_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    ∃ cash, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash := by
  have hrd := hexact
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hrd
  cases h : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
  | error e => rw [h] at hrd; simp [bind, Except.bind] at hrd
  | ok c => exact ⟨c, rfl⟩

/-- A cash the asset stores exactly is at most the largest IOU amount, `(10^16 - 1)·10^80`. -/
lemma Vault.cash_top_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    v.assetsAvailable.toRat ≤ (10 ^ 16 - 1) * 10 ^ 80 := by
  have hrep := (STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg).mp
    hexact
  rcases hrep with h0 | hrep
  · rw [h0]; norm_num
  cases hnt : v.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hrep
    obtain ⟨-, k, -, hk, hkv⟩ := hrep
    have hk' : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
    rw [hkv]; linarith
  | fractional =>
    rw [hnt] at hrep
    obtain ⟨m, e, -, hm, -, he, hv⟩ := hrep
    have hm' : (m : ℚ) ≤ 10 ^ 16 - 1 := by
      have : m ≤ 10 ^ 16 - 1 := by omega
      have h' : (m : ℚ) ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) := by exact_mod_cast this
      norm_num at h' ⊢; exact h'
    have hpe : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    rw [hv]
    calc (m : ℚ) * 10 ^ e ≤ (10 ^ 16 - 1) * 10 ^ (80 : ℤ) :=
          mul_le_mul hm' hpe hp.le (by norm_num)
      _ = _ := by norm_num

/-- A cash the asset stores exactly is below `10^96`. -/
lemma Vault.cash_lt_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    v.assetsAvailable.toRat < 10 ^ 96 := by
  linarith [Vault.cash_top_of_exact hexact]

/-- A positive cash the asset stores exactly is at least `10⁻⁸¹`, the smallest positive IOU amount. -/
lemma Vault.cash_floor_of_exact {v : Vault}
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) (hA : 0 < v.assetsAvailable.toRat) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ v.assetsAvailable.toRat := by
  have hrep := (STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm hA.le).mp hexact
  rcases hrep with h0 | hrep
  · linarith
  cases hnt : v.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hrep
    obtain ⟨-, k, -, -, hkv⟩ := hrep
    have hk : (1 : ℚ) ≤ k := by
      have : k ≠ 0 := fun h => by rw [hkv, h] at hA; simp at hA
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [hkv]
    exact le_trans (by norm_num) hk
  | fractional =>
    rw [hnt] at hrep
    obtain ⟨m, e, hm, -, he, -, hv⟩ := hrep
    have hm' : (10 : ℚ) ^ 15 ≤ m := by exact_mod_cast hm
    have hpe : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) he
    rw [hv]
    calc (10 : ℚ) ^ (-81 : ℤ) = 10 ^ 15 * 10 ^ (-96 : ℤ) := by norm_num
      _ ≤ m * 10 ^ e := mul_le_mul hm' hpe (by positivity) (by positivity)

/-- An XRP or MPT cash the asset stores exactly is a whole number of units within the asset's maximum. -/
lemma Vault.cash_integral_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hint : v.numericType.isIntegral = true) (hA : 0 < v.assetsAvailable.toRat) :
    0 ≤ v.numericType.maxOffset ∧ ∃ k : ℕ, k ≤ v.numericType.maxValue.toNat ∧ k ≤ 2 ^ 63 - 1 ∧
      v.assetsAvailable.toRat = k := by
  have hrep := (STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm hA.le).mp hexact
  rcases hrep with h0 | hrep
  · linarith
  cases hnt : v.numericType with
  | fractional => rw [hnt] at hint; exact absurd hint (by decide)
  | integral mv mo ms msh =>
    rw [hnt] at hrep
    exact hrep

/-- A whole number at most `2^63 - 1` stays so as a rational. -/
lemma cast_le_maxRep {k : ℕ} (hk : k ≤ 2 ^ 63 - 1) : (k : ℚ) ≤ 2 ^ 63 - 1 := by
  have h2 : ((k + 1 : ℕ) : ℚ) ≤ ((2 ^ 63 : ℕ) : ℚ) := by exact_mod_cast (by omega : k + 1 ≤ 2 ^ 63)
  push_cast at h2
  linarith

/-- On an XRP or MPT vault a cash stored exactly less a whole amount it covers converts into the asset. The
difference is a whole number below `2^63`, which the 19-digit rounding keeps exactly. -/
lemma Vault.integral_rest_ok_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hint : v.numericType.isIntegral = true) (hA : 0 < v.assetsAvailable.toRat) (y : ℚ) (hy : y.den = 1)
    (hy0 : 0 ≤ y) (hyA : y ≤ v.assetsAvailable.toRat)
    (X : Number) (hXn : X.isNormalized) (hr : X.RoundsToRepresentable (v.assetsAvailable.toRat - y) .to_nearest) :
    ∃ st, STAmount.ofNumber v.numericType X .to_nearest = .ok st := by
  obtain ⟨hmo, k, hkmax, hk63, hkv⟩ := Vault.cash_integral_of_exact hexact hint hA
  obtain ⟨q, hq⟩ : ∃ q : ℤ, y = q := ⟨_, (Rat.coe_int_num_of_den_eq_one hy).symm⟩
  have hkq := cast_le_maxRep hk63
  have hdiff : (((k : ℤ) - q : ℤ) : ℚ) = v.assetsAvailable.toRat - y := by push_cast; rw [hkv, hq]
  have hnum0 : (0 : ℤ) ≤ (k : ℤ) - q := by
    have : (0 : ℚ) ≤ (((k : ℤ) - q : ℤ) : ℚ) := by rw [hdiff]; linarith
    exact_mod_cast this
  have hnum63 : (k : ℤ) - q < 2 ^ 63 := by
    have : (((k : ℤ) - q : ℤ) : ℚ) < 2 ^ 63 := by rw [hdiff]; linarith
    exact_mod_cast this
  obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow ((k : ℤ) - q) 0 ⟨by omega, hnum63⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  rw [zpow_zero, mul_one, hdiff] at hwv
  have hXv : X.toRat = v.assetsAvailable.toRat - y := Number.RoundsToRepresentable.eq_of_representable _ _ hr w hwn hwv
  have hkm : (k : ℚ) ≤ v.numericType.maxValue.toNat := by exact_mod_cast hkmax
  have hden : X.toRat.den = 1 := by rw [hXv, ← hdiff]; exact Rat.den_intCast _
  exact STAmount.ofNumber_integral_ok_of_le _ _ _ hint hmo hXn
    (Number.negative_false_of_nonneg _ hXn (by rw [hXv]; linarith)) hden (by linarith) (by linarith)

/-- The scale of a positive cash the asset stores exactly is the exponent of the cash amount, never finer than
the base exponent. -/
lemma Vault.cash_exponent_of_exact {v : Vault} (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash) :
    numberExponent v.assetsAvailable v.baseExponent v.numericType = .ok (max v.baseExponent cash.exponent) := by
  have hAAn := v.wf.assetsAvailable_norm
  have hcv := Vault.final_payout_exact v cash hexact hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hA.le hcash hcm
  have hct := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  have hneg := Number.negative_false_of_pos _ hA
  obtain ⟨Y, hY, hYm⟩ : ∃ Y, STAmount.ofNumber v.numericType v.assetsAvailable .downward = .ok Y ∧
      Y.mValue ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · obtain ⟨hmo, k, hkmax, hk63, hkv⟩ := Vault.cash_integral_of_exact hexact hint hA
      have hden : v.assetsAvailable.toRat.den = 1 := by rw [hkv]; exact Rat.den_natCast k
      have hkm : (k : ℚ) ≤ v.numericType.maxValue.toNat := by exact_mod_cast hkmax
      obtain ⟨Y, hY⟩ := STAmount.ofNumber_integral_ok_of_le _ _ _ hint hmo hAAn hneg hden
        (by rw [hkv]; exact cast_le_maxRep hk63) (by rw [hkv]; exact hkm)
      refine ⟨Y, hY, fun h0 => ?_⟩
      have hYv := STAmount.ofNumber_integral_exact _ _ _ _ hint hAAn hden hY
      rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hYv
      linarith
    · have hfr := NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)
      rw [hfr]
      obtain ⟨Y, hY⟩ := STAmount.ofNumber_fractional_downward_ok _ hAAn hA (Vault.cash_lt_of_exact hexact)
      exact ⟨Y, hY, STAmount.ofNumber_frac_ne_zero_of_ge _ _ _ hAAn (Vault.cash_floor_of_exact hexact hA) hY⟩
  have hYc := STAmount.ofNumber_downward_self v.numericType cash hcE hct (by rw [hcv]; exact hA) _ hAAn
    hcv.symm Y hY hYm
  subst hYc
  unfold numberExponent
  have hz0 : ¬ v.assetsAvailable.operator_eq Number.zero = true :=
    Number.not_operator_eq_zero_of_mantissa_ne (Number.mantissa_ne_zero_of_toRat_ne_zero hA.ne')
  simp only [hz0, Bool.false_eq_true, if_false, hY, bind, Except.bind, pure, Except.pure]

/-- The 19-digit worth of some shares sits within `2·10⁻¹⁸` times their exact worth on a vault priced at its cash,
and converting it into the asset gives their price. -/
lemma Vault.price_quotient (v : Vault) (shares : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hnav : v.assetsTotalForWithdrawal waive = .ok v.assetsAvailable)
    (hs1 : 1 ≤ shares.toRat) (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (hA10 : (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat) (hA96 : v.assetsAvailable.toRat < 10 ^ 96)
    (hV : (10 : ℚ) ^ (-50 : ℤ) ≤ shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ an : Number, an.isNormalized ∧ 0 < an.toRat ∧
      |an.toRat - shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal| ≤
        shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal * (2 / 10 ^ 18) ∧
      ∀ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p → v.sharesToAssetsWithdraw shares waive = .ok p := by
  have hAAn := v.wf.assetsAvailable_norm
  have hA : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) hA10
  have hAm : v.assetsAvailable.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hA.ne'
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSTle := Vault.sharesTotal_le_maxRep v
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := by rw [← hcast]; linarith
  have hSTpos : 0 < v.sharesTotal.toRat := by linarith
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hSTpos.ne'
  have hsnpos : 0 < sn.toRat := by rw [hsnv]; linarith
  have hsnm : sn.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hsnpos.ne'
  have hsnS : sn.toRat ≤ v.sharesTotal.toRat := by rw [hsnv, ← hcast]; exact hle
  -- exponents: the cash sits in `[-28, 77]`, the shares in `[-18, 0]`
  have hAAe_lo : (-29 : ℤ) < v.assetsAvailable.exponent_ := exponent_gt_of_le _ _ hAAn hA (by
    calc (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-29 : ℤ) = 10 ^ (-10 : ℤ) := by norm_num
      _ ≤ _ := hA10)
  have hAAe_hi : v.assetsAvailable.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt _ _ hAAn (Number.negative_false_of_pos _ hA)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  have hsne_lo : (-19 : ℤ) < sn.exponent_ := exponent_gt_of_le _ _ hsnn hsnpos (by norm_num; linarith)
  have hsne_hi : sn.exponent_ ≤ 0 :=
    Number.exponent_le_of_toRat_lt _ _ hsnn (Number.negative_false_of_pos _ hsnpos)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  have hSTe_lo : (-19 : ℤ) < v.sharesTotal.exponent_ :=
    exponent_gt_of_le _ _ v.wf.sharesTotal_norm hSTpos (by norm_num; linarith)
  obtain ⟨NS, hmul⟩ := Number.operator_mul_ok_of_normalized v.assetsAvailable sn .to_nearest hAAn hsnn hAm hsnm
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hNSr := operator_mul_rounded_to_nearest _ _ _ hAAn hsnn hmul
  have hNSge : v.assetsAvailable.toRat ≤ NS.toRat :=
    Number.RoundsToRepresentable.ge_of_ge_normalized NS _ hNSr _ hAAn (by nlinarith)
  have hNSpos : 0 < NS.toRat := lt_of_lt_of_le hA hNSge
  have hNSm : NS.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hNSpos.ne'
  have hNSn : NS.isNormalized := operator_mul_result_isNormalized _ _ _ _ hAAn hsnn hAm hsnm hmul hNSm
  obtain ⟨w, hwn, hwv⟩ := Exact.exists_normalized_grid 1 115 le_rfl (by norm_num)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hNSle : NS.toRat ≤ 10 ^ 115 := by
    have h := Number.RoundsToRepresentable.le_of_le_normalized NS _ hNSr _ hwn (by
      rw [hwv]
      have h63 : sn.toRat ≤ 10 ^ 19 := by linarith
      have h96 : v.assetsAvailable.toRat ≤ 10 ^ 96 := by linarith
      calc v.assetsAvailable.toRat * sn.toRat ≤ 10 ^ 96 * 10 ^ 19 :=
            mul_le_mul h96 h63 (by linarith) (by norm_num)
        _ = ((1 : ℕ) : ℚ) * 10 ^ (115 : ℤ) := by norm_num)
    rw [hwv] at h; norm_num at h; exact h
  have hNSe_hi : NS.exponent_ ≤ 97 :=
    Number.exponent_le_of_toRat_lt _ _ hNSn (Number.negative_false_of_pos _ hNSpos)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  obtain ⟨an, hdiv⟩ := Number.operator_div_ok_of_normalized NS v.sharesTotal .to_nearest hNSn
    v.wf.sharesTotal_norm hNSm hSTm (by unfold maxExponent; omega)
  have hVw : v.assetsAvailable.toRat * sn.toRat / v.sharesTotal.toRat =
      shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal := by rw [hsnv, hcast]; ring
  obtain ⟨hann, hanpos, hb⟩ := pipe_large v.assetsAvailable sn NS an v.sharesTotal hAAn hsnn
    v.wf.sharesTotal_norm hA.le hsnpos.le hSTpos hST1 (by rw [hVw]; exact hV) hmul hdiv
  rw [hVw] at hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hV0 := le_trans (zpow_pos (by norm_num : (0 : ℚ) < 10) (-50 : ℤ)).le hV
  refine ⟨an, hann, hanpos, le_trans hb (mul_le_mul_of_nonneg_left hδ hV0), fun p hp => ?_⟩
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure, hnav, hsn, hmul, hdiv, hp]
  simp [hAm]

/-- On an XRP or MPT vault whose cash is stored exactly, a 19-digit value between one half and half a unit past
the cash converts into a whole amount between one and the cash, within half a unit of the value. -/
lemma Vault.integral_price_ok (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hint : v.numericType.isIntegral = true) (an : Number) (hann : an.isNormalized) (hlo : 1 / 2 < an.toRat)
    (hhi : an.toRat < v.assetsAvailable.toRat + 1 / 2) (hcap : an.toRat ≤ 2 ^ 63 - 1) :
    ∃ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p ∧ 1 ≤ p.toRat ∧
      p.toRat ≤ v.assetsAvailable.toRat ∧ |p.toRat - an.toRat| ≤ 1 / 2 := by
  have hanneg := Number.negative_false_of_pos an (by linarith)
  have hA : 0 < v.assetsAvailable.toRat := by linarith
  obtain ⟨hmo, k, hkmax, -, hkv⟩ := Vault.cash_integral_of_exact hexact hint hA
  obtain ⟨r, hr, hr0, hru64, heq⟩ := STAmount.ofNumber_integral_reduce v.numericType an .to_nearest hint hann
    hanneg hcap
  have hhalf := Number.to_rep_to_nearest_within_half an r hann hanneg hr
  obtain ⟨hh1, hh2⟩ := abs_le.mp hhalf
  have hrlo : 1 ≤ r.toInt := by
    have : (0 : ℚ) < r.toInt := by linarith
    have : 0 < r.toInt := by exact_mod_cast this
    omega
  have hrhi : r.toInt ≤ k := by
    have : (r.toInt : ℚ) < k + 1 := by rw [hkv] at hhi; linarith
    have : r.toInt < (k : ℤ) + 1 := by exact_mod_cast this
    omega
  have hrnat : (r.toUInt64.toNat : ℤ) = r.toInt := toUInt64_toNat_of_nonneg r hr0
  obtain ⟨p, hp⟩ : ∃ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p := by
    rw [heq]
    obtain ⟨res, hres⟩ := STAmount.canonicalize_integral_ok_of_le
      (STAmount.unchecked v.numericType r.toUInt64 0 false) .to_nearest hint rfl rfl hru64
      (by show r.toUInt64.toNat ≤ v.numericType.maxValue.toNat; omega) hmo
    exact ⟨res, by rw [STAmount.checked]; exact hres⟩
  obtain ⟨iv, hiv, hpv⟩ := STAmount.ofNumber_integral_toRat _ an .to_nearest p hint hanneg hp
  obtain rfl : iv = r := Except.ok.inj (hiv.symm.trans hr)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · rw [hpv]; exact_mod_cast hrlo
  · rw [hpv, hkv]; exact_mod_cast hrhi
  · rw [hpv]; exact hhalf

/-- On a settled vault shares worth one unit at the scale of the cash or more price between that unit and the
cash. The 19-digit price sits within `2·10⁻¹⁸` times their worth, too close for the rounding to cross either bound. -/
private lemma Vault.Settled.price_part (v : Vault) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical) (hs1 : 1 ≤ shares.toRat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal) (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hworth : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤
      shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ p, v.sharesToAssetsWithdraw shares waive = .ok p ∧
      (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ p.toRat ∧ p.toRat ≤ v.assetsAvailable.toRat := by
  have hAAn := v.wf.assetsAvailable_norm
  have hAAtop := hz.cash_top
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  have hcv := Vault.final_payout_exact v cash hz.cashExact hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hA.le hcash hcm
  have hct := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  set E := max v.baseExponent cash.exponent with hE
  have hE10 : (-10 : ℤ) ≤ E := le_trans hblo (le_max_left _ _)
  obtain ⟨an, hann, hanpos, hb2, hprice⟩ := Vault.price_quotient v shares waive hc
    (hz.assetsTotalForWithdrawal_eq waive) hs1 hle (hz.cash_ge hA).2 hz.cash_lt
    (le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) hworth)
  set V := shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal with hV
  have hVE : (10 : ℚ) ^ E ≤ V := hworth
  have hVle : V ≤ v.assetsAvailable.toRat := by
    have hS1 : (1 : ℚ) ≤ v.toExact.sharesTotal := le_trans hs1 hle
    rw [hV, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb2
  have hpE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  by_cases hint : v.numericType.isIntegral = true
  · -- a whole-number asset: the quotient rounds to a whole number between one and the cash
    have hcoff : cash.exponent = 0 := (hcE.resolve_left (fun hio => by
      have := hio.is_fractional; rw [hct] at this; rw [this] at hint; exact absurd hint (by decide))).1.offset_zero
    have hE0 : E = 0 := by rw [hE, hbint hint, hcoff]; rfl
    rw [hE0, zpow_zero] at hVE
    rw [hE0, zpow_zero]
    have hfit := hz.cashFit hint
    obtain ⟨p, hp, hp1, hpA, -⟩ := Vault.integral_price_ok v hz.cashExact hint an hann (by linarith)
      (by linarith) (by linarith)
    exact ⟨p, hprice p hp, hp1, hpA⟩
  -- an IOU asset
  have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : cash.IOUCanonical := hcE.resolve_right (fun h => by
    have := h.1.is_integral; rw [hct] at this; exact hint this)
  have hE80 : E ≤ 80 := max_le (by omega) hio.exp_hi
  obtain ⟨p, hp⟩ : ∃ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p := by
    rw [hfr]; exact STAmount.ofNumber_fractional_ok_below an hann hanpos (by nlinarith)
  have hpm : p.mValue ≠ 0 := STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest p hann
    (le_trans (le_trans (by norm_num : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2)
      (div_le_div_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) hE10) (by norm_num))) (by linarith))
    (hfr ▸ hp)
  refine ⟨p, hprice p hp, ?_, ?_⟩
  · -- one unit at the scale of the cash is an IOU amount, which the price does not round below
    set a : STAmount := ⟨.fractional, kMinValue, E - 15, false⟩ with ha_def
    have hkm : kMinValue.toNat = 10 ^ 15 := by decide
    have haio : a.IOUCanonical :=
      ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
        by show (-96 : ℤ) ≤ E - 15; omega, by show E - 15 ≤ 80; omega⟩
    have hav : a.toRat = 10 ^ E := by
      rw [STAmount.toRat_of_nonneg a rfl]
      show (kMinValue.toNat : ℚ) * 10 ^ (E - 15) = _
      rw [hkm, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
      push_cast
      field_simp
    by_cases hge : (10 : ℚ) ^ E ≤ an.toRat
    · have h := STAmount.ofNumber_to_nearest_ge_of_canonical _ an p a hann hanpos.le (Or.inl haio)
        (by rw [hfr]) (by rw [hav]; exact hge) hp hpm
      rwa [hav] at h
    · push Not at hge
      have hae : a.exponent = E - 15 := rfl
      have hnear : |an.toRat - a.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (a.exponent - 1) := by
        rw [hav, hae, abs_of_neg (by linarith), show E - 15 - 1 = E - 16 by ring,
          zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
        have h1 : (1 / 2 : ℚ) * (10 ^ E / 10 ^ (16 : ℤ)) = 10 ^ E * (1 / (2 * 10 ^ 16)) := by
          rw [show (10 : ℚ) ^ (16 : ℤ) = 10 ^ 16 by norm_num]; ring
        rw [h1]
        nlinarith
      have h := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an p a hann hanpos.le (Or.inl haio)
        (by rw [hfr]) (by rw [hav]; exact hpE) hnear hp hpm
      rw [h, hav]
  · -- the price never rounds past the cash, an IOU amount stored exactly
    by_cases hanle : an.toRat ≤ v.assetsAvailable.toRat
    · rw [← hcv]
      exact STAmount.ofNumber_to_nearest_le_of_canonical _ an p cash hann hanpos.le hcE hct
        (by rw [hcv]; exact hanle) hp hpm
    push Not at hanle
    have hnear : |an.toRat - cash.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) := by
      rw [hcv, abs_of_pos (by linarith)]
      have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) = (10 : ℚ) ^ cash.exponent / 20 := by
        rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
      rw [hu]
      obtain ⟨-, hhi⟩ := STAmount.IOUCanonical.toRat_bounds cash hio (by rw [hcv]; exact hA)
      rw [hcv] at hhi
      have h16 : (10 : ℚ) ^ (cash.exponent + 16) = 10 ^ cash.exponent * 10 ^ 16 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      rw [h16] at hhi
      linarith
    have heq := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an p cash hann hanpos.le hcE hct
      (by rw [hcv]; exact hA) hnear hp hpm
    rw [heq, hcv]

/-- Two amounts that compare equal are the same record. -/
private lemma STAmount.eq_of_operator_eq {a b : STAmount} (h : a.operator_eq b = true) : a = b := by
  obtain ⟨a1, v1, o1, n1⟩ := a
  obtain ⟨a2, v2, o2, n2⟩ := b
  simp only [STAmount.operator_eq, STAmount.areComparable, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4
  rfl

/-- A debit of one unit at the scale of a cash stored exactly or more, and at most the cash, passes the dust
check. The cash it leaves is at least one unit below the cash, more than the rounding into the asset can close. -/
lemma Vault.dust_ok_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (pN : Number) (hpNn : pN.isNormalized) (hlo : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ pN.toRat)
    (hhi : pN.toRat ≤ v.assetsAvailable.toRat) (hden : v.numericType.isIntegral = true → pN.toRat.den = 1) :
    v.checkDebitNotDust pN = .ok .tesSUCCESS := by
  set E := max v.baseExponent cash.exponent with hE
  have hAAn := v.wf.assetsAvailable_norm
  have hcv := Vault.final_payout_exact v cash hexact hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hA.le hcash hcm
  have hcneg := STAmount.mIsNegative_false_of_pos cash (by rw [hcv]; exact hA)
  have hpE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  have hpN0 : 0 < pN.toRat := lt_of_lt_of_le hpE hlo
  have hpNz : pN.operator_eq Number.zero = false := by
    simpa using Number.not_operator_eq_zero_of_mantissa_ne (Number.mantissa_ne_zero_of_toRat_ne_zero hpN0.ne')
  have hcle : cash.exponent ≤ E := le_max_right _ _
  have hcrange : (-96 : ℤ) ≤ cash.exponent ∧ cash.exponent ≤ 80 ∧ cash.mValue.toNat < 2 ^ 63 := by
    rcases hcE with hio | ⟨hic, h63⟩
    · exact ⟨hio.exp_lo, hio.exp_hi, by have := hio.mant_hi; omega⟩
    · have h0 : cash.exponent = 0 := hic.offset_zero
      exact ⟨by omega, by omega, by omega⟩
  have hcval : v.assetsAvailable.toRat = (cash.mValue.toNat : ℚ) * 10 ^ cash.exponent := by
    rw [← hcv, STAmount.toRat_of_nonneg cash hcneg]; rfl
  obtain ⟨m, hmn, hmv⟩ : ∃ m : Number, m.isNormalized ∧ m.toRat = v.assetsAvailable.toRat - 10 ^ E := by
    set d := (E - cash.exponent).toNat with hd
    have hdE : (10 : ℚ) ^ E = (10 ^ d : ℕ) * 10 ^ cash.exponent := by
      rw [hd]; push_cast
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]; ring_nf
    have hval : v.assetsAvailable.toRat - 10 ^ E =
        (((cash.mValue.toNat : ℤ) - (10 ^ d : ℕ) : ℤ) : ℚ) * 10 ^ cash.exponent := by
      rw [hcval, hdE]; push_cast; ring
    have hnn : (0 : ℤ) ≤ (cash.mValue.toNat : ℤ) - (10 ^ d : ℕ) := by
      have h1 : (0 : ℚ) ≤ (((cash.mValue.toNat : ℤ) - (10 ^ d : ℕ) : ℤ) : ℚ) * 10 ^ cash.exponent := by
        rw [← hval]; linarith
      have h2 : (0 : ℚ) ≤ (((cash.mValue.toNat : ℤ) - (10 ^ d : ℕ) : ℤ) : ℚ) :=
        nonneg_of_mul_nonneg_left h1 (zpow_pos (by norm_num) _)
      exact_mod_cast h2
    have hD0 : (0 : ℤ) ≤ ((10 ^ d : ℕ) : ℤ) := Int.natCast_nonneg _
    have hcm63 : (cash.mValue.toNat : ℤ) < 2 ^ 63 := by have := hcrange.2.2; omega
    obtain ⟨m, hmn, hmv⟩ := Number.exists_normalized_int_mul_pow ((cash.mValue.toNat : ℤ) - (10 ^ d : ℕ))
      cash.exponent ⟨by omega, by omega⟩
      ⟨by have := hcrange.1; unfold minExponent; omega, by have := hcrange.2.1; unfold maxExponent; omega⟩
    exact ⟨m, hmn, by rw [hmv, hval]⟩
  obtain ⟨A', hsub⟩ := Number.operator_sub_ok_of_exp v.assetsAvailable pN .to_nearest hAAn hpNn
    (Number.exponent_headroom_of_lt _ hAAn hA.le (Vault.cash_lt_of_exact hexact))
    (Number.exponent_headroom_of_lt _ hpNn hpN0.le (by linarith [Vault.cash_lt_of_exact hexact]))
  have hsub' := hsub
  unfold Number.operator_sub at hsub'
  have hnegn := Number.operator_neg_isNormalized pN hpNn
  have hr := operator_add_rounded_to_nearest _ _ _ hAAn hnegn hsub'
  rw [Number.toRat_neg, ← sub_eq_add_neg] at hr
  have hA'n := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hnegn hsub'
  have hA'0 : 0 ≤ A'.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hr (by linarith)
  have hA'le : A'.toRat ≤ v.assetsAvailable.toRat - 10 ^ E := by
    rw [← hmv]; exact Number.RoundsToRepresentable.le_of_le_normalized _ _ hr m hmn (by rw [hmv]; linarith)
  obtain ⟨st, hst⟩ : ∃ st, STAmount.ofNumber v.numericType A' .to_nearest = .ok st := by
    by_cases hint : v.numericType.isIntegral = true
    · exact Vault.integral_rest_ok_of_exact hexact hint hA _ (hden hint) hpN0.le hhi A' hA'n hr
    · have hfr := NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)
      rw [hfr]
      by_cases hA'm : A'.mantissa_ = 0
      · rw [Number.eq_zero_of_mantissa_zero A' hA'n hA'm]
        exact ⟨_, STAmount.ofNumber_fractional_zero _⟩
      · exact STAmount.ofNumber_fractional_ok_below A' hA'n
          (lt_of_le_of_ne hA'0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hA'm)))
          (by linarith [Vault.cash_top_of_exact hexact])
  -- the converted cash left differs from the cash: equal amounts would sit within half a unit of the cash
  have hne : st.operator_eq cash = false := by
    rw [Bool.eq_false_iff]
    intro heq
    have hsc := STAmount.eq_of_operator_eq heq
    subst hsc
    have hh := STAmount.ofNumber_to_nearest_within_half _ _ _ hA'n hA'0 hst hcm
    rw [hcv] at hh
    have hu : (10 : ℚ) ^ st.exponent ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) hcle
    have := (abs_le.mp hh).2
    linarith
  simp only [Vault.checkDebitNotDust, hpNz, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch, hsub, hcash, hst, hne]

/-- An XRP or MPT amount, canonical or zero, is a whole number. -/
lemma STAmount.CanonicalOrZero.den_one {a : STAmount} (ha : a.CanonicalOrZero)
    (hint : a.mNumericType.isIntegral = true) : a.toRat.den = 1 := by
  rcases ha with hc | hz
  · exact (hc.1 hint).1.den_eq_one
  · rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)]; rfl

/-- Converting a priced amount back down into the asset returns it unchanged, for an amount of at least `10⁻¹⁰`
and at most a cash stored exactly. -/
lemma Vault.payout_self_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hA : 0 < v.assetsAvailable.toRat)
    (p : STAmount) (hpc : p.Canonical) (hpt : p.mNumericType = v.numericType)
    (hlo : (10 : ℚ) ^ (-10 : ℤ) ≤ p.toRat) (hhi : p.toRat ≤ v.assetsAvailable.toRat)
    (pN : Number) (hpNn : pN.isNormalized) (hpNv : pN.toRat = p.toRat) :
    STAmount.ofNumber v.numericType pN .downward = .ok p := by
  have hp0 : 0 < p.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) hlo
  have hpE := STAmount.Canonical.exactCanonical _ hpc
  have hpNneg := Number.negative_false_of_pos pN (by rw [hpNv]; exact hp0)
  obtain ⟨Y, hY, hYm⟩ : ∃ Y, STAmount.ofNumber v.numericType pN .downward = .ok Y ∧ Y.mValue ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · obtain ⟨hmo, k, hkmax, hk63, hkv⟩ := Vault.cash_integral_of_exact hexact hint hA
      have hden : pN.toRat.den = 1 := by
        rw [hpNv]; exact (hpc.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1.den_eq_one
      have hkq := cast_le_maxRep hk63
      have hkm : (k : ℚ) ≤ v.numericType.maxValue.toNat := by exact_mod_cast hkmax
      obtain ⟨Y, hY⟩ := STAmount.ofNumber_integral_ok_of_le _ _ _ hint hmo hpNn hpNneg hden
        (by rw [hpNv]; linarith) (by rw [hpNv]; linarith)
      refine ⟨Y, hY, fun h0 => ?_⟩
      have hYv := STAmount.ofNumber_integral_exact _ _ _ _ hint hpNn hden hY
      rw [(STAmount.toRat_eq_zero_iff _).mpr h0, hpNv] at hYv
      linarith
    · have hfr := NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)
      rw [hfr]
      obtain ⟨Y, hY⟩ := STAmount.ofNumber_fractional_downward_ok _ hpNn (by rw [hpNv]; exact hp0)
        (by rw [hpNv]; linarith [Vault.cash_lt_of_exact hexact])
      exact ⟨Y, hY, STAmount.ofNumber_frac_ne_zero_of_ge _ _ _ hpNn
        (by rw [hpNv]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hlo) hY⟩
  rw [hY, STAmount.ofNumber_downward_self v.numericType p hpE hpt hp0 pN hpNn hpNv Y hY hYm]

/-- Burning some shares for a payout a cash stored exactly covers never throws in the cash update. -/
lemma Vault.adjust_ok_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (c shares : STAmount) (hc : c.CanonicalOrZero) (hct : c.mNumericType = v.numericType)
    (hc0 : 0 ≤ c.toRat) (hcA : c.toRat ≤ v.assetsAvailable.toRat)
    (hsh : shares.IntegralCanonical) (hsh64 : shares.mNumericType = .int64) (hs0 : 0 ≤ shares.toRat)
    (hsle : shares.toRat ≤ v.toExact.sharesTotal) :
    ∃ raw, (v.adjustAssetsAndShares c.operator_neg shares.operator_neg).run = .ok (.ok raw) := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  have hcap := (Vault.cash_lt_of_exact hexact)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSTle := Vault.sharesTotal_le_maxRep v
  have hSTnn := v.wf.sharesTotal_nonneg
  have hcn : c.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg hc
  obtain ⟨an, han⟩ := STAmount.CanonicalOrZero.toNumber_ok hcn
  obtain ⟨hanv, hann⟩ := STAmount.CanonicalOrZero.toNumber_exact hcn an han
  have hshc : shares.Canonical := hsh.canonical (by rw [hsh64]; decide)
  have hshn : shares.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg (Or.inl hshc)
  obtain ⟨sn, hsn⟩ := STAmount.CanonicalOrZero.toNumber_ok hshn
  obtain ⟨hsnv, hsnn⟩ := STAmount.CanonicalOrZero.toNumber_exact hshn sn hsn
  rw [STAmount.operator_neg_toRat] at hanv hsnv
  obtain ⟨st', hst⟩ := Number.operator_add_ok_of_exp v.sharesTotal sn .to_nearest v.wf.sharesTotal_norm hsnn
    (Number.exponent_headroom_of_lt _ v.wf.sharesTotal_norm hSTnn (by linarith))
    (exponent_headroom_of_neg _ hsnn (by rw [hsnv]; rw [← hcast] at hSTle; linarith) (by rw [hsnv]; linarith))
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_exp v.assetsAvailable an .to_nearest hAAn hann
    (Number.exponent_headroom_of_lt _ hAAn hAA0 hcap)
    (exponent_headroom_of_neg _ hann (by rw [hanv]; linarith) (by rw [hanv]; linarith))
  have hsr := operator_add_rounded_to_nearest _ _ _ hAAn hann hs
  rw [hanv, ← sub_eq_add_neg] at hsr
  have hsn' := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hann hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hsr (by linarith)
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized _ _ hsr _ hAAn (by linarith)
  obtain ⟨y, hround⟩ : ∃ y, STAmount.roundToNumericType v.numericType s .to_nearest = .ok y := by
    by_cases hsm : s.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero s hsn' hsm]
      exact ⟨_, STAmount.roundToNumericType_zero_to_nearest _⟩
    have hspos : 0 < s.toRat := lt_of_le_of_ne hs0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hsm))
    obtain ⟨ret, hret⟩ : ∃ ret, STAmount.ofNumber v.numericType s .to_nearest = .ok ret := by
      by_cases hint : v.numericType.isIntegral = true
      · exact Vault.integral_rest_ok_of_exact hexact hint (by linarith) _
          (STAmount.CanonicalOrZero.den_one hc (by rw [hct]; exact hint)) hc0 hcA s hsn' hsr
      · have hfr := NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)
        rw [hfr]
        exact STAmount.ofNumber_fractional_ok_below s hsn' hspos (by linarith [Vault.cash_top_of_exact hexact])
    obtain ⟨y, hy⟩ := STAmount.CanonicalOrZero.toNumber_ok (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hret).1
    exact ⟨y, by simp only [STAmount.roundToNumericType, hret, hy]⟩
  -- every other step is a check, so the update returns a record or a `TER`
  cases h : (v.adjustAssetsAndShares c.operator_neg shares.operator_neg).run with
  | ok res =>
    cases res with
    | ok raw => exact ⟨raw, rfl⟩
    | error ter =>
      exfalso
      obtain rfl := Vault.adjustAssetsAndShares_rejected_bad_ledger v _ _ ter h
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hcn
        (by rw [STAmount.operator_neg_toRat]; linarith) h
  | error e =>
    exfalso
    simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
    unfold_ter at h
    simp [han, hsn, hst, hs, hround, Number.operator_add_zero_right] at h
    split_ifs at h

/-- Rounding a positive IOU amount toward zero at the top IOU scale `80` never throws. The amount is below
`10^95`, so adding the reference `10^95` and taking it back stays within sixteen digits at that scale. -/
private lemma STAmount.roundToExponent_top_ok (value : STAmount) (hc : value.IOUCanonical)
    (hneg : value.mIsNegative = false) (hev : value.mOffset < 80) :
    ∃ r, STAmount.roundToExponent value 80 .towards_zero = .ok r := by
  have h_int : value.integral = false := by unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv : value.mValue ≠ 0 := by
    intro h0
    have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo
    omega
  have hz : value.isZero = false := by simp [STAmount.isZero, h_mv]
  have hkMin : kMinValue.toNat = 10 ^ 15 := by decide
  have hexp : ¬ (80 : ℤ) ≤ value.exponent := by show ¬ (80 : ℤ) ≤ value.mOffset; omega
  unfold STAmount.roundToExponent
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg (by rw [hz]; exact Bool.false_ne_true),
    if_neg hexp]
  have hchk : STAmount.checked value.mNumericType kMinValue 80 value.negative .towards_zero =
      .ok ⟨.fractional, kMinValue, 80, false⟩ := by
    rw [hc.is_fractional]
    show STAmount.checked .fractional kMinValue 80 value.mIsNegative .towards_zero = _
    rw [hneg]
    exact STAmount.checked_reference 80 false .towards_zero (by norm_num) le_rfl
  rw [hchk]
  simp only []
  set refA : STAmount := ⟨.fractional, kMinValue, 80, false⟩ with hrefA_def
  have hcr : refA.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ 80; norm_num, by show (80 : ℤ) ≤ 80; norm_num⟩
  have hrefv : refA.toRat = (10 : ℚ) ^ 95 := by
    rw [STAmount.toRat_of_nonneg refA rfl]
    show (kMinValue.toNat : ℚ) * 10 ^ (80 : ℤ) = _
    rw [hkMin]; norm_num
  have hvv : value.toRat < (10 : ℚ) ^ 95 := by
    rw [STAmount.toRat_of_nonneg value hneg]
    have hm : (value.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
    have hp : (10 : ℚ) ^ value.mOffset ≤ (10 : ℚ) ^ (79 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (value.mValue.toNat : ℚ) * 10 ^ value.mOffset
        ≤ (value.mValue.toNat : ℚ) * 10 ^ (79 : ℤ) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ < 10 ^ 16 * 10 ^ (79 : ℤ) := mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
      _ = 10 ^ 95 := by norm_num
  have hv0 : 0 ≤ value.toRat := by rw [STAmount.toRat_of_nonneg value hneg]; positivity
  obtain ⟨sum, hsum⟩ : ∃ sum, STAmount.operator_add value refA .towards_zero = .ok sum := by
    rw [STAmount.operator_add_iou_unfold value refA .towards_zero hc hcr]
    set v1n : Number := ⟨value.mIsNegative, value.mValue * 10 * 10 * 10, value.mOffset - 3⟩ with hv1n_def
    set v2n : Number := ⟨refA.mIsNegative, refA.mValue * 10 * 10 * 10, refA.mOffset - 3⟩ with hv2n_def
    have hv1_norm : v1n.isNormalized :=
      lift_isNormalized _ _ _ hc.mant_lo hc.mant_hi
        (by have := hc.exp_lo; unfold minExponent; omega) (by have := hc.exp_hi; unfold maxExponent; omega)
    have hv2_norm : v2n.isNormalized :=
      lift_isNormalized _ _ _ hcr.mant_lo hcr.mant_hi
        (by have := hcr.exp_lo; unfold minExponent; omega) (by have := hcr.exp_hi; unfold maxExponent; omega)
    have hv1_val : v1n.toRat = value.toRat := lift_toRat value hc.mant_hi
    have hv2_val : v2n.toRat = refA.toRat := lift_toRat refA hcr.mant_hi
    obtain ⟨n, hadd⟩ := Number.operator_add_ok_of_exp v1n v2n .towards_zero hv1_norm hv2_norm
      (by show value.mOffset - 3 + 22 ≤ maxExponent; have := hc.exp_hi; unfold maxExponent; omega)
      (by show (80 : ℤ) - 3 + 22 ≤ maxExponent; unfold maxExponent; omega)
    rw [hadd]
    simp only []
    have hR := operator_add_rounded_towards_zero _ _ _ hv1_norm hv2_norm hadd
    have h95 : (0 : ℚ) ≤ 10 ^ 95 := by norm_num
    have ht0 : 0 ≤ v1n.toRat + v2n.toRat := by rw [hv1_val, hv2_val, hrefv]; linarith
    have hRd : n.RoundsToRepresentable (v1n.toRat + v2n.toRat) .downward := by
      unfold Number.RoundsToRepresentable at hR ⊢
      rw [if_pos ht0] at hR
      exact hR
    obtain ⟨P, hPn, hPv⟩ := Number.exists_normalized_int_mul_pow 1 95 (by norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hPv' : P.toRat = 10 ^ 95 := by rw [hPv]; norm_num
    obtain ⟨Q, hQn, hQv⟩ := Number.exists_normalized_int_mul_pow 2 95 (by norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hQv' : Q.toRat = 2 * 10 ^ 95 := by rw [hQv]; norm_num
    have hnlo : (10 : ℚ) ^ 95 ≤ n.toRat := by
      rw [← hPv']
      exact hRd.ge_of_le (Or.inr (Or.inr rfl)) P hPn (by rw [hPv', hv1_val, hv2_val, hrefv]; linarith)
    have hnhi : n.toRat ≤ 2 * 10 ^ 95 := by
      rw [← hQv']
      exact hRd.le_of_ge (Or.inr (Or.inr rfl)) Q hQn (by rw [hQv', hv1_val, hv2_val, hrefv]; linarith)
    have hnpos : 0 < n.toRat := lt_of_lt_of_le (by positivity) hnlo
    have hnm : n.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hnpos.ne'
    have hnn : n.isNormalized := operator_add_isNormalized _ _ _ _ hv1_norm hv2_norm hadd hnm
    obtain ⟨hlo, hhi⟩ := hnn.mantissaBounds_nat hnm
    have he_hi : n.exponent_ ≤ 77 :=
      Number.exponent_le_of_toRat_lt n 77 hnn (Number.negative_false_of_pos n hnpos)
        (by unfold minExponent; norm_num) (by norm_num; linarith)
    have he_lo : 76 < n.exponent_ := exponent_gt_of_le n 76 hnn hnpos (by norm_num; linarith)
    obtain ⟨⟨m, e⟩, hnorm⟩ := normalizeToRange_16_ok n .towards_zero hlo hhi
      (by unfold minExponent; omega) (by unfold maxExponent; omega)
    have herange := normalizeToRange_16_exp_range n .towards_zero m e hlo hhi
      (by unfold minExponent; omega) (by unfold maxExponent; omega) hnorm
    have hulp := normalizeToRange_16_within_ulp n .towards_zero m e hlo hhi
      (by unfold minExponent; omega) (by unfold maxExponent; omega) hnorm
    have hmr := normalizeToRange_16_mantissa_range n .towards_zero m e hlo hhi
      (by unfold minExponent; omega) (by unfold maxExponent; omega) hnorm
    have hcmin : cMinValue.toNat = 10 ^ 15 := by decide
    -- a carry to exponent `81` would need a value of at least `10^96`
    have he80 : e = 80 := by
      by_contra hne
      have he81 : e = 81 := by omega
      have hn77 : n.exponent_ = 77 := by omega
      rw [he81, hn77] at hulp
      have hm15 : (10 : ℚ) ^ 15 ≤ |(m.toInt : ℚ)| := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        have : 10 ^ 15 ≤ m.toInt.natAbs := by rw [← hcmin]; exact hmr.1
        exact_mod_cast this
      have h81 : (0 : ℚ) < 10 ^ (81 : ℤ) := by positivity
      have h1 := abs_sub_abs_le_abs_sub ((m.toInt : ℚ) * 10 ^ (81 : ℤ)) n.toRat
      rw [abs_mul, abs_of_pos h81, abs_of_pos hnpos] at h1
      have h2 : (10 : ℚ) ^ 15 * 10 ^ (81 : ℤ) ≤ |(m.toInt : ℚ)| * 10 ^ (81 : ℤ) :=
        mul_le_mul_of_nonneg_right hm15 h81.le
      have h3 : (10 : ℚ) ^ 15 * 10 ^ (81 : ℤ) = 10 ^ 96 := by norm_num
      have h4 : (10 : ℚ) ^ (77 + 3 : ℤ) = 10 ^ 80 := by norm_num
      rw [h4] at hulp
      have h5 : (2 : ℚ) * 10 ^ 95 + 10 ^ 80 < 10 ^ 96 := by norm_num
      linarith
    have hof : IOUAmount.ofNumber n .towards_zero = .ok ⟨m, e⟩ := by
      unfold IOUAmount.ofNumber IOUAmount.fromNumber
      rw [hnorm]
      simp only []
      rw [if_neg (by unfold cMaxOffset; omega), if_neg (by unfold cMinOffset; omega)]
    rw [hof]
    simp only []
    have hne : (⟨m, e⟩ : IOUAmount).mantissa_ ≠ 0 := by
      intro hz
      have : m.toInt.natAbs = 0 := by
        show (⟨m, e⟩ : IOUAmount).mantissa_.toInt.natAbs = 0
        rw [hz]; rfl
      omega
    have hr := IOUAmount.ofNumber_InRange16 n .towards_zero ⟨m, e⟩ hlo hhi
      (by unfold minExponent; omega) (by unfold maxExponent; omega) hof hne
    exact ⟨_, STAmount.ofIOU_canonical _ _ hr⟩
  rw [hsum]
  simp only []
  -- the sum is `10^15 + k` units at exponent `80`, with `k` the whole units of the amount, below `10^15`
  have hrefeq : refA = ⟨value.mNumericType, kMinValue, 80, value.mIsNegative⟩ := by
    rw [hc.is_fractional, hneg]
  obtain ⟨k, -, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, -, htz, -⟩ :=
    STAmount.roundToExponent_sum_spec value 80 .towards_zero hc hev (by norm_num) le_rfl sum
      (by rw [← hrefeq]; exact hsum)
  have hk := htz rfl
  rw [abs_of_nonneg hv0] at hk
  have hk_lt : k < 10 ^ 15 := by
    have h1 : value.toRat / 10 ^ (80 : ℤ) < (10 ^ 15 : ℤ) := by
      rw [div_lt_iff₀ (by positivity)]
      have h := hvv
      push_cast
      norm_num at h ⊢
      linarith
    have h2 := Int.floor_lt.mpr h1
    rw [← hk] at h2
    exact_mod_cast h2
  have hc_sum : sum.IOUCanonical :=
    { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
      mant_lo := by omega
      mant_hi := by omega
      exp_lo := by rw [h_sum_off]; norm_num
      exp_hi := by rw [h_sum_off] }
  have hsumv : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ (80 : ℤ) := by
    rw [STAmount.toRat_of_nonneg sum (by rw [h_sum_neg, hneg]), h_sum_mv, h_sum_off]
  unfold STAmount.operator_sub
  have h_negRef : refA.operator_neg = ⟨.fractional, kMinValue, 80, true⟩ := by
    rw [STAmount.operator_neg_of_ne refA (by show kMinValue ≠ 0; decide)]
    rfl
  rw [h_negRef]
  set negRef : STAmount := ⟨.fractional, kMinValue, 80, true⟩ with hnegRef_def
  have hcneg : negRef.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ 80; norm_num, by show (80 : ℤ) ≤ 80; norm_num⟩
  have hnegv : negRef.toRat = -(10 : ℚ) ^ 95 := by
    rw [STAmount.toRat_of_neg negRef rfl]
    show -((kMinValue.toNat : ℚ) * 10 ^ (80 : ℤ)) = _
    rw [hkMin]; norm_num
  apply STAmount.operator_add_iou_ok sum negRef .towards_zero hc_sum hcneg
  intro n hadd hn0
  have hs1 := lift_isNormalized sum.mIsNegative sum.mValue sum.mOffset hc_sum.mant_lo hc_sum.mant_hi
    (by have := hc_sum.exp_lo; unfold minExponent; omega) (by have := hc_sum.exp_hi; unfold maxExponent; omega)
  have hs2 := lift_isNormalized negRef.mIsNegative negRef.mValue negRef.mOffset hcneg.mant_lo hcneg.mant_hi
    (by have := hcneg.exp_lo; unfold minExponent; omega) (by have := hcneg.exp_hi; unfold maxExponent; omega)
  have hR := operator_add_rounded_towards_zero _ _ _ hs1 hs2 hadd
  rw [lift_toRat sum hc_sum.mant_hi, lift_toRat negRef hcneg.mant_hi, hsumv, hnegv] at hR
  have htv : ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ (80 : ℤ) + -(10 : ℚ) ^ 95 = (k : ℚ) * 10 ^ (80 : ℤ) := by
    push_cast; norm_num; ring
  rw [htv] at hR
  have ht0 : 0 ≤ (k : ℚ) * 10 ^ (80 : ℤ) := by positivity
  unfold Number.RoundsToRepresentable at hR
  rw [if_pos ht0] at hR
  obtain ⟨l, hl, hnv⟩ := hR
  have hle := Number.lower_le _ l hl
  have hl0 := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact ht0)
  rw [Number.toRat_zero] at hl0
  have hnn := operator_add_isNormalized _ _ _ _ hs1 hs2 hadd hn0
  have hk' : (k : ℚ) + 1 ≤ 10 ^ 15 := by exact_mod_cast hk_lt
  have hlt : n.toRat < (10 : ℚ) ^ (19 : ℕ) * 10 ^ (76 : ℤ) := by
    rw [hnv]
    have h80 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ (76 : ℤ) = 10 ^ 15 * 10 ^ (80 : ℤ) := by norm_num
    rw [h80]
    have : (k : ℚ) * 10 ^ (80 : ℤ) < 10 ^ 15 * 10 ^ (80 : ℤ) :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    linarith
  exact Number.exponent_le_of_toRat_lt n 76 hnn (Number.negative_false_of_nonneg n hnn (by rw [hnv]; exact hl0))
    (by unfold minExponent; norm_num) hlt

/-- A positive IOU amount is not reported nonpositive. -/
private lemma STAmount.isFractionalNonPositive_pos (a : STAmount) (ht : a.mNumericType = .fractional)
    (hpos : 0 < a.toRat) : a.isFractionalNonPositive = .ok false := by
  have hm : a.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hpos; exact lt_irrefl _ hpos
  have hn : a.mIsNegative = false := STAmount.mIsNegative_false_of_pos a hpos
  unfold STAmount.isFractionalNonPositive
  have hint : ¬ a.integral = true := by
    show ¬ a.mNumericType.isIntegral = true; rw [ht]; decide
  rw [if_neg hint]
  have hz0 : STAmount.zero a.numericType = ⟨.fractional, 0, -100, false⟩ := by
    show STAmount.zero a.mNumericType = _; rw [ht]; rfl
  rw [hz0]
  unfold STAmount.operator_le STAmount.operator_lt STAmount.areComparable
  simp [ht, hm, hn]

/-- The clamp of a payout of one unit at the scale of a cash stored exactly or more keeps something. The
cash it leaves has a grid no coarser than that unit, and the payout floored onto that grid keeps a step. -/
lemma Vault.clamp_ok_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (p : STAmount) (hpc : p.Canonical) (hpt : p.mNumericType = v.numericType)
    (hlo : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ p.toRat) (hhi : p.toRat ≤ v.assetsAvailable.toRat) :
    ∃ c, clampToSumExponent v.assetsAvailable p.operator_neg v.baseExponent = .ok c ∧
      c.isFractionalNonPositive = .ok false ∧ c.CanonicalOrZero ∧ c.mNumericType = v.numericType ∧
      0 ≤ c.toRat ∧ c.toRat ≤ p.toRat := by
  set E := max v.baseExponent cash.exponent with hE
  have hAAn := v.wf.assetsAvailable_norm
  have hbr := v.baseExponent_range
  have hblo := (Vault.baseExponent_bounds v).1
  have hpE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  have hp0 : 0 < p.toRat := lt_of_lt_of_le hpE hlo
  have hpm : p.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hp0; exact lt_irrefl _ hp0
  have hpneg : p.mIsNegative = false := STAmount.mIsNegative_false_of_pos p hp0
  have hnc : p.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg (Or.inl hpc)
  suffices hex : ∃ c, clampToSumExponent v.assetsAvailable p.operator_neg v.baseExponent = .ok c ∧ 0 < c.toRat by
    obtain ⟨c, hcl, hc0⟩ := hex
    obtain ⟨hcc, hct, -⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hnc hbr.1 hbr.2 hcl
    have hle := clampToSumExponent_le_abs _ _ _ _ hnc hbr.1 hbr.2 hcl
    rw [STAmount.operator_neg_toRat, abs_neg, abs_of_pos hp0] at hle
    have hct' : c.mNumericType = v.numericType := by rw [hct, STAmount.operator_neg_mNumericType, hpt]
    refine ⟨c, hcl, ?_, hcc, hct', hc0.le, hle⟩
    by_cases hint : v.numericType.isIntegral = true
    · unfold STAmount.isFractionalNonPositive
      rw [if_pos (by show c.mNumericType.isIntegral = true; rw [hct']; exact hint)]
    · exact STAmount.isFractionalNonPositive_pos c
        (by rw [hct']; exact NumericType.eq_fractional_of_not_integral (by simpa using hint)) hc0
  by_cases hint : v.numericType.isIntegral = true
  · -- an XRP or MPT clamp returns the payout itself
    have hni : p.operator_neg.integral = true := by
      unfold STAmount.integral; rw [STAmount.operator_neg_mNumericType, hpt]; exact hint
    refine ⟨_, clampToSumExponent_integral _ _ _ hni, ?_⟩
    obtain ⟨-, -, -, hrat⟩ := clamp_magnitude p.operator_neg
    rw [hrat, STAmount.operator_neg_toRat, abs_neg, abs_of_pos hp0]
    exact hp0
  -- an IOU clamp floors the payout onto the grid of the cash it leaves
  have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hpio : p.IOUCanonical := hpc.2 (by unfold STAmount.integral; rw [hpt]; simpa using hint)
  have hnfr : p.operator_neg.integral = false := by
    unfold STAmount.integral; rw [STAmount.operator_neg_mNumericType, hpt]; simpa using hint
  obtain ⟨dN, hdN⟩ := STAmount.CanonicalOrZero.toNumber_ok hnc
  obtain ⟨hdNv, hdNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hnc dN hdN
  rw [STAmount.operator_neg_toRat] at hdNv
  obtain ⟨S2, hS2⟩ := Number.operator_add_ok_of_exp v.assetsAvailable dN .to_nearest hAAn hdNn
    (Number.exponent_headroom_of_lt _ hAAn hA.le (Vault.cash_lt_of_exact hexact))
    (exponent_headroom_of_neg _ hdNn (by rw [hdNv]; linarith [Vault.cash_lt_of_exact hexact])
      (by rw [hdNv]; linarith))
  have hr := operator_add_rounded_to_nearest _ _ _ hAAn hdNn hS2
  rw [hdNv, ← sub_eq_add_neg] at hr
  have hS2n := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hdNn hS2
  have hS20 : 0 ≤ S2.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hr (by linarith)
  have hS2le : S2.toRat ≤ v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized _ _ hr _ hAAn (by linarith)
  obtain ⟨E', hE'⟩ : ∃ E', numberExponent S2 v.baseExponent .fractional = .ok E' := by
    unfold numberExponent
    by_cases hz0 : S2.operator_eq Number.zero = true
    · rw [if_pos hz0]; exact ⟨_, rfl⟩
    · rw [if_neg hz0]
      have hS2pos : 0 < S2.toRat := lt_of_le_of_ne hS20 (fun h => hz0
        ((operator_eq_iff _ _ hS2n Number.zero_isNormalized).mpr (by rw [← h, Number.toRat_zero])))
      obtain ⟨st, hst⟩ := STAmount.ofNumber_fractional_downward_ok S2 hS2n hS2pos
        (by linarith [Vault.cash_lt_of_exact hexact])
      simp only [hst, bind, Except.bind, pure, Except.pure]
      exact ⟨_, rfl⟩
  have hps : postSumExponent v.assetsAvailable dN v.baseExponent .fractional = .ok E' := by
    simp only [postSumExponent, hS2, bind, Except.bind, hE']
  obtain ⟨hgeE', -, hE'80⟩ := postSumExponent_range _ _ _ _ _ hbr.1 hbr.2 hps
  have hEeq := Vault.cash_exponent_of_exact hexact hmax hA cash hcash
  rw [hfr] at hEeq
  have hAlt : v.assetsAvailable.toRat < 10 ^ (E + 16) :=
    numberExponent_frac_lt _ _ _ hAAn (by omega) hEeq
  have hE'E : E' ≤ E := by
    by_cases hgt : v.baseExponent < E'
    · obtain ⟨-, hP⟩ := numberExponent_frac_lower S2 _ E' hS2n hS20 (by omega) hE' hgt
      have h1 : (10 : ℚ) ^ (E' + 15) < 10 ^ (E + 16) := by linarith
      have h2 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
      omega
    · push Not at hgt
      exact le_trans hgt (le_max_left _ _)
  have hmag : (if p.operator_neg.negative then p.operator_neg.operator_neg else p.operator_neg) = p := by
    obtain ⟨pt, pv, po, pn⟩ := p
    obtain rfl : pn = false := hpneg
    have hpv : (pv == 0) = false := by simpa using hpm
    simp only [STAmount.operator_neg, STAmount.negative, hpv, Bool.false_eq_true, if_false, Bool.not_false,
      if_true, Bool.not_true]
  have hnt : p.operator_neg.numericType = .fractional := by
    show p.operator_neg.mNumericType = _; rw [STAmount.operator_neg_mNumericType, hpt, hfr]
  have hclamp : clampToSumExponent v.assetsAvailable p.operator_neg v.baseExponent =
      STAmount.roundToExponent p E' .towards_zero := by
    simp only [clampToSumExponent, hnfr, Bool.false_eq_true, if_false, hmag, hdN, hnt, hps, bind, Except.bind,
      pure, Except.pure]
  rw [hclamp]
  have hpE' : (10 : ℚ) ^ E' ≤ p.toRat := le_trans (zpow_le_zpow_right₀ (by norm_num) hE'E) hlo
  by_cases hpe : E' ≤ p.exponent
  · exact ⟨p, STAmount.roundToExponent_eq_self p E' _ (Or.inr (Or.inr hpe)), hp0⟩
  push Not at hpe
  obtain ⟨c, hc⟩ : ∃ c, STAmount.roundToExponent p E' .towards_zero = .ok c := by
    by_cases h79 : E' ≤ 79
    · exact STAmount.roundToExponent_ok_any p E' .towards_zero hpio hpneg (by omega) h79
    · have h80 : E' = 80 := by omega
      rw [h80]
      exact STAmount.roundToExponent_top_ok p hpio hpneg (by have : p.exponent = p.mOffset := rfl; omega)
  refine ⟨c, hc, ?_⟩
  have hround := STAmount.roundToExponent_rounded_of_scale p c E' .towards_zero hpio (by omega) hE'80 hc
  simp only [RoundsToRepresentableAt] at hround
  change c.toRat = _ at hround
  rw [if_pos hp0.le] at hround
  rw [hround]
  have hpp : (0 : ℚ) < 10 ^ E' := zpow_pos (by norm_num) _
  have hq : (1 : ℚ) ≤ p.toRat / 10 ^ E' := by rw [le_div_iff₀ hpp]; linarith
  have hfl : (1 : ℤ) ≤ ⌊p.toRat / 10 ^ E'⌋ := Int.le_floor.mpr (by exact_mod_cast hq)
  have hfl' : (1 : ℚ) ≤ (⌊p.toRat / 10 ^ E'⌋ : ℚ) := by exact_mod_cast hfl
  nlinarith

/-- Paying out a nonnegative amount a cash stored exactly covers never raises the cash. The cash is stored
exactly, so rounding the cash left into the asset never lands above it. -/
lemma Vault.debit_le_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (c shares : STAmount) (raw : RawVault) (hc : c.CanonicalOrZero) (hc0 : 0 ≤ c.toRat)
    (hcA : c.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares c.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  have hAAn := v.wf.assetsAvailable_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ :=
    STAmount.CanonicalOrZero.toNumber_exact (STAmount.CanonicalOrZero.operator_neg hc) assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hv
  have hr := operator_add_rounded_to_nearest _ _ _ hAAn hnorm hs
  rw [hv, ← sub_eq_add_neg] at hr
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hnorm hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hr (by linarith)
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized _ _ hr _ hAAn (by linarith)
  show aa'.toRat ≤ _
  unfold STAmount.roundToNumericType at haa
  cases hof : STAmount.ofNumber v.numericType s .to_nearest with
  | error e => rw [hof] at haa; exact absurd haa (by simp)
  | ok st =>
    rw [hof] at haa
    simp only at haa
    rw [(STAmount.CanonicalOrZero.toNumber_exact (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hof).1 aa' haa).1]
    by_cases hst0 : st.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hst0]; exact hAA0
    obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hexact
    have hcv := Vault.final_payout_exact v cash hexact hmax hcash
    by_cases hcm : cash.mValue = 0
    · -- no cash leaves only a zero value, which converts to zero
      have hA0 : v.assetsAvailable.toRat = 0 := by rw [← hcv, STAmount.toRat_eq_zero_of_mValue_zero _ hcm]
      have hsz : s = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hsn).mp (by linarith)
      subst hsz
      exact absurd (STAmount.ofNumber_source_ne_zero _ _ _ st hof hst0) (by decide)
    have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hAA0 hcash hcm
    have hct := STAmount.ofNumber_mNumericType _ _ _ _ hcash
    rw [← hcv]
    exact STAmount.ofNumber_to_nearest_le_of_canonical _ s st cash hsn hs0 hcE hct (by rw [hcv]; exact hsle) hof
      hst0

/-- A redemption of some but not all shares, priced between one unit at the scale of the cash and the cash,
succeeds on a vault with nothing lent, nothing lost and its cash stored exactly, when no early-exit fee applies. -/
lemma Vault.withdraw_part_ok_of_price (v : Vault) (t : UInt32)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero) (_hLU : v.lossUnrealized = Number.zero)
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hfee : v.earlyExitFeeRateAt t = 0)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal) (hApos : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (p : STAmount) (hpr : v.sharesToAssetsWithdraw shares waive = .ok p)
    (hplo : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ p.toRat) (hphi : p.toRat ≤ v.assetsAvailable.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.shares = shares ∧ clampToSumExponent v.assetsAvailable p.operator_neg v.baseExponent = .ok r.assets ∧
      (v.adjustAssetsAndShares r.assets.operator_neg shares.operator_neg).run = .ok (.ok r.vault'.toRawVault) := by
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
  have hpc : p.Canonical := hpcz.resolve_right (by simp [hpz])
  obtain ⟨pN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hpcz
  obtain ⟨hpNv, hpNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hpcz pN haN
  have hdust := Vault.dust_ok_of_exact v hexact hmax hApos cash hcash pN hpNn (by rw [hpNv]; exact hplo)
    (by rw [hpNv]; exact hphi)
    (fun hint => by rw [hpNv]; exact STAmount.CanonicalOrZero.den_one hpcz (by rw [hpt]; exact hint))
  have hge : v.assetsAvailable.operator_lt pN = false := Vault.lt_cash_false v p pN hpcz haN hphi
  -- no fee: the payout is the priced amount, clamped onto the grid of the cash it leaves
  have hzr := tenthBipsOfValue_zero_rate pN hpNn .upward
  have hsub : pN.operator_sub Number.zero .downward = .ok pN :=
    Number.operator_sub_zero_right pN Number.zero _ Number.zero_isNormalized rfl
  have hp' := Vault.payout_self_of_exact v hexact hApos p hpc hpt hp10 hphi pN hpNn hpNv
  obtain ⟨c, hcl, hnp, hcc, hct, hc0, hcle⟩ :=
    Vault.clamp_ok_of_exact v hexact hmax hApos cash hcash p hpc hpt hplo hphi
  obtain ⟨cN, hcN⟩ := STAmount.CanonicalOrZero.toNumber_ok hcc
  have hlt' : v.assetsAvailable.operator_lt cN = false := Vault.lt_cash_false v c cN hcc hcN (by linarith)
  obtain ⟨raw, hadj⟩ := Vault.adjust_ok_of_exact v hexact hmax c shares hcc hct hc0 (by linarith) hsic hty
    hspos.le hlt.le
  have hlaw := Vault.withdraw_update_lawful v c shares raw hmax
    (Vault.clamp_grid v _ _ _ (STAmount.CanonicalOrZero.operator_neg (Or.inl hpc)) hcl)
    hcc (by rw [STAmount.operator_neg_toRat]; linarith) hsic hty hspos.le hlt.le
    (fun h => absurd h (ne_of_lt hlt)) hadj
  obtain ⟨v', hv', hraw⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  refine ⟨{ vault' := v', assets := c, shares := shares }, ?_, rfl, hcl, by rw [← hraw] at hadj; exact hadj⟩
  simp only [ExceptT.run] at hcomp hadj
  simp only [Vault.withdraw]
  unfold_ter
  simp [hopen, hcomp, hS, hnf, haN, hnav, hpz, hdust, hfee, hge, hzr, hsub, hp', hcl, hnp, hcN, hlt', hadj,
    hv', show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide,
    show ((0 : TenthBips32) == maxEarlyExitFeeRate) = false by decide]

/-- On a settled vault a redemption of some but not all shares succeeds and never raises the cash at a time
without an early-exit fee, when the shares are worth at least one unit at the scale of the cash, or there is no cash. -/
lemma Vault.Settled.withdraw_part_ok (v : Vault) (t : UInt32) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hfee : v.earlyExitFeeRateAt t = 0)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal)
    (hworth : 0 < v.assetsAvailable.toRat →
      ∀ E, numberExponent v.assetsAvailable v.baseExponent v.numericType = .ok E →
        (10 : ℚ) ^ E ≤ shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.shares = shares ∧ r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  have hnav := hz.assetsTotalForWithdrawal_eq waive
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
  rcases eq_or_lt_of_le hAA0 with hAAz | hApos
  · -- no cash: the shares price at zero and nothing is paid
    have hAm : v.assetsAvailable.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp hAAz.symm
    have hAz : v.assetsAvailable = Number.zero := Number.eq_zero_of_mantissa_zero _ hAAn hAm
    have hpr := Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ hnav hAm
    have hcomp := computeWithdraw_shares_ok_of_price v shares _ waive hsz hpr
    obtain ⟨hzc, hzt⟩ := STAmount.zero_canonicalOrZero v.numericType
    obtain ⟨pN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hzc
    obtain ⟨hpNv, hpNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hzc pN haN
    have hz0 : (STAmount.zero v.numericType).toRat = 0 :=
      (STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)
    have hpNz : pN = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hpNn).mp (by rw [hpNv, hz0])
    subst hpNz
    have hpz : (STAmount.zero v.numericType).isZero = true := by
      simp [STAmount.isZero, STAmount.zero_mValue]
    have hne : v.assetsAvailable.operator_ne Number.zero = false := by rw [hAz]; decide
    have hdust : v.checkDebitNotDust Number.zero = .ok .tesSUCCESS := by
      simp [Vault.checkDebitNotDust, show Number.zero.operator_eq Number.zero = true by decide]
      rfl
    have hge : v.assetsAvailable.operator_lt Number.zero = false := by rw [hAz]; decide
    obtain ⟨raw, hadj⟩ := Vault.adjust_ok_of_exact v hz.cashExact hmax _ shares hzc hzt (by rw [hz0])
      (by rw [hz0]; exact hAA0) hsic hty hspos.le hlt.le
    have hlaw := Vault.withdraw_update_lawful v _ shares raw hmax ⟨0, by rw [hz0]; simp⟩ hzc
      (by rw [STAmount.operator_neg_toRat, hz0]; linarith) hsic hty hspos.le hlt.le
      (fun h => absurd h (ne_of_lt hlt)) hadj
    obtain ⟨v', hv', hraw⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
    refine ⟨{ vault' := v', assets := STAmount.zero v.numericType, shares := shares }, ?_, rfl, ?_⟩
    swap
    · show v'.toRawVault.assetsAvailable.toRat ≤ _
      rw [hraw]
      exact Vault.debit_le_of_exact v hz.cashExact hmax _ _ raw hzc (by rw [hz0]) (by rw [hz0]; exact hAA0) hadj
    simp only [ExceptT.run] at hcomp hadj
    simp only [Vault.withdraw]
    unfold_ter
    simp [hopen, hcomp, hS, hnf, haN, hnav, hpz, hne, hdust, hge, hadj, hv',
      show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]
  -- positive cash: the shares price between one unit at the scale of the cash and the cash
  obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hz.cashExact
  have hE := Vault.cash_exponent_of_exact hz.cashExact hmax hApos cash hcash
  obtain ⟨p, hpr, hplo, hphi⟩ := Vault.Settled.price_part v hz hmax shares waive hc hs1 hlt.le hApos cash hcash
    (hworth hApos _ hE)
  obtain ⟨r, hrun, hrs, hcl, hadj⟩ := Vault.withdraw_part_ok_of_price v t hmax hz.assetsDeployed hz.lossUnrealized
    hz.cashExact waive hopen hfee shares hc hty hpos hlt hApos cash hcash p hpr hplo hphi
  refine ⟨r, hrun, hrs, ?_⟩
  -- the cash does not grow: the payout is a nonnegative amount at most the price
  have hp0 : 0 ≤ p.toRat := le_trans (zpow_pos (by norm_num) _).le hplo
  have hpn := STAmount.CanonicalOrZero.operator_neg (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).1
  have hbr := v.baseExponent_range
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hpn hbr.1 hbr.2 hcl
  have hle := clampToSumExponent_le_abs _ _ _ _ hpn hbr.1 hbr.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hp0] at hle
  exact Vault.debit_le_of_exact v hz.cashExact hmax _ _ _ hcc hc0 (by linarith) hadj

end XRPL.Model.SingleAssetVault
