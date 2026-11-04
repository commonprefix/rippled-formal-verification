import XRPL.Properties.Vault.Proofs.CanEmpty
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeBound

/-! # Paying out a settled vault

A vault with nothing lent and nothing lost, whose cash is a whole number of base units stored exactly, pays out all
its cash to one withdrawal of every share. An XRP or MPT cash must stay below `2.5·10^17` units, where the
19-digit price of all the shares together is less than half a unit from the cash. -/

namespace XRPL.Model.Protocol

/-- A to-nearest IOU `ofNumber` of a positive value below `(10^16 - 1/2)·10^80` never throws. The rounding
moves the value by at most half a unit of its 16th digit, so it never carries past the IOU ceiling. -/
lemma STAmount.ofNumber_fractional_ok_below (r : Number) (hn : r.isNormalized) (hpos : 0 < r.toRat)
    (hlt : r.toRat < (10 ^ 16 - 1 / 2) * 10 ^ 80) :
    ∃ result, STAmount.ofNumber .fractional r .to_nearest = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hr_ne
  have hneg := Number.negative_false_of_pos r hpos
  have hre_lo := Number.exponent_ge_min r hn hr_ne
  have hre_hi : r.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt r 77 hn hneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  by_cases h4 : r.exponent_ + 4 ≤ cMaxOffset
  · exact STAmount.ofNumber_fractional_ok r .to_nearest hr_lo hr_hi hre_lo h4
  have hco : cMaxOffset = 80 := rfl
  have hme : maxExponent = 32768 := rfl
  have he77 : r.exponent_ = 77 := by omega
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok r .to_nearest hr_lo hr_hi (by omega) (by omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts r .to_nearest mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hhalf := normalizeToRange_16_within_half_ulp r mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hrange := normalizeToRange_16_exp_range r .to_nearest mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  -- a carry would need a value of at least `10^96`, half a unit above the bound
  have hexp_hi : exp ≤ cMaxOffset := by
    by_contra hc
    have hexp : exp = 81 := by omega
    have hm15 : (10 : ℚ) ^ 15 ≤ (mant.toInt : ℚ) := by
      have h' : ((10 ^ 15 : ℕ) : ℤ) ≤ mant.toInt := by omega
      exact_mod_cast h'
    rw [hexp, he77] at hhalf
    have h1 := (abs_le.mp hhalf).2
    norm_num at h1
    nlinarith
  have hs : decide (r.signum < 0) = false := by
    simpa using Number.signum_nonneg_of_negative_false r hneg
  have hnorm' : r.normalizeToRange kMinValue kMaxValue .to_nearest = .ok (mant, exp) := hnorm
  unfold STAmount.ofNumber
  rw [if_neg (by decide), hs]
  simp only [Bool.false_eq_true, if_false, hnorm']
  have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp false).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
  have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops.toInt64
      = if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant.toUInt64 exp false).mValue.toNat < 10 ^ 16 from hmtu_hi),
        signed_mantissa_toInt false mant.toUInt64 h_fit]
    show (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    simp
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp false).iou .to_nearest
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp false .to_nearest hmtu_lo hmtu_hi
      (by omega) (by omega)
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by omega)]
  split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A vault with nothing lent and nothing lost, whose cash is a whole number of base units, stored exactly. An
XRP or MPT cash is below `2.5·10^17` units. -/
structure Vault.Settled (v : Vault) : Prop where
  assetsDeployed : v.assetsDeployed = Number.zero
  lossUnrealized : v.lossUnrealized = Number.zero
  cash : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent
  cashExact : STAmount.isRounded v.numericType v.assetsAvailable = false
  cashFit : v.numericType.isIntegral = true → v.assetsAvailable.toRat < 25 * 10 ^ 16

/-- A settled vault prices a withdrawal at its cash. -/
lemma Vault.Settled.assetsTotalForWithdrawal_eq {v : Vault} (hz : v.Settled) (waive : Bool) :
    v.assetsTotalForWithdrawal waive = .ok v.assetsAvailable := by
  have hsub : v.assetsAvailable.operator_sub Number.zero .to_nearest = .ok v.assetsAvailable :=
    Number.operator_sub_zero _ _
  have htot : v.assetsTotal = .ok v.assetsAvailable := by
    unfold RawVault.assetsTotal
    rw [hz.assetsDeployed]
    exact Number.operator_add_zero_right _ _
  cases waive
  · simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, htot, hz.lossUnrealized]
    exact hsub
  · simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, htot]
    exact hsub

/-- A settled vault's withdrawal price is its cash. -/
lemma Vault.Settled.nav_eq_cash {v : Vault} (hz : v.Settled) (waive : Bool) (nav : Number)
    (hsub : v.assetsTotalForWithdrawal waive = .ok nav) : nav.toRat = v.assetsAvailable.toRat := by
  rw [hz.assetsTotalForWithdrawal_eq waive, Except.ok.injEq] at hsub
  rw [hsub]

/-- A settled vault's cash is at most the largest IOU amount, `(10^16 - 1)·10^80`. -/
lemma Vault.Settled.cash_top {v : Vault} (hz : v.Settled) :
    v.assetsAvailable.toRat ≤ (10 ^ 16 - 1) * 10 ^ 80 := by
  have hrep := (STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg).mp
    hz.cashExact
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

/-- A settled vault's cash is below `10^96`. -/
lemma Vault.Settled.cash_lt {v : Vault} (hz : v.Settled) : v.assetsAvailable.toRat < 10 ^ 96 := by
  linarith [hz.cash_top]

/-- A settled vault with cash holds at least one step of its base grid, at least `10⁻¹⁰`. -/
lemma Vault.Settled.cash_ge {v : Vault} (hz : v.Settled) (hA : 0 < v.assetsAvailable.toRat) :
    (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat ∧ (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat := by
  obtain ⟨k, hkv⟩ := hz.cash
  have hk1 : (1 : ℚ) ≤ k := by
    have : k ≠ 0 := fun h => by rw [hkv, h] at hA; simp at hA
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hbk : (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat := by rw [hkv]; nlinarith
  exact ⟨hbk, le_trans (zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).1) hbk⟩

/-- On a settled vault the price of all the shares together computes without an error. -/
lemma Vault.Settled.sharesToAssetsWithdraw_all_ok (v : Vault) (hz : v.Settled)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hall : shares.toRat = v.toExact.sharesTotal) :
    ∃ assets, v.sharesToAssetsWithdraw shares waive = .ok assets := by
  have hnav := hz.assetsTotalForWithdrawal_eq waive
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  by_cases hAm : v.assetsAvailable.mantissa_ = 0
  · exact ⟨_, Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ hnav hAm⟩
  have hAApos : 0 < v.assetsAvailable.toRat :=
    lt_of_le_of_ne hAA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))
  obtain ⟨-, hAA10⟩ := hz.cash_ge hAApos
  have hAAn := v.wf.assetsAvailable_norm
  have hAAtop := hz.cash_top
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hsnST : sn.toRat = v.sharesTotal.toRat := by rw [hsnv, hall, hcast]
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
    intro h0
    have hST0 : v.sharesTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ h0
    obtain ⟨hAA, -⟩ := v.valid.empty_shares (Number.eq_zero_of_mantissa_zero _ v.wf.sharesTotal_norm h0)
    rw [hAA] at hAm
    exact hAm rfl
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := rat_one_le_of_den_one_pos _ v.wf.sharesTotal_int hSTpos
  have hSTle := Vault.sharesTotal_le_maxRep v
  have hsnm : sn.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnST]; exact hSTpos.ne')
  -- exponents: the cash sits in `[-28, 77]`, the shares in `[-18, 0]`
  have hAAe_lo : (-29 : ℤ) < v.assetsAvailable.exponent_ := exponent_gt_of_le _ _ hAAn hAApos (by
    calc (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-29 : ℤ) = 10 ^ (-10 : ℤ) := by norm_num
      _ ≤ _ := hAA10)
  have hAAe_hi : v.assetsAvailable.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt _ _ hAAn (Number.negative_false_of_pos _ hAApos)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  have hsne_lo : (-19 : ℤ) < sn.exponent_ := exponent_gt_of_le _ _ hsnn (by rw [hsnST]; exact hSTpos) (by
    rw [hsnST]; norm_num; linarith)
  have hsne_hi : sn.exponent_ ≤ 0 :=
    Number.exponent_le_of_toRat_lt _ _ hsnn (Number.negative_false_of_pos _ (by rw [hsnST]; exact hSTpos))
      (by unfold minExponent; norm_num) (by rw [hsnST]; norm_num; linarith)
  have hSTe_lo : (-19 : ℤ) < v.sharesTotal.exponent_ :=
    exponent_gt_of_le _ _ v.wf.sharesTotal_norm hSTpos (by norm_num; linarith)
  obtain ⟨NS, hmul⟩ := Number.operator_mul_ok_of_normalized v.assetsAvailable sn .to_nearest hAAn hsnn hAm hsnm
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hNSr := operator_mul_rounded_to_nearest _ _ _ hAAn hsnn hmul
  have hNSge : v.assetsAvailable.toRat ≤ NS.toRat :=
    Number.RoundsToRepresentable.ge_of_ge_normalized NS _ hNSr _ hAAn (by
      rw [hsnST]; nlinarith)
  have hNSpos : 0 < NS.toRat := lt_of_lt_of_le hAApos hNSge
  have hNSm : NS.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hNSpos.ne'
  have hNSn : NS.isNormalized := operator_mul_result_isNormalized _ _ _ _ hAAn hsnn hAm hsnm hmul hNSm
  obtain ⟨w, hwn, hwv⟩ := Exact.exists_normalized_grid 1 115 le_rfl (by norm_num)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hNSle : NS.toRat ≤ 10 ^ 115 := by
    have h := Number.RoundsToRepresentable.le_of_le_normalized NS _ hNSr _ hwn (by
      rw [hwv, hsnST]
      have h63 : v.sharesTotal.toRat ≤ 10 ^ 19 := by linarith
      have h96 : v.assetsAvailable.toRat ≤ 10 ^ 96 := by linarith
      calc v.assetsAvailable.toRat * v.sharesTotal.toRat ≤ 10 ^ 96 * 10 ^ 19 :=
            mul_le_mul h96 h63 (by linarith) (by norm_num)
        _ = ((1 : ℕ) : ℚ) * 10 ^ (115 : ℤ) := by norm_num)
    rw [hwv] at h; norm_num at h; exact h
  have hNSe_hi : NS.exponent_ ≤ 97 :=
    Number.exponent_le_of_toRat_lt _ _ hNSn (Number.negative_false_of_pos _ hNSpos)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  obtain ⟨an, hdiv⟩ := Number.operator_div_ok_of_normalized NS v.sharesTotal .to_nearest hNSn
    v.wf.sharesTotal_norm hNSm hSTm (by unfold maxExponent; omega)
  have hT : v.assetsAvailable.toRat * sn.toRat / v.sharesTotal.toRat = v.assetsAvailable.toRat := by
    rw [hsnST]; field_simp
  obtain ⟨hann, hanpos, hb⟩ := pipe_large v.assetsAvailable sn NS an v.sharesTotal hAAn hsnn
    v.wf.sharesTotal_norm hAA0 (by rw [hsnST]; exact hSTpos.le) hSTpos hST1
    (by rw [hT]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hAA10) hmul hdiv
  rw [hT] at hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hb2 : |an.toRat - v.assetsAvailable.toRat| ≤ v.assetsAvailable.toRat * (2 / 10 ^ 18) :=
    le_trans hb (mul_le_mul_of_nonneg_left hδ hAA0)
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb2
  have hanneg := Number.negative_false_of_pos an hanpos
  have hanm : an.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hanpos.ne'
  obtain ⟨a, hof⟩ : ∃ a, STAmount.ofNumber v.numericType an .to_nearest = .ok a := by
    by_cases hint : v.numericType.isIntegral = true
    · -- a whole-number asset: the quotient rounds to the same whole cash as the cash itself
      obtain ⟨k, hkv⟩ := hz.cash
      rw [(Vault.baseExponent_bounds v).2.2 hint, zpow_zero, mul_one] at hkv
      have hfit := hz.cashFit hint
      have hane : an.exponent_ ≤ -1 :=
        Number.exponent_le_of_toRat_lt _ _ hann hanneg (by unfold minExponent; norm_num) (by norm_num; nlinarith)
      have hAAe0 : v.assetsAvailable.exponent_ ≤ -1 :=
        Number.exponent_le_of_toRat_lt _ _ hAAn (Number.negative_false_of_pos _ hAApos)
          (by unfold minExponent; norm_num) (by norm_num; linarith)
      obtain ⟨cash, hcash⟩ : ∃ cash, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash := by
        have hrd := hz.cashExact
        unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hrd
        cases h : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
        | error e => rw [h] at hrd; simp [bind, Except.bind] at hrd
        | ok c => exact ⟨c, rfl⟩
      have hAAneg := Number.negative_false_of_pos _ hAApos
      obtain ⟨i, hi⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos an .to_nearest hanneg
        (by unfold Number.exponent; split_ifs <;> omega)
      obtain ⟨i', hi'⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos v.assetsAvailable .to_nearest hAAneg
        (by unfold Number.exponent; split_ifs <;> omega)
      have h1 := Number.to_rep_to_nearest_within_half an i hann hanneg hi
      have h2 := Number.to_rep_to_nearest_within_half _ i' hAAn hAAneg hi'
      have hround : ∀ j : Int64, |(j.toInt : ℚ) - v.assetsAvailable.toRat| < 1 → j.toInt = k := by
        intro j hj
        rw [hkv] at hj
        have hj' : |((j.toInt - (k : ℤ) : ℤ) : ℚ)| < 1 := by push_cast; exact hj
        have hj'' : |j.toInt - (k : ℤ)| < 1 := by exact_mod_cast hj'
        have := abs_lt.mp hj''
        omega
      have hik := hround i (by
        have : |an.toRat - v.assetsAvailable.toRat| < 1 / 2 := by
          rw [abs_lt]; constructor <;> nlinarith
        calc |(i.toInt : ℚ) - v.assetsAvailable.toRat|
            ≤ |(i.toInt : ℚ) - an.toRat| + |an.toRat - v.assetsAvailable.toRat| := abs_sub_le _ _ _
          _ < 1 := by linarith)
      have hi'k := hround i' (by linarith)
      have hii : i = i' := Int64.toInt_inj.mp (hik.trans hi'k.symm)
      have hs1 : decide (an.signum < 0) = false := by
        simpa using Number.signum_nonneg_of_negative_false an hanneg
      have hs2 : decide (v.assetsAvailable.signum < 0) = false := by
        simpa using Number.signum_nonneg_of_negative_false _ hAAneg
      refine ⟨cash, ?_⟩
      rw [← hcash]
      unfold STAmount.ofNumber
      simp only [hs1, hs2, Bool.false_eq_true, if_false, hint, if_true, hi, hi', hii]
    · -- an IOU asset: the quotient stays half a unit below the IOU ceiling
      rw [NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)]
      exact STAmount.ofNumber_fractional_ok_below an hann hanpos (by nlinarith)
  refine ⟨a, ?_⟩
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure, hnav, hsn, hmul, hdiv, hof]
  simp [hAm]

/-- On a settled vault all the shares together are worth exactly the cash. The vault prices at its cash, and
the 19-digit price of all the shares sits so close to it that the conversion rounds back to it. -/
lemma Vault.Settled.sharesToAssetsWithdraw_all (v : Vault) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares assets : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hall : shares.toRat = v.toExact.sharesTotal)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    assets.toRat = v.assetsAvailable.toRat := by
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hs0 : 0 ≤ shares.toRat := by rw [hall]; exact Nat.cast_nonneg _
  have hp0 := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive (Or.inl hc) hs0 hok
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  rcases eq_or_lt_of_le hAA0 with hAAz | hAApos
  · -- no cash prices every share at zero
    have hAm : v.assetsAvailable.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp hAAz.symm
    rw [Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ (hz.assetsTotalForWithdrawal_eq waive) hAm,
      Except.ok.injEq] at hok
    rw [← hok, ← hAAz, (STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]
  -- the cash is a positive whole number of base steps, at least `10⁻¹⁰`
  obtain ⟨k, hkv⟩ := hz.cash
  have hk1 : (1 : ℚ) ≤ k := by
    have : k ≠ 0 := fun h => by rw [hkv, h] at hAApos; simp at hAApos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hbk : (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat := by rw [hkv]; nlinarith
  have hAA10 : (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat :=
    le_trans (zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).1) hbk
  obtain ⟨nav, hsub, hnavn, hcase⟩ := WdPrice.price_cases v _ _ waive hok
  have hnavv := hz.nav_eq_cash waive nav hsub
  rcases hcase with ⟨h0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav h0] at hnavv
    linarith
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hSTm := operator_div_divisor_ne_zero _ _ _ _ v.wf.sharesTotal_norm hdiv
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := rat_one_le_of_den_one_pos _ v.wf.sharesTotal_int hSTpos
  have hT : nav.toRat * sn0.toRat / v.sharesTotal.toRat = v.assetsAvailable.toRat := by
    rw [hnavv, hsnv, hall, hcast]
    field_simp
  obtain ⟨hann, hanpos, hb⟩ := pipe_large nav sn0 NS an v.sharesTotal hnavn hsnn v.wf.sharesTotal_norm
    (by rw [hnavv]; exact hAA0) (by rw [hsnv]; exact hs0) hSTpos hST1
    (by rw [hT]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hAA10) hmul hdiv
  rw [hT] at hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hb2 : |an.toRat - v.assetsAvailable.toRat| ≤ v.assetsAvailable.toRat * (2 / 10 ^ 18) :=
    le_trans hb (mul_le_mul_of_nonneg_left hδ hAA0)
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb2
  -- a whole-number asset: the price rounds to the whole cash, less than half a unit away
  by_cases hint : v.numericType.isIntegral = true
  · have hanneg := Number.negative_false_of_pos an hanpos
    obtain ⟨iv, -, hiv⟩ := STAmount.ofNumber_integral_toRat _ an .to_nearest assets hint hanneg hof
    have hhalf := STAmount.ofNumber_integral_within_half _ an assets hint hann hanneg hof
    rw [(Vault.baseExponent_bounds v).2.2 hint, zpow_zero, mul_one] at hkv
    have hfit := hz.cashFit hint
    have hnear : |an.toRat - v.assetsAvailable.toRat| < 1 / 2 := by
      rw [abs_lt]; constructor <;> nlinarith
    have hj : |((iv.toInt - (k : ℤ) : ℤ) : ℚ)| < 1 := by
      push_cast
      rw [← hiv, ← hkv]
      calc |assets.toRat - v.assetsAvailable.toRat|
          ≤ |assets.toRat - an.toRat| + |an.toRat - v.assetsAvailable.toRat| := abs_sub_le _ _ _
        _ < 1 := by linarith
    have hj' : |iv.toInt - (k : ℤ)| < 1 := by exact_mod_cast hj
    have hik : iv.toInt = k := by have := abs_lt.mp hj'; omega
    rw [hiv, hkv, hik]
    push_cast
    rfl
  have hrd := hz.cashExact
  obtain ⟨cash, hcash⟩ : ∃ cash, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash := by
    unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hrd
    cases h : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
    | error e => rw [h] at hrd; simp [bind, Except.bind] at hrd
    | ok c => exact ⟨c, rfl⟩
  have hcv := Vault.final_payout_exact v cash hrd hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ v.wf.assetsAvailable_norm hAA0 hcash hcm
  have hct : cash.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  have hnear : |an.toRat - cash.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) := by
    rw [hcv]
    refine lt_of_le_of_lt hb2 ?_
    have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) = (10 : ℚ) ^ cash.exponent / 20 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
    rw [hu]
    rcases hcE with hiou | ⟨hic, -⟩
    · -- an IOU cash is below `10 ^ (exponent + 16)`
      obtain ⟨-, hhi⟩ := STAmount.IOUCanonical.toRat_bounds cash hiou (by rw [hcv]; exact hAApos)
      rw [hcv] at hhi
      have h16 : (10 : ℚ) ^ (cash.exponent + 16) = 10 ^ cash.exponent * 10 ^ 16 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      have hp : (0 : ℚ) < 10 ^ cash.exponent := zpow_pos (by norm_num) _
      nlinarith
    · exact absurd (hct ▸ hic.is_integral) hint
  have hpz : assets.mValue ≠ 0 := by
    intro h0
    by_cases hint : v.numericType.isIntegral = true
    · have hhalf := STAmount.ofNumber_integral_within_half _ an assets hint hann
        (Number.negative_false_of_pos an hanpos) hof
      rw [(STAmount.toRat_eq_zero_iff _).mpr h0, zero_sub, abs_neg, abs_of_pos hanpos] at hhalf
      have hb0 := v.baseExponent_bounds.2.2 hint
      rw [hb0, zpow_zero] at hbk
      linarith
    · have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
      have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ an.toRat := by
        have h1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2 := by norm_num
        calc (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2 := h1
          _ ≤ v.assetsAvailable.toRat / 2 := div_le_div_of_nonneg_right hAA10 (by norm_num)
          _ ≤ an.toRat := by linarith
      exact STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest assets hann hge (hvfr ▸ hof) h0
  have heq := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an assets cash hann hanpos.le hcE hct
    (by rw [hcv]; exact hAApos) hnear hof hpz
  rw [heq, hcv]

/-- A normalized value above `-10^96` and at most zero leaves the headroom `operator_add` needs. -/
private lemma exponent_headroom_of_neg (n : Number) (hn : n.isNormalized) (hlo : -10 ^ 96 < n.toRat)
    (hhi : n.toRat ≤ 0) : n.exponent_ + 22 ≤ maxExponent := by
  by_cases hm : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm]
    show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  have hneg := Number.exponent_headroom_of_lt n.operator_neg (Number.operator_neg_isNormalized n hn)
    (by rw [Number.toRat_neg]; linarith) (by rw [Number.toRat_neg]; linarith)
  have he : n.operator_neg.exponent_ = n.exponent_ := by
    unfold Number.operator_neg; rw [if_neg (by simpa using hm)]
  rwa [he] at hneg

/-- Burning every share and paying out all the cash updates the vault, for any cash below `10^96`. -/
lemma Vault.adjustAssetsAndShares_burn_all_ok' (v : Vault) (assets shares : STAmount)
    (hc : assets.CanonicalOrZero) (hpay : assets.toRat = v.assetsAvailable.toRat)
    (hcap : v.assetsAvailable.toRat < 10 ^ 96)
    (hsh : shares.IntegralCanonical) (hsh64 : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal) :
    ∃ raw, (v.adjustAssetsAndShares assets.operator_neg shares.operator_neg).run = .ok (.ok raw) := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSTle := Vault.sharesTotal_le_maxRep v
  have hSTnn := v.wf.sharesTotal_nonneg
  have hcn : assets.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg hc
  obtain ⟨an, han⟩ := STAmount.CanonicalOrZero.toNumber_ok hcn
  obtain ⟨hanv, hann⟩ := STAmount.CanonicalOrZero.toNumber_exact hcn an han
  have hshc : shares.Canonical := hsh.canonical (by rw [hsh64]; decide)
  have hshn : shares.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg (Or.inl hshc)
  obtain ⟨sn, hsn⟩ := STAmount.CanonicalOrZero.toNumber_ok hshn
  obtain ⟨hsnv, hsnn⟩ := STAmount.CanonicalOrZero.toNumber_exact hshn sn hsn
  rw [STAmount.operator_neg_toRat] at hanv hsnv
  obtain ⟨st', hst⟩ := Number.operator_add_ok_of_exp v.sharesTotal sn .to_nearest v.wf.sharesTotal_norm hsnn
    (Number.exponent_headroom_of_lt _ v.wf.sharesTotal_norm hSTnn (by linarith))
    (exponent_headroom_of_neg _ hsnn (by rw [hsnv, hall, hcast]; linarith) (by rw [hsnv, hall, hcast]; linarith))
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_exp v.assetsAvailable an .to_nearest hAAn hann
    (Number.exponent_headroom_of_lt _ hAAn hAA0 hcap)
    (exponent_headroom_of_neg _ hann (by rw [hanv, hpay]; linarith) (by rw [hanv, hpay]; linarith))
  have hsum : v.assetsAvailable.toRat + an.toRat = 0 := by rw [hanv, hpay]; ring
  have hsr := operator_add_rounded_to_nearest _ _ _ hAAn hann hs
  rw [hsum] at hsr
  have hs0 : s.toRat = 0 :=
    Number.RoundsToRepresentable.eq_of_representable s 0 hsr Number.zero (Or.inl rfl) Number.toRat_zero
  have hsz : s = Number.zero := Number.eq_zero_of_mantissa_zero s
    (operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hann hs) (Number.toRat_eq_zero_iff.mp hs0)
  rw [hsz] at hs
  -- every other step is a check, so the update returns a record or a `TER`
  cases h : (v.adjustAssetsAndShares assets.operator_neg shares.operator_neg).run with
  | ok res =>
    cases res with
    | ok raw => exact ⟨raw, rfl⟩
    | error ter =>
      exfalso
      obtain rfl := Vault.adjustAssetsAndShares_rejected_bad_ledger v _ _ ter h
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hcn
        (by rw [STAmount.operator_neg_toRat, hpay]; simp) h
  | error e =>
    exfalso
    simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
    unfold_ter at h
    simp [han, hsn, hst, hs, STAmount.roundToNumericType_zero_to_nearest, Number.operator_add_zero_right] at h
    split_ifs at h

/-- On a settled vault one withdrawal of every share succeeds at a time withdrawals are open. It
burns the shares, pays out all the cash and leaves no cash and no shares. -/
lemma Vault.Settled.withdraw_all (v : Vault) (t : UInt32) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧ r.shares = shares ∧
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  -- the share total as an amount, which the shares equal: the withdrawal is final
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hfinal : shares.operator_eq S = true := (Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS).mpr hall
  obtain ⟨a, hpr⟩ := Vault.Settled.sharesToAssetsWithdraw_all_ok v hz shares waive hc hall
  have hav := Vault.Settled.sharesToAssetsWithdraw_all v hz hmax shares a waive hc hall hpr
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
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff _ _ hAAn haNn, haNv, hav]
    exact lt_irrefl _
  have hAD : v.assetsDeployed.operator_ne Number.zero = false := by rw [hz.assetsDeployed]; decide
  have hLU : v.lossUnrealized.operator_ne Number.zero = false := by rw [hz.lossUnrealized]; decide
  obtain ⟨cash, hcash⟩ : ∃ cash, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash := by
    have hrd := hz.cashExact
    unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hrd
    cases h : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
    | error e => rw [h] at hrd; simp [bind, Except.bind] at hrd
    | ok c => exact ⟨c, rfl⟩
  have hcashv := Vault.final_payout_exact v cash hz.cashExact hmax hcash
  have hcashc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
  obtain ⟨raw, hadj⟩ := Vault.adjustAssetsAndShares_burn_all_ok' v cash shares hcashc hcashv hz.cash_lt hsic hty hall
  have hzero : v.assetsAvailable.toRat + cash.operator_neg.toRat = 0 := by
    rw [STAmount.operator_neg_toRat, hcashv]; ring
  obtain ⟨k, hk⟩ := v.exact.assetsAvailable_onGrid
  have hlaw := Vault.withdraw_update_lawful v cash shares raw hmax ⟨k, by rw [hcashv]; exact hk⟩ hcashc
    (le_of_eq hzero.symm) hsic hty hspos.le hall.le (fun _ => ⟨hzero, hz.assetsDeployed⟩) hadj
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  have hrun : (v.withdraw (.vaultShares shares) waive t hpos).run =
      .ok (.ok { vault' := v', assets := cash, shares := shares }) := by
    simp only [ExceptT.run] at hcomp hadj
    simp only [Vault.withdraw]
    unfold_ter
    simp [hopen, hcomp, hS, hfinal, hAD, haN, hge, hLU, hcash, hadj, hv']
  obtain ⟨hp, h1, h2⟩ :=
    Vault.withdraw_final_empties v (.vaultShares shares) waive t hpos hc hty hmax hz.cashExact _ hrun hall
  exact ⟨_, hrun, rfl, hp, h1, h2⟩

end XRPL.Model.SingleAssetVault
