import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional

/-! # Emptying a reachable vault

On a reachable vault all the shares together are worth exactly the cash, so one withdrawal of every
share pays out all of it and leaves the vault empty. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A positive normalized `Number` of at least `10^19` units at a scale has its exponent above it. -/
lemma exponent_gt_of_le (n : Number) (s : ℤ) (hn : n.isNormalized) (hpos : 0 < n.toRat)
    (hge : (10 : ℚ) ^ (19 : ℕ) * 10 ^ s ≤ n.toRat) : s < n.exponent_ := by
  have hm0 : n.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat hm0
  have hval := Number.toRat_of_nonneg n (Number.negative_false_of_pos n hpos)
  have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have hpe : (0 : ℚ) < 10 ^ n.exponent_ := zpow_pos (by norm_num) _
  by_contra hc
  push Not at hc
  have h1 : (10 : ℚ) ^ n.exponent_ ≤ 10 ^ s := zpow_le_zpow_right₀ (by norm_num) hc
  have h2 : n.toRat < (10 : ℚ) ^ (19 : ℕ) * 10 ^ s := by
    rw [hval]
    calc (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ < 10 ^ (19 : ℕ) * 10 ^ n.exponent_ :=
          mul_lt_mul_of_pos_right hm hpe
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- On a reachable vault the whole share total prices without throwing. -/
lemma Vault.Reachable.sharesToAssetsWithdraw_all_ok (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hall : shares.toRat = v.toExact.sharesTotal) :
    ∃ assets, v.sharesToAssetsWithdraw shares waive = .ok assets := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hnav := hz.assetsTotalForWithdrawal_eq waive
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  by_cases hAm : v.assetsAvailable.mantissa_ = 0
  · exact ⟨_, Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ hnav hAm⟩
  have hAApos : 0 < v.assetsAvailable.toRat :=
    lt_of_le_of_ne hAA0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm))
  obtain ⟨-, hAA10⟩ := hz.cash_ge hAApos
  have hAAn := v.wf.assetsAvailable_norm
  have hAA9 := hz.cash_le
  have hAAlt : v.assetsAvailable.toRat < 10 ^ 16 := by linarith
  -- the shares, as a `Number`, are the share total
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hsnST : sn.toRat = v.sharesTotal.toRat := by rw [hsnv, hall, hcast]
  obtain ⟨hSTpos, hST1, hSTle⟩ := Vault.sharesTotal_bounds_of_cash v hAApos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hSTpos.ne'
  have hsnm : sn.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnST]; exact hSTpos.ne')
  -- exponents: the cash sits in `[-28, -3]`, the shares in `[-18, 0]`
  have hAAe_lo : (-29 : ℤ) < v.assetsAvailable.exponent_ := exponent_gt_of_le _ _ hAAn hAApos (by
    calc (10 : ℚ) ^ (19 : ℕ) * 10 ^ (-29 : ℤ) = 10 ^ (-10 : ℤ) := by norm_num
      _ ≤ _ := hAA10)
  have hAAe_hi : v.assetsAvailable.exponent_ ≤ -3 :=
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
  obtain ⟨w35, hw35n, hw35v⟩ := Exact.exists_normalized_grid 1 35 le_rfl (by norm_num)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hNSle : NS.toRat ≤ 10 ^ 35 := by
    have h := Number.RoundsToRepresentable.le_of_le_normalized NS _ hNSr _ hw35n (by
      rw [hw35v, hsnST]
      have h63 : v.sharesTotal.toRat ≤ 10 ^ 19 := by linarith
      calc v.assetsAvailable.toRat * v.sharesTotal.toRat ≤ 10 ^ 16 * 10 ^ 19 :=
            mul_le_mul hAAlt.le h63 (by linarith) (by norm_num)
        _ = ((1 : ℕ) : ℚ) * 10 ^ (35 : ℤ) := by norm_num)
    rw [hw35v] at h; norm_num at h; exact h
  have hNSe_hi : NS.exponent_ ≤ 17 :=
    Number.exponent_le_of_toRat_lt _ _ hNSn (Number.negative_false_of_pos _ hNSpos)
      (by unfold minExponent; norm_num) (by norm_num; linarith)
  -- the quotient by the share total, within `sharesε` of the cash
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
  have hane : an.exponent_ ≤ -3 :=
    Number.exponent_le_of_toRat_lt _ _ hann hanneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  obtain ⟨a, hof⟩ : ∃ a, STAmount.ofNumber v.numericType an .to_nearest = .ok a := by
    by_cases hint : v.numericType.isIntegral = true
    · -- a whole-number asset: the quotient rounds to the same whole cash as the cash itself
      obtain ⟨k, -, hkv⟩ := hz.cash
      rw [(Vault.baseExponent_bounds v).2.2 hint, zpow_zero, mul_one] at hkv
      obtain ⟨cash, hcash⟩ := STAmount.ofNumber_ok_of_isRounded_false _ _ hz.cashExact
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
        have : |an.toRat - v.assetsAvailable.toRat| ≤ 2 / 100 := by
          rw [abs_le]; constructor <;> nlinarith
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
    · -- a fractional asset: the quotient sits well inside the IOU range
      rw [NumericType.eq_fractional_of_not_integral (nt := v.numericType) (by simpa using hint)]
      obtain ⟨hlo, hhi⟩ := hann.mantissaBounds_nat hanm
      exact STAmount.ofNumber_fractional_ok an .to_nearest hlo hhi (Number.exponent_ge_min an hann hanm)
        (by unfold cMaxOffset; omega)
  refine ⟨a, ?_⟩
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure, hnav, hsn, hmul, hdiv, hof]
  simp [hAm]

/-- A normalized `Number` of magnitude at most `2^63 - 1` leaves `operator_add` its headroom. -/
private lemma exponent_headroom_of_abs (n : Number) (hn : n.isNormalized) (h : |n.toRat| ≤ 2 ^ 63 - 1) :
    n.exponent_ + 22 ≤ maxExponent := by
  by_cases hm : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm]
    show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  · obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat hm
    have hmge : (10 : ℚ) ^ (18 : ℕ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
    rw [abs_toRat_eq] at h
    by_contra hc
    push Not at hc
    have h1 : (10 : ℚ) ^ (1 : ℤ) ≤ 10 ^ n.exponent_ :=
      zpow_le_zpow_right₀ (by norm_num) (by unfold maxExponent at hc; omega)
    have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (1 : ℤ) ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ :=
      mul_le_mul hmge h1 (by norm_num) (by positivity)
    norm_num at h2
    linarith

/-- Burning every share for all the cash never throws in the cash update. -/
lemma Vault.adjustAssetsAndShares_burn_all_ok (v : Vault) (assets shares : STAmount)
    (hc : assets.CanonicalOrZero) (hpay : assets.toRat = v.assetsAvailable.toRat)
    (hcap : v.assetsAvailable.toRat ≤ 2 ^ 63 - 1)
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
  -- the share total less every share, and the cash less all of it
  obtain ⟨st', hst⟩ := Number.operator_add_ok_of_exp v.sharesTotal sn .to_nearest v.wf.sharesTotal_norm hsnn
    (exponent_headroom_of_abs _ v.wf.sharesTotal_norm (by rw [abs_of_nonneg hSTnn]; exact hSTle))
    (exponent_headroom_of_abs _ hsnn (by rw [hsnv, abs_neg, hall, hcast, abs_of_nonneg hSTnn]; exact hSTle))
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_exp v.assetsAvailable an .to_nearest hAAn hann
    (exponent_headroom_of_abs _ hAAn (by rw [abs_of_nonneg hAA0]; exact hcap))
    (exponent_headroom_of_abs _ hann (by rw [hanv, abs_neg, hpay, abs_of_nonneg hAA0]; exact hcap))
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

/-- On a reachable vault one withdrawal of every share succeeds at a time withdrawals are open. It
pays out all the cash and leaves no cash and no shares. -/
lemma Vault.withdraw_all_proof (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero := by
  -- the vault has shares, so its asset fits
  have hmax := Vault.Reachable.maxValue_fits v t0 hr (by rw [← hall]; exact hpos)
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  -- the share total as an amount, which the shares equal: the withdrawal is final
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hfinal : shares.operator_eq S = true := (Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS).mpr hall
  -- all the shares together price at the cash
  obtain ⟨a, hpr⟩ := Vault.Reachable.sharesToAssetsWithdraw_all_ok v t0 hr hmax shares waive hc hall
  have hav := Vault.Reachable.sharesToAssetsWithdraw_all v t0 hr hmax shares a waive hc hall hpr
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
  -- nothing is deployed and nothing is lost
  have hAD : v.assetsDeployed.operator_ne Number.zero = false := by rw [hz.assetsDeployed]; decide
  have hLU : v.lossUnrealized.operator_ne Number.zero = false := by rw [hz.lossUnrealized]; decide
  -- the cash, stored exactly, is paid out
  obtain ⟨cash, hcash⟩ := STAmount.ofNumber_ok_of_isRounded_false _ _ hz.cashExact
  have hcashv := Vault.final_payout_exact v cash hz.cashExact hmax hcash
  have hcashc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
  have hcap : v.assetsAvailable.toRat ≤ 2 ^ 63 - 1 := le_trans hz.cash_le (by norm_num)
  obtain ⟨raw, hadj⟩ := Vault.adjustAssetsAndShares_burn_all_ok v cash shares hcashc hcashv hcap hsic hty hall
  have hzero : v.assetsAvailable.toRat + cash.operator_neg.toRat = 0 := by
    rw [STAmount.operator_neg_toRat, hcashv]; ring
  obtain ⟨k, hk⟩ := v.exact.assetsAvailable_onGrid
  have hlaw := Vault.withdraw_update_lawful v cash shares raw hmax ⟨k, by rw [hcashv]; exact hk⟩ hcashc
    (le_of_eq hzero.symm) hsic hty hspos.le
    hall.le (fun _ => ⟨hzero, hz.assetsDeployed⟩) hadj
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  -- the withdrawal runs every check and records the update
  have hrun : (v.withdraw (.vaultShares shares) waive t hpos).run =
      .ok (.ok { vault' := v', assets := cash, shares := shares }) := by
    simp only [ExceptT.run] at hcomp hadj
    simp only [Vault.withdraw]
    unfold_ter
    simp [hopen, hcomp, hS, hfinal, hAD, haN, hge, hLU, hcash, hadj, hv']
  obtain ⟨hp, h1, h2⟩ := Vault.withdraw_final_proof v (.vaultShares shares) waive t t0 hpos hr hc hty hmax _ hrun hall
  exact ⟨_, hrun, hp, h1, h2⟩

/-- The first time at or after `t` outside the investment phase: the redemption date of a closed-ended
vault still investing, or `t` itself. -/
def Vault.redemptionOpenAt (v : Vault) (t : UInt32) : UInt32 :=
  match v.schedule with
  | some s => if t < s.redemptionDate then s.redemptionDate else t
  | none => t

lemma Vault.le_redemptionOpenAt (v : Vault) (t : UInt32) : t ≤ v.redemptionOpenAt t := by
  unfold Vault.redemptionOpenAt
  split
  · split_ifs with h
    · exact UInt32.le_of_lt h
    · exact UInt32.le_refl t
  · exact UInt32.le_refl t

/-- No vault is investing at `redemptionOpenAt`: a closed-ended vault has reached its redemption date,
which comes after its subscription date. -/
lemma Vault.phase_redemptionOpenAt (v : Vault) (t : UInt32) : v.phase (v.redemptionOpenAt t) ≠ .investment := by
  unfold Vault.phase Vault.redemptionOpenAt
  cases hs : v.schedule with
  | none => simp
  | some s =>
    simp only []
    have hgap := v.valid.schedule_gap s (by rw [hs]; rfl)
    unfold VaultSchedule.hasValidGap minInvestmentPeriod at hgap
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hgap
    have hsub : s.subscriptionDate < s.redemptionDate := by
      rw [UInt32.lt_iff_toNat_lt]; omega
    have hred : s.redemptionDate ≤ (if t < s.redemptionDate then s.redemptionDate else t) := by
      split_ifs with h
      · exact UInt32.le_refl _
      · exact UInt32.not_lt.mp h
    have hsub' : (if t < s.redemptionDate then s.redemptionDate else t) > s.subscriptionDate :=
      UInt32.lt_of_lt_of_le hsub hred
    simp [hsub', hred]

/-- Proof of `Vault.Reachable.canEmpty`. -/
lemma Vault.Reachable.canEmpty_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) : CanEmpty v t := by
  by_cases h0 : v.toExact.sharesTotal = 0
  · exact CanEmpty.done v t h0
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  obtain ⟨hsic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) hS
  have hSv : S.toRat = v.sharesTotal.toRat :=
    STAmount.ofNumber_integral_exact .int64 _ _ _ (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hS
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hall : S.toRat = v.toExact.sharesTotal := by rw [hSv, hcast]
  have hpos : 0 < (WithdrawAmount.vaultShares S).amount.toRat := by
    show 0 < S.toRat
    rw [hall]; exact_mod_cast Nat.pos_of_ne_zero h0
  -- redeem every share once withdrawals are open
  have hopen : (v.earlyExitFeeRate.isNone && v.phase (v.redemptionOpenAt t) == .investment) = false := by
    simp [Vault.phase_redemptionOpenAt v t]
  obtain ⟨r, hrun, -, -, hST⟩ := Vault.withdraw_all_proof v t (v.redemptionOpenAt t) hr false hopen S
    (hsic.canonical (by rw [hty]; decide)) hty hall hpos
  refine CanEmpty.step v t _ _ r (Vault.le_redemptionOpenAt v t) hpos hrun (CanEmpty.done _ _ ?_)
  show r.vault'.sharesTotal.toRat.num.toNat = 0
  rw [hST, Number.toRat_zero]
  rfl

end XRPL.Model.SingleAssetVault
