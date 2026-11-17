import XRPL.Properties.Protocol.Common.ErrorKinds
import XRPL.Properties.Vault.Proofs.WithdrawPricing
import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Vault.Proofs.Support.ExactCash
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Lending.Common.PoolBalances

/-! # Which errors the pricing of a withdrawal returns

The pricing of a withdrawal or a clawback runs inside a `try` that turns an overflow error into `tecPATH_DRY`. On an
IOU or MPT vault every error of the pricing is an overflow error or a wrap. On an XRP vault the price of the shares
is built as an XRP amount, which fails with `outOfRange` above `10^17` drops (FV_M2_25). -/

namespace XRPL.Model.SingleAssetVault.VaultWithdrawErrors

open XRPL.Model.Protocol XRPL.Model.Protocol.ErrorKinds

/-- The net asset value a withdrawal prices against fails to compute only with an overflow error. -/
lemma nav_error {v : Vault} {w : Bool} {e : Error} (h : v.assetsTotalForWithdrawal w = .error e) :
    isOverflow e = true ∨ e = .wrap := by
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind] at h
  cases hat : v.assetsTotal with
  | error e' =>
    rw [hat] at h
    cases h
    exact number_add_error v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hat
  | ok total =>
    rw [hat] at h
    dsimp only at h
    have htn := (Vault.assetsTotal_ge_deployed v total hat).1
    cases w
    · exact number_sub_error htn v.wf.lossUnrealized_norm h
    · exact number_sub_error htn Number.zero_isNormalized h

/-- The shares an asset amount is worth fail to compute only with an overflow error or a wrap. -/
lemma assetsToShares_error {v : Vault} {a : STAmount} {t w : Bool} {e : Error}
    (h : assetsToSharesWithdraw v a t w = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact nav_error ‹_›
    | exact toNumber_error ‹_›
    | exact number_mul_error ‹_›
    | exact number_div_error ‹_›
    | exact number_truncate_error ‹_›
    | exact ofNumber_int64_error ‹_›

/-- On an IOU or MPT vault the assets some shares are worth fail to compute only with an overflow error or a
wrap. -/
lemma sharesToAssets_error {v : Vault} {sh : STAmount} {w : Bool} {e : Error}
    (hnt : v.numericType = .fractional ∨ v.numericType = NumericType.int64)
    (h : v.sharesToAssetsWithdraw sh w = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact nav_error ‹_›
    | exact toNumber_error ‹_›
    | exact number_mul_error ‹_›
    | exact number_div_error ‹_›
    | exact ofNumber_error_of hnt ‹_›

/-- The price of some shares on an XRP vault converts into an XRP amount when the shares are worth at most `10^17`
drops at the computed net asset value, with a margin of `0.3` drops for the rounding of that value. -/
lemma native_price_ok (v : Vault) (sh : STAmount) (w : Bool) (hc : sh.Canonical) (hnn : 0 ≤ sh.toRat)
    (nav sn NS an : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav)
    (hb : nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat)
    (hsn : sh.toNumber .to_nearest = .ok sn) (hmul : nav.operator_mul sn .to_nearest = .ok NS)
    (hdiv : NS.operator_div v.sharesTotal .to_nearest = .ok an) :
    ∃ r, STAmount.ofNumber NumericType.native an .to_nearest = .ok r := by
  obtain ⟨hnavn, hN0⟩ := Vault.assetsTotalForWithdrawal_nonneg v w nav hnav
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hNSn := Number.operator_mul_isNormalized nav sn0 NS _ hnavn hsnn hmul
  have hann := Number.operator_div_isNormalized NS v.sharesTotal an _ hNSn v.wf.sharesTotal_norm hdiv
  refine (STAmount.ofNumber_ok_iff NumericType.native an .to_nearest hann (Or.inr (Or.inl rfl))
    (Or.inr (Or.inl rfl))).mpr ?_
  rw [STAmount.roundsInRange_native_iff]
  refine Or.inl ?_
  by_cases han : an.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero an han]; norm_num

  -- the division succeeded, so SharesTotal is not zero
  have hyne : ¬ v.sharesTotal.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := fun h0 => hyne (by
    rw [Number.eq_zero_of_mantissa_zero _ v.wf.sharesTotal_norm h0]; decide)
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))

  obtain ⟨-, hanpos, hbnd⟩ := WdPrice.pipe nav sn0 NS an v.sharesTotal hnavn hN0 hsnn (hsnv ▸ hnn)
    v.wf.sharesTotal_norm hSTpos hmul hdiv han
  rw [hsnv] at hbnd
  have hI : nav.toRat * sh.toRat / v.sharesTotal.toRat ≤ 10 ^ 17 + 3 / 10 := by
    rw [div_le_iff₀ hSTpos]; exact hb
  obtain ⟨-, hup⟩ := abs_le.mp hbnd
  rw [abs_of_pos hanpos]
  unfold sharesε at hup
  norm_num at hup ⊢
  linarith

/-- On an XRP vault the assets some shares are worth fail to compute only with an overflow error or a wrap, when
the shares are worth at most `10^17` drops at the computed net asset value. -/
lemma sharesToAssets_native_error {v : Vault} {sh : STAmount} {w : Bool} {e : Error}
    (hnt : v.numericType = NumericType.native) (hc : sh.Canonical) (hnn : 0 ≤ sh.toRat)
    (hb : ∀ nav, v.assetsTotalForWithdrawal w = .ok nav →
      nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat)
    (h : v.sharesToAssetsWithdraw sh w = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact nav_error ‹_›
    | exact toNumber_error ‹_›
    | exact number_mul_error ‹_›
    | exact number_div_error ‹_›
    | skip
  -- the price converts into an XRP amount
  have hnav : v.assetsTotalForWithdrawal w = .ok _ := ‹_›
  have hof : STAmount.ofNumber v.numericType _ .to_nearest = .error e := ‹_›
  obtain ⟨r, hr⟩ := native_price_ok v sh w hc hnn _ _ _ _ hnav (hb _ hnav) ‹_› ‹_› ‹_›
  rw [hnt, hr] at hof
  cases hof

/-- An XRP amount, canonical or zero, is at most `10^17` drops in size. -/
lemma native_abs_le {a : STAmount} (ha : a.CanonicalOrZero) (hnt : a.mNumericType = NumericType.native) :
    |a.toRat| ≤ 10 ^ 17 := by
  rcases ha with hc | hz
  · obtain ⟨hic, -⟩ := hc.1 (by simp [STAmount.integral, hnt, NumericType.native, NumericType.isIntegral])
    rw [STAmount.abs_toRat, hic.offset_zero, zpow_zero, mul_one]
    have hin := hic.in_range
    rw [hnt] at hin
    have h17 : NumericType.native.maxValue.toNat = 10 ^ 17 := by decide
    rw [h17] at hin
    exact_mod_cast hin
  · rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)]
    norm_num

/-- The shares a withdrawal by assets burns on an XRP vault are worth at most the requested amount, up to the
rounding of the pricing. -/
lemma native_assets_worth {v : Vault} {a sh : STAmount} {w : Bool} (hc : a.Canonical) (hpos : 0 < a.toRat)
    (hnt : a.mNumericType = NumericType.native) (hok : assetsToSharesWithdraw v a true w = .ok sh)
    (hnz : sh.isZero = false) (nav : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav) :
    nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat := by
  obtain ⟨-, hs0, hsle, -⟩ := WdTight.shares_bounds v a sh w nav hnav hpos hc hok hnz
  obtain ⟨-, hN0⟩ := Vault.assetsTotalForWithdrawal_nonneg v w nav hnav
  have hS0 : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have ha17 : a.toRat ≤ 10 ^ 17 := le_trans (le_abs_self _) (native_abs_le (Or.inl hc) hnt)
  unfold RawVault.idealSharesWithdrawAt at hsle
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf] at hsle
  rcases eq_or_lt_of_le hN0 with hN | hN
  · rw [← hN, zero_mul]
    positivity
  · -- nav * sh ≤ S * a * (1 + sharesε)
    have h1 : nav.toRat * sh.toRat ≤ v.sharesTotal.toRat * a.toRat * (1 + sharesε) := by
      have := mul_le_mul_of_nonneg_left hsle hN.le
      calc nav.toRat * sh.toRat
          ≤ nav.toRat * (v.sharesTotal.toRat * a.toRat / nav.toRat * (1 + sharesε)) := this
        _ = v.sharesTotal.toRat * a.toRat * (1 + sharesε) := by field_simp
    have h2 : v.sharesTotal.toRat * a.toRat * (1 + sharesε) ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat := by
      unfold sharesε
      nlinarith
    linarith

/-- The pricing of a withdrawal leaves its `try` only with a wrap. On an XRP vault a withdrawal by shares needs the
shares to be worth at most `10^17` drops at the computed net asset value. -/
lemma computeWithdraw_error {v : Vault} {amount : WithdrawAmount} {w : Bool} {e : Error}
    (hasset : Lending.Vault.HoldsAsset v) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hpos : 0 < amount.amount.toRat)
    (hxrp : v.numericType = NumericType.native → ∀ sh, amount = .vaultShares sh → ∀ nav,
      v.assetsTotalForWithdrawal w = .ok nav →
      nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat)
    (h : (computeWithdraw v amount w).run = .error e) : e = .wrap := by
  have hprice : ∀ sh : STAmount, sh.Canonical → 0 ≤ sh.toRat →
      (v.numericType = NumericType.native → ∀ nav, v.assetsTotalForWithdrawal w = .ok nav →
        nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat) →
      v.sharesToAssetsWithdraw sh w = .error e → isOverflow e = true ∨ e = .wrap := by
    intro sh hsc hs0 hb hs
    rcases hasset with hnt | hnt | hnt
    · exact sharesToAssets_error (Or.inl hnt) hs
    · exact sharesToAssets_native_error hnt hsc hs0 (hb hnt) hs
    · exact sharesToAssets_error (Or.inr hnt) hs
  cases amount with
  | vaultShares sh =>
    simp only [WithdrawAmount.amount, WithdrawAmount.InAsset] at hc hty hpos
    simp only [computeWithdraw] at h
    unfold_ter at h
    walk_ok
    exact (hprice sh hc hpos.le (fun hnt nav hnav => hxrp hnt sh rfl nav hnav) ‹_›).resolve_left ‹_›
  | vaultAssets a =>
    simp only [WithdrawAmount.amount, WithdrawAmount.InAsset] at hc hty hpos
    -- the shares the amount prices to are worth at most the amount
    have key : ∀ sh : STAmount, assetsToSharesWithdraw v a true w = .ok sh → ¬ sh.isZero = true →
        v.sharesToAssetsWithdraw sh w = .error e → isOverflow e = true ∨ e = .wrap := by
      intro sh hsh hnz hs
      obtain ⟨hic, h64⟩ := assetsToSharesWithdraw_int64_canonical v a sh true w hsh
      refine hprice sh (hic.canonical (by rw [h64]; decide))
        (assetsToSharesWithdraw_nonneg v a sh w (Or.inl hc) hpos.le hsh) (fun hnt nav hnav => ?_) hs
      exact native_assets_worth hc hpos (hty.trans hnt) hsh (by simpa using hnz) nav hnav
    simp only [computeWithdraw] at h
    unfold_ter at h
    walk_ok
    · exact (assetsToShares_error ‹_›).resolve_left ‹_›
    · exact (key _ ‹_› ‹_› ‹_›).resolve_left ‹_›

/-- The cash of an XRP vault is a whole number of drops up to `10^17`. -/
lemma native_cash {v : Vault} (hnt : v.numericType = NumericType.native) :
    v.assetsAvailable.toRat.den = 1 ∧ 0 ≤ v.assetsAvailable.toRat ∧ v.assetsAvailable.toRat ≤ 10 ^ 17 := by
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  rcases eq_or_lt_of_le hA0 with h0 | hpos
  · rw [← h0]; exact ⟨rfl, le_rfl, by norm_num⟩
  · obtain ⟨-, k, hkmax, -, hkv⟩ := Vault.cash_integral_of_exact v.valid.assetsAvailable_representable
      (by rw [hnt]; rfl) hpos
    rw [hkv]
    refine ⟨Rat.den_natCast k, Nat.cast_nonneg k, ?_⟩
    rw [hnt] at hkmax
    have h17 : NumericType.native.maxValue.toNat = 10 ^ 17 := by decide
    rw [h17] at hkmax
    exact_mod_cast hkmax

/-- On an XRP vault the cash less an XRP amount converts into an XRP amount. Both are whole drops up to `10^17`, so
the difference is exact and at most `10^17` in size. -/
lemma native_rest_ok {v : Vault} (hnt : v.numericType = NumericType.native) {a : STAmount}
    (ha : a.CanonicalOrZero) (hat : a.mNumericType = v.numericType) (ha0 : 0 ≤ a.toRat) {n X : Number}
    (hn : a.toNumber .to_nearest = .ok n) (hsub : v.assetsAvailable.operator_sub n .to_nearest = .ok X) :
    ∃ st, STAmount.ofNumber v.numericType X .to_nearest = .ok st := by
  obtain ⟨hnv, hnn⟩ := ha.toNumber_exact n hn
  obtain ⟨hAd, hA0, hA17⟩ := native_cash hnt
  have hAn := v.wf.assetsAvailable_norm
  have had : n.toRat.den = 1 := by
    rw [hnv]; exact STAmount.CanonicalOrZero.den_one ha (by rw [hat, hnt]; rfl)
  have ha17 : n.toRat ≤ 10 ^ 17 := by
    rw [hnv]; exact le_trans (le_abs_self _) (native_abs_le ha (hat.trans hnt))
  have hn0 : 0 ≤ n.toRat := by rw [hnv]; exact ha0

  -- the subtraction of two whole numbers below `2^63` is exact
  have hbound : (v.assetsAvailable.toRat - n.toRat).num.natAbs < 2 ^ 63 := by
    have := Rat.num_natAbs_add_lt_of_den_one v.assetsAvailable.toRat (-n.toRat) hAd
      (by rw [Rat.neg_den]; exact had) (by norm_num; linarith) (by norm_num; linarith)
    rwa [← sub_eq_add_neg] at this
  obtain ⟨hXv, -⟩ := Number.operator_sub_exact_int _ _ X hAn hnn hAd had hbound hsub
  have hXn := Number.operator_sub_isNormalized_any _ _ X _ hAn hnn hsub

  rw [hnt]
  refine (STAmount.ofNumber_ok_iff NumericType.native X .to_nearest hXn (Or.inr (Or.inl rfl))
    (Or.inr (Or.inl rfl))).mpr ?_
  rw [STAmount.roundsInRange_native_iff]
  refine Or.inl ?_
  rw [hXv, abs_lt]
  constructor <;> norm_num <;> linarith

/-- The dust check of a debit throws only a wrap: an overflow error inside it becomes `tecPATH_DRY`. -/
lemma checkDebitNotDust_error {v : Vault} {a : STAmount} {n : Number} {e : Error}
    (hasset : Lending.Vault.HoldsAsset v) (ha : a.CanonicalOrZero) (hat : a.mNumericType = v.numericType)
    (ha0 : 0 ≤ a.toRat) (hn : a.toNumber .to_nearest = .ok n)
    (h : v.checkDebitNotDust n = .error e) : e = .wrap := by
  obtain ⟨-, hnn⟩ := ha.toNumber_exact n hn
  have key : ∀ X : Number, v.assetsAvailable.operator_sub n .to_nearest = .ok X →
      STAmount.ofNumber v.numericType X .to_nearest = .error e → isOverflow e = true ∨ e = .wrap := by
    intro X hX hof
    rcases hasset with hnt | hnt | hnt
    · exact ofNumber_error_of (Or.inl hnt) hof
    · obtain ⟨st, hst⟩ := native_rest_ok hnt ha hat ha0 hn hX
      rw [hst] at hof
      cases hof
    · exact ofNumber_error_of (Or.inr hnt) hof
  have hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest ≠ .error e := by
    obtain ⟨c, hc⟩ := Vault.cash_ok_of_exact v.valid.assetsAvailable_representable
    rw [hc]
    exact nofun
  simp only [Vault.checkDebitNotDust] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact (number_sub_error v.wf.assetsAvailable_norm hnn ‹_›).resolve_left ‹_›
    | exact absurd ‹_› hcash
    | exact (key _ ‹_› ‹_›).resolve_left ‹_›

/-- The net asset value a withdrawal computes is at most the exact one, up to the rounding of one subtraction. -/
lemma nav_le {v : Vault} {w : Bool} {nav : Number} (h : v.assetsTotalForWithdrawal w = .ok nav) :
    nav.toRat ≤ (if w then v.depositNav else v.withdrawNav) * (1 + 1 / 10 ^ 18) := by
  obtain ⟨total, hat, hdown, hnear, -⟩ := Vault.assetsTotalForWithdrawal_steps_proof v w nav h
  obtain ⟨n, hlo, hval⟩ := hdown
  have htle : total.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
    rw [hval]; exact Number.lower_le _ n hlo
  obtain ⟨htn, hDle⟩ := Vault.assetsTotal_ge_deployed v total hat
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hL0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  have hLD : v.lossUnrealized.toRat ≤ v.assetsDeployed.toRat := v.exact.lossUnrealized_le
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind] at h
  rw [hat] at h
  dsimp only at h
  cases w with
  | true =>
    rw [Number.operator_sub_zero] at h
    obtain rfl := Except.ok.inj h
    show total.toRat ≤ (v.assetsAvailable.toRat + v.assetsDeployed.toRat) * (1 + 1 / 10 ^ 18)
    nlinarith
  | false =>
    show nav.toRat ≤
      (v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat) * (1 + 1 / 10 ^ 18)
    have hnear' : nav.RoundsToRepresentable (total.toRat - v.lossUnrealized.toRat) .to_nearest := by
      simpa using hnear
    have ht0 : 0 ≤ total.toRat - v.lossUnrealized.toRat := by linarith
    -- a result of zero, or a difference of zero, gives at most zero
    have hzero : total.toRat - v.lossUnrealized.toRat = 0 → nav.toRat ≤ 0 := fun h0 =>
      Number.RoundsToRepresentable.nonpos_of_nonpos nav _ hnear' h0.le
    have key : nav.toRat ≤ (total.toRat - v.lossUnrealized.toRat) * (1 + 1 / 10 ^ 18) := by
      by_cases hn0 : nav.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero nav hn0]; positivity
      by_cases hLm : v.lossUnrealized.mantissa_ = 0
      · rw [Number.operator_sub_zero_right total _ _ v.wf.lossUnrealized_norm hLm] at h
        obtain rfl := Except.ok.inj h
        rw [Number.toRat_eq_zero_of_mantissa_zero _ hLm]
        nlinarith
      by_cases htm : total.mantissa_ = 0
      · have ht : total.toRat - v.lossUnrealized.toRat = 0 := by
          have := Number.toRat_eq_zero_of_mantissa_zero total htm
          linarith
        rw [ht, zero_mul]
        exact hzero ht
      by_cases heq : total.operator_eq v.lossUnrealized = true
      · have ht : total.toRat - v.lossUnrealized.toRat = 0 := by
          rw [(Number.operator_eq_iff _ _ htn v.wf.lossUnrealized_norm).mp heq, sub_self]
        rw [ht, zero_mul]
        exact hzero ht
      · have hr := Number.operator_sub_rounds_to_nearest total v.lossUnrealized nav htn v.wf.lossUnrealized_norm
          htm hLm heq h hn0
        change |nav.toRat - (total.toRat - v.lossUnrealized.toRat)| ≤ _ at hr
        rw [abs_of_nonneg ht0] at hr
        obtain ⟨-, hup⟩ := abs_le.mp hr
        have hε : (total.toRat - v.lossUnrealized.toRat) * (6 / (2 ^ 63 - 3)) ≤
            (total.toRat - v.lossUnrealized.toRat) * (1 / 10 ^ 18) :=
          mul_le_mul_of_nonneg_left (by norm_num) ht0
        linarith
    nlinarith

end XRPL.Model.SingleAssetVault.VaultWithdrawErrors
