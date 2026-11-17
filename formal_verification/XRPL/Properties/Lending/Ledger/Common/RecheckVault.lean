import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Lending.Ledger.Common.ShareInv
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # Vault transactions pass their lawfulness re-check

A vault transaction on a reachable ledger never fails the model with `notLawful`, given the C++ checks and
balances the model runs elsewhere or not at all. A VaultClawback on an MPT vault needs the vault below `10^16`
units. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The deposit rounding reads only Number and STAmount operations. -/
private lemma Vault.roundedDepositAmount_ne_notLawful (v : Vault) (amount : STAmount) :
    (v.roundedDepositAmount amount).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.roundedDepositAmount] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [RawVault.assetsTotal_ne_notLawful, clampToSumExponent_ne_notLawful]

/-- The deposit share pricing reads only Number and STAmount operations. -/
private lemma assetsToSharesDeposit_ne_notLawful (v : Vault) (amount : STAmount) :
    assetsToSharesDeposit v amount ≠ .error .notLawful := by
  unfold assetsToSharesDeposit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, Number.normalized_ne_notLawful, Number.truncate_ne_notLawful,
    STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful, Number.operator_mul_ne_notLawful,
    Number.operator_div_ne_notLawful]

/-- The deposit asset pricing reads only Number and STAmount operations. -/
private lemma sharesToAssetsDeposit_ne_notLawful (v : Vault) (shares : STAmount) :
    sharesToAssetsDeposit v shares ≠ .error .notLawful := by
  unfold sharesToAssetsDeposit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, STAmount.checked_ne_notLawful,
    STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful, Number.operator_mul_ne_notLawful,
    Number.operator_div_ne_notLawful]

/-- An STAmount comparison never raises `notLawful`. -/
private lemma STAmount.operator_gt_ne_notLawful (lhs rhs : STAmount) :
    lhs.operator_gt rhs ≠ .error .notLawful := by
  unfold STAmount.operator_gt
  exact STAmount.operator_lt_ne_notLawful _ _

/-- The deposit computation passes on only Protocol errors. -/
private lemma computeDeposit_ne_notLawful (v : Vault) (amount : STAmount) (isDonation : Bool) :
    (computeDeposit v amount isDonation).run ≠ .error .notLawful := by
  intro h
  simp only [computeDeposit] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [assetsToSharesDeposit_ne_notLawful, sharesToAssetsDeposit_ne_notLawful,
    STAmount.operator_gt_ne_notLawful, RawVault.assetsTotal_ne_notLawful, clampToSumExponent_ne_notLawful,
    STAmount.isFractionalNonPositive_ne_notLawful]

/-- The deposit inflow check reads only Number and STAmount operations. -/
private lemma Vault.checkOpenLimit_ne_notLawful (v : Vault) (amount : STAmount) :
    v.checkOpenLimit amount ≠ .error .notLawful := by
  unfold Vault.checkOpenLimit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, STAmount.toNumber_ne_notLawful,
    postSumExponent_ne_notLawful, XRPL.Model.Lending.Vault.exceedsOpenLimit_ne_notLawful]

/-- A deposit never fails its lawfulness re-check when the minted shares keep SharesTotal within the share
MPT maximum. -/
lemma Vault.deposit_lawful (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hsupply : ∀ ra amounts, (v.roundedDepositAmount amount).run = .ok (.ok ra) →
      (computeDeposit v ra isDonation).run = .ok (.ok amounts) →
      (v.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) :
    (v.deposit amount isDonation t hpos).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.deposit] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  all_goals try first
    | exact Vault.roundedDepositAmount_ne_notLawful _ _ ‹_›
    | exact computeDeposit_ne_notLawful _ _ _ ‹_›
    | exact Vault.adjustAssetsAndShares_ne_notLawful _ _ _ ‹_›
    | exact Vault.checkOpenLimit_ne_notLawful _ _ ‹_›
    | exact RawVault.assetsTotal_ne_notLawful _ ‹_›
  have hrounded : (v.roundedDepositAmount amount).run = .ok (.ok _) := ‹v.roundedDepositAmount amount = _›
  have hcomp : (computeDeposit v _ isDonation).run = .ok (.ok _) := ‹computeDeposit v _ isDonation = _›
  have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.ok _) := ‹v.adjustAssetsAndShares _ _ = _›
  obtain ⟨hwf, hval⟩ := Vault.deposit_success_lawful v amount isDonation t hc hty _ _ _ ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
    hrounded hcomp hadj (hsupply _ _ hrounded hcomp)
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hwf hval
  have hbad := hv'.symm.trans ‹RawVault.to_lawful _ = Except.error Error.notLawful›
  cases hbad

/-- The burn checks read only an STAmount conversion. -/
lemma Vault.canBurnShares_ne_notLawful (v : Vault) (amount holderShares : STAmount) :
    (v.canBurnShares amount holderShares).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.canBurnShares] at h
  unfold_ter at h
  walk_ok
  exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›

/-- A burn that passed its checks never fails its lawfulness re-check when it destroys a whole number of
shares, at most SharesTotal. -/
lemma Vault.burnShares_lawful (v : Vault) (amount holderShares sharesTotalAmount : STAmount)
    (hcan : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount))
    (hcanon : holderShares.IntegralCanonical) (hnn : holderShares.negative = false)
    (hle : holderShares.toRat ≤ sharesTotalAmount.toRat) :
    (v.burnShares holderShares).run ≠ .error .notLawful := by
  intro h
  have h0 := h
  simp only [Vault.burnShares] at h
  unfold_ter at h
  walk_ok
  all_goals try first
    | exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
  obtain ⟨v', hok, -⟩ := Vault.burnShares_ok_proof v amount holderShares holderShares sharesTotalAmount _ _ hcan
    hcanon hnn (by simpa using ‹¬ holderShares.isZero = true›) hle ‹_› ‹_›
  rw [hok] at h0
  cases h0

/-- On a vault with nothing deployed all the shares together are priced at exactly the cash, when the cash is whole
base units the asset stores, and an XRP or MPT cash is below `10^16` units. -/
private lemma Vault.sharesToAssetsWithdraw_all_idle (v : Vault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero)
    (hgrid : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hrd : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hopen : v.numericType.isIntegral = true → v.assetsAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (shares assets : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hall : shares.toRat = v.toExact.sharesTotal)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    assets.toRat = v.assetsAvailable.toRat := by
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hs0 : 0 ≤ shares.toRat := by rw [hall]; exact Nat.cast_nonneg _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨nav, hsub, hnavn, hcase⟩ := WdPrice.price_cases v _ _ waive hok
  have hnavv : nav.toRat = v.assetsAvailable.toRat := by
    rw [WdPrice.nav_exact v waive nav (Vault.withdrawNavExact_of_noLending v hAD waive) hsub]
    have hLU := Vault.lossUnrealized_eq_zero_of_deployed v hAD
    cases waive
    · show v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat = _
      rw [hAD, hLU, Number.toRat_zero]; ring
    · show v.assetsAvailable.toRat + v.assetsDeployed.toRat = _
      rw [hAD, Number.toRat_zero]; ring
  rcases eq_or_lt_of_le hAA0 with hAAz | hAApos
  · -- an empty cash prices every share at zero
    rcases hcase with ⟨-, hp⟩ | ⟨hnz, -⟩
    · rw [hp, ← hAAz]; exact (STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)
    · exact absurd (hnavv.trans hAAz.symm) (Number.toRat_ne_zero_of_mantissa_ne_zero _ hnz)
  -- the cash is a positive whole number of base steps, at least `10⁻¹⁰`
  obtain ⟨k, hkv⟩ := hgrid
  have hk1 : (1 : ℚ) ≤ k := by
    have : k ≠ 0 := fun h => by rw [hkv, h] at hAApos; simp at hAApos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hbk : (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat := by rw [hkv]; nlinarith
  have hAA10 : (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat :=
    le_trans (zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).1) hbk
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
  obtain ⟨hb3, -⟩ := abs_le.mp hb2
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
    · -- an integral cash is below `10¹⁶`
      have hoff : cash.exponent = 0 := hic.offset_zero
      have hint : v.numericType.isIntegral = true := by rw [← hct]; exact hic.is_integral
      have hb0 := v.baseExponent_bounds.2.2 hint
      have hopen := hopen hint
      rw [hb0] at hopen
      rw [hoff, zpow_zero]
      norm_num at hopen ⊢
      nlinarith
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


/-- On a vault with nothing deployed a clawback of every share recovers all the cash, when the cash is whole base
units the asset stores, and an XRP or MPT cash is below `10^16` units. -/
lemma Vault.computeClawback_final_idle (v : Vault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hAD : v.assetsDeployed = Number.zero)
    (hgrid : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hrd : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hopen : v.numericType.isIntegral = true → v.assetsAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hhs : holderShares.ShareBalance) (amounts : VaultAmounts)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts))
    (hall : amounts.shares.toRat = v.toExact.sharesTotal) :
    amounts.assets.toRat = v.assetsAvailable.toRat := by
  obtain ⟨rec, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v _ _ waive _ hcomp
  obtain ⟨hsic, hs64, -, hrc, hr0, -⟩ := hpr.form hc hnn hhs hmax
  obtain ⟨hs2a, -, -⟩ := hpr.recovered hmax
  have hsc : amounts.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  have hrv := Vault.sharesToAssetsWithdraw_all_idle v hmax hAD hgrid hrd hopen _ _ waive hsc hall hs2a
  rcases hrec with ⟨-, heq⟩ | ⟨-, hcl, hfnp⟩
  · rw [heq]; exact hrv
  have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral clamp keeps the worth
    have hni : rec.operator_neg.integral = true := by
      unfold STAmount.integral
      rw [(STAmount.operator_neg_fields rec).1, hpt]
      exact hint
    rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
    obtain ⟨-, -, -, hrat⟩ := clamp_magnitude rec.operator_neg
    rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0] at hrat
    rw [hrat, hrv]
  -- a fractional clamp of the whole cash leaves nothing, so it floors onto the base grid
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hat : amounts.assets.mNumericType = .fractional := by
    have h := (clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg
      v.baseExponent_range.1 v.baseExponent_range.2 hcl).2.1
    rw [h, (STAmount.operator_neg_fields rec).1, hpt, hvfr]
  have hrm : amounts.assets.mValue ≠ 0 := fun h0 => by
    rw [STAmount.isFractionalNonPositive_zero _ hat h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  obtain ⟨dN, e, hdN, hps, hge, hfl⟩ := Vault.clamp_floor v rec amounts.assets hrc (by rw [hpt, hvfr]) hr0 hrm hcl
  have he : e = v.baseExponent := by
    by_contra hne
    have hgt : v.baseExponent < e := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨s, hs, hne'⟩ := postSumExponent_reduces _ _ _ _ _ hps
    obtain ⟨hdv, hdn⟩ := hrc.operator_neg.toNumber_exact dN hdN
    rw [STAmount.operator_neg_toRat] at hdv
    have hr1 := operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hdn hs
    rw [hdv, ← sub_eq_add_neg, hrv, sub_self] at hr1
    have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hdn hs
    have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s _ hr1 le_rfl
    have hsle : s.toRat ≤ 0 := by
      have := Number.RoundsToRepresentable.le_of_le_normalized s _ hr1 Number.zero Number.zero_isNormalized
        (by rw [Number.toRat_zero])
      rwa [Number.toRat_zero] at this
    obtain ⟨-, hlarge⟩ := numberExponent_frac_lower s _ e hsn hs0
      (by have := v.baseExponent_range.1; omega) hne' hgt
    have : (0 : ℚ) < 10 ^ (e + 15) := zpow_pos (by norm_num) _
    linarith
  rw [he] at hfl
  obtain ⟨k, hkv⟩ := hgrid
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  rw [hfl, hrv, hkv, mul_div_cancel_right₀ _ hbp.ne', Int.floor_natCast]
  push_cast
  ring

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultAmounts WithdrawAmount computeWithdraw computeClawback
  computeDeposit)

/-- The VaultSet checks read the vault through Number comparisons only. -/
lemma Vault.canVaultUpdate_ne_notLawful (v : Vault) (assetsMaximum : Option Number)
    (blockDeposit : Option Bool) :
    v.canVaultUpdate assetsMaximum blockDeposit ≠ .error .notLawful := by
  unfold XRPL.Model.SingleAssetVault.Vault.canVaultUpdate
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.isOnExponentGrid_ne_notLawful, RawVault.assetsTotal_ne_notLawful]

/-- The vault with a new maximum and deposit flag is lawful when a set maximum is above zero and only an owner
allowed to block deposits blocks them. -/
private lemma Vault.with_flags_lawful (v : Vault) (am : Option Number) (db : Bool)
    (ham : ∀ m ∈ am, m.isNormalized ∧ Number.zero.operator_lt m = true)
    (hdb : db = true → v.ownerCanBlockDeposit = true) :
    ∃ v', ({ v.toRawVault with assetsMaximum := am, depositBlocked := db } : RawVault).to_lawful = .ok v' := by
  have hwf : ({ v.toRawVault with assetsMaximum := am, depositBlocked := db } : RawVault).WF :=
    { v.wf with assetsMaximum_norm := fun m hm => (ham m hm).1 }
  have hvalid : ({ v.toRawVault with assetsMaximum := am, depositBlocked := db } : RawVault).Valid :=
    { v.valid with assetsMaximum_pos := fun m hm => (ham m hm).2, depositBlocked_owner := hdb }
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hwf hvalid
  exact ⟨v', hv'⟩

/-- A VaultSet that passed its preflight and checks writes a lawful vault. A nonzero maximum is above
zero, and only an owner allowed to block deposits can block them. -/
lemma Vault.update_ok_of_checks (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    (hmax : ∀ m ∈ assetsMaximum, m.isNormalized ∧ Number.zero.operator_le m = true)
    (hcan : v.canVaultUpdate assetsMaximum blockDeposit = .ok .tesSUCCESS) :
    ∃ v', v.update assetsMaximum blockDeposit = .ok v' := by
  have hperm : (!v.ownerCanBlockDeposit && blockDeposit.isSome) = false := by
    cases hp : (!v.ownerCanBlockDeposit && blockDeposit.isSome)
    · rfl
    · exfalso
      unfold XRPL.Model.SingleAssetVault.Vault.canVaultUpdate at hcan
      simp only [bind, Except.bind, pure, Except.pure] at hcan
      revert hcan
      cases assetsMaximum with
      | none => simp [hp]
      | some m =>
        simp only
        cases hg : m.isOnExponentGrid v.baseExponent v.numericType with
        | error e => simp
        | ok b => cases b <;> simp [hp]
  unfold XRPL.Model.SingleAssetVault.Vault.update
  dsimp only
  apply Vault.with_flags_lawful
  · intro m hm
    cases assetsMaximum with
    | none => exact ⟨v.wf.assetsMaximum_norm m hm, v.valid.assetsMaximum_pos m hm⟩
    | some m0 =>
      obtain ⟨hn, hle⟩ := hmax m0 rfl
      simp only at hm
      split at hm
      · cases hm
      · rename_i hne
        obtain rfl : m0 = m := Option.some.inj hm
        have h0 : 0 ≤ m0.toRat := by
          have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp hle
          rwa [Number.toRat_zero] at this
        have hne' : m0.toRat ≠ 0 := by
          intro h
          exact hne ((operator_eq_iff _ _ hn Number.zero_isNormalized).mpr (by rw [h, Number.toRat_zero]))
        exact ⟨hn, (operator_lt_iff _ _ Number.zero_isNormalized hn).mpr
          (by rw [Number.toRat_zero]; exact lt_of_le_of_ne h0 (Ne.symm hne'))⟩
  · intro hb
    cases hbd : blockDeposit
    · simp only [hbd, Option.getD_none] at hb
      exact v.valid.depositBlocked_owner hb
    · cases ho : v.ownerCanBlockDeposit
      · simp [ho, hbd] at hperm
      · rfl

/-- A VaultSet never fails its lawfulness re-check. -/
lemma LendingLedger.vaultSet_ne_notLawful (l : LendingLedger) (assetsMaximum : Option Number)
    (blockDeposit : Option Bool) :
    (l.apply (.vaultSet assetsMaximum blockDeposit)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_vault rfl
  intro hpre _ h
  have hmax : ∀ m ∈ assetsMaximum, m.isNormalized ∧ Number.zero.operator_le m = true := by
    intro m hm
    rw [Option.mem_def] at hm
    subst hm
    have hc : isNonnegativeInput m = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp [LendingTx.preflight, hne] at hpre
    simpa [isNonnegativeInput] using hc
  simp only [LendingLedger.applyVault] at h
  unfold_ter at h
  walk_ok'
  · exact Vault.canVaultUpdate_ne_notLawful _ _ _ ‹_›
  · rename_i hu
    have hcan : l.vault.canVaultUpdate assetsMaximum blockDeposit = .ok _ := ‹_›
    have hok : ∀ t : TER, ¬ (!t.isTesSuccess) = true → t = .tesSUCCESS := fun t ht =>
      (TER.isTesSuccess_iff t).mp (by simpa using ht)
    rename_i t _ _ hc _ _
    rw [hok t hc] at hcan
    obtain ⟨v', hv'⟩ := Vault.update_ok_of_checks l.vault assetsMaximum blockDeposit hmax hcan
    rw [hv'] at hu
    cases hu

/-- A withdrawal that passed its preflight names a canonical amount of the vault's asset or of its shares. -/
lemma LendingTx.preflight_vaultWithdraw_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (h : Nat)
    (amount : WithdrawAmount) (hpre : (LendingTx.vaultWithdraw h amount).preflight l = .tesSUCCESS) :
    amount.amount.Canonical ∧ amount.InAsset l.vault.numericType := by
  cases amount with
  | vaultAssets a =>
    have hc : (isCanonicalAmount a l.vault.numericType && isPositiveAmount a) = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp [LendingTx.preflight, hne] at hpre
    rw [Bool.and_eq_true] at hc
    have hnz : a.mValue ≠ 0 := by
      have := hc.2
      simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
      exact this.2
    exact isCanonicalAmount_canonical a _ hasset.maxValue_le hc.1 hnz
  | vaultShares a =>
    have hc : (isCanonicalAmount a .int64 && isPositiveAmount a) = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp [LendingTx.preflight, hne] at hpre
    rw [Bool.and_eq_true] at hc
    have hnz : a.mValue ≠ 0 := by
      have := hc.2
      simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
      exact this.2
    exact isCanonicalAmount_canonical a _ (fun _ => by decide) hc.1 hnz

/-- A deposit that passed its preflight deposits a canonical amount of the vault's asset. -/
lemma LendingTx.preflight_vaultDeposit_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (h : Nat)
    (amount : STAmount) (isDonation : Bool)
    (hpre : (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS) :
    amount.Canonical ∧ amount.mNumericType = l.vault.numericType := by
  have hc : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true] at hc
  have hnz : amount.mValue ≠ 0 := by
    have := hc.2
    simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    exact this.2
  exact isCanonicalAmount_canonical amount _ hasset.maxValue_le hc.1 hnz

/-- A deposit never fails its lawfulness re-check when its shares keep SharesTotal within the share MPT
maximum. -/
lemma LendingLedger.vaultDeposit_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (h : Nat) (amount : STAmount)
    (isDonation : Bool)
    -- the new shares keep SharesTotal within the share MPT maximum, which C++ accountSend enforces (tecPATH_DRY)
    -- and the model does not run
    (hsupply : ∀ ra amounts, (l.vault.roundedDepositAmount amount).run = .ok (.ok ra) →
      (computeDeposit l.vault ra isDonation).run = .ok (.ok amounts) →
      (l.vault.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) :
    (l.apply (.vaultDeposit h amount isDonation)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_vault rfl
  intro hpre _ hrun
  obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit_canonical l hr.holdsAsset h amount isDonation hpre
  simp only [LendingLedger.applyVault] at hrun
  split at hrun
  · rename_i hpos
    unfold_ter at hrun
    walk_ok'
    · exact Vault.deposit_lawful l.vault amount isDonation l.now hpos hc hty hsupply
        (by simpa only [ExceptT.run] using ‹_›)
    · exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    · exact Number.operator_add_ne_notLawful _ _ _ ‹_›
  · cases hrun

/-- A burn of a holder's shares never fails its lawfulness re-check. The owner burns every share the holder
owns on an insolvent vault. -/
lemma LendingLedger.vaultBurnShares_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (amount : STAmount)
    -- the holder's shares are a whole number within SharesTotal, as C++ keeps the share MPT balance
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) :
    (l.apply (.vaultBurnShares h amount)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_vault rfl
  intro _ _ hrun
  obtain ⟨hden, h0, hle⟩ := hbal
  have hn := hr.sharesNormalized.sharesOf h
  simp only [LendingLedger.applyVault] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›
  · exact Vault.canBurnShares_ne_notLawful _ _ _ (by simpa only [ExceptT.run] using ‹_›)
  · -- the holder's shares convert exactly, and the burn destroys at most SharesTotal
    have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
    have hcan : (l.vault.canBurnShares amount _).run = .ok (.ok _) := ‹l.vault.canBurnShares amount _ = _›
    obtain ⟨hty, hoff, hneg, -, hval⟩ := STAmount.ofNumber_int64_shape _ _ _ hn h0 hden
      (le_trans hle l.vault.sharesTotal_le_maxRep) hof
    have hcanon : STAmount.IntegralCanonical _ :=
      ⟨by rw [hty]; rfl, hoff, (STAmount.ofNumber_integral_canonical _ _ _ _ (by decide) hof).1.in_range⟩
    have hST := Vault.canBurnShares_assets_exact_proof l.vault amount _ _ hcan
    rw [RawVault.WF.toExact_sharesTotal _ l.vault.wf] at hST
    exact Vault.burnShares_lawful l.vault amount _ _ hcan hcanon hneg (by rw [hval, hST]; exact hle)
      (by simpa only [ExceptT.run] using ‹_›)

/-- A withdrawal never fails its lawfulness re-check. It redeems at most the holder's shares, and a final
withdrawal pays out all the cash, which a reachable ledger stores exactly. -/
lemma LendingLedger.vaultWithdraw_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (amount : WithdrawAmount)
    -- the holder's shares are within SharesTotal, as C++ keeps the share MPT balance
    (hbal : (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) :
    (l.apply (.vaultWithdraw h amount)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_vault rfl
  intro hpre _ hrun
  obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset h amount hpre
  simp only [LendingLedger.applyVault] at hrun
  split at hrun
  · rename_i hpos
    unfold_ter at hrun
    walk_ok'
    · exact Vault.withdraw_holder_ne_notLawful l.vault amount _ l.now hpos _ hc hty hr.holdsAsset.maxValue_le
        (hr.sharesNormalized.sharesOf h) (by rw [RawVault.WF.toExact_sharesTotal _ l.vault.wf]; exact hbal)
        (fun _ _ _ => hr.availableStored) (by simpa only [ExceptT.run] using ‹_›)
    · exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    · exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
  · cases hrun

/-- A clawback that passed its preflight claws a canonical amount, or zero, which claws all the holder's shares. -/
lemma LendingTx.preflight_vaultClawback_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (h : Nat)
    (assets : STAmount) (hpre : (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS) :
    assets.CanonicalOrZero := by
  have hc : (isCanonicalAmount assets l.vault.numericType && !assets.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true] at hc
  by_cases hz : assets.mValue = 0
  · exact Or.inr (by simp [STAmount.isZero, hz])
  · exact Or.inl (isCanonicalAmount_canonical assets _ hasset.maxValue_le hc.1 hz).1

/-- The holder's shares as an amount of shares: a canonical nonnegative MPT amount. -/
private lemma LendingLedger.holderShares_balance (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat)
    (hs : STAmount) (hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs) :
    hs.ShareBalance ∧ hs.toRat = (l.sharesOf h).toRat := by
  obtain ⟨hden, h0, hle⟩ := hbal
  obtain ⟨hty, -, hneg, -, hval⟩ := STAmount.ofNumber_int64_shape _ _ _ (hr.sharesNormalized.sharesOf h) h0 hden
    (le_trans hle l.vault.sharesTotal_le_maxRep) hof
  have hic := (STAmount.ofNumber_integral_canonical _ _ _ _ (by decide) hof).1
  exact ⟨⟨hty, hic.canonical (by rw [hty]; decide), hneg⟩, hval⟩

/-- A clawback of every share recovers all the cash on a reachable ledger whose XRP or MPT vault is not
coarsened. Nothing is deployed, so all the shares together are worth the cash. -/
private lemma LendingLedger.clawback_final_recovers (l : LendingLedger) (hr : l.Reachable)
    (htotal : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (assets hs : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hhs : hs.ShareBalance) (amounts : VaultAmounts)
    (hcomp : (computeClawback l.vault assets hs waive).run = .ok (.ok amounts))
    (hall : amounts.shares.toRat = l.vault.toExact.sharesTotal) :
    l.vault.assetsAvailable.toRat + amounts.assets.operator_neg.toRat = 0 := by
  have hmax := hr.holdsAsset.maxValue_le
  obtain ⟨_, _, hpr, hst, hobl, -⟩ := SingleAssetVault.computeClawback_success_reduces l.vault _ _ waive _ hcomp
  obtain ⟨hic, h64, h0, -, -, -⟩ := hpr.form hc hnn hhs hmax
  have hAD : l.vault.assetsDeployed = Number.zero := by
    rcases eq_or_lt_of_le h0 with h0 | hpos
    · have hS : l.vault.sharesTotal = Number.zero := by
        rw [← Number.toRat_eq_zero_iff_eq_zero l.vault.wf.sharesTotal_norm,
          ← RawVault.WF.toExact_sharesTotal _ l.vault.wf, ← hall, ← h0]
      exact (l.vault.valid.empty_shares hS).2
    · have hfin := (Vault.isFinalWithdrawal_iff l.vault _ _ hic h64 hpos hst).mpr hall
      by_contra hne
      rw [hfin, (Number.operator_ne_iff_ne _ _).mpr hne] at hobl
      exact absurd hobl (by decide)
  have hAD0 : l.vault.assetsDeployed.toRat = 0 := by rw [hAD, Number.toRat_zero]
  have hrec := Vault.computeClawback_final_idle l.vault hmax hAD (hr.assetsAvailable_units hr.holdsAsset)
    hr.availableStored (fun hi => by have := htotal hi; rw [hAD0, add_zero] at this; exact this) assets hs waive
    hc hnn hhs amounts hcomp hall
  rw [STAmount.operator_neg_toRat, hrec]
  ring

/-- A clawback never fails its lawfulness re-check when the holder owns the shares it destroys and an MPT vault holds
less than `10^16` units. -/
lemma LendingLedger.vaultClawback_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (assets : STAmount)
    -- the holder's shares are a whole number within SharesTotal, as C++ keeps the share MPT balance
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat)
    -- the holder owns the shares the clawback destroys, which C++ accountSend checks (VaultClawback.cpp:466)
    (hheld : ∀ (hs : STAmount) (amounts : VaultAmounts), STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
      (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ (l.sharesOf h).toRat)
    -- an MPT vault holds less than `10^16` units, so the price of all the shares rounds back to the cash
    (htotal : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    (l.apply (.vaultClawback h assets)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_vault rfl
  intro hpre _ hrun
  have hc := LendingTx.preflight_vaultClawback_canonical l hr.holdsAsset h assets hpre
  -- the preflight rejects a clawback on an XRP vault, so an XRP or MPT vault here is an MPT vault
  have htotal' : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := fun hint => by
    have hnat := LendingTx.preflight_vaultClawback_not_native l h assets hpre
    rcases hr.holdsAsset with hnt | hnt | hnt
    · rw [hnt] at hint; cases hint
    · exact absurd hnt hnat
    · exact htotal hnt
  simp only [LendingLedger.applyVault] at hrun
  split at hrun
  · rename_i hnn
    unfold_ter at hrun
    walk_ok'
    · exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›
    · have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
      obtain ⟨hhs, -⟩ := l.holderShares_balance hr h hbal _ hof
      refine Vault.clawback_lawful l.vault assets _ _ hnn hc hhs hr.holdsAsset.maxValue_le (fun a ha => ?_)
        (fun a ha hall => l.clawback_final_recovers hr htotal' assets _ _ hc hnn hhs a ha hall)
        (by simpa only [ExceptT.run] using ‹_›)
      rw [RawVault.WF.toExact_sharesTotal _ l.vault.wf]
      exact le_trans (hheld _ a hof ha) hbal.2.2
    · exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    · exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
  · cases hrun

end XRPL.Model.Lending
