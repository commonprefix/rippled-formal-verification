import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultWithdrawPricing
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.Support.ComputeClawback

/-! # Which errors a withdrawal, a clawback and a burn of shares return

Outside the `try` of its pricing a vault operation converts amounts the vault stores or just priced, compares
them and updates the cash. On a lawful vault none of these steps fails, so the operation ends in an error only
through the pricing (a wrap, or `outOfRange` on an XRP vault) or the final lawfulness re-check. -/

namespace XRPL.Model.SingleAssetVault.VaultWithdrawErrors

open XRPL.Model.Protocol XRPL.Model.Protocol.ErrorKinds

/-- The `to_lawful` re-check fails only as `notLawful`. -/
lemma to_lawful_error {rv : RawVault} {e : Error} (h : rv.to_lawful = .error e) : e = .notLawful := by
  unfold RawVault.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- The check for a nonpositive IOU amount never fails. -/
lemma isFractionalNonPositive_ne_error (a : STAmount) (e : Error) : a.isFractionalNonPositive ≠ .error e := by
  unfold STAmount.isFractionalNonPositive
  split
  · exact nofun
  · unfold STAmount.operator_le STAmount.operator_lt
    have hcmp : STAmount.areComparable (STAmount.zero a.numericType) a = true := by
      simp [STAmount.areComparable, STAmount.zero_mNumericType, STAmount.numericType]
    rw [hcmp]
    exact nofun

/-- SharesTotal of a lawful vault converts into a share amount. -/
lemma sharesTotal_ne_error (v : Vault) (e : Error) :
    STAmount.ofNumber .int64 v.sharesTotal .to_nearest ≠ .error e := by
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg)
    (Vault.sharesTotal_le_maxRep v)
  rw [hS]
  exact nofun

/-- On an XRP vault the payout after the early-exit fee converts into an XRP amount: it is between zero and the
priced amount. -/
lemma native_payout_ok {a : STAmount} {aN fee pN : Number} {rate : TenthBips32} (ha : a.CanonicalOrZero)
    (hat : a.mNumericType = NumericType.native) (ha0 : 0 ≤ a.toRat) (haN : a.toNumber .to_nearest = .ok aN)
    (hrate : rate.toNat < 100000) (hfee : tenthBipsOfValue aN rate .upward = .ok fee)
    (hsub : aN.operator_sub fee .downward = .ok pN) :
    ∃ r, STAmount.ofNumber NumericType.native pN .downward = .ok r := by
  obtain ⟨hnv, haNn⟩ := ha.toNumber_exact aN haN
  have hden : a.toRat.den = 1 := STAmount.CanonicalOrZero.den_one ha (by rw [hat]; rfl)
  have ha17 : a.toRat ≤ 10 ^ 17 := le_trans (le_abs_self _) (native_abs_le ha hat)
  -- a whole number of drops is zero or at least one
  have hsmall : aN.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ aN.toRat := by
    rw [hnv]
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · exact Or.inl h0.symm
    · refine Or.inr ?_
      have hq : a.toRat = (a.toRat.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
      have h1 : (1 : ℚ) ≤ a.toRat := by
        rw [hq]
        exact_mod_cast Rat.num_pos.mpr hpos
      have h2 : (10 : ℚ) ^ (-1000 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      linarith
  obtain ⟨hp0, hple, -⟩ := payoutNumber_bounds aN fee pN rate haNn (by rw [hnv]; exact ha0) hsmall hrate hfee hsub
  have hfeen := tenthBipsOfValue_isNormalized haNn hfee
  have hpNn := Number.operator_sub_isNormalized_any aN fee pN _ haNn hfeen hsub
  refine (STAmount.ofNumber_ok_iff NumericType.native pN .downward hpNn (Or.inr (Or.inl rfl)) (Or.inl hp0)).mpr ?_
  rw [STAmount.roundsInRange_native_iff]
  have hr0 : (0 : ℚ) ≤ (rate.toNat : ℚ) / 100000 := by positivity
  have hle : pN.toRat ≤ a.toRat := by
    rw [hnv] at hple
    nlinarith
  refine ⟨by norm_num; linarith, by norm_num; linarith⟩

set_option maxHeartbeats 1600000 in
-- the walk splits the 51 failing paths of the withdrawal and closes each with a list of candidates
/-- A withdrawal that checks the holder's shares ends in an error only as `notLawful` or a wrap. On an XRP vault a
withdrawal by shares needs the shares to be worth at most `10^17` drops at the computed net asset value. -/
lemma withdraw_error {v : Vault} {amount : WithdrawAmount} {waive : Bool} {t : UInt32}
    {hpos : 0 < amount.amount.toRat} {held : Number} {e : Error}
    (hasset : Lending.Vault.HoldsAsset v) (hts : v.TotalStored) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (hn : held.isNormalized) (hbal : held.toRat ≤ v.toExact.sharesTotal)
    (hxrp : v.numericType = NumericType.native → ∀ sh, amount = .vaultShares sh → ∀ nav,
      v.assetsTotalForWithdrawal waive = .ok nav →
      nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * v.sharesTotal.toRat)
    (h : (v.withdraw amount waive t hpos (some held)).run = .error e) : e = .notLawful ∨ e = .wrap := by
  have hmax := hasset.maxValue_le
  have hexact := v.valid.assetsAvailable_representable
  have hform : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.assets.CanonicalOrZero ∧ amounts.assets.mNumericType = v.numericType ∧ 0 ≤ amounts.assets.toRat ∧
      amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧ 0 < amounts.shares.toRat := by
    intro amounts hcomp
    obtain ⟨hsic, hs64, hspos⟩ := computeWithdraw_shares_form v amount waive amounts hc hty hpos hcomp
    have hpr := computeWithdraw_ok_priced v amount waive amounts hcomp
    obtain ⟨haf, hat⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr
    exact ⟨haf, hat, Vault.sharesToAssetsWithdraw_nonneg v _ _ waive
      (Or.inl (hsic.canonical (by rw [hs64]; decide))) hspos.le hpr, hsic, hs64, hspos⟩
  have hst := sharesTotal_ne_error v e
  have hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest ≠ .error e := by
    obtain ⟨c, hc'⟩ := Vault.cash_ok_of_exact hexact
    rw [hc']; exact nofun
  have hnum : ∀ c : STAmount, c.CanonicalOrZero → c.toNumber .to_nearest ≠ .error e := by
    intro c hc' h'
    obtain ⟨n, hn'⟩ := hc'.toNumber_ok
    rw [hn'] at h'; cases h'
  have hnumS : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toNumber .to_nearest ≠ .error e := by
    intro amounts hcomp
    obtain ⟨-, -, -, hsic, hs64, -⟩ := hform amounts hcomp
    exact hnum _ (Or.inl (hsic.canonical (by rw [hs64]; decide)))
  have hwrap : isOverflow e = false → isOverflow e = true ∨ e = .wrap → e = .wrap :=
    fun h1 h2 => h2.resolve_left (by simp [h1])
  have hnav : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      v.assetsTotalForWithdrawal waive ≠ .error e := by
    intro amounts hcomp h'
    obtain ⟨nav, hnav, -⟩ := WdPrice.price_cases v _ _ waive
      (computeWithdraw_ok_priced v amount waive amounts hcomp)
    rw [hnav] at h'; cases h'
  have hdust : ∀ (amounts : VaultAmounts) (n : Number), (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.assets.toNumber .to_nearest = .ok n → v.checkDebitNotDust n = .error e → e = .wrap := by
    intro amounts n hcomp hn' hd
    obtain ⟨haf, hat, ha0, -⟩ := hform amounts hcomp
    exact checkDebitNotDust_error hasset haf hat ha0 hn' hd
  have hsub : ∀ (amounts : VaultAmounts) (aN fee : Number) (rate : TenthBips32),
      (computeWithdraw v amount waive).run = .ok (.ok amounts) → amounts.assets.toNumber .to_nearest = .ok aN →
      tenthBipsOfValue aN rate .upward = .ok fee → aN.operator_sub fee .downward = .error e →
      isOverflow e = true ∨ e = .wrap := by
    intro amounts aN fee rate hcomp haN hfee hs
    obtain ⟨-, haNn⟩ := (hform amounts hcomp).1.toNumber_exact aN haN
    exact number_sub_error haNn (tenthBipsOfValue_isNormalized haNn hfee) hs
  have hpay : ∀ (amounts : VaultAmounts) (aN fee pN : Number),
      (computeWithdraw v amount waive).run = .ok (.ok amounts) → amounts.assets.toNumber .to_nearest = .ok aN →
      tenthBipsOfValue aN (v.earlyExitFeeRateAt t) .upward = .ok fee → aN.operator_sub fee .downward = .ok pN →
      (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false →
      STAmount.ofNumber v.numericType pN .downward = .error e → isOverflow e = true ∨ e = .wrap := by
    intro amounts aN fee pN hcomp haN hfee hs hmaxf hof
    obtain ⟨haf, hat, ha0, -⟩ := hform amounts hcomp
    rcases hasset with hnt | hnt | hnt
    · exact ofNumber_error_of (Or.inl hnt) hof
    · have hne : v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate := by simpa using hmaxf
      have hle := Vault.earlyExitFeeRateAt_le v t
      have hne' : (v.earlyExitFeeRateAt t).toNat ≠ 100000 := fun h => hne (UInt32.toNat_inj.mp h)
      obtain ⟨r, hr⟩ := native_payout_ok haf (hat.trans hnt) ha0 haN (by omega) hfee hs
      rw [hnt, hr] at hof
      cases hof
    · exact ofNumber_error_of (Or.inr hnt) hof
  have hclamp : ∀ (pN : Number) (payout clamped : STAmount),
      STAmount.ofNumber v.numericType pN .downward = .ok payout →
      clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped →
      clamped.CanonicalOrZero ∧ clamped.mNumericType = v.numericType ∧ 0 ≤ clamped.toRat := by
    intro pN payout clamped hp hcl
    obtain ⟨hpc, hpt⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp
    obtain ⟨h1, h2, h3⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg
      v.baseExponent_range.1 v.baseExponent_range.2 hcl
    exact ⟨h1, by rw [h2, STAmount.operator_neg_mNumericType, hpt], h3⟩
  have hle : ∀ (c : STAmount) (cn : Number), c.CanonicalOrZero → c.toNumber .to_nearest = .ok cn →
      v.assetsAvailable.operator_lt cn = false → c.toRat ≤ v.assetsAvailable.toRat := by
    intro c cn hcc hcn hlt
    obtain ⟨hv, hnorm⟩ := hcc.toNumber_exact cn hcn
    rw [← hv]
    exact (Number.operator_lt_eq_false_iff _ _ v.wf.assetsAvailable_norm hnorm).mp hlt
  have hadj : ∀ (amounts : VaultAmounts) (c : STAmount) (sn : Number),
      (computeWithdraw v amount waive).run = .ok (.ok amounts) → c.CanonicalOrZero →
      c.mNumericType = v.numericType → 0 ≤ c.toRat → c.toRat ≤ v.assetsAvailable.toRat →
      amounts.shares.toNumber .to_nearest = .ok sn → held.operator_lt sn = false →
      (v.adjustAssetsAndShares c.operator_neg amounts.shares.operator_neg).run ≠ .error e := by
    intro amounts c sn hcomp hcc hct hc0 hcA hsn hlt
    obtain ⟨-, -, -, hsic, hs64, hspos⟩ := hform amounts hcomp
    obtain ⟨sn', hsn', hsv, hsnn, -⟩ := STAmount.toNumber_integral_exact amounts.shares .to_nearest hsic
      (by rw [hs64]; decide)
    obtain rfl := Except.ok.inj (hsn'.symm.trans hsn)
    have hsle : amounts.shares.toRat ≤ v.toExact.sharesTotal := by
      rw [← hsv]
      exact le_trans ((Number.operator_lt_eq_false_iff _ _ hn hsnn).mp hlt) hbal
    obtain ⟨raw, hraw⟩ := Vault.adjust_ok_of_exact v hexact hmax (hts.debitStores hasset) c amounts.shares hcc hct
      hc0 hcA hsic hs64 hspos.le hsle
    rw [hraw]
    exact nofun
  simp only [Vault.withdraw] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals first
    | exact Or.inr (computeWithdraw_error hasset hc hty hpos hxrp ‹_›)
    | exact Or.inl (to_lawful_error ‹_›)
    | exact absurd ‹_› hst
    | exact absurd ‹_› hcash
    | exact absurd ‹_› (hnav _ ‹_›)
    | exact Or.inr (hdust _ _ ‹_› ‹_› ‹_›)
    | exact absurd ‹_› (hnum _ (hform _ ‹_›).1)
    | exact absurd ‹_› (hnumS _ ‹_›)
    | exact absurd ‹_› (isFractionalNonPositive_ne_error _ _)
    | exact Or.inr (hwrap ‹_› (tenthBips_error ‹_›))
    | exact Or.inr (hwrap ‹_› (clampToSumExponent_error v.wf.assetsAvailable_norm ‹_›))
    | exact Or.inr (hwrap ‹_› (hsub _ _ _ _ ‹_› ‹_› ‹_› ‹_›))
    | exact Or.inr (hwrap ‹_› (hpay _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›))
    | exact absurd ‹_› (hnum _ (STAmount.zero_canonicalOrZero _).1)
    | exact absurd ‹_› (hnum _ (hclamp _ _ _ ‹_› ‹_›).1)
    | exact absurd ‹_› (hadj _ (STAmount.zero v.numericType) _ ‹_› (STAmount.zero_canonicalOrZero _).1
        (STAmount.zero_canonicalOrZero _).2 (by rw [STAmount.zero_toRat])
        (hle _ _ (STAmount.zero_canonicalOrZero _).1 ‹_› ‹_›) ‹_› ‹_›)
    | exact absurd ‹_› (hadj _ _ _ ‹_› (hclamp _ _ _ ‹_› ‹_›).1 (hclamp _ _ _ ‹_› ‹_›).2.1
        (hclamp _ _ _ ‹_› ‹_›).2.2 (hle _ _ (hclamp _ _ _ ‹_› ‹_›).1 ‹_› ‹_›) ‹_› ‹_›)
    | exact absurd ‹_› (hadj _ _ _ ‹_› (hform _ ‹_›).1 (hform _ ‹_›).2.1 (hform _ ‹_›).2.2.1
        (hle _ _ (hform _ ‹_›).1 ‹_› ‹_›) ‹_› ‹_›)
    | exact absurd ‹_› (hadj _ _ _ ‹_› (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ‹_›).1
        (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ‹_›).2
        (by rw [Vault.final_payout_exact v _ hexact hmax ‹_›]; exact v.exact.assetsAvailable_nonneg)
        (le_of_eq (Vault.final_payout_exact v _ hexact hmax ‹_›)) ‹_› ‹_›)

/-- The shares a clawback names fail to compute only with an overflow error or a wrap. -/
lemma assetsToSharesClawback_error {v : Vault} {a hs : STAmount} {w : Bool} {e : Error}
    (h : assetsToSharesClawback v a hs w = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [assetsToSharesClawback, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact ofNumber_int64_error ‹_›
    | exact assetsToShares_error ‹_›

/-- The pricing of a clawback on an IOU or MPT vault leaves its `try` only with a wrap. -/
lemma computeClawback_error {v : Vault} {assets holderShares : STAmount} {w : Bool} {e : Error}
    (hnt : v.numericType = .fractional ∨ v.numericType = NumericType.int64)
    (h : (computeClawback v assets holderShares w).run = .error e) : e = .wrap := by
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact (assetsToSharesClawback_error ‹_›).resolve_left ‹_›
    | exact (sharesToAssets_error hnt ‹_›).resolve_left ‹_›
    | exact (toNumber_error ‹_›).resolve_left ‹_›
    | exact (ofNumber_error_of hnt ‹_›).resolve_left ‹_›
    | exact (assetsToShares_error ‹_›).resolve_left ‹_›
    | exact (ofNumber_int64_error ‹_›).resolve_left ‹_›
    | exact (clampToSumExponent_error v.wf.assetsAvailable_norm ‹_›).resolve_left ‹_›
    | exact absurd ‹_› (isFractionalNonPositive_ne_error _ _)

/-- Comparing two share amounts never fails. -/
lemma shares_lt_ne_error {a b : STAmount} (ha : a.mNumericType = .int64) (hb : b.mNumericType = .int64)
    (e : Error) : a.operator_lt b ≠ .error e := by
  unfold STAmount.operator_lt
  have hcmp : STAmount.areComparable a b = true := by simp [STAmount.areComparable, ha, hb]
  rw [hcmp]
  exact nofun

/-- A clawback ends in an error only as `notLawful` or a wrap, when it destroys at most SharesTotal. An XRP vault
rejects the clawback before any pricing. -/
lemma clawback_error {v : Vault} {assets holderShares : STAmount} {waive : Bool} {hnn : 0 ≤ assets.toRat}
    {e : Error} (hasset : Lending.Vault.HoldsAsset v) (hts : v.TotalStored) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.ShareBalance)
    (hle : ∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ v.toExact.sharesTotal)
    (h : (v.clawback assets holderShares waive hnn).run = .error e) : e = .notLawful ∨ e = .wrap := by
  have hmax := hasset.maxValue_le
  have hexact := v.valid.assetsAvailable_representable
  have hnt : (v.numericType == NumericType.native) = false →
      v.numericType = .fractional ∨ v.numericType = NumericType.int64 := by
    intro hne
    rcases hasset with h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1] at hne; exact absurd hne (by decide)
    · exact Or.inr h1
  -- what the pricing returned: shares the holder check can compare, and a recovery the cash covers
  have hform : ∀ amounts : VaultAmounts,
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧ 0 ≤ amounts.shares.toRat ∧
      amounts.assets.CanonicalOrZero ∧ amounts.assets.mNumericType = v.numericType ∧
      0 ≤ amounts.assets.toRat ∧ amounts.assets.toRat ≤ v.assetsAvailable.toRat := by
    intro amounts hcomp
    obtain ⟨hsic, hs64, hs0, hac, hcover⟩ := computeClawback_amounts_form v assets holderShares waive amounts hc
      hnn hhs hmax hcomp
    obtain ⟨recovered, S, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts
      hcomp
    obtain ⟨-, -, -, hrc, hr0, -⟩ := hpr.form hc hnn hhs hmax
    have hrt : recovered.mNumericType = v.numericType := by
      cases hpr with
      | direct _ _ n ha2s hs2a hn hgt => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
      | capped _ _ cash _ _ _ n _ _ _ _ hcash ha2s hs2a hn hgt =>
        exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
    rw [STAmount.operator_neg_toRat] at hcover
    refine ⟨hsic, hs64, hs0, hac, ?_, ?_, by linarith⟩
    · rcases hrec with ⟨-, heq⟩ | ⟨-, hcl, -⟩
      · rw [heq]; exact hrt
      · obtain ⟨-, h2, -⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg
          v.baseExponent_range.1 v.baseExponent_range.2 hcl
        rw [h2, STAmount.operator_neg_mNumericType, hrt]
    · rcases hrec with ⟨-, heq⟩ | ⟨-, hcl, -⟩
      · rw [heq]; exact hr0
      · exact (clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg
          v.baseExponent_range.1 v.baseExponent_range.2 hcl).2.2
  have hnum : ∀ amounts : VaultAmounts,
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.assets.toNumber .to_nearest ≠ .error e := by
    intro amounts hcomp h'
    obtain ⟨n, hn'⟩ := (hform amounts hcomp).2.2.2.1.toNumber_ok
    rw [hn'] at h'; cases h'
  have hdust : ∀ (amounts : VaultAmounts) (n : Number),
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.assets.toNumber .to_nearest = .ok n → v.checkDebitNotDust n = .error e → e = .wrap := by
    intro amounts n hcomp hn' hd
    obtain ⟨-, -, -, haf, hat, ha0, -⟩ := hform amounts hcomp
    exact checkDebitNotDust_error hasset haf hat ha0 hn' hd
  have hlt : ∀ amounts : VaultAmounts,
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      holderShares.operator_lt amounts.shares ≠ .error e :=
    fun amounts hcomp => shares_lt_ne_error hhs.int64 (hform amounts hcomp).2.1 e
  have hadj : ∀ amounts : VaultAmounts,
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      (v.adjustAssetsAndShares amounts.assets.operator_neg amounts.shares.operator_neg).run ≠ .error e := by
    intro amounts hcomp
    obtain ⟨hsic, hs64, hs0, haf, hat, ha0, hacov⟩ := hform amounts hcomp
    obtain ⟨raw, hraw⟩ := Vault.adjust_ok_of_exact v hexact hmax (hts.debitStores hasset) amounts.assets
      amounts.shares haf hat ha0 hacov hsic hs64 hs0 (hle amounts hcomp)
    rw [hraw]
    exact nofun
  simp only [Vault.clawback] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  all_goals first
    | exact Or.inr (computeClawback_error (hnt ‹_›) ‹_›)
    | exact Or.inl (to_lawful_error ‹_›)
    | exact absurd ‹_› (hnum _ ‹_›)
    | exact Or.inr (hdust _ _ ‹_› ‹_› ‹_›)
    | exact absurd ‹_› (hlt _ ‹_›)
    | exact absurd ‹_› (hadj _ ‹_›)

/-- The checks of a burn of shares never end in an error. -/
lemma canBurnShares_ne_error (v : Vault) (amount hs : STAmount) (e : Error) :
    (v.canBurnShares amount hs).run ≠ .error e := by
  intro h
  simp only [Vault.canBurnShares] at h
  unfold_ter at h
  walk_ok
  exact absurd ‹_› (sharesTotal_ne_error v e)

/-- A burn of a holder's shares ends in an error only as `notLawful`. -/
lemma burnShares_error {v : Vault} {hs : STAmount} {e : Error} (hhs : hs.ShareBalance)
    (h : (v.burnShares hs).run = .error e) : e = .notLawful := by
  have hic : hs.IntegralCanonical := (hhs.canonical.1 (by simp only [STAmount.integral, hhs.int64]; decide)).1
  obtain ⟨sn, hsn, hsv, hsnn, -⟩ := STAmount.toNumber_integral_exact hs .to_nearest hic
    (by rw [hhs.int64]; decide)
  have hs0 : 0 ≤ hs.toRat := STAmount.toRat_nonneg_of _ hhs.nonneg
  have hcap : hs.toRat ≤ 2 ^ 63 - 1 := le_trans (le_abs_self _) (hic.abs_le_int64 hhs.int64)
  -- SharesTotal less the shares burned: both are whole numbers below `2^63`
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_normalized_cap v.sharesTotal sn .to_nearest v.wf.sharesTotal_norm hsnn
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg)
    (Number.negative_false_of_nonneg _ hsnn (by rw [hsv]; exact hs0)) (Vault.sharesTotal_le_maxRep v)
    (by rw [hsv]; exact hcap)
  have hnum : hs.toNumber .to_nearest ≠ .error e := by rw [hsn]; exact nofun
  have hsub : ∀ x : Number, hs.toNumber .to_nearest = .ok x →
      v.sharesTotal.operator_sub x .to_nearest ≠ .error e := by
    intro x hx
    obtain rfl := Except.ok.inj (hsn.symm.trans hx)
    rw [hd]
    exact nofun
  simp only [Vault.burnShares] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact to_lawful_error ‹_›
    | exact absurd ‹_› hnum
    | exact absurd ‹_› (hsub _ ‹_›)

end XRPL.Model.SingleAssetVault.VaultWithdrawErrors
