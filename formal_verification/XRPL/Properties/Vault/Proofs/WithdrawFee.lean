import XRPL.Properties.Vault.Proofs.WithdrawUpdates
import XRPL.Properties.Vault.Proofs.WithdrawPricing
import XRPL.Properties.Vault.Proofs.Support.EarlyExitFee
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Vault.Proofs.WithdrawMono.OfNumber
import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Protocol.Number.Add.RoundsWithin
import XRPL.Properties.Protocol.Number.Add.Common.Rounded

/-! # The payout of a withdrawal after the early-exit fee

A non-final withdrawal prices the burned shares, takes the early-exit fee from that priced amount
rounding up, rounds the rest down into the asset and clamps it onto the grid of the cash it leaves.
The payout never exceeds the priced amount less the exact fee share. `WithdrawPayoutFloor` shows that
on a reachable vault it is exactly that amount floored onto the vault's base grid. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Subtracting a zero `Number` returns the other operand. -/
lemma Number.operator_sub_zero_right (x y : Number) (mode : rounding_mode) (hy : y.isNormalized)
    (hy0 : y.mantissa_ = 0) : x.operator_sub y mode = .ok x := by
  rw [Number.eq_zero_of_mantissa_zero y hy hy0]
  unfold Number.operator_sub
  rw [show Number.zero.operator_neg = Number.zero by decide, Number.operator_add_zero_right]

/-- The payout `Number` left after the fee. Below a 100% fee rate it is nonnegative, at most the
exact remainder `a·(1 - rate)` and at least that remainder less `5·10⁻¹⁸` of the priced amount. -/
lemma payoutNumber_bounds (a fee pN : Number) (rate : TenthBips32) (ha : a.isNormalized)
    (ha0 : 0 ≤ a.toRat) (hsmall : a.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ a.toRat)
    (hrate : rate.toNat < 100000)
    (hfee : tenthBipsOfValue a rate .upward = .ok fee)
    (hsub : a.operator_sub fee .downward = .ok pN) :
    0 ≤ pN.toRat ∧ pN.toRat ≤ a.toRat * (1 - rate.toNat / 100000) ∧
      a.toRat * (1 - rate.toNat / 100000) - a.toRat * (5 / 10 ^ 18) ≤ pN.toRat := by
  obtain ⟨hflo, hfhi⟩ := tenthBipsOfValue_upward_bounds a rate fee ha ha0 hsmall hfee
  have hfn := (tenthBipsOfValue_upward_facts a rate fee ha ha0 hfee).1
  have hr9 : (rate.toNat : ℚ) ≤ 99999 := by exact_mod_cast (by omega : rate.toNat ≤ 99999)
  have hr0 : (0 : ℚ) ≤ rate.toNat := by positivity
  -- the fee is at most `0.99999·(1 + 3·10⁻¹⁸)` of the priced amount, so something remains
  have hrem : a.toRat * (1 - rate.toNat / 100000) - a.toRat * (3 / 10 ^ 18) ≤ a.toRat - fee.toRat := by
    have : a.toRat * rate.toNat / 100000 * (1 + 3 / 10 ^ 18) ≤
        a.toRat * rate.toNat / 100000 + a.toRat * (3 / 10 ^ 18) := by
      have h1 : a.toRat * rate.toNat / 100000 ≤ a.toRat := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      nlinarith
    linarith
  -- a zero priced amount leaves nothing
  by_cases ha00 : a.toRat = 0
  · have hf0 : fee.toRat = 0 := by
      rw [ha00] at hflo hfhi
      linarith
    have hfm : fee.mantissa_ = 0 := by
      rw [(Number.toRat_eq_zero_iff_eq_zero hfn).mp hf0]; rfl
    rw [Number.operator_sub_of_mantissa_zero a fee .downward hfm, Except.ok.injEq] at hsub
    rw [← hsub, ha00]
    norm_num
  have hapos : 0 < a.toRat := lt_of_le_of_ne ha0 (Ne.symm ha00)
  have hd1000 := hsmall.resolve_left ha00
  have ham : a.mantissa_ ≠ 0 := fun h => ha00 (Number.toRat_eq_zero_of_mantissa_zero a h)
  -- at least `10⁻⁵` of the priced amount remains after the fee, less `3·10⁻¹⁸` of it
  have hrest : a.toRat * (1 / 100000) ≤ a.toRat * (1 - rate.toNat / 100000) := by
    apply mul_le_mul_of_nonneg_left _ ha0
    rw [le_sub_iff_add_le, ← add_div, div_le_one (by norm_num)]
    linarith
  have hTpos : a.toRat * (1 / 200000) ≤ a.toRat - fee.toRat := by nlinarith
  by_cases hfm : fee.mantissa_ = 0
  · -- a zero fee leaves the priced amount, and forces a zero rate
    have hf0 : fee.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero fee hfm
    rw [Number.operator_sub_of_mantissa_zero a fee .downward hfm, Except.ok.injEq] at hsub
    subst hsub
    have hz : a.toRat * rate.toNat / 100000 = 0 := le_antisymm (by rw [← hf0]; exact hflo) (by positivity)
    have : a.toRat * (1 - rate.toNat / 100000) = a.toRat - a.toRat * rate.toNat / 100000 := by ring
    refine ⟨ha0, ?_, ?_⟩
    · linarith
    · nlinarith
  have hfneg := Number.operator_neg_isNormalized fee hfn
  have hne : ¬ a.operator_eq fee = true := by
    rw [operator_eq_iff _ _ ha hfn]
    intro h
    nlinarith
  by_cases hpm : pN.mantissa_ = 0
  · -- a remainder this large does not underflow to zero
    exfalso
    have hsub' := hsub
    unfold Number.operator_sub at hsub'
    have hfpos : 0 < fee.toRat := lt_of_le_of_ne (le_trans (by positivity) hflo)
      (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero fee hfm))
    have hdiff : a.negative_ ≠ fee.operator_neg.negative_ := by
      rw [Number.operator_neg_negative_of_ne fee hfm, Number.negative_false_of_pos a hapos,
        Number.negative_false_of_pos fee hfpos]
      decide
    have hnz : ¬ a.operator_eq fee.operator_neg.operator_neg = true := by
      rw [operator_eq_iff _ _ ha (Number.operator_neg_isNormalized _ hfneg), Number.toRat_neg,
        Number.toRat_neg, neg_neg]
      intro h
      nlinarith
    have h := operator_add_underflow_truth_small a fee.operator_neg pN .downward ha hfneg ham
      (by rw [Number.operator_neg_mantissa_of_ne fee hfm]; exact hfm) hdiff hnz hsub' hpm
    rw [Number.toRat_neg, ← sub_eq_add_neg, abs_of_pos (by nlinarith)] at h
    have htiny : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) <
        (10 : ℚ) ^ (-1000 : ℤ) * (1 / 200000) := by
      unfold minExponent
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      have h5 : (10 : ℚ) ^ (-1006 : ℤ) < 10 ^ (-1000 : ℤ) * (1 / 200000) := by
        rw [show (10 : ℚ) ^ (-1006 : ℤ) = 10 ^ (-1000 : ℤ) * 10 ^ (-6 : ℤ) by
          rw [← zpow_add₀ (by norm_num)]; norm_num]
        apply mul_lt_mul_of_pos_left _ (zpow_pos (by norm_num) _)
        norm_num
      exact lt_trans (zpow_lt_zpow_right₀ (by norm_num) (by norm_num)) h5
    nlinarith
  obtain ⟨hlo, hhi⟩ := operator_sub_rounds_downward a fee pN ha hfn ham hfm hne hsub hpm
  change pN.toRat ≤ a.toRat - fee.toRat at hlo
  change a.toRat - fee.toRat - pN.toRat ≤ |a.toRat - fee.toRat| * _ at hhi
  rw [abs_of_pos (by nlinarith)] at hhi
  have hsmallε : (11 / (2 ^ 63 - 18) : ℚ) ≤ 2 / 10 ^ 18 := by norm_num
  have hT1 : a.toRat - fee.toRat ≤ a.toRat := by linarith [le_trans (by positivity) hflo]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have : a.toRat * rate.toNat / 100000 = a.toRat * (rate.toNat / 100000) := by ring
    nlinarith
  · nlinarith

/-- The early-exit fee rate is at most 100% on a lawful vault. -/
lemma Vault.earlyExitFeeRateAt_le (v : Vault) (t : UInt32) : (v.earlyExitFeeRateAt t).toNat ≤ 100000 := by
  unfold Vault.earlyExitFeeRateAt
  split
  · rename_i rate h
    have hle : rate ≤ maxEarlyExitFeeRate := v.valid.earlyExitFeeRate_le rate (by simp [h])
    rw [UInt32.le_iff_toNat_le] at hle
    split
    · exact hle
    · simp
  · simp

/-- The priced amount of a withdrawal is a nonnegative amount of the asset, canonical or zero, and
zero or far above `10⁻¹⁰⁰⁰`, the floor `payoutNumber_bounds` asks for (it is in fact at least `10⁻⁸¹`). -/
lemma Vault.withdraw_priced_facts (v : Vault) (shares priced : STAmount) (waive : Bool)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hsc : shares.Canonical) (hpos : 0 < shares.toRat)
    (hpr : v.sharesToAssetsWithdraw shares waive = .ok priced) :
    priced.CanonicalOrZero ∧ 0 ≤ priced.toRat ∧
      (priced.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ priced.toRat) := by
  have hpc := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).1
  obtain ⟨-, -, -, hp0, -⟩ := WdPrice.price_spec v _ _ waive hpos.le hsc hpr
  refine ⟨hpc, hp0, ?_⟩
  by_cases hm : priced.mValue = 0
  · exact Or.inl ((STAmount.toRat_eq_zero_iff _).mpr hm)
  · right
    have h81 := STAmount.Canonical.abs_toRat_ge _ (hpc.resolve_right (by simpa [STAmount.isZero] using hm)) hm
    rw [abs_of_nonneg hp0] at h81
    exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) h81

/-- The fee path of a payout: the priced amount reads exactly as a `Number`, what is left after the
fee is a nonnegative normalized `Number` at most the exact remainder, and it rounds down to a nonzero amount. -/
lemma Vault.feePayout_shape (v : Vault) (priced payout : STAmount) (aN fee pN : Number) (rate : TenthBips32)
    (hpc : priced.CanonicalOrZero) (hp0 : 0 ≤ priced.toRat)
    (hsmall : priced.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ priced.toRat) (hrate : rate.toNat < 100000)
    (haN : priced.toNumber .to_nearest = .ok aN)
    (hfee : tenthBipsOfValue aN rate .upward = .ok fee)
    (hsub : aN.operator_sub fee .downward = .ok pN)
    (hpo : STAmount.ofNumber v.numericType pN .downward = .ok payout) (hpz : payout.isZero = false) :
    aN.toRat = priced.toRat ∧ aN.isNormalized ∧ fee.isNormalized ∧
    0 ≤ pN.toRat ∧ pN.toRat ≤ priced.toRat * (1 - rate.toNat / 100000) ∧ pN.isNormalized ∧
    payout.mValue ≠ 0 ∧ payout.toRat ≤ pN.toRat ∧ 0 ≤ payout.toRat := by
  obtain ⟨hav, han⟩ := hpc.toNumber_exact aN haN
  obtain ⟨hpN0, hpNle, -⟩ := payoutNumber_bounds aN fee pN rate han (hav ▸ hp0) (hav ▸ hsmall) hrate hfee hsub
  have hpm : payout.mValue ≠ 0 := by simpa [STAmount.isZero] using hpz
  have hfn := (tenthBipsOfValue_upward_facts aN rate fee han (hav ▸ hp0) hfee).1
  have hpNn := operator_sub_isNormalized _ _ _ _ han hfn hsub (STAmount.ofNumber_source_ne_zero _ _ _ _ hpo hpm)
  obtain ⟨hple, -, hpay0⟩ := STAmount.ofNumber_downward_floor_bounds _ _ _ hpNn
    (Number.negative_false_of_nonneg _ hpNn hpN0) hpo hpm
  rw [hav] at hpNle
  exact ⟨hav, han, hfn, hpN0, hpNle, hpNn, hpm, hple, hpay0⟩

/-- The clamped payout is at most the priced amount less the exact fee share. The fee is at least
its exact share, and every later rounding goes down. -/
lemma Vault.feePayout_le (v : Vault) (priced payout clamped : STAmount) (aN fee pN : Number)
    (rate : TenthBips32)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpc : priced.CanonicalOrZero) (hp0 : 0 ≤ priced.toRat)
    (hsmall : priced.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ priced.toRat) (hrate : rate.toNat < 100000)
    (haN : priced.toNumber .to_nearest = .ok aN)
    (hfee : tenthBipsOfValue aN rate .upward = .ok fee)
    (hsub : aN.operator_sub fee .downward = .ok pN)
    (hpo : STAmount.ofNumber v.numericType pN .downward = .ok payout) (hpz : payout.isZero = false)
    (hcl : clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped) :
    clamped.toRat ≤ priced.toRat * (1 - rate.toNat / 100000) := by
  obtain ⟨-, -, -, -, hpNle, -, -, hple, hpay0⟩ :=
    Vault.feePayout_shape v priced payout aN fee pN rate hpc hp0 hsmall hrate haN hfee hsub hpo hpz
  have hcle := clampToSumExponent_le_abs _ _ _ _ (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo).1.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0] at hcle
  linarith

/-- Proof of the valid-vault line of `Vault.withdraw_payout`. -/
lemma Vault.withdraw_payout_le_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      r.assets.toRat ≤ priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  obtain ⟨priced, hpr, hcase⟩ := Vault.withdraw_payout_cases v amount waive t hpos hc hty r hok hlt
  obtain ⟨hpc, hp0, hsmall⟩ :=
    Vault.withdraw_priced_facts v _ _ waive hmax (hsic.canonical (by rw [hs64]; decide)) hspos hpr
  have hρ : ((v.earlyExitFeeRateAt t).toNat : ℚ) ≤ 100000 := by exact_mod_cast v.earlyExitFeeRateAt_le t
  refine ⟨priced, hpr, ?_⟩
  rcases hcase with ⟨h0, -⟩ | ⟨aN, fee, pN, -, payout, hlow, haN, hfee, hsub, hpo, hpz, hcl, -, -, -⟩
  · rw [h0]
    apply mul_nonneg hp0
    rw [sub_nonneg, div_le_one (by norm_num)]
    exact hρ
  exact Vault.feePayout_le v _ _ _ _ _ _ _ hmax hpc hp0 hsmall
    (lt_of_le_of_ne (v.earlyExitFeeRateAt_le t) (fun h => hlow (UInt32.toNat_inj.mp h))) haN hfee hsub hpo hpz hcl

/-- On an Open-zone vault, shares up to the share total are never priced above the cash. The vault
prices at its cash, and the 19-digit price is so close to the worth that the conversion never rounds past it. -/
lemma Vault.OpenZone.sharesToAssetsWithdraw_le_cash {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares assets : STAmount) (waive : Bool) (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    assets.toRat ≤ v.assetsAvailable.toRat := by
  obtain ⟨nav, hsub, hnav0, -, hcase⟩ := WdPrice.price_spec v shares assets waive hnn hc hok
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  by_cases hpz : assets.mValue = 0
  · rw [(STAmount.toRat_eq_zero_iff _).mpr hpz]; exact hAA0
  rcases hcase with hz | ⟨-, hSTpos, an, hanpos, hb, -, hann, hof⟩
  · exact absurd hz hpz
  have hnavv : nav.toRat = v.assetsAvailable.toRat :=
    congrArg Number.toRat (Except.ok.inj (hsub.symm.trans (hz.assetsTotalForWithdrawal_eq waive)))
  -- the exact worth is at most the cash
  set ideal := nav.toRat * shares.toRat / v.sharesTotal.toRat with hideal_def
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hideal0 : 0 ≤ ideal := div_nonneg (mul_nonneg hnav0 hnn) hSTpos.le
  have hideal : ideal ≤ v.assetsAvailable.toRat := by
    rw [hideal_def, hnavv, div_le_iff₀ hSTpos]
    have : shares.toRat ≤ v.sharesTotal.toRat := by rw [← hcast]; exact hle
    nlinarith
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hanle' : an.toRat ≤ v.assetsAvailable.toRat + v.assetsAvailable.toRat * (2 / 10 ^ 18) := by nlinarith
  -- the cash, as an amount of the asset
  have hrd := hz.cashExact
  obtain ⟨cash, hcash⟩ : ∃ cash, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash := by
    unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hrd
    cases h : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
    | error e => rw [h] at hrd; simp [bind, Except.bind] at hrd
    | ok c => exact ⟨c, rfl⟩
  have hcv := Vault.final_payout_exact v cash hrd hmax hcash
  have hAApos : 0 < v.assetsAvailable.toRat := by
    by_contra h
    push Not at h
    have : ideal ≤ 0 := by linarith
    nlinarith
  have hcm : cash.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ v.wf.assetsAvailable_norm hAA0 hcash hcm
  have hct : cash.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  by_cases hanle : an.toRat ≤ v.assetsAvailable.toRat
  · rw [← hcv]
    exact STAmount.ofNumber_to_nearest_le_of_canonical _ an assets cash hann hanpos.le hcE hct
      (by rw [hcv]; exact hanle) hof hpz
  -- the 19-digit price is just above the cash, which the conversion rounds back to
  push Not at hanle
  have hnear : |an.toRat - cash.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) := by
    rw [hcv, abs_of_pos (by linarith)]
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
    · -- an integral cash is a whole amount in the Open zone, below `9·10¹⁵`
      have hoff : cash.exponent = 0 := hic.offset_zero
      have hint : v.numericType.isIntegral = true := by rw [← hct]; exact hic.is_integral
      have hb0 := v.baseExponent_bounds.2.2 hint
      have hopen := hz.assetsAvailable_le_openLimit
      rw [hb0] at hopen
      rw [hoff, zpow_zero]
      norm_num at hopen ⊢
      nlinarith
  have heq := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an assets cash hann hanpos.le hcE hct
    (by rw [hcv]; exact hAApos) hnear hof hpz
  rw [heq, hcv]

/-- On a reachable vault, shares up to the share total are never priced above the cash. -/
lemma Vault.Reachable.sharesToAssetsWithdraw_le_cash (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares assets : STAmount) (waive : Bool) (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    assets.toRat ≤ v.assetsAvailable.toRat :=
  (Vault.Reachable.openZone_proof v t0 hr hmax).sharesToAssetsWithdraw_le_cash hmax shares assets waive hnn hc hle
    hok

/-- On a reachable vault the clamp of an amount the cash covers floors onto the base grid. The cash
left is below `10 ^ (16 + base)` like the cash, so its 16-digit grid is no coarser than the base grid. -/
lemma Vault.Reachable.clamp_base (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (X clamped : STAmount) (hX : X.CanonicalOrZero) (hXt : X.mNumericType = .fractional)
    (hX0 : 0 ≤ X.toRat) (hXle : X.toRat ≤ v.assetsAvailable.toRat) (hnz : clamped.mValue ≠ 0)
    (hcl : clampToSumExponent v.assetsAvailable X.operator_neg v.baseExponent = .ok clamped) :
    clamped.toRat = (⌊X.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨dN, e, hdN, hps, hge, hfl⟩ := Vault.clamp_floor v X clamped hX hXt hX0 hnz hcl
  suffices he : e = v.baseExponent by rw [← he]; exact hfl
  by_contra hne
  have hgt : v.baseExponent < e := lt_of_le_of_ne hge (Ne.symm hne)
  obtain ⟨s, hs, hne'⟩ := postSumExponent_reduces _ _ _ _ _ hps
  obtain ⟨hdv, hdn⟩ := hX.operator_neg.toNumber_exact dN hdN
  rw [STAmount.operator_neg_toRat] at hdv
  have hr1 := operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hdn hs
  rw [hdv, ← sub_eq_add_neg] at hr1
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hdn hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s _ hr1 (by linarith)
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized s _ hr1 _ v.wf.assetsAvailable_norm (by linarith)
  obtain ⟨-, hlarge⟩ := numberExponent_frac_lower s _ e hsn hs0
    (by have := v.baseExponent_range.1; omega) hne' hgt
  have hopen := (Vault.Reachable.openZone_proof v t0 hr hmax).assetsAvailable_le_openLimit
  have hbig : 9 * (10 : ℚ) ^ (15 + v.baseExponent) < 10 ^ (16 + v.baseExponent) := by
    rw [show (16 : ℤ) + v.baseExponent = (15 + v.baseExponent) + 1 by ring, zpow_add_one₀ (by norm_num)]
    have : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
    linarith
  have : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

/-- The cash guard passes an amount the cash covers. -/
lemma Vault.lt_cash_false (v : Vault) (X : STAmount) (n : Number) (hX : X.CanonicalOrZero)
    (hn : X.toNumber .to_nearest = .ok n) (hle : X.toRat ≤ v.assetsAvailable.toRat) :
    v.assetsAvailable.operator_lt n = false := by
  obtain ⟨hv, hnorm⟩ := hX.toNumber_exact n hn
  cases h : v.assetsAvailable.operator_lt n with
  | false => rfl
  | true =>
    have := (operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm).mp h
    linarith

/-- Proof of `Vault.withdraw_under_available`. A reachable vault prices shares up to the share total at
most at its cash, the fee and the roundings only lower the payout, and a final withdrawal pays the cash. -/
lemma Vault.withdraw_under_available_proof (v : Vault) (shares : STAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (hr : Vault.Reachable v t0)
    (hc : shares.Canonical)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal) :
    (v.withdraw (.vaultShares shares) waive t hpos).run ≠ .ok (.error .tecINSUFFICIENT_FUNDS) := by
  intro hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- the helpers never refuse for insufficient funds
  all_goals try (rcases Vault.checkDebitNotDust_codes _ _ _ ‹_› with h | h | h <;> exact absurd h (by decide))
  all_goals try (rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
  all_goals try (rcases computeWithdraw_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))
  -- the shares are priced at most at the cash
  all_goals
    have hcomp : (computeWithdraw v (.vaultShares shares) waive).run = .ok (.ok _) := ‹_›
    have hpr := computeWithdraw_ok_priced v _ waive _ hcomp
    rw [WdTight.computeWithdraw_vaultShares_shares v shares waive _ hcomp] at hpr
    have hcash := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax shares _ waive hpos.le hc hle hpr
    have hac := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).1
  · -- the guard before the fee compares the priced amount
    have hg : _ ∧ v.assetsAvailable.operator_lt _ = true := ‹_›
    rw [Vault.lt_cash_false v _ _ hac ‹(VaultAmounts.assets _).toNumber .to_nearest = .ok _› hcash] at hg
    exact absurd hg.2 (by decide)
  · -- a 100% fee pays nothing
    have hg : v.assetsAvailable.operator_lt _ = true := ‹_›
    rw [Vault.lt_cash_false v _ _ (STAmount.zero_canonicalOrZero _).1
      ‹(STAmount.zero _).toNumber .to_nearest = .ok _›
      (by rw [STAmount.zero_toRat _]; exact v.exact.assetsAvailable_nonneg)] at hg
    exact absurd hg (by decide)
  · -- the clamped payout after the fee is at most the priced amount
    have hg : v.assetsAvailable.operator_lt _ = true := ‹_›
    obtain ⟨-, hp0, hsmall⟩ := Vault.withdraw_priced_facts v _ _ waive hmax hc hpos hpr
    have hlow : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false := ‹_›
    have hrate : (v.earlyExitFeeRateAt t).toNat < 100000 :=
      lt_of_le_of_ne (v.earlyExitFeeRateAt_le t) (fun h => by
        have h' : v.earlyExitFeeRateAt t = maxEarlyExitFeeRate := UInt32.toNat_inj.mp h
        rw [h'] at hlow; exact absurd hlow (by decide))
    have hpo : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    have hle' := Vault.feePayout_le v _ _ _ _ _ _ _ hmax hac hp0 hsmall hrate
      ‹(VaultAmounts.assets _).toNumber .to_nearest = .ok _› ‹tenthBipsOfValue _ _ _ = _›
      ‹Number.operator_sub _ _ _ = _› hpo ‹STAmount.isZero _ = false› hcl
    have hρ : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
    have hcc := (clampToSumExponent_canonicalOrZero _ _ _ _
      (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo).1.operator_neg
      v.baseExponent_range.1 v.baseExponent_range.2 hcl).1
    rw [Vault.lt_cash_false v _ _ hcc ‹STAmount.toNumber _ _ = _› (by nlinarith)] at hg
    exact absurd hg (by decide)
  -- a zero priced amount, and a final withdrawal, compare the priced amount
  all_goals
    have hg : v.assetsAvailable.operator_lt _ = true := ‹_›
    rw [Vault.lt_cash_false v _ _ hac ‹(VaultAmounts.assets _).toNumber .to_nearest = .ok _› hcash] at hg
    exact absurd hg (by decide)

end XRPL.Model.SingleAssetVault
