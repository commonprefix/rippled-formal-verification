import XRPL.Properties.Vault.Proofs.Lawful
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts

/-! # Emptying a reachable `int64` vault

Peel one share per withdrawal: the one-share run always succeeds on a reachable
`int64` vault within the caps, strictly lowers the share total, and preserves the
hypotheses, so strong induction on the share total reaches zero. -/

namespace XRPL.Model.SingleAssetVault

/-- A finite withdrawal sequence that drains the vault to zero shares. `done`
records that the vault already has no shares; `step` performs one non-loss-waiving
withdrawal that runs without a throw and then empties the resulting vault. -/
inductive CanEmpty : Vault → Prop where
  | done (v : Vault) : v.toExact.sharesTotal = 0 → CanEmpty v
  | step (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult) :
      (hpos : 0 < amount.amount.toRat) → v.withdraw amount false hpos = .ok r → r.error = none → CanEmpty r.vault' → CanEmpty v

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.SingleAssetVault.CanEmp

open XRPL.Model.Protocol

lemma exp_ge_of_one_le (n : Number) (hn : n.isNormalized) (hne : n.mantissa_ ≠ 0)
    (h : 1 ≤ |n.toRat|) : -18 ≤ n.exponent_ := by
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat hne
  have hmlt : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℤ) := by exact_mod_cast hhi
  have hpe : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hlt : (10 : ℚ) ^ (0 : ℤ) < (10 : ℚ) ^ ((19 : ℤ) + n.exponent_) := by
    rw [zpow_add₀ (by norm_num), zpow_zero]
    rw [abs_toRat_eq] at h
    nlinarith
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp hlt
  omega

lemma exp_le_zero_of_cap (n : Number) (hn : n.isNormalized) (hne : n.mantissa_ ≠ 0)
    (h : |n.toRat| ≤ 2 ^ 63 - 1) : n.exponent_ ≤ 0 := by
  obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat hne
  have hmge : (10 : ℚ) ^ (18 : ℤ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
  have hpe : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hlt : (10 : ℚ) ^ ((18 : ℤ) + n.exponent_) < (10 : ℚ) ^ (19 : ℤ) := by
    rw [zpow_add₀ (by norm_num)]
    rw [abs_toRat_eq] at h
    have : (10 : ℚ) ^ (18 : ℤ) * 10 ^ n.exponent_ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ :=
      mul_le_mul_of_nonneg_right hmge hpe.le
    have h2 : (2 : ℚ) ^ 63 - 1 < 10 ^ (19 : ℤ) := by norm_num
    linarith
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp hlt
  omega

/-- One canonical `int64` share. -/
def oneShare : STAmount := ⟨.int64, 1, 0, false⟩

lemma oneShare_toRat : oneShare.toRat = 1 := by decide

lemma oneShare_ic : oneShare.IntegralCanonical := ⟨rfl, rfl, by decide⟩

lemma oneShare_toNumber : ∃ sn : Number, oneShare.toNumber .to_nearest = .ok sn ∧
    sn.toRat = 1 ∧ sn.isNormalized := by
  obtain ⟨sn, h, hv, hn⟩ := STAmount.toNumber_integral_small_exact oneShare .to_nearest
    oneShare_ic (by decide)
  exact ⟨sn, h, by rw [hv, oneShare_toRat], hn⟩

/-- Pricing one share on a loss-free `int64` vault with integral, capped totals. -/
lemma price_oneShare (v : Vault) (hL0 : v.lossUnrealized.mantissa_ = 0)
    (hAnn : 0 ≤ v.assetsTotal.toRat) (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hAint : v.assetsTotal.toRat.den = 1)
    (hS1 : 1 ≤ v.sharesTotal.toRat) (hScap : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64) :
    ∃ (assets : STAmount) (aN : Number),
      v.sharesToAssetsWithdraw oneShare false = .ok assets ∧
      assets.toNumber .to_nearest = .ok aN ∧ aN.isNormalized ∧ aN.toRat = assets.toRat ∧
      aN.toRat.den = 1 ∧ assets.IntegralCanonical ∧ assets.mNumericType = .int64 ∧
      0 ≤ assets.toRat ∧ assets.toRat ≤ v.assetsTotal.toRat := by
  have hAnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hSnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
  have hSm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  have hSe : -18 ≤ v.sharesTotal.exponent_ :=
    exp_ge_of_one_le _ hSnorm hSm (by rw [abs_of_pos (by linarith)]; exact hS1)
  unfold Vault.sharesToAssetsWithdraw
  simp only []
  rw [Number.operator_sub_of_mantissa_zero v.assetsTotal v.lossUnrealized _ hL0, ok_bind]
  by_cases hAm0 : v.assetsTotal.mantissa_ = 0
  · rw [if_pos (by rw [hAm0]; rfl), hint]
    have hz : STAmount.zero .int64 = ⟨.int64, 0, 0, false⟩ := by decide
    rw [hz]
    obtain ⟨aN, h1, h2, h3, h4⟩ := STAmount.toNumber_integral_exact' (⟨.int64, 0, 0, false⟩ : STAmount)
      .to_nearest rfl rfl (by decide)
    refine ⟨_, aN, rfl, h1, h3, h2, by rw [h2]; exact h4, ⟨rfl, rfl, by decide⟩, rfl,
      by decide, ?_⟩
    rw [show (⟨.int64, 0, 0, false⟩ : STAmount).toRat = 0 from by decide]; exact hAnn
  · rw [if_neg (by simpa using hAm0)]
    obtain ⟨sn, hsn, hsnv, hsnn⟩ := oneShare_toNumber
    rw [hsn, ok_bind]
    have hsnm : sn.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnv]; norm_num)
    have hsne1 : -18 ≤ sn.exponent_ := exp_ge_of_one_le _ hsnn hsnm (by rw [hsnv]; norm_num)
    have hsne2 : sn.exponent_ ≤ 0 := exp_le_zero_of_cap _ hsnn hsnm (by rw [hsnv]; norm_num)
    have hApos : 0 < v.assetsTotal.toRat :=
      lt_of_le_of_ne hAnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hAm0))
    have hA1 : 1 ≤ v.assetsTotal.toRat := by
      have := rat_one_le_sub_of_lt v.assetsTotal.toRat 0 hAint rfl hApos
      simpa using this
    have hAe1 := exp_ge_of_one_le _ hAnorm hAm0 (by rw [abs_of_pos hApos]; exact hA1)
    have hAe2 := exp_le_zero_of_cap _ hAnorm hAm0 (by rw [abs_of_pos hApos]; exact hcap)
    obtain ⟨NS, hmul⟩ := Number.operator_mul_ok_of_normalized v.assetsTotal sn .to_nearest
      hAnorm hsnn hAm0 hsnm (by unfold minExponent; omega) (by unfold maxExponent; omega)
    rw [hmul, ok_bind]
    have hNSv : NS.toRat = v.assetsTotal.toRat := by
      have h := Number.RoundsToRepresentable.eq_of_representable NS (v.assetsTotal.toRat * sn.toRat)
        (operator_mul_rounded_to_nearest _ _ _ hAnorm hsnn hmul) v.assetsTotal hAnorm
        (by rw [hsnv, mul_one])
      rw [h, hsnv, mul_one]
    have hNSm : NS.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hNSv]; exact hApos.ne')
    have hNSn : NS.isNormalized :=
      operator_mul_result_isNormalized _ _ _ _ hAnorm hsnn hAm0 hsnm hmul hNSm
    have hNSe2 := exp_le_zero_of_cap _ hNSn hNSm (by rw [hNSv, abs_of_pos hApos]; exact hcap)
    obtain ⟨q, hdiv⟩ := Number.operator_div_ok_of_normalized NS v.sharesTotal .to_nearest
      hNSn hSnorm hNSm hSm (by unfold maxExponent; omega)
    rw [hdiv, ok_bind]
    have hqr := operator_div_rounded_to_nearest _ _ _ hNSn hSnorm hdiv
    have hSpos : (0 : ℚ) < v.sharesTotal.toRat := by linarith
    have hq_le : q.toRat ≤ v.assetsTotal.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized q _ hqr v.assetsTotal hAnorm
        (by rw [hNSv]; exact div_le_self hAnn hS1)
    have hq_nn : 0 ≤ q.toRat :=
      Number.RoundsToRepresentable.nonneg_of_nonneg q _ hqr (by rw [hNSv]; positivity)
    have hq_ge : (10 : ℚ) ^ (-20 : ℤ) ≤ NS.toRat / v.sharesTotal.toRat := by
      rw [hNSv, le_div_iff₀ hSpos]
      have h1 : (10 : ℚ) ^ (-20 : ℤ) * v.sharesTotal.toRat ≤ (10 : ℚ) ^ (-20 : ℤ) * (2 ^ 63 - 1) :=
        mul_le_mul_of_nonneg_left hScap (by positivity)
      have h2 : (10 : ℚ) ^ (-20 : ℤ) * (2 ^ 63 - 1) ≤ 1 := by norm_num
      linarith
    have hw_norm : (⟨false, 1000000000000000000, -38⟩ : Number).isNormalized := by decide
    have hw_val : (⟨false, 1000000000000000000, -38⟩ : Number).toRat = (10 : ℚ) ^ (-20 : ℤ) := by
      rw [Number.toRat_of_nonneg _ rfl]
      norm_num [show (1000000000000000000 : UInt64).toNat = 1000000000000000000 from rfl]
    have hq_pos : 0 < q.toRat := by
      have h := Number.RoundsToRepresentable.ge_of_ge_normalized q _ hqr _ hw_norm
        (by rw [hw_val]; exact hq_ge)
      rw [hw_val] at h
      exact lt_of_lt_of_le (by positivity) h
    have hqm : q.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hq_pos.ne'
    have hqn : q.isNormalized :=
      operator_div_result_isNormalized _ _ _ _ hNSn hSnorm hNSm hSm hdiv hqm
    have hqneg := Number.negative_false_of_normalized_nonneg q hqn hq_nn
    obtain ⟨assets, hof⟩ := STAmount.ofNumber_int64_ok q .to_nearest hqn hqneg
      (le_trans hq_le hcap)
    rw [hint, hof]
    obtain ⟨hic, hnt⟩ := STAmount.ofNumber_integral_canonical .int64 q .to_nearest assets rfl hof
    have hw1 := STAmount.ofNumber_integral_within_one .int64 q .to_nearest assets rfl hqn
      hqneg hof
    obtain ⟨aN, haN, haNv, haNn, hden⟩ := STAmount.toNumber_integral_exact' assets .to_nearest
      hic.is_integral hic.offset_zero (by
        have h := hic.in_range
        rw [hnt] at h
        exact le_trans h (by decide))
    obtain ⟨hw1a, hw1b⟩ := abs_lt.mp hw1
    refine ⟨assets, aN, rfl, haN, haNn, haNv, by rw [haNv]; exact hden, hic, hnt, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have := rat_one_le_sub_of_lt 0 assets.toRat rfl hden hc
      linarith
    · by_contra hc
      push Not at hc
      have := rat_one_le_sub_of_lt assets.toRat v.assetsTotal.toRat hden hAint hc
      linarith

/-- The withdraw clamp is inert on a nonnegative canonical integral payout. -/
lemma clampToSumExponent_neg_int (A : Number) (a : STAmount) (hic : a.IntegralCanonical) (hnn : 0 ≤ a.toRat) :
    clampToSumExponent A a.operator_neg = .ok a := by
  have hint : a.integral = true := hic.is_integral
  by_cases hm : a.mValue = 0
  · have hneg : a.operator_neg = a := by
      unfold STAmount.operator_neg; rw [if_pos (by rw [hm]; rfl)]
    unfold clampToSumExponent
    rw [hneg, if_pos hint]
    split <;> simp_all [pure, Except.pure]
  · have hsign : a.mIsNegative = false := by
      rcases h : a.mIsNegative with _ | _
      · rfl
      · exfalso
        rw [STAmount.IntegralCanonical.toRat_eq_signedDrops a hic] at hnn
        unfold STAmount.signedDrops at hnn
        rw [if_pos h] at hnn
        have h1 : (0 : ℤ) ≤ -(a.mValue.toNat : ℤ) := by exact_mod_cast hnn
        have h2 : a.mValue.toNat ≠ 0 := fun h0 => hm (UInt64.toNat_inj.mp (by rw [h0]; rfl))
        omega
    have hneg : a.operator_neg = { a with mIsNegative := true } := by
      unfold STAmount.operator_neg; rw [if_neg (by simpa using hm), hsign]; rfl
    unfold clampToSumExponent
    rw [hneg]
    have hi2 : ({ a with mIsNegative := true } : STAmount).integral = true := hint
    simp only [hi2, if_true, STAmount.negative, STAmount.operator_neg, pure, Except.pure]
    rw [if_neg (by simpa using hm)]
    cases a; simp_all

lemma frac_int (a : STAmount) (hic : a.IntegralCanonical) :
    a.isFractionalNonPositive = .ok false := by
  unfold STAmount.isFractionalNonPositive
  rw [if_pos (show a.integral = true from hic.is_integral)]

lemma oneShare_pos : 0 < (WithdrawAmount.vaultShares oneShare).amount.toRat := by
  show 0 < oneShare.toRat
  rw [oneShare_toRat]; norm_num

/-- One-share withdrawal on a reachable `int64` vault succeeds and shrinks the share total. -/
lemma step (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1)
    (hpos : 0 < v.toExact.sharesTotal) :
    ∃ r : WithdrawResult, v.withdraw (.vaultShares oneShare) false oneShare_pos = .ok r ∧ r.error = none ∧
      r.sharesBurned = oneShare ∧ r.vault'.toExact.sharesTotal < v.toExact.sharesTotal ∧
      r.vault'.assetsTotal.toRat ≤ v.assetsTotal.toRat ∧ r.vault'.assetsTotal.toRat.den = 1 ∧
      r.vault'.numericType = v.numericType := by
  have hpar : v.assetsAvailable = v.assetsTotal := Vault.Reachable.asset_parity_proof v hr
  have hL : v.toExact.lossUnrealized = 0 := Vault.Reachable.lossUnrealized_zero_proof v hr
  have hL0 : v.lossUnrealized.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp hL
  have hAnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hAnn : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hSnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
  have hSeq : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hScap : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hSeq]; exact hfit
  have hS1 : 1 ≤ v.sharesTotal.toRat := by
    rw [← hSeq]; exact_mod_cast hpos
  obtain ⟨assets, aN, hpr, haN, haNn, haNv, haNd, hic, hnt, hann, hale⟩ :=
    price_oneShare v hL0 hAnn hcap hAint hS1 hScap hint
  have hcomp := computeWithdrawByShares_ok_of_price v oneShare assets hpr
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure, hcomp]
  have hAAnorm : v.assetsAvailable.isNormalized := v.wf.assetsAvailable_norm
  have hfunds : v.assetsAvailable.operator_lt aN = false := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff _ _ hAAnorm haNn, not_lt, hpar, haNv]
    exact hale
  have hSnn : 0 ≤ v.sharesTotal.toRat := by linarith
  have hSden : v.sharesTotal.toRat.den = 1 := v.wf.sharesTotal_int
  have hSneg := Number.negative_false_of_normalized_nonneg _ hSnorm hSnn
  obtain ⟨sta, hsta⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest hSnorm hSneg hScap
  obtain ⟨hsnt, hsoff, hsneg, hsmv, -⟩ :=
    STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest sta hSnorm hSnn hSden hScap hsta
  have hfin_iff : oneShare.operator_eq sta = true ↔ v.sharesTotal.toRat = 1 := by
    unfold STAmount.operator_eq STAmount.areComparable
    rw [hsnt, hsoff, hsneg, ← hsmv]
    simp only [oneShare, beq_self_eq_true, Bool.true_and, beq_iff_eq]
    constructor
    · intro h; rw [← h]; rfl
    · intro h
      have h1 : sta.mValue.toNat = 1 := by exact_mod_cast h
      exact (UInt64.toNat_inj.mp (by rw [h1]; rfl)).symm
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, haN, hfunds, hsta]
  by_cases hS : v.sharesTotal.toRat = 1
  · rw [if_pos (hfin_iff.mpr hS)]
    have hLz : v.lossUnrealized = Number.zero :=
      Number.eq_zero_of_mantissa_zero _ v.wf.lossUnrealized_norm hL0
    have hAAneg : v.assetsAvailable.negative_ = false := by
      rw [hpar]; exact Number.negative_false_of_normalized_nonneg _ hAnorm hAnn
    obtain ⟨allA, hallA⟩ := STAmount.ofNumber_int64_ok v.assetsAvailable .to_nearest hAAnorm
      hAAneg (by rw [hpar]; exact hcap)
    obtain ⟨v', htl, hv'⟩ := Vault.zero_record_never_notLawful v hL
    rw [← hint] at hallA
    rw [hLz, if_neg (by decide), hallA]
    simp only []
    dsimp only at htl hv'
    rw [hLz] at htl hv'
    rw [htl]
    have hsT : v'.sharesTotal = Number.zero := by
      rw [show v'.sharesTotal = v'.toRawVault.sharesTotal from rfl, hv']
    have haT : v'.assetsTotal = Number.zero := by
      rw [show v'.assetsTotal = v'.toRawVault.assetsTotal from rfl, hv']
    have hnT : v'.numericType = v.numericType := by
      rw [show v'.numericType = v'.toRawVault.numericType from rfl, hv']
    refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_, hnT⟩
    · show v'.sharesTotal.toRat.num.toNat < _
      rw [hsT, Number.toRat_zero]; simpa using hpos
    · show v'.assetsTotal.toRat ≤ _
      rw [haT, Number.toRat_zero]; exact hAnn
    · show v'.assetsTotal.toRat.den = 1
      rw [haT, Number.toRat_zero]; rfl
  · have hfin : oneShare.operator_eq sta = false := by
      rw [Bool.eq_false_iff, ne_eq, hfin_iff]; exact hS
    have hS2 : 2 ≤ v.sharesTotal.toRat := by
      have := rat_one_le_sub_of_lt v.sharesTotal.toRat 1 hSden rfl
        (lt_of_le_of_ne hS1 (Ne.symm hS))
      linarith
    rw [if_neg (by rw [hfin]; decide), clampToSumExponent_neg_int v.assetsTotal assets hic hann]
    simp only []
    rw [frac_int assets hic]
    simp only [Bool.false_eq_true, if_false, haN]
    obtain ⟨sn, hsn, hsnv, hsnn⟩ := oneShare_toNumber
    rw [hsn]
    simp only []
    have hAneg := Number.negative_false_of_normalized_nonneg _ hAnorm hAnn
    have haNnn : 0 ≤ aN.toRat := by rw [haNv]; exact hann
    have haNneg := Number.negative_false_of_normalized_nonneg _ haNn haNnn
    have haNcap : aN.toRat ≤ 2 ^ 63 - 1 := by rw [haNv]; linarith
    obtain ⟨at', hat⟩ := Number.operator_sub_ok_of_normalized_cap v.assetsTotal aN .to_nearest
      hAnorm haNn hAneg haNneg hcap haNcap
    have hdnn : 0 ≤ v.assetsTotal.toRat - aN.toRat := by rw [haNv]; linarith
    have hdd : (v.assetsTotal.toRat - aN.toRat).den = 1 := by
      rw [rat_sub_eq_num_cast _ _ hAint haNd]; exact Rat.den_intCast _
    have hdcap : v.assetsTotal.toRat - aN.toRat ≤ 2 ^ 63 - 1 := by linarith
    obtain ⟨hatv, hatd⟩ := operator_sub_exact_int v.assetsTotal aN at' hAnorm haNn hAint haNd
      (rat_num_natAbs_lt_of_le _ hdd hdnn hdcap) hat
    have hatn : at'.isNormalized := operator_sub_isNormalized_to_nearest' _ _ _ hAnorm haNn hat
    have hatnn : 0 ≤ at'.toRat := by rw [hatv]; exact hdnn
    have hatneg := Number.negative_false_of_normalized_nonneg _ hatn hatnn
    have hatcap : at'.toRat ≤ 2 ^ 63 - 1 := by rw [hatv]; exact hdcap
    rw [hat]
    simp only []
    obtain ⟨atr, hatr⟩ := STAmount.ofNumber_int64_ok v.assetsTotal .to_nearest hAnorm hAneg hcap
    obtain ⟨atr', hatr'⟩ := STAmount.ofNumber_int64_ok at' .to_nearest hatn hatneg hatcap
    obtain ⟨-, -, -, hmv1, -⟩ :=
      STAmount.ofNumber_int64_shape v.assetsTotal .to_nearest atr hAnorm hAnn hAint hcap hatr
    obtain ⟨-, -, -, hmv2, -⟩ :=
      STAmount.ofNumber_int64_shape at' .to_nearest atr' hatn hatnn hatd hatcap hatr'
    rw [← hint] at hatr hatr'
    rw [hatr, hatr']
    simp only []
    have hguard : (aN.mantissa_ != 0 && atr.operator_eq atr') = false := by
      by_cases ham : aN.mantissa_ = 0
      · simp [ham]
      · have hne : atr.mValue ≠ atr'.mValue := by
          intro h
          have h' : (atr.mValue.toNat : ℚ) = (atr'.mValue.toNat : ℚ) := by rw [h]
          rw [hmv1, hmv2, hatv] at h'
          exact ham (Number.toRat_eq_zero_iff.mp (by linarith))
        simp [STAmount.operator_eq, hne]
    have hav : v.assetsAvailable.operator_sub aN .to_nearest = .ok at' := by rw [hpar]; exact hat
    have hsnneg := Number.negative_false_of_normalized_nonneg _ hsnn (by rw [hsnv]; norm_num)
    obtain ⟨st', hst⟩ := Number.operator_sub_ok_of_normalized_cap v.sharesTotal sn .to_nearest
      hSnorm hsnn hSneg hsnneg hScap (by rw [hsnv]; norm_num)
    have hsnd : sn.toRat.den = 1 := by rw [hsnv]; rfl
    have hsdd : (v.sharesTotal.toRat - sn.toRat).den = 1 := by
      rw [rat_sub_eq_num_cast _ _ hSden hsnd]; exact Rat.den_intCast _
    obtain ⟨hstv, -⟩ := operator_sub_exact_int v.sharesTotal sn st' hSnorm hsnn hSden hsnd
      (rat_num_natAbs_lt_of_le _ hsdd (by rw [hsnv]; linarith) (by rw [hsnv]; linarith)) hst
    rw [if_neg (by rw [hguard]; decide), hav, hst]
    simp only []
    obtain ⟨v', htl, hv'⟩ := Vault.subtract_record_never_notLawful v aN sn at' at' st' hL hpar haNn haNnn
      (by rw [haNv]; exact hale) hsnn (by rw [hsnv]; norm_num) hsnd (by rw [hsnv]; linarith)
      hScap hat hav hst (fun h0 => by rw [hstv, hsnv] at h0; linarith)
    dsimp only at htl hv'
    rw [htl]
    have hsT : v'.sharesTotal = st' := by
      rw [show v'.sharesTotal = v'.toRawVault.sharesTotal from rfl, hv']
    have haT : v'.assetsTotal = at' := by
      rw [show v'.assetsTotal = v'.toRawVault.assetsTotal from rfl, hv']
    have hnT : v'.numericType = v.numericType := by
      rw [show v'.numericType = v'.toRawVault.numericType from rfl, hv']
    refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_, hnT⟩
    · show v'.toExact.sharesTotal < v.toExact.sharesTotal
      have h1 : ((v'.toExact.sharesTotal : ℕ) : ℚ) = v'.sharesTotal.toRat :=
        RawVault.WF.toExact_sharesTotal v'.toRawVault v'.wf
      rw [hsT, hstv, hsnv] at h1
      have h2 : ((v'.toExact.sharesTotal : ℕ) : ℚ) < ((v.toExact.sharesTotal : ℕ) : ℚ) := by
        rw [h1, hSeq]; linarith
      exact_mod_cast h2
    · show v'.assetsTotal.toRat ≤ _
      rw [haT, hatv]; linarith
    · show v'.assetsTotal.toRat.den = 1
      rw [haT]; exact hatd

lemma canEmpty_aux : ∀ (n : ℕ) (v : Vault), Vault.Reachable v →
    (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → v.assetsTotal.toRat ≤ 2 ^ 63 - 1 →
    v.numericType = .int64 → v.assetsTotal.toRat.den = 1 →
    v.toExact.sharesTotal = n → CanEmpty v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hr hfit hcap hint hAint hn
    rcases Nat.eq_zero_or_pos n with hz | hposn
    · exact CanEmpty.done v (hn.trans hz)
    · have hpos : 0 < v.toExact.sharesTotal := hn ▸ hposn
      obtain ⟨r, hok, herr, hsb, hdec, hA, hAd, hnt⟩ := step v hr hfit hcap hint hAint hpos
      have hr' : Vault.Reachable r.vault' :=
        Vault.Reachable.withdraw v _ false r hr oneShare_pos hok (by rw [hsb]; exact oneShare_ic)
          (by rw [hsb]; rfl) (by rw [hsb]; rfl)
          (by rw [hsb, oneShare_toRat]; exact_mod_cast hpos) hfit
      have hfit' : (r.vault'.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 := by
        have : (r.vault'.toExact.sharesTotal : ℚ) < (v.toExact.sharesTotal : ℚ) := by
          exact_mod_cast hdec
        linarith
      exact CanEmpty.step v _ r oneShare_pos hok herr
        (ih _ (hn ▸ hdec) r.vault' hr' hfit' (le_trans hA hcap) (hnt.trans hint) hAd rfl)

end XRPL.Model.SingleAssetVault.CanEmp

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.Reachable.canEmpty_proof (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1) : CanEmpty v :=
  CanEmp.canEmpty_aux _ v hr hfit hcap hint hAint rfl

end XRPL.Model.SingleAssetVault
