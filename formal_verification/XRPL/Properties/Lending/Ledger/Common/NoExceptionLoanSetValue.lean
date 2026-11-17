import XRPL.Properties.Lending.Loan.Common.FactorComputes
import XRPL.Properties.Lending.Loan.Common.NextPayment
import XRPL.Properties.Lending.Loan.Common.PayoffComponents
import XRPL.Properties.Lending.Loan.Common.RoundTotal
import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Protocol.STAmount.Range.Success
import XRPL.Properties.Vault.Proofs.Support.NoOverflow

/-! # The values of a new loan compute

A LoanSet computes the periodic rate, the PeriodicPayment, the total value and the fee of its loan before any
check on them. Each step returns a value: the `Number` steps stay far inside the `Number` range, and the amounts
of the asset stay inside the asset's range while PeriodicPayment × PaymentTotal does. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_ge Number.ofInt64_one_toRat from XRPL.Properties.Lending.Loan.Common.SetLawful
open private zero_checks Number.tenth12 computePowerMinusOneHybrid_computes
  from XRPL.Properties.Lending.Loan.Common.FactorComputes
open private loanPeriodicRate_computes from XRPL.Properties.Lending.Loan.Common.NextPayment

local notation "ε" => Number.nearestError

/-- The payment factor computes for a rate of at least `10^-12` with `k` times the rate at most `137`. It is
between `10^-82` and `10^15`. -/
private lemma computePaymentFactor_range (rate : Number) (k : UInt32) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hk0 : k ≠ 0) (hkr : (k.toNat : ℚ) * rate.toRat ≤ 137) :
    ∃ f, computePaymentFactor rate (Number.ofInt64 k.toInt64) k = .ok f ∧ f.isNormalized ∧
      1 / 10 ^ 82 ≤ f.toRat ∧ f.toRat ≤ 10 ^ 15 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hone := Number.ofInt64_isNormalized 1
  have hk1 : (1 : ℚ) ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h0 => hk0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hr0 : 0 ≤ rate.toRat := le_trans (by positivity) hlow
  have hr137 : rate.toRat ≤ 137 := le_trans (le_mul_of_one_le_left hr0 hk1) hkr
  obtain ⟨hk', hz⟩ := zero_checks rate k hrate (lt_of_lt_of_le (by positivity) hlow) hk0
  obtain ⟨⟨w12, hw12N, hw12⟩, -⟩ := Number.tenth12
  obtain ⟨pm, hpm, hpmN, hpmlo, hpmhi⟩ := computePowerMinusOneHybrid_computes rate k hrate hlow hk0 hkr
  have hpm0 : 0 < pm.toRat := lt_of_lt_of_le (by positivity) hpmlo

  -- `1 + pm`
  obtain ⟨rr, hrr⟩ := Number.operator_add_ok_of_abs (Number.ofInt64 1) pm .to_nearest hone hpmN
    (by rw [Number.ofInt64_one_toRat]; norm_num)
    (by rw [abs_of_nonneg hpm0.le]; linarith [show (10 : ℚ) ^ 70 < 10 ^ 200 by norm_num])
  have hrrN := Number.operator_add_isNormalized_to_nearest_sz _ _ rr hone hpmN hrr
  have hrrR := Number.operator_add_rounded_to_nearest _ _ _ hone hpmN hrr
  rw [Number.ofInt64_one_toRat] at hrrR
  have hrr1 : 1 ≤ rr.toRat := by
    have := rn_ge hrrR _ hone (by rw [Number.ofInt64_one_toRat]; linarith)
    rwa [Number.ofInt64_one_toRat] at this
  have hrrle := (Number.add_near _ _ _ hone hpmN hrr).le (by rw [Number.ofInt64_one_toRat]; linarith)
  rw [Number.ofInt64_one_toRat] at hrrle
  have hrrl : rr.toRat ≤ 10 ^ 71 := by
    calc rr.toRat ≤ (1 + pm.toRat) * (1 + ε) := hrrle
      _ ≤ (1 + 10 ^ 70) * 2 := by gcongr; linarith
      _ ≤ 10 ^ 71 := by norm_num

  -- `rate * (1 + pm)`
  obtain ⟨num, hnum⟩ := Number.operator_mul_ok_of_abs rate rr .to_nearest hrate hrrN
    (by rw [abs_of_nonneg hr0]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 71 < 10 ^ 200 by norm_num])
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
  have hnumR := Number.operator_mul_rounded_to_nearest _ _ _ hrate hrrN hnum
  have hnumlo : 1 / 10 ^ 12 ≤ num.toRat := by
    have := rn_ge hnumR w12 hw12N (by rw [hw12]; nlinarith)
    rwa [hw12] at this
  have hnumle := (Number.mul_near _ _ _ hrate hrrN hnum).le (by nlinarith)
  have hnuml : num.toRat ≤ 10 ^ 75 := by
    calc num.toRat ≤ rate.toRat * rr.toRat * (1 + ε) := hnumle
      _ ≤ 137 * 10 ^ 71 * 2 := by gcongr; linarith
      _ ≤ 10 ^ 75 := by norm_num

  -- the factor `rate * (1 + pm) / pm`
  obtain ⟨f, hf⟩ := Number.operator_div_ok_of_abs num pm .to_nearest hnumN hpmN
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 75 < 10 ^ 200 by norm_num])
    (by
      rw [abs_of_nonneg hpm0.le]
      refine le_trans ?_ hpmlo
      rw [zpow_neg]; norm_num)
  have hfN := Number.operator_div_isNormalized _ _ f _ hnumN hpmN hf
  obtain ⟨w82, hw82N, hw82⟩ := Number.exists_normalized_int_mul_pow 1 (-82) (by norm_num)
    (by unfold minExponent maxExponent; norm_num)
  have hflo : 1 / 10 ^ 82 ≤ f.toRat := by
    have hq : (1 : ℚ) / 10 ^ 82 ≤ num.toRat / pm.toRat := by
      rw [le_div_iff₀ hpm0]
      calc 1 / 10 ^ 82 * pm.toRat ≤ 1 / 10 ^ 82 * 10 ^ 70 := by gcongr
        _ ≤ 1 / 10 ^ 12 := by norm_num
        _ ≤ num.toRat := hnumlo
    have := rn_ge (Number.operator_div_rounded_to_nearest _ _ _ hnumN hpmN hf) w82 hw82N
      (by rw [hw82]; norm_num at hq ⊢; linarith)
    rw [hw82] at this
    norm_num at this ⊢
    linarith

  -- above, the factor is `rate * (1 + 1 / pm)` and three roundings
  have hfhi : f.toRat ≤ 10 ^ 15 := by
    have hfle := (Number.div_near _ _ _ hnumN hpmN hf).le (div_nonneg (by linarith) hpm0.le)
    have h3 : (1 + ε) * (1 + ε) * (1 + ε) ≤ 2 := by nlinarith
    have hinv : 1 / pm.toRat ≤ 10 ^ 12 := by
      rw [div_le_iff₀ hpm0]
      calc (1 : ℚ) = 10 ^ 12 * (1 / 10 ^ 12) := by norm_num
        _ ≤ 10 ^ 12 * pm.toRat := by gcongr
    have hq : num.toRat / pm.toRat ≤ rate.toRat * (1 / pm.toRat + 1) * ((1 + ε) * (1 + ε)) := by
      rw [div_le_iff₀ hpm0]
      calc num.toRat ≤ rate.toRat * rr.toRat * (1 + ε) := hnumle
        _ ≤ rate.toRat * ((1 + pm.toRat) * (1 + ε)) * (1 + ε) := by gcongr
        _ = rate.toRat * (1 / pm.toRat + 1) * ((1 + ε) * (1 + ε)) * pm.toRat := by
            field_simp
    calc f.toRat ≤ num.toRat / pm.toRat * (1 + ε) := hfle
      _ ≤ rate.toRat * (1 / pm.toRat + 1) * ((1 + ε) * (1 + ε)) * (1 + ε) := by gcongr
      _ = rate.toRat * (1 / pm.toRat + 1) * ((1 + ε) * (1 + ε) * (1 + ε)) := by ring
      _ ≤ 137 * (10 ^ 12 + 1) * 2 := by gcongr
      _ ≤ 10 ^ 15 := by norm_num

  refine ⟨f, ?_, hfN, hflo, hfhi⟩
  unfold computePaymentFactor
  rw [hk', if_neg (by decide)]
  dsimp only
  rw [pure_bind, hz, if_neg (by decide), hpm, ok_bind, hrr, ok_bind, hnum, ok_bind, hf]

/-- `k` payment intervals fit the 32-bit clock, so `k` times the periodic rate is at most `137`. -/
private lemma count_mul_rate_le (rate : Number) (ir : TenthBips32) (interval k : UInt32)
    (hrate : loanPeriodicRate ir interval = .ok rate) (hir : ir.toNat ≤ 100000)
    (hk : k.toNat * interval.toNat < 2 ^ 32) : (k.toNat : ℚ) * rate.toRat ≤ 137 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hup, -⟩ := loanPeriodicRate_bounds ir interval rate hrate
  have hki : (k.toNat : ℚ) * interval.toNat ≤ 2 ^ 32 := by exact_mod_cast hk.le
  have hirq : (ir.toNat : ℚ) ≤ 100000 := by exact_mod_cast hir
  have hk0' : (0 : ℚ) ≤ k.toNat := by positivity
  have he3 : (1 + ε) ^ 3 ≤ 1 + 1 / 10 ^ 9 := by
    have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
    push_cast at this; linarith
  calc (k.toNat : ℚ) * rate.toRat
      ≤ k.toNat * (interval.toNat * ir.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3) := by gcongr
    _ = (k.toNat * interval.toNat) * ir.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 := by ring
    _ ≤ 2 ^ 32 * 100000 / (10 ^ 5 * 31536000) * (1 + 1 / 10 ^ 9) := by gcongr
    _ ≤ 137 := by norm_num

/-- The PeriodicPayment of a LoanSet computes. It is at least zero and at most `10^16` times the principal. -/
lemma loanPeriodicPayment_range (principal rate : Number) (ir : TenthBips32) (interval n : UInt32)
    (hrate : loanPeriodicRate ir interval = .ok rate) (hir : ir.toNat ≤ 100000) (hiv : 60 ≤ interval.toNat)
    (hn0 : n ≠ 0) (hk : n.toNat * interval.toNat < 2 ^ 32) (hp : principal.isNormalized)
    (hpos : 0 < principal.toRat) (hpl : principal.toRat < 10 ^ 100) :
    ∃ pp, loanPeriodicPayment principal rate n = .ok pp ∧ pp.isNormalized ∧ 0 ≤ pp.toRat ∧
      pp.toRat ≤ principal.toRat * 10 ^ 16 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hrN := loanPeriodicRate_isNormalized ir interval rate hrate
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hn32 : (n.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast n.toNat_lt
  have hn1 : (1 : ℚ) ≤ n.toNat := by
    have : n.toNat ≠ 0 := fun h0 => hn0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hpz : principal.operator_eq Number.zero = false := by
    cases hc : principal.operator_eq Number.zero
    · rfl
    · have := (Number.operator_eq_iff principal Number.zero hp Number.zero_isNormalized).mp hc
      rw [Number.toRat_zero] at this
      linarith
  have hn' : (n == 0) = false := by simpa using hn0
  have hpabs : |principal.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg hpos.le]; linarith [show (10 : ℚ) ^ 100 < 10 ^ 200 by norm_num]
  unfold loanPeriodicPayment
  rw [hpz, hn']
  simp only [Bool.or_self, Bool.false_eq_true, if_false]
  by_cases hz : rate.operator_eq Number.zero = true

  · -- no interest: the principal over the count
    rw [if_pos hz]
    obtain ⟨pp, hpp⟩ := Number.operator_div_ok_of_abs principal _ .to_nearest hp hN hpabs
      (by
        rw [hNv, abs_of_nonneg (by positivity)]
        refine le_trans ?_ hn1
        rw [zpow_neg]; norm_num)
    have hnear := Number.div_near _ _ _ hp hN hpp
    rw [hNv] at hnear
    have hq0 : 0 ≤ principal.toRat / n.toNat := div_nonneg hpos.le (by positivity)
    refine ⟨pp, hpp, Number.operator_div_isNormalized _ _ pp _ hp hN hpp, hnear.nonneg hq0, ?_⟩
    calc pp.toRat ≤ principal.toRat / n.toNat * (1 + ε) := hnear.le hq0
      _ ≤ principal.toRat / 1 * 2 := by gcongr; linarith
      _ ≤ principal.toRat * 10 ^ 16 := by rw [div_one]; nlinarith

  · -- interest: the principal times the payment factor
    rw [if_neg hz]
    have hr00 : rate.toRat ≠ 0 := fun h0 =>
      hz ((Number.operator_eq_iff rate Number.zero hrN Number.zero_isNormalized).mpr (by
        rw [h0, Number.toRat_zero]))
    have hlow := loanPeriodicRate_ge ir interval rate hiv hrate hr00
    have hkr := count_mul_rate_le rate ir interval n hrate hir hk
    obtain ⟨f, hf, hfN, hflo, hfhi⟩ := computePaymentFactor_range rate n hrN hlow hn0 hkr
    have hf0 : 0 ≤ f.toRat := le_trans (by positivity) hflo
    obtain ⟨pp, hpp⟩ := Number.operator_mul_ok_of_abs principal f .to_nearest hp hfN hpabs
      (by rw [abs_of_nonneg hf0]; linarith [show (10 : ℚ) ^ 15 < 10 ^ 200 by norm_num])
    have hnear := Number.mul_near _ _ _ hp hfN hpp
    have hq0 : 0 ≤ principal.toRat * f.toRat := mul_nonneg hpos.le hf0
    refine ⟨pp, ?_, Number.operator_mul_isNormalized _ _ pp _ hp hfN hpp, hnear.nonneg hq0, ?_⟩
    · rw [hf, ok_bind, hpp]; rfl
    · calc pp.toRat ≤ principal.toRat * f.toRat * (1 + ε) := hnear.le hq0
        _ ≤ principal.toRat * 10 ^ 15 * 2 := by gcongr; linarith
        _ ≤ principal.toRat * 10 ^ 16 := by nlinarith

/-- A `Number` the asset stores exactly rounds into the asset's range. -/
private lemma STAmount.roundsInRange_of_isRounded_false (nt : NumericType) (x : Number) (hx : x.isNormalized)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (h : STAmount.isRounded nt x = false) : STAmount.RoundsInRange nt .to_nearest x.toRat := by
  unfold STAmount.isRounded at h
  cases heq : STAmount.equalAfterNumberConvert nt x with
  | error e => rw [heq] at h; cases h
  | ok b =>
    unfold STAmount.equalAfterNumberConvert at heq
    obtain ⟨st, hst, -⟩ := bind_ok_peel _ _ _ heq
    exact (STAmount.ofNumber_ok_iff nt x .to_nearest hx hnt (Or.inr (Or.inl rfl))).mp ⟨st, hst⟩

/-- XRP or an MPT: a value from zero up to the asset's maximum rounds into the asset's range. -/
private lemma STAmount.roundsInRange_of_le_max (nt : NumericType)
    (hnt : nt = NumericType.native ∨ nt = NumericType.int64) (mode : rounding_mode) (v : ℚ) (h0 : 0 ≤ v)
    (hle : v ≤ nt.maxValue.toNat) : STAmount.RoundsInRange nt mode v := by
  rcases hnt with rfl | rfl <;> cases mode <;>
    simp only [STAmount.RoundsInRange, NumericType.native, NumericType.int64, NumericType.maxValue] at hle ⊢
  all_goals first
    | (left; rw [abs_of_nonneg h0]; linarith)
    | (rw [abs_of_nonneg h0]; linarith)
    | (constructor <;> linarith)

/-- XRP or an MPT: a value that rounds to nearest into the asset's range is at most half a unit above the
maximum. -/
private lemma STAmount.le_max_of_roundsInRange (nt : NumericType)
    (hnt : nt = NumericType.native ∨ nt = NumericType.int64) (v : ℚ)
    (h : STAmount.RoundsInRange nt .to_nearest v) : |v| ≤ (nt.maxValue.toNat : ℚ) + 1 / 2 := by
  rcases hnt with rfl | rfl <;>
    simp only [STAmount.RoundsInRange, NumericType.native, NumericType.int64, NumericType.maxValue] at h ⊢
  all_goals
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le

/-- XRP or an MPT: a nonnegative `Number` that rounds into the asset's range rounds to an amount of it. -/
private lemma STAmount.roundToNumericType_integral_of_inRange (nt : NumericType)
    (hnt : nt = NumericType.native ∨ nt = NumericType.int64) (x : Number) (mode : rounding_mode) (s : Option Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hin : STAmount.RoundsInRange nt mode x.toRat) :
    ∃ y, STAmount.roundToNumericType nt x mode s = .ok y := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  obtain ⟨ret, hret⟩ := (STAmount.ofNumber_ok_iff nt x mode hx (Or.inr hnt) (Or.inl h0)).mpr hin
  obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical nt x mode ret hint hret
  have hret_int : ret.integral = true := by
    unfold STAmount.integral; rw [hrnt]; exact hint
  obtain ⟨y, hy, -, -, -⟩ := STAmount.toNumber_integral_exact ret mode hc (by rw [hrnt]; exact hmr)
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  cases s with
  | none => exact hy
  | some s => simp only [hret_int, ↓reduceIte]; exact hy

/-- An IOU amount converted from a value below `10^45` in size has an exponent at most `30`. -/
private lemma STAmount.ofNumber_fractional_exponent_le (n : Number) (mode : rounding_mode) (a : STAmount)
    (hn : n.isNormalized) (hlt : |n.toRat| < 10 ^ 45) (hok : STAmount.ofNumber .fractional n mode = .ok a) :
    a.exponent ≤ 30 := by
  show a.mOffset ≤ 30
  rcases (STAmount.ofNumber_fractional_fczr n mode a hok).2 with hc | hz
  · have hm : a.mValue ≠ 0 := fun h => by have := hc.mant_lo; rw [h] at this; simp at this
    have hn0 := STAmount.ofNumber_source_ne_zero _ n mode a hok hm
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hn0
    have hnlt := Number.exponent_lt_of_abs_lt n hn hn0 27 (by norm_num; exact hlt)
    have hemin := Number.exponent_ge_min n hn hn0
    obtain ⟨hb, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional n mode a rfl hlo hhi hemin
      (by unfold maxExponent; omega) hok hm
    by_contra hcon
    push Not at hcon
    have h3 : (10 : ℚ) ^ (n.exponent_ + 3) ≤ 10 ^ (30 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have habs : |a.toRat| ≤ 10 ^ 45 + 10 ^ 30 := by
      have := abs_sub_abs_le_abs_sub a.toRat n.toRat
      norm_num at h3
      linarith
    rw [STAmount.abs_toRat] at habs
    have hm15 : (10 : ℚ) ^ 15 ≤ a.mValue.toNat := by exact_mod_cast hc.mant_lo
    have h31 : (10 : ℚ) ^ (31 : ℤ) ≤ 10 ^ a.mOffset := zpow_le_zpow_right₀ (by norm_num) hcon
    have : (10 : ℚ) ^ 15 * 10 ^ (31 : ℤ) ≤ a.mValue.toNat * 10 ^ a.mOffset :=
      mul_le_mul hm15 h31 (by positivity) (by positivity)
    norm_num at this
    linarith
  · have hoff : a.mOffset = -100 := by
      rw [STAmount.ofNumber] at hok
      split at hok
      · exact absurd ‹NumericType.fractional.isIntegral = true› (by decide)
      · split at hok
        · exact absurd hok (by simp)
        · obtain ⟨v, -, hok⟩ := bind_ok_peel _ _ _ hok
          rw [STAmount.checked] at hok
          exact STAmount.canonicalize_fractional_zero_offset _ a mode rfl hok hz
    omega

/-- The theoretical principal of a normalized PeriodicPayment and rate is normalized. -/
private lemma loanPrincipalFromPeriodicPayment_normalized_of_ok (pp rate : Number) (k : UInt32) (tpo : Number)
    (hpp : pp.isNormalized) (hrate : rate.isNormalized)
    (h : loanPrincipalFromPeriodicPayment pp rate k = .ok tpo) : tpo.isNormalized := by
  have hN := Number.ofInt64_isNormalized k.toInt64
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact Number.zero_isNormalized
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · exact Number.operator_mul_isNormalized _ _ tpo _ hpp hN h
  · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
    exact Number.operator_div_isNormalized _ _ tpo _ hpp (computePaymentFactor_isNormalized _ _ _ f hrate hN hf) h

/-- The rounded values a LoanSet computes from its raw total value `amount`, and their sizes. `amountSt` is the
total value as an amount, whose exponent sets LoanScale. -/
private def LoanValueSteps (nt : NumericType) (amount principal : Number) (mode : rounding_mode) (mgmt : TenthBips16)
    (minScale : Int) (amountSt : STAmount) (tvo rp ti mfo : Number) : Prop :=
  STAmount.ofNumber nt amount mode = .ok amountSt ∧
  STAmount.roundToNumericType nt amount mode (some (max minScale amountSt.exponent)) = .ok tvo ∧
  STAmount.roundToNumericType nt principal .to_nearest (some (max minScale amountSt.exponent)) = .ok rp ∧
  tvo.operator_sub rp .to_nearest = .ok ti ∧
  computeManagementFee nt ti mgmt (max minScale amountSt.exponent) = .ok mfo ∧
  (-10 ≤ max minScale amountSt.exponent ∧ max minScale amountSt.exponent ≤ 30) ∧
  (nt.isIntegral = true → max minScale amountSt.exponent = 0) ∧
  tvo.isNormalized ∧ 0 ≤ tvo.toRat ∧
  (∃ k : ℕ, k < 2 ^ 63 ∧ tvo.toRat = (k : ℚ) * 10 ^ max minScale amountSt.exponent) ∧
  mfo.isNormalized ∧ |mfo.toRat| < 10 ^ 100

/-- The management fee rate of a broker as a rational is at most `10000` tenth bips. -/
private lemma mgmt_toNat_le (mgmt : TenthBips16) (hmgmt : mgmt.toNat ≤ 10000) :
    (mgmt.toTenthBips32.toNat : ℚ) ≤ 10000 := by
  show ((mgmt.toUInt32).toNat : ℚ) ≤ 10000
  rw [UInt16.toNat_toUInt32]; exact_mod_cast hmgmt

/-- XRP or an MPT: the rounded values compute when the raw total value is within the asset's maximum. -/
private lemma loanValueSteps_integral (nt : NumericType) (hnt : nt = NumericType.native ∨ nt = NumericType.int64)
    (amount principal : Number) (mode : rounding_mode) (mgmt : TenthBips16) (minScale : Int)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hscale : -10 ≤ minScale ∧ minScale ≤ 0)
    (hmgmt : mgmt.toNat ≤ 10000) (hamountN : amount.isNormalized) (hamount0 : 0 ≤ amount.toRat)
    (hamountM : amount.toRat ≤ nt.maxValue.toNat) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hstR : STAmount.RoundsInRange nt .to_nearest principal.toRat) :
    ∃ amountSt tvo rp ti mfo, LoanValueSteps nt amount principal mode mgmt minScale amountSt tvo rp ti mfo := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hM17n : 10 ^ 17 ≤ nt.maxValue.toNat := by rcases hnt with rfl | rfl <;> decide
  have hM17 : (10 : ℚ) ^ 17 ≤ nt.maxValue.toNat := by exact_mod_cast hM17n
  have hM63n : nt.maxValue.toNat ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
  have hM63 : (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hM63n
  have hmbn' : nt.mantissaBound = nt.maxValue.toNat + 1 := by rcases hnt with rfl | rfl <;> decide
  have hmb : (nt.mantissaBound : ℚ) = nt.maxValue.toNat + 1 := by rw [hmbn']; push_cast; ring
  have hmbn : nt.mantissaBound ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
  have hin := STAmount.roundsInRange_of_le_max nt hnt mode amount.toRat hamount0 hamountM

  -- the total value as an amount, at exponent zero
  obtain ⟨amountSt, hst⟩ :=
    (STAmount.ofNumber_ok_iff nt amount mode hamountN (Or.inr hnt) (Or.inl hamount0)).mpr hin
  have hoff := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint hst).1.offset_zero
  have hls : max minScale amountSt.exponent = 0 := by
    unfold STAmount.exponent; rw [hoff]; exact max_eq_right hscale.2

  -- the rounded total value and principal
  obtain ⟨tvo, htvo⟩ :=
    STAmount.roundToNumericType_integral_of_inRange nt hnt amount mode (some 0) hamountN hamount0 hin
  obtain ⟨rp, hrp⟩ :=
    STAmount.roundToNumericType_integral_of_inRange nt hnt principal .to_nearest (some 0) hp hpos.le hstR
  have htvoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hrpN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrp
  have htvo0 := STAmount.roundToNumericType_some_nonneg nt amount tvo mode 0 hamountN hamount0 hmode
    ⟨by norm_num, by norm_num⟩ htvo
  have hrp0 := STAmount.roundToNumericType_some_nonneg nt principal rp .to_nearest 0 hp hpos.le (Or.inl rfl)
    ⟨by norm_num, by norm_num⟩ hrp
  have htvolt := STAmount.roundToNumericType_int_lt_bound nt hint amount tvo mode (some 0) hamountN hamount0 htvo
  have hrplt := STAmount.roundToNumericType_int_lt_bound nt hint principal rp .to_nearest (some 0) hp hpos.le hrp
  obtain ⟨-, ⟨k, hk⟩, -, -⟩ :=
    STAmount.roundToNumericType_int_grid nt hint amount tvo mode (some 0) hamountN hamount0 hmode htvo
  have hk63 : k < 2 ^ 63 := by
    have : (k : ℚ) < nt.mantissaBound := by rw [← hk]; exact htvolt
    have : k < nt.mantissaBound := by exact_mod_cast this
    omega
  rw [hmb] at htvolt hrplt

  -- the interest
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs tvo rp .to_nearest htvoN hrpN
    (by rw [abs_of_nonneg htvo0]; linarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hrp0]; linarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 200 by norm_num])
  have htiN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ htvoN hrpN hti
  have htiabs : |ti.toRat| ≤ (nt.maxValue.toNat + 1) * (1 + ε) := by
    refine le_trans (Number.sub_near _ _ _ htvoN hrpN hti).abs_le ?_
    gcongr
    rw [abs_le]; constructor <;> linarith

  -- the fee is at most a tenth of it
  obtain ⟨raw, hraw, hrawN, hrawabs⟩ := tenthBipsOfValue_ok_of_abs ti mgmt.toTenthBips32 htiN
    (lt_of_le_of_lt htiabs (by nlinarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 180 by norm_num]))
  have hrawM : |raw.toRat| + 1 ≤ nt.maxValue.toNat := by
    have h3 : (1 + ε) * (1 + ε) ^ 2 ≤ 2 := by nlinarith
    have hq := mgmt_toNat_le mgmt hmgmt
    have : |raw.toRat| ≤ (nt.maxValue.toNat + 1) * (1 + ε) * 10000 / 100000 * (1 + ε) ^ 2 :=
      le_trans hrawabs (by gcongr)
    nlinarith
  obtain ⟨mfo, hmfo, hmfoN, hmfoabs⟩ :=
    STAmount.roundToNumericType_integral_ok_abs nt raw .downward (some 0) hnt hrawN hrawM

  refine ⟨amountSt, tvo, rp, ti, mfo, hst, ?_, ?_, hti, ?_, ?_, fun _ => hls, htvoN, htvo0, ⟨k, hk63, ?_⟩, hmfoN,
    ?_⟩
  · rw [hls]; exact htvo
  · rw [hls]; exact hrp
  · rw [hls]; unfold computeManagementFee; rw [hraw, ok_bind, hmfo]
  · rw [hls]; norm_num
  · rw [hls, hk]; simp
  · linarith [show (2 : ℚ) ^ 63 * 2 + 1 < 10 ^ 100 by norm_num]

/-- An IOU: the rounded values compute for a raw total value below `10^42` and a principal below `10^16`. -/
private lemma loanValueSteps_frac (amount principal : Number) (mode : rounding_mode) (mgmt : TenthBips16)
    (minScale : Int) (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hscale : -10 ≤ minScale ∧ minScale ≤ 0) (hmgmt : mgmt.toNat ≤ 10000) (hamountN : amount.isNormalized)
    (hamount0 : 0 ≤ amount.toRat) (hamountlt : amount.toRat < 10 ^ 42) (hp : principal.isNormalized)
    (hpos : 0 < principal.toRat) (hp16 : principal.toRat < 10 ^ 16) :
    ∃ amountSt tvo rp ti mfo,
      LoanValueSteps .fractional amount principal mode mgmt minScale amountSt tvo rp ti mfo := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have habs : |amount.toRat| = amount.toRat := abs_of_nonneg hamount0
  have hpabs : |principal.toRat| = principal.toRat := abs_of_nonneg hpos.le

  -- the total value as an amount, at an exponent of at most 30
  obtain ⟨amountSt, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr amount mode hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 90 by norm_num])
  have hexp := STAmount.ofNumber_fractional_exponent_le amount mode amountSt hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 45 by norm_num]) hst
  obtain ⟨ls, hlsdef⟩ : ∃ ls, max minScale amountSt.exponent = ls := ⟨_, rfl⟩
  have hls : -10 ≤ ls ∧ ls ≤ 30 := by
    rw [← hlsdef]; exact ⟨le_max_of_le_left hscale.1, max_le (by linarith [hscale.2]) hexp⟩
  have hp10 : (10 : ℚ) ^ ls ≤ 10 ^ 30 := by
    have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hls.2
    norm_num at this ⊢
    exact this
  have hp0 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _

  -- the rounded total value and principal
  obtain ⟨tvo, htvo, htvoN, htvoabs⟩ := STAmount.roundToNumericType_frac_ok_abs amount mode ls hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 90 by norm_num]) ⟨by omega, by omega⟩
  obtain ⟨rp, hrp, hrpN, hrpabs⟩ := STAmount.roundToNumericType_frac_ok_abs principal .to_nearest ls hp
    (by rw [hpabs]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 90 by norm_num]) ⟨by omega, by omega⟩
  have htvo0 := STAmount.roundToNumericType_some_nonneg .fractional amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ htvo
  have hexp' : ∀ st, STAmount.ofNumber .fractional amount mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ ls :=
    fun st hst2 _ => by
      rw [hst, Except.ok.injEq] at hst2
      rw [← hst2, ← hlsdef]; exact le_max_right _ _
  obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_frac_grid amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ hexp' htvo
  have hle := STAmount.roundToNumericType_frac_le amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ hexp' htvo
  have hk63 : k < 2 ^ 63 := by
    rw [hk] at hle
    have : k ≤ 10 ^ 16 - 1 := by exact_mod_cast le_of_mul_le_mul_right hle hp0
    omega
  rw [habs] at htvoabs
  rw [hpabs] at hrpabs

  -- the interest
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs tvo rp .to_nearest htvoN hrpN
    (by linarith [show (2 : ℚ) * 10 ^ 42 + 10 ^ 30 < 10 ^ 200 by norm_num])
    (by linarith [show (2 : ℚ) * 10 ^ 16 + 10 ^ 30 < 10 ^ 200 by norm_num])
  have htiN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ htvoN hrpN hti
  have htiabs : |ti.toRat| ≤ 10 ^ 44 := by
    refine le_trans (Number.sub_near _ _ _ htvoN hrpN hti).abs_le ?_
    have h1 : |tvo.toRat - rp.toRat| ≤ |tvo.toRat| + |rp.toRat| := abs_sub _ _
    have h2 : |tvo.toRat - rp.toRat| ≤ 10 ^ 43 := by
      linarith [show (2 : ℚ) * 10 ^ 42 + 10 ^ 30 + (2 * 10 ^ 16 + 10 ^ 30) ≤ 10 ^ 43 by norm_num]
    calc |tvo.toRat - rp.toRat| * (1 + ε) ≤ 10 ^ 43 * 2 := by gcongr; linarith
      _ ≤ 10 ^ 44 := by norm_num

  -- the fee is at most a tenth of it
  obtain ⟨raw, hraw, hrawN, hrawabs⟩ := tenthBipsOfValue_ok_of_abs ti mgmt.toTenthBips32 htiN
    (lt_of_le_of_lt htiabs (by norm_num))
  have hraw45 : |raw.toRat| ≤ 10 ^ 44 := by
    have h2 : (1 + ε) ^ 2 ≤ 2 := by nlinarith
    have hq := mgmt_toNat_le mgmt hmgmt
    calc |raw.toRat| ≤ |ti.toRat| * mgmt.toTenthBips32.toNat / 100000 * (1 + ε) ^ 2 := hrawabs
      _ ≤ 10 ^ 44 * 10000 / 100000 * 2 := by gcongr
      _ ≤ 10 ^ 44 := by norm_num
  obtain ⟨mfo, hmfo, hmfoN, hmfoabs⟩ := STAmount.roundToNumericType_frac_ok_abs raw .downward ls hrawN
    (lt_of_le_of_lt hraw45 (by norm_num)) ⟨by omega, by omega⟩

  refine ⟨amountSt, tvo, rp, ti, mfo, ?_⟩
  unfold LoanValueSteps
  rw [hlsdef]
  refine ⟨hst, htvo, hrp, hti, ?_, hls, fun h => absurd h (by decide), htvoN, htvo0, ⟨k, hk63, hk⟩, hmfoN, ?_⟩
  · unfold computeManagementFee; rw [hraw, ok_bind, hmfo]
  · linarith [show (2 : ℚ) * 10 ^ 44 + 10 ^ 30 < 10 ^ 100 by norm_num]

/-- The sizes of the values a LoanSet computed, which the checks after them rely on. -/
structure LoanProperties.SetSizes (props : LoanProperties) (nt : NumericType) : Prop where
  periodicPayment_norm : props.periodicPayment.isNormalized
  periodicPayment_nonneg : 0 ≤ props.periodicPayment.toRat
  periodicPayment_lt : props.periodicPayment.toRat < 10 ^ 36
  -- XRP or an MPT: the payment is within the asset's maximum
  periodicPayment_max : nt.isIntegral = true → props.periodicPayment.toRat ≤ nt.maxValue.toNat
  totalValue_norm : props.totalValueOutstanding.isNormalized
  totalValue_nonneg : 0 ≤ props.totalValueOutstanding.toRat
  totalValue_units : ∃ k : ℕ, k < 2 ^ 63 ∧ props.totalValueOutstanding.toRat = (k : ℚ) * 10 ^ props.loanScale
  managementFee_norm : props.managementFeeOutstanding.isNormalized
  managementFee_abs : |props.managementFeeOutstanding.toRat| < 10 ^ 100
  loanScale_range : -10 ≤ props.loanScale ∧ props.loanScale ≤ 30
  loanScale_integral : nt.isIntegral = true → props.loanScale = 0

/-- The loan properties of a LoanSet compute. `hfrac` - an IOU principal is below `10^16`, as the vault at its base
scale holds it. `hvalue` - on XRP or an MPT, PeriodicPayment × PaymentTotal is within the asset's maximum. -/
lemma computeLoanProperties_computes (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (hp : principal.isNormalized)
    (hpos : 0 < principal.toRat) (hst : STAmount.isRounded nt principal = false) (hir : ir.toNat ≤ 100000)
    (hiv : 60 ≤ interval.toNat) (hn0 : n ≠ 0) (hk : n.toNat * interval.toNat < 2 ^ 32)
    (hmgmt : mgmt.toNat ≤ 10000)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hscale : -10 ≤ minScale ∧ minScale ≤ 0) (hfrac : nt = .fractional → principal.toRat < 10 ^ 16)
    (hvalue : nt.isIntegral = true → ∀ rate pp : Number, loanPeriodicRate ir interval = .ok rate →
      loanPeriodicPayment principal rate n = .ok pp → pp.toRat * n.toNat ≤ nt.maxValue.toNat) :
    ∃ props, computeLoanProperties principal ir interval n mgmt nt minScale = .ok props ∧ props.SetSizes nt := by
  have hstR := STAmount.roundsInRange_of_isRounded_false nt principal hp hnt hst
  have hint_cases : nt = .fractional ∨ (nt = NumericType.native ∨ nt = NumericType.int64) := hnt
  have hM63 : nt.isIntegral = true → (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by
    intro hi
    have : nt.maxValue.toNat ≤ 2 ^ 63 := by
      rcases hnt with rfl | rfl | rfl
      · cases hi
      all_goals decide
    exact_mod_cast this

  -- the principal is below `10^20`
  have hp20 : principal.toRat < 10 ^ 20 := by
    rcases hint_cases with hfr | hnt'
    · linarith [hfrac hfr, show (10 : ℚ) ^ 16 < 10 ^ 20 by norm_num]
    · have := STAmount.le_max_of_roundsInRange nt hnt' _ hstR
      rw [abs_of_nonneg hpos.le] at this
      have hm := hM63 (by rcases hnt' with rfl | rfl <;> rfl)
      linarith [show (2 : ℚ) ^ 63 + 1 / 2 < 10 ^ 20 by norm_num]

  -- the periodic rate and the periodic payment
  obtain ⟨rate, hrate⟩ := loanPeriodicRate_computes ir interval
  have hrN := loanPeriodicRate_isNormalized ir interval rate hrate
  have hr0 := loanPeriodicRate_nonneg ir interval rate hrate
  obtain ⟨pp, hpp, hppN, hpp0, hpple⟩ := loanPeriodicPayment_range principal rate ir interval n hrate hir hiv hn0
    hk hp hpos (by linarith [show (10 : ℚ) ^ 20 < 10 ^ 100 by norm_num])
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hn32 : (n.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast n.toNat_lt
  have hnn : n.toNat ≠ 0 := fun h0 => hn0 (UInt32.toNat_inj.mp (by simpa using h0))
  have hn1 : (1 : ℚ) ≤ n.toNat := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnn
  have hpp36 : pp.toRat < 10 ^ 36 := by nlinarith

  -- the raw total value
  obtain ⟨amount, hamount⟩ := Number.operator_mul_ok_of_abs pp (Number.ofInt64 n.toInt64) (valueMode rate) hppN hN
    (by rw [abs_of_nonneg hpp0]; linarith [show (10 : ℚ) ^ 36 < 10 ^ 200 by norm_num])
    (by rw [hNv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num])
  have hamountN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamount
  have hmode : valueMode rate = .to_nearest ∨ valueMode rate = .upward ∨ valueMode rate = .downward :=
    (valueMode_cases rate).elim Or.inl (fun h => Or.inr (Or.inl h))
  have hamount0 : 0 ≤ amount.toRat := by
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamount h0
      have := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by
        rw [Number.toRat_zero, hNv]; positivity)
      rwa [Number.toRat_zero] at this
  have hamount_le : ∀ w : Number, w.isNormalized → pp.toRat * n.toNat ≤ w.toRat → amount.toRat ≤ w.toRat := by
    intro w hw hle
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]; exact le_trans (by positivity) hle
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamount h0
      exact hR.le_of_ge hmode w hw (by rw [hNv]; exact hle)

  -- the rounded values, by asset
  obtain ⟨amountSt, tvo, rp, ti, mfo, hst', htvo, hrp, hti, hmfo, hls, hlsi, htvoN, htvo0, hunits, hmfoN, hmfoabs⟩ :
      ∃ amountSt tvo rp ti mfo,
        LoanValueSteps nt amount principal (valueMode rate) mgmt minScale amountSt tvo rp ti mfo := by
    rcases hint_cases with hfr | hnt'
    · subst hfr
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 5 41 (by norm_num)
        (by unfold minExponent maxExponent; norm_num)
      have hlt : amount.toRat < 10 ^ 42 := by
        have := hamount_le w hw (by
          rw [hwv]
          have hpp32 : pp.toRat ≤ 10 ^ 16 * 10 ^ 16 := by nlinarith [hfrac rfl]
          calc pp.toRat * n.toNat ≤ 10 ^ 16 * 10 ^ 16 * 2 ^ 32 := by gcongr
            _ ≤ ((5 : ℤ) : ℚ) * 10 ^ (41 : ℤ) := by norm_num)
        rw [hwv] at this
        norm_num at this ⊢
        linarith
      exact loanValueSteps_frac amount principal _ mgmt minScale hmode hscale hmgmt hamountN hamount0 hlt hp hpos
        (hfrac rfl)
    · have hint : nt.isIntegral = true := by rcases hnt' with rfl | rfl <;> rfl
      have hM := hM63 hint
      have hMn : nt.maxValue.toNat < 2 ^ 63 := by rcases hnt' with rfl | rfl <;> decide
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (nt.maxValue.toNat : ℤ) 0
        ⟨by have : (0 : ℤ) ≤ (nt.maxValue.toNat : ℤ) := by positivity
            linarith, by exact_mod_cast hMn⟩
        (by unfold minExponent maxExponent; norm_num)
      have hwv' : w.toRat = (nt.maxValue.toNat : ℚ) := by rw [hwv]; simp
      have hle : amount.toRat ≤ nt.maxValue.toNat := by
        have := hamount_le w hw (by rw [hwv']; exact hvalue hint rate pp hrate hpp)
        rwa [hwv'] at this
      exact loanValueSteps_integral nt hnt' amount principal _ mgmt minScale hmode hscale hmgmt hamountN hamount0
        hle hp hpos hstR

  -- the principal part of the first payment
  have hpp100 : pp.toRat < 10 ^ 100 := by linarith [show (10 : ℚ) ^ 36 < 10 ^ 100 by norm_num]
  obtain ⟨tpo, htpo⟩ := loanPrincipalFromPeriodicPayment_computes pp rate ir interval n hrate hir hiv hk hppN hpp0
    hpp100
  have hone : (1 : UInt32) ≤ n := by
    rw [UInt32.le_iff_toNat_le]
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  have hsub : n.subChecked 1 = .ok (n - 1) := UInt32.subChecked_of_le hone
  have hpred : (n - 1).toNat ≤ n.toNat := by
    rw [UInt32.toNat_sub_of_le n 1 hone]; omega
  have hk' : (n - 1).toNat * interval.toNat < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hpred) hk
  obtain ⟨tpo', htpo'⟩ := loanPrincipalFromPeriodicPayment_computes pp rate ir interval (n - 1) hrate hir hiv hk'
    hppN hpp0 hpp100
  have htpoN := loanPrincipalFromPeriodicPayment_normalized_of_ok pp rate n tpo hppN hrN htpo
  have htpoN' := loanPrincipalFromPeriodicPayment_normalized_of_ok pp rate (n - 1) tpo' hppN hrN htpo'
  obtain ⟨htpo0, htpole, -⟩ := loanPrincipalFromPeriodicPayment_le_payments pp rate n tpo hppN hpp0 hrN hr0 htpo
  obtain ⟨htpo0', htpole', -⟩ :=
    loanPrincipalFromPeriodicPayment_le_payments pp rate (n - 1) tpo' hppN hpp0 hrN hr0 htpo'
  have hpredq : ((n - 1).toNat : ℚ) ≤ n.toNat := by exact_mod_cast hpred
  have hbig : (70 : ℚ) * 2 ^ 32 * 10 ^ 36 < 10 ^ 200 := by norm_num
  have htpolt : |tpo.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htpo0]
    have : 70 * (n.toNat : ℚ) * pp.toRat ≤ 70 * 2 ^ 32 * 10 ^ 36 := by gcongr
    linarith
  have htpolt' : |tpo'.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htpo0']
    have : 70 * ((n - 1).toNat : ℚ) * pp.toRat ≤ 70 * 2 ^ 32 * 10 ^ 36 := by gcongr; linarith
    linarith
  obtain ⟨first, hfirst⟩ := Number.operator_sub_ok_of_abs tpo tpo' .to_nearest htpoN htpoN' htpolt htpolt'

  let props : LoanProperties :=
    { periodicPayment := pp
      totalValueOutstanding := tvo
      managementFeeOutstanding := mfo
      loanScale := max minScale amountSt.exponent
      principalOutstanding := rp
      firstPaymentPrincipal := first }
  refine ⟨props, ?_, ?_⟩
  · unfold computeLoanProperties
    rw [hrate, ok_bind]
    unfold computeLoanPropertiesFromPeriodicRate
    rw [hpp, ok_bind]
    dsimp only
    rw [hamount, ok_bind, hst', ok_bind, htvo, ok_bind, hrp, ok_bind, hti, ok_bind, hmfo, ok_bind, htpo, ok_bind]
    rw [hsub, ok_bind]
    rw [htpo', ok_bind, hfirst, ok_bind]
    rfl
  · exact { periodicPayment_norm := hppN
            periodicPayment_nonneg := hpp0
            periodicPayment_lt := hpp36
            periodicPayment_max := fun hint => by
              have := hvalue hint rate pp hrate hpp
              nlinarith
            totalValue_norm := htvoN
            totalValue_nonneg := htvo0
            totalValue_units := hunits
            managementFee_norm := hmfoN
            managementFee_abs := hmfoabs
            loanScale_range := hls
            loanScale_integral := hlsi }

end XRPL.Model.Lending
