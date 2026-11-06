import XRPL.Properties.Lending.Loan.Common.FactorBound
import XRPL.Properties.Lending.Loan.Common.RoundToNearest

/-! # The theoretical principal of the payments left is positive

A lawful loan's periodic rate is at most `200`, so the payment factor is at most `210`. A PeriodicPayment of at
least `10^-40` then has a theoretical principal of at least `10^-43`, which never rounds up to zero at LoanScale. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_ge rn_nonneg Number.ofInt64_one_toRat Number.ofInt64_nat_nonneg computePowerMinusOneHybrid_nonneg
  from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.eq_zero_of_toRat Number.div_zero_error from XRPL.Properties.Lending.Loan.Common.PaymentFactor
open private STAmount.ofNumber_frac_zero_small from XRPL.Properties.Lending.Loan.Common.SetValue

local notation "ε" => Number.nearestError

/-- A periodic rate of at most 100% a year is at most `200`. The interval is below `2^32` seconds. -/
lemma loanPeriodicRate_le (ir : TenthBips32) (interval : UInt32) (rate : Number) (hir : ir ≤ maxLoanRate)
    (h : loanPeriodicRate ir interval = .ok rate) : rate.toRat ≤ 200 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have heq : loanPeriodicRate ir interval =
      (((Number.ofInt64 interval.toInt64).operator_mul ir.toNumber .to_nearest) >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨p, hp, ht⟩ := bind_ok_peel _ _ _ ht
  have hI := Number.ofInt64_isNormalized interval.toInt64
  have hIv := Number.ofInt64_count interval
  obtain ⟨hB, hBv⟩ := TenthBips32.toNumber_facts ir
  obtain ⟨hU, hUv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  obtain ⟨hY, hYv⟩ := TenthBips32.toNumber_facts (31536000 : UInt32)
  have hU' : (kTenthBipsPerUnity.toNat : ℚ) = 100000 := rfl
  have hY' : ((31536000 : UInt32).toNat : ℚ) = 31536000 := rfl
  have hy : secondsInYear = TenthBips32.toNumber (31536000 : UInt32) := rfl
  rw [hy] at h
  rw [hU'] at hUv
  rw [hY'] at hYv
  have hpN := Number.operator_mul_isNormalized _ _ p _ hI hB hp
  have htN := Number.operator_div_isNormalized _ _ t _ hpN hU ht
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hI hB hp) (by rw [hIv, hBv]; positivity)
  have ht0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpN hU ht) (by rw [hUv]; positivity)
  have g1 := (Number.mul_near _ _ _ hI hB hp).le (by rw [hIv, hBv]; positivity)
  have g2 := (Number.div_near _ _ _ hpN hU ht).le (by rw [hUv]; positivity)
  have g3 := (Number.div_near _ _ _ htN hY h).le (by rw [hYv]; positivity)
  rw [hIv, hBv] at g1
  rw [hUv] at g2
  rw [hYv] at g3
  have hint : (interval.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast interval.toNat_lt.le
  have hirn : (ir.toNat : ℚ) ≤ 100000 := by
    have : ir.toNat ≤ maxLoanRate.toNat := (UInt32.le_iff_toNat_le).mp hir
    exact_mod_cast this
  calc rate.toRat ≤ t.toRat / 31536000 * (1 + ε) := g3
    _ ≤ p.toRat / 100000 * (1 + ε) / 31536000 * (1 + ε) := by gcongr
    _ ≤ interval.toNat * ir.toNat * (1 + ε) / 100000 * (1 + ε) / 31536000 * (1 + ε) := by gcongr
    _ ≤ 2 ^ 32 * 100000 * (1 + 1 / 10 ^ 18) / 100000 * (1 + 1 / 10 ^ 18) / 31536000 * (1 + 1 / 10 ^ 18) := by
        gcongr
    _ ≤ 200 := by norm_num

/-- A power of a base at least one, to an exponent of at least one, is at least the base. -/
private lemma Number.power_ge_base (base : Number) (hb : base.isNormalized) (h1 : 1 ≤ base.toRat) :
    ∀ (k : Nat) (r : Number), 1 ≤ k → base.power k = .ok r → base.toRat ≤ r.toRat := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hk h
    match k, ih with
    | 0, _ => omega
    | 1, _ =>
      rw [Number.power] at h
      cases h; exact le_refl _
    | j + 2, ih =>
      rw [Number.power] at h
      obtain ⟨half, hh, h⟩ := bind_ok_peel _ _ _ h
      have hhalfN := Number.power_isNormalized base hb _ half hh
      have hhalf := ih ((j + 2) / 2) (by omega) half (by omega) hh
      obtain ⟨sq, hs, h⟩ := bind_ok_peel _ _ _ h
      have hsqN := Number.operator_mul_isNormalized _ _ sq _ hhalfN hhalfN hs
      have hsq : base.toRat ≤ sq.toRat :=
        rn_ge (operator_mul_rounded_to_nearest _ _ _ hhalfN hhalfN hs) _ hb (by nlinarith)
      split at h
      · exact rn_ge (operator_mul_rounded_to_nearest _ _ _ hsqN hb h) _ hb (by nlinarith)
      · cases h; exact hsq

/-- The binomial series of `(1 + rate)^n − 1` never drops below its first partial sum. Each term is at least
zero, so each partial sum rounds a sum at least the previous one. -/
private lemma powerMinusOneLoop_ge (rate : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (pr : Nat)
    (hpr : pr < 2 ^ 32) :
    ∀ (d index : Nat) (ct rs r : Number), pr - index = d → ct.isNormalized → rs.isNormalized →
      0 ≤ ct.toRat → powerMinusOneLoop rate pr index ct rs = .ok r → rs.toRat ≤ r.toRat := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index ct rs r hd hc hs hc0 h
    rw [powerMinusOneLoop] at h
    split at h
    · rename_i hlt
      obtain ⟨c1, h1, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, hk, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨-, rfl⟩ := Nat.toInt64Checked_eq_ok.mp hk
      obtain ⟨c2, h2, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, hk, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨-, rfl⟩ := Nat.toInt64Checked_eq_ok.mp hk
      obtain ⟨c3, h3, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨ns, h4, h⟩ := bind_ok_peel _ _ _ h
      have hc1 := Number.operator_mul_isNormalized _ _ c1 _ hc hrate h1
      have hc2 := Number.operator_mul_isNormalized _ _ c2 _ hc1 (Number.ofInt64_isNormalized _) h2
      have hc3 := Number.operator_div_isNormalized _ _ c3 _ hc2 (Number.ofInt64_isNormalized _) h3
      have hns := operator_add_isNormalized_to_nearest_sz _ _ ns hs hc3 h4
      have hc10 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc hrate h1) (mul_nonneg hc0 hr0)
      have hc20 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc1 (Number.ofInt64_isNormalized _) h2)
        (mul_nonneg hc10 (Number.ofInt64_nat_nonneg _ (by omega)))
      have hc30 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hc2 (Number.ofInt64_isNormalized _) h3)
        (div_nonneg hc20 (Number.ofInt64_nat_nonneg _ (by omega)))
      have hns0 := rn_ge (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) rs hs (by linarith)
      split at h
      · cases h; exact le_refl _
      · exact hns0.trans (ih (pr - (index + 1)) (by omega) (index + 1) c3 ns r rfl hc3 hns hc30 h)
    · cases h; exact le_refl _

/-- `(1 + rate)^n − 1` is at least a third of the rate for a rate of at least `10^-12`, when it is not zero.
The closed form rounds `1 + rate` and its powers, the series starts at `n·rate`. -/
private lemma computePowerMinusOneHybrid_ge (rate : Number) (pr : UInt32) (pm : Number) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hpm : pm.toRat ≠ 0)
    (h : computePowerMinusOneHybrid rate (Number.ofInt64 pr.toInt64) pr = .ok pm) :
    rate.toRat / 3 ≤ pm.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hr0 : 0 < rate.toRat := lt_of_lt_of_le (by norm_num) hlow
  have hone := Number.ofInt64_isNormalized 1
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  unfold computePowerMinusOneHybrid at h
  dsimp only at h
  split at h
  · cases h; exact absurd Number.toRat_zero hpm
  rename_i hz
  have hpr0 : pr ≠ 0 := by intro h0; apply hz; simp [h0]
  have hN1 : 1 ≤ pr.toNat := by
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨nr, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨th, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · -- the closed form: `(1 + rate)^n` is at least `1 + rate` rounded
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨raised, hraised, h⟩ := bind_ok_peel _ _ _ h
    have hbN := operator_add_isNormalized_to_nearest_sz _ _ b hone hrate hb
    have hb1 : 1 ≤ b.toRat := by
      have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hrate hb) _ hone
        (by rw [Number.ofInt64_one_toRat]; linarith)
      rwa [Number.ofInt64_one_toRat] at this
    have hbge := (Number.add_near _ _ _ hone hrate hb).ge (by linarith)
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at hbge
    have hraisedN := Number.power_isNormalized b hbN _ raised hraised
    have hrb := Number.power_ge_base b hbN hb1 pr.toNat raised hN1 hraised
    have hpmge := (Number.sub_near _ _ _ hraisedN hone h).ge hpm
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at hpmge
    have h1 : rate.toRat / 2 ≤ raised.toRat - 1 := by nlinarith
    nlinarith
  · -- the series: it starts at `n·rate`, at least the rate
    unfold computePowerMinusOne at h
    dsimp only at h
    split at h
    · cases h; exact absurd Number.toRat_zero hpm
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
    have hcN := Number.operator_mul_isNormalized _ _ c _ hN hrate hc
    have hc0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hN hrate hc)
      (by rw [hNv]; positivity)
    have hcr : rate.toRat ≤ c.toRat := rn_ge (operator_mul_rounded_to_nearest _ _ _ hN hrate hc) _ hrate
      (by rw [hNv]; have : (1 : ℚ) ≤ pr.toNat := by exact_mod_cast hN1
          nlinarith)
    have := powerMinusOneLoop_ge rate hrate hr0.le pr.toNat pr.toNat_lt _ 1 c c pm rfl hcN hcN hc0 h
    linarith

/-- The payment factor of a rate between `10^-12` and `200` is at most `210`. `(1 + rate)^n − 1` is at least
a third of the rate, so `rate·(1 + m)/m` is at most `rate + 3`, plus three roundings. -/
private lemma computePaymentFactor_le (rate : Number) (pr : UInt32) (f : Number) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hhigh : rate.toRat ≤ 200)
    (h : computePaymentFactor rate (Number.ofInt64 pr.toInt64) pr = .ok f) : f.toRat ≤ 210 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hr0 : 0 < rate.toRat := lt_of_lt_of_le (by norm_num) hlow
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  have hone := Number.ofInt64_isNormalized 1
  unfold computePaymentFactor at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rw [Number.toRat_zero]; norm_num
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · rename_i hz
    have := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp hz
    rw [Number.toRat_zero] at this; linarith
  obtain ⟨pmo, hpmo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨rr, hrr, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨num, hnum, h⟩ := bind_ok_peel _ _ _ h
  have hpN := computePowerMinusOneHybrid_isNormalized rate _ pr pmo hrate hN hpmo
  have hp0 := computePowerMinusOneHybrid_nonneg rate _ pr pmo hrate hr0.le hN (by rw [hNv]; positivity) hpmo
  have hpne : pmo.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hpN h0) h
  have hp : 0 < pmo.toRat := lt_of_le_of_ne hp0 (Ne.symm hpne)
  have hpm3 := computePowerMinusOneHybrid_ge rate pr pmo hrate hlow hpne hpmo
  have hrrN := operator_add_isNormalized_to_nearest_sz _ _ rr hone hpN hrr
  have hrr0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ hone hpN hrr)
    (by rw [Number.ofInt64_one_toRat]; linarith)
  have hrrle := (Number.add_near _ _ _ hone hpN hrr).le (by rw [Number.ofInt64_one_toRat]; linarith)
  rw [Number.ofInt64_one_toRat] at hrrle
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
  have hnum0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hrate hrrN hnum) (mul_nonneg hr0.le hrr0)
  have hnumle := (Number.mul_near _ _ _ hrate hrrN hnum).le (mul_nonneg hr0.le hrr0)
  have hfle := (Number.div_near _ _ _ hnumN hpN h).le (div_nonneg hnum0 hp0)
  -- `rate/m ≤ 3`, so `rate·(1 + m)/m ≤ 203`
  have hq : rate.toRat * (1 + pmo.toRat) / pmo.toRat ≤ 203 := by
    rw [div_le_iff₀ hp]
    nlinarith
  have h3 : (1 + ε) ^ 3 ≤ 210 / 203 := by
    have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
    push_cast at this; linarith
  calc f.toRat ≤ num.toRat / pmo.toRat * (1 + ε) := hfle
    _ ≤ rate.toRat * rr.toRat * (1 + ε) / pmo.toRat * (1 + ε) := by gcongr
    _ ≤ rate.toRat * ((1 + pmo.toRat) * (1 + ε)) * (1 + ε) / pmo.toRat * (1 + ε) := by gcongr
    _ = rate.toRat * (1 + pmo.toRat) / pmo.toRat * (1 + ε) ^ 3 := by ring
    _ ≤ 203 * (210 / 203) := mul_le_mul hq h3 (by positivity) (by norm_num)
    _ = 210 := by norm_num

/-- The periodic payment of a principal of at least `B` over fewer than `2^32` payments is at least
`B·(1 − ε)^4 / (3·2^32)`, when it is not zero. The payment factor over `n` payments is at least `1/(3·n)`. -/
lemma loanPeriodicPayment_ge (principal rate : Number) (pr : UInt32) (pp : Number) (B : ℚ) (hB : 0 ≤ B)
    (hp : principal.isNormalized) (hP : B ≤ principal.toRat) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (hlow : rate.toRat ≠ 0 → 1 / 10 ^ 12 ≤ rate.toRat) (hpp : pp.toRat ≠ 0)
    (h : loanPeriodicPayment principal rate pr = .ok pp) : B * (1 - ε) ^ 4 / (3 * 2 ^ 32) ≤ pp.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have h1e : 0 ≤ 1 - ε := by linarith
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  have hn32 : (pr.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast pr.toNat_lt.le
  have hP0 : 0 ≤ principal.toRat := le_trans hB hP
  unfold loanPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact absurd Number.toRat_zero hpp
  rename_i hz
  have hpr0 : pr ≠ 0 := by intro h0; apply hz; simp [h0]
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hNpos : (0 : ℚ) < pr.toNat := by linarith
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · -- no interest: `principal / n`
    have hge := (Number.div_near _ _ _ hp hN h).ge hpp (by rw [hNv]; positivity)
    rw [hNv] at hge
    have h3 : (1 - ε) ^ 3 / 3 ≤ 1 := by
      have : (1 - ε) ^ 3 ≤ 1 := pow_le_one₀ h1e (by linarith)
      linarith
    calc B * (1 - ε) ^ 4 / (3 * 2 ^ 32) = B / 2 ^ 32 * (1 - ε) * ((1 - ε) ^ 3 / 3) := by ring
      _ ≤ B / 2 ^ 32 * (1 - ε) * 1 := by gcongr
      _ ≤ principal.toRat / pr.toNat * (1 - ε) := by rw [mul_one]; gcongr
      _ ≤ pp.toRat := hge
  · -- interest: `principal · f` with `f ≥ (1 − ε)^3 / (3·n)`
    rename_i hz'
    have hrne : rate.toRat ≠ 0 := by
      intro h0
      apply hz'
      rw [Number.eq_zero_of_mantissa_zero rate hrate (Number.toRat_eq_zero_iff.mp h0)]; decide
    obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
    have hfN := computePaymentFactor_isNormalized rate _ pr f hrate hN hf
    have hf0 := computePaymentFactor_nonneg rate _ pr f hrate hr0 hN (by rw [hNv]; positivity) hf
    have hnear := Number.mul_near _ _ _ hp hfN h
    have hfne : f.toRat ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hnear
      rcases hnear with h1 | h1
      · exact hpp h1
      · rw [abs_zero, zero_mul, sub_zero] at h1
        exact hpp (abs_nonpos_iff.mp h1)
    have hfge := computePaymentFactor_ge_third rate pr f hrate (hlow hrne) hf hfne
    have hge := hnear.ge hpp (by positivity)
    calc B * (1 - ε) ^ 4 / (3 * 2 ^ 32) = B * ((1 - ε) ^ 3 / (3 * 2 ^ 32)) * (1 - ε) := by ring
      _ ≤ principal.toRat * ((1 - ε) ^ 3 / (3 * pr.toNat)) * (1 - ε) := by gcongr
      _ ≤ principal.toRat * f.toRat * (1 - ε) := by gcongr
      _ ≤ pp.toRat := hge

/-- The smallest positive `Number` is below `10^-100`. -/
private lemma Number.underflow_lt : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) < 1 / 10 ^ 100 := by
  have : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-200 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
  calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (18 : ℕ) * 10 ^ (-200 : ℤ) := by gcongr
    _ < 1 / 10 ^ 100 := by norm_num

/-- A PeriodicPayment of at least `10^-40` has a theoretical principal of at least `10^-43` over one payment or
more, at a periodic rate of at most `200` that is zero or at least `10^-12`. -/
lemma loanPrincipalFromPeriodicPayment_ge (pp rate : Number) (pr : UInt32) (tpo : Number)
    (hpp : pp.isNormalized) (hppL : 1 / 10 ^ 40 ≤ pp.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hlow : rate.toRat ≠ 0 → 1 / 10 ^ 12 ≤ rate.toRat) (hhigh : rate.toRat ≤ 200) (hpr : pr ≠ 0)
    (h : loanPrincipalFromPeriodicPayment pp rate pr = .ok tpo) : 1 / 10 ^ 43 ≤ tpo.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have : pr.toNat ≠ 0 := fun h0 => hpr (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hppm : pp.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_iff.mpr h0] at hppL; norm_num at hppL
  have hNm : (Number.ofInt64 pr.toInt64).mantissa_ ≠ 0 := fun h0 => by
    rw [← Number.toRat_eq_zero_iff, hNv] at h0; linarith
  have hu := Number.underflow_lt
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · rename_i h0; exact absurd (by simpa using h0) hpr
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · -- no interest: `pp·n` is at least `pp`
    have hm : tpo.mantissa_ ≠ 0 := by
      intro h0
      have := operator_mul_underflow_truth_small _ _ _ _ hpp hN hppm hNm h h0
      rw [hNv, abs_of_nonneg (by positivity)] at this
      nlinarith
    have hge := (Number.mul_near _ _ _ hpp hN h).ge (fun h0 => hm (Number.toRat_eq_zero_iff.mp h0))
      (by rw [hNv]; positivity)
    rw [hNv] at hge
    have h1 : pp.toRat ≤ pp.toRat * pr.toNat := le_mul_of_one_le_right (by linarith) hN1
    calc (1 : ℚ) / 10 ^ 43 ≤ 1 / 10 ^ 40 * (1 - 1 / 10 ^ 18) := by norm_num
      _ ≤ pp.toRat * (1 - ε) := by gcongr
      _ ≤ pp.toRat * pr.toNat * (1 - ε) := by gcongr; linarith
      _ ≤ tpo.toRat := hge
  · -- interest: `pp/f` with the factor at most `210`
    rename_i hz
    have hrne : rate.toRat ≠ 0 := by
      intro h0
      apply hz
      rw [Number.eq_zero_of_toRat hrate h0]; decide
    obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
    have hfN := computePaymentFactor_isNormalized rate _ pr f hrate hN hf
    have hf0 := computePaymentFactor_nonneg rate _ pr f hrate hr0 hN (by rw [hNv]; positivity) hf
    have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) h
    have hfpos : 0 < f.toRat := lt_of_le_of_ne hf0 (Ne.symm hfne)
    have hfle := computePaymentFactor_le rate pr f hrate (hlow hrne) hhigh hf
    have hfm : f.mantissa_ ≠ 0 := fun h0 => hfne (Number.toRat_eq_zero_iff.mpr h0)
    have hq : 1 / 10 ^ 40 / 210 ≤ pp.toRat / f.toRat := by
      rw [div_le_div_iff₀ (by norm_num) hfpos]; nlinarith
    have hm : tpo.mantissa_ ≠ 0 := by
      intro h0
      have := operator_div_underflow_truth_small _ _ _ _ hpp hfN hppm hfm h h0
      rw [abs_of_nonneg (by positivity)] at this
      linarith
    have hge := (Number.div_near _ _ _ hpp hfN h).ge (fun h0 => hm (Number.toRat_eq_zero_iff.mp h0))
      (by positivity)
    nlinarith

/-- Rounding up at a scale never lowers a value of at least `10^-81`. Such a value never rounds to a zero
STAmount. -/
lemma STAmount.roundToNumericType_upward_ge_of_large (nt : NumericType) (x T : Number) (s : ℤ)
    (hx : x.isNormalized) (hlarge : (10 : ℚ) ^ (-81 : ℤ) ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType nt x .upward (some s) = .ok T) : x.toRat ≤ T.toRat := by
  have h0 : 0 ≤ x.toRat := le_trans (by positivity) hlarge
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    exact (STAmount.roundToNumericType_int_grid _ rfl x T .upward _ hx h0 (Or.inr (Or.inl rfl)) hok).2.2.1 rfl
  | fractional =>
    rw [hnt] at hok
    by_cases hT : T.toRat = 0
    · exfalso
      have hok' := hok
      unfold STAmount.roundToNumericType at hok'
      cases hof : STAmount.ofNumber .fractional x .upward with
      | error e => rw [hof] at hok'; exact absurd hok' (by simp)
      | ok st =>
        by_cases hst : st.mValue = 0
        · exact absurd hlarge (not_le.mpr (STAmount.ofNumber_frac_zero_small x .upward st hx h0 hof hst))
        · -- a nonzero stage rounds up to at least the value, which is positive
          have hpos : 0 < x.toRat := lt_of_lt_of_le (by positivity) hlarge
          rw [hof] at hok'
          simp only at hok'
          have hfc := STAmount.ofNumber_fractional_fczr x .upward st hof
          have hsti : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
          rw [if_neg (by rw [hsti]; decide)] at hok'
          cases hr : STAmount.roundToExponent st s .upward with
          | error e => rw [hr] at hok'; exact absurd hok' (by simp)
          | ok r =>
            rw [hr] at hok'
            simp only at hok'
            have hrc := STAmount.roundToExponent_fczr st r s .upward hfc hr
            have hrint : r.integral = false := by unfold STAmount.integral; rw [hrc.1]; rfl
            have hTr : T.toRat = r.toRat := by
              rcases hrc.2 with hrcan | hrz
              · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .upward hrcan
                rw [hsn, Except.ok.injEq] at hok'
                rw [← hok', hv]
              · rw [STAmount.toNumber_zero_fractional r .upward hrint hrz, Except.ok.injEq] at hok'
                rw [← hok', Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hrz]
            rcases hfc.2 with hstc | hstz
            · obtain ⟨-, -, -, hup, -⟩ :=
                STAmount.ofNumber_frac_stage x .upward st hx h0 (Or.inr (Or.inl rfl)) hof hst
              have hR := STAmount.roundToExponent_rounded_of_scale st r s .upward hstc hs.1 hs.2 hr
              unfold RoundsToRepresentableAt at hR
              have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
              have hce : st.toRat / 10 ^ s ≤ (⌈st.toRat / 10 ^ s⌉ : ℚ) := Int.le_ceil _
              have : st.toRat ≤ r.toRat := by
                rw [show r.toRat = _ from hR]
                calc st.toRat = st.toRat / 10 ^ s * 10 ^ s := by field_simp
                  _ ≤ _ := mul_le_mul_of_nonneg_right hce hp.le
              linarith [hup rfl]
            · exact hst hstz
    · exact STAmount.roundToNumericType_frac_upward_ge x T s hx h0 hs hT hok

end XRPL.Model.Lending
