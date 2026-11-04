import XRPL.Properties.Lending.Loan.Common.PaymentFactor
import XRPL.Properties.Protocol.Common.TenthBips

/-! # The payment factor of a loan's periodic rate

A loan's nonzero periodic rate is at least `10^-12`, so the closed form for `(1 + rate)^n − 1` loses little to
rounding. The payment factor over `n` payments is then at least `1/(3·n)`, less three roundings. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Number.power_ge_one computePowerMinusOneHybrid_nonneg rn_ge rn_nonneg Number.ofInt64_one_toRat
  from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.power_le Number.cancellationThreshold powerMinusOneLoop_le Number.eq_zero_of_toRat
  Number.div_zero_error Number.zero_div_eq from XRPL.Properties.Lending.Loan.Common.PaymentFactor

local notation "ε" => Number.nearestError

/-- A nonzero periodic rate over at least 60 seconds is at least `10^-12`. The rate is at least one tenth bip
a year, prorated to the interval, less three roundings. -/
lemma loanPeriodicRate_ge (ir : TenthBips32) (interval : UInt32) (rate : Number) (hint : 60 ≤ interval.toNat)
    (h : loanPeriodicRate ir interval = .ok rate) (hr : rate.toRat ≠ 0) : 1 / 10 ^ 12 ≤ rate.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have heq : loanPeriodicRate ir interval =
      (((Number.ofInt64 interval.toUInt64.toInt64).operator_mul ir.toNumber .to_nearest) >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨p, hp, ht⟩ := bind_ok_peel _ _ _ ht
  have hI := Number.ofInt64_isNormalized interval.toUInt64.toInt64
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
  have hi0 : (0 : ℚ) ≤ interval.toNat := by positivity
  have hb0 : (0 : ℚ) ≤ ir.toNat := by positivity
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hI hB hp) (by rw [hIv, hBv]; positivity)
  have ht0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpN hU ht) (by rw [hUv]; positivity)
  have hr0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ htN hY h) (by rw [hYv]; positivity)
  have nr := Number.div_near _ _ _ htN hY h
  have nt := Number.div_near _ _ _ hpN hU ht
  have np := Number.mul_near _ _ _ hI hB hp
  rw [hYv] at nr
  rw [hUv] at nt
  rw [hIv, hBv] at np
  -- every step before the rate is nonzero, or the rate would be zero
  have ht' : t.toRat ≠ 0 := by
    intro h0
    have := nr.le (by rw [h0]; norm_num)
    rw [h0] at this
    exact hr (le_antisymm (by linarith) hr0)
  have hp' : p.toRat ≠ 0 := by
    intro h0
    have := nt.le (by rw [h0]; norm_num)
    rw [h0] at this
    exact ht' (le_antisymm (by linarith) ht0)
  have hir : (1 : ℚ) ≤ ir.toNat := by
    rcases Nat.eq_zero_or_pos ir.toNat with h0 | h0
    · exfalso
      have := np.le (by positivity)
      rw [h0] at this
      push_cast at this
      exact hp' (le_antisymm (by linarith) hp0)
    · exact_mod_cast h0
  have g1 := np.ge hp' (by positivity)
  have g2 := nt.ge ht' (by positivity)
  have g3 := nr.ge hr (by positivity)
  have h60 : (60 : ℚ) ≤ interval.toNat := by exact_mod_cast hint
  have h1e : (1 - 1 / 10 ^ 18 : ℚ) ≤ 1 - ε := by linarith
  have h1e0 : (0 : ℚ) < 1 - ε := by linarith
  calc (1 : ℚ) / 10 ^ 12 ≤ 60 * 1 / 100000 / 31536000 * (1 - 1 / 10 ^ 18) ^ 3 := by norm_num
    _ ≤ interval.toNat * ir.toNat / 100000 / 31536000 * (1 - ε) ^ 3 := by gcongr
    _ = interval.toNat * ir.toNat * (1 - ε) / 100000 * (1 - ε) / 31536000 * (1 - ε) := by ring
    _ ≤ p.toRat / 100000 * (1 - ε) / 31536000 * (1 - ε) := by gcongr
    _ ≤ t.toRat / 31536000 * (1 - ε) := by gcongr
    _ ≤ rate.toRat := g3

/-- `(1 + rate)^n − 1` is at most `3·n·rate` while `n` times the rate is at most one half, for a rate of at
least `10^-12`. The closed form loses at most `12·n·ε` to rounding, tiny next to `n·rate`. -/
private lemma computePowerMinusOneHybrid_le_three (rate : Number) (pr : UInt32) (pm : Number)
    (hrate : rate.isNormalized) (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hsmall : (pr.toNat : ℚ) * rate.toRat ≤ 1 / 2)
    (h : computePowerMinusOneHybrid rate (Number.ofInt64 pr.toUInt64.toInt64) pr = .ok pm) :
    pm.toRat ≤ 3 * pr.toNat * rate.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hr0 : 0 ≤ rate.toRat := le_trans (by norm_num) hlow
  have hN := Number.ofInt64_isNormalized pr.toUInt64.toInt64
  have hNv := Number.ofInt64_count pr
  have hone := Number.ofInt64_isNormalized 1
  have hpr32 : pr.toNat < 2 ^ 32 := pr.toNat_lt
  have hpr32' : (pr.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast hpr32.le
  have hx0 : 0 ≤ (pr.toNat : ℚ) * rate.toRat := by positivity
  unfold computePowerMinusOneHybrid at h
  dsimp only at h
  split at h
  · cases h; rw [Number.toRat_zero]; positivity
  rename_i hz
  have hpr0 : pr ≠ 0 := by
    intro h0; apply hz; simp [h0]
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨nr, hnr, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨th, hth, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨w, hw, hwN, hwv⟩ := Number.cancellationThreshold
  rw [hw, Except.ok.injEq] at hth
  subst hth
  have hnrN := Number.operator_mul_isNormalized _ _ nr _ hN hrate hnr
  have hnrle := (Number.mul_near _ _ _ hN hrate hnr).le (by rw [hNv]; exact hx0)
  rw [hNv] at hnrle
  split at h
  · -- the closed form: `(1 + rate)^n` by squaring, less one
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨raised, hraised, h⟩ := bind_ok_peel _ _ _ h
    have hbN := operator_add_isNormalized_to_nearest_sz _ _ b hone hrate hb
    have hb1 : 1 ≤ b.toRat := by
      have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hrate hb) _ hone
        (by rw [Number.ofInt64_one_toRat]; linarith)
      rwa [Number.ofInt64_one_toRat] at this
    have hble := (Number.add_near _ _ _ hone hrate hb).le (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at hble
    have hraisedN := Number.power_isNormalized b hbN _ raised hraised
    have hR1 := Number.power_ge_one b hbN hb1 _ raised hraised
    have hR := Number.power_le b hbN hb1 _ raised (by exact_mod_cast hN1) hraised
    have hpm := (Number.sub_near _ _ _ hraisedN hone h).le (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at hpm
    -- `b^n (1 + ε)^(2n) ≤ (1 + 2·n·rate) (1 + 6·n·ε)`
    have hbpow : b.toRat ^ pr.toNat ≤ (1 + rate.toRat) ^ pr.toNat * (1 + ε) ^ pr.toNat := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hble _
    have hlin1 := one_add_pow_le_lin rate.toRat pr.toNat hr0 hsmall
    have hlin2 := one_add_pow_le_lin ε (3 * pr.toNat) he.le (by
      push_cast
      calc (3 : ℚ) * pr.toNat * ε ≤ 3 * 2 ^ 32 * (1 / 10 ^ 18) := by gcongr
        _ ≤ 1 / 2 := by norm_num)
    push_cast at hlin2
    have hpow3 : (1 + ε) ^ pr.toNat * (1 + ε) ^ (2 * pr.toNat) = (1 + ε) ^ (3 * pr.toNat) := by
      rw [← pow_add]; ring_nf
    have hraised : raised.toRat ≤ (1 + 2 * pr.toNat * rate.toRat) * (1 + 6 * pr.toNat * ε) := by
      have h1 : raised.toRat ≤ raised.toRat * (1 + ε) := by nlinarith
      have h2 : b.toRat ^ pr.toNat * (1 + ε) ^ (2 * pr.toNat) ≤
          (1 + rate.toRat) ^ pr.toNat * (1 + ε) ^ (3 * pr.toNat) := by
        rw [← hpow3, ← mul_assoc]; gcongr
      have h3 : (1 + rate.toRat) ^ pr.toNat * (1 + ε) ^ (3 * pr.toNat) ≤
          (1 + 2 * pr.toNat * rate.toRat) * (1 + 2 * (3 * pr.toNat) * ε) := by
        gcongr
      have e3 : (1 + 2 * (3 * (pr.toNat : ℚ)) * ε) = 1 + 6 * pr.toNat * ε := by ring
      rw [e3] at h3
      linarith
    -- the rounding error `6·n·ε` is tiny next to `n·rate`, as the rate is at least `10^-12`
    have hNe : 6 * (pr.toNat : ℚ) * ε ≤ (pr.toNat * rate.toRat) / 10 ^ 5 := by
      calc 6 * (pr.toNat : ℚ) * ε ≤ 6 * pr.toNat * (1 / 10 ^ 18) := by gcongr
        _ = pr.toNat * (1 / 10 ^ 12) * (6 / 10 ^ 6) := by ring
        _ ≤ pr.toNat * rate.toRat * (6 / 10 ^ 6) := by gcongr
        _ ≤ (pr.toNat * rate.toRat) / 10 ^ 5 := by nlinarith
    have hxe : 12 * (pr.toNat : ℚ) * rate.toRat * pr.toNat * ε ≤ (pr.toNat * rate.toRat) / 10 ^ 5 := by
      have e : 12 * (pr.toNat : ℚ) * rate.toRat * pr.toNat * ε = (pr.toNat * rate.toRat) * (12 * pr.toNat * ε) := by
        ring
      rw [e]
      have : 12 * (pr.toNat : ℚ) * ε ≤ 1 / 10 ^ 5 := by
        calc 12 * (pr.toNat : ℚ) * ε ≤ 12 * 2 ^ 32 * (1 / 10 ^ 18) := by gcongr
          _ ≤ 1 / 10 ^ 5 := by norm_num
      nlinarith
    calc pm.toRat ≤ (raised.toRat - 1) * (1 + ε) := hpm
      _ ≤ ((1 + 2 * pr.toNat * rate.toRat) * (1 + 6 * pr.toNat * ε) - 1) * (1 + ε) := by gcongr
      _ = (2 * pr.toNat * rate.toRat + 6 * pr.toNat * ε + 12 * pr.toNat * rate.toRat * pr.toNat * ε) *
          (1 + ε) := by ring
      _ ≤ ((2 + 2 / 10 ^ 5) * (pr.toNat * rate.toRat)) * (1 + ε) := by gcongr; linarith
      _ ≤ 3 * pr.toNat * rate.toRat := by nlinarith
  · -- the binomial series, for `n·rate` below `10^-9`
    rename_i hlt
    have hsm : (pr.toNat : ℚ) * rate.toRat < 1 / 10 ^ 9 := by
      by_contra hc
      push Not at hc
      have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hN hrate hnr) w hwN (by rw [hwv, hNv]; exact hc)
      exact hlt ((operator_ge_iff nr w hnrN hwN).mpr this)
    unfold computePowerMinusOne at h
    dsimp only at h
    split at h
    · cases h; rw [Number.toRat_zero]; positivity
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
    rw [hnr, Except.ok.injEq] at hc
    subst hc
    have hnr0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hN hrate hnr) (by rw [hNv]; exact hx0)
    have hloop := powerMinusOneLoop_le rate hrate hr0 pr.toNat hpr32 hsm _ 1 nr nr pm rfl le_rfl hnrN hnrN
      hnr0 hnr0 h
    have hpowN : (1 + ε) ^ (pr.toNat - 1) ≤ 1 + 1 / 10 ^ 8 := by
      have := one_add_pow_le_lin ε (pr.toNat - 1) he.le (by
        calc ((pr.toNat - 1 : ℕ) : ℚ) * ε ≤ 2 ^ 32 * (1 / 10 ^ 18) := by
              gcongr
              exact le_trans (by exact_mod_cast Nat.sub_le _ _) hpr32'
          _ ≤ 1 / 2 := by norm_num)
      refine le_trans this ?_
      have : ((pr.toNat - 1 : ℕ) : ℚ) * ε ≤ 2 ^ 32 * (1 / 10 ^ 18) := by
        gcongr
        exact le_trans (by exact_mod_cast Nat.sub_le _ _) hpr32'
      nlinarith
    calc pm.toRat ≤ (nr.toRat + nr.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ (pr.toNat - 1) := hloop
      _ ≤ (nr.toRat + nr.toRat / (10 ^ 9 - 1)) * (1 + 1 / 10 ^ 8) := by gcongr
      _ ≤ (pr.toNat * rate.toRat * (1 + ε) + pr.toNat * rate.toRat * (1 + ε) / (10 ^ 9 - 1)) *
          (1 + 1 / 10 ^ 8) := by gcongr
      _ = pr.toNat * rate.toRat * ((1 + ε) * (1 + 1 / (10 ^ 9 - 1)) * (1 + 1 / 10 ^ 8)) := by ring
      _ ≤ pr.toNat * rate.toRat * ((1 + 1 / 10 ^ 18) * (1 + 1 / (10 ^ 9 - 1)) * (1 + 1 / 10 ^ 8)) := by
          gcongr
      _ ≤ pr.toNat * rate.toRat * 3 := by
          gcongr
          norm_num
      _ = 3 * pr.toNat * rate.toRat := by ring

/-- A nonzero payment factor of a rate of at least `10^-12` over `n` payments is at least `1/(3·n)`, less three
roundings. `(1 + rate)^n − 1` is at most `3·n·rate` while `n·rate ≤ 1/2`, else the factor is the rate or more. -/
lemma computePaymentFactor_ge_third (rate : Number) (pr : UInt32) (f : Number) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (h : computePaymentFactor rate (Number.ofInt64 pr.toUInt64.toInt64) pr = .ok f)
    (hf : f.toRat ≠ 0) : (1 - ε) ^ 3 / (3 * pr.toNat) ≤ f.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hr0 : 0 < rate.toRat := lt_of_lt_of_le (by norm_num) hlow
  have hN := Number.ofInt64_isNormalized pr.toUInt64.toInt64
  have hNv := Number.ofInt64_count pr
  have hone := Number.ofInt64_isNormalized 1
  unfold computePaymentFactor at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact absurd Number.toRat_zero hf
  rename_i hpr
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have hpr0 : pr ≠ 0 := by intro h0; apply hpr; simp [h0]
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
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
  have hrrN := operator_add_isNormalized_to_nearest_sz _ _ rr hone hpN hrr
  have hrrge := (Number.add_near _ _ _ hone hpN hrr).ge (by
    have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hpN hrr) _ hone
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at this
    linarith) (by rw [Number.ofInt64_one_toRat]; linarith)
  rw [Number.ofInt64_one_toRat] at hrrge
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
  have hnumne : num.toRat ≠ 0 := by
    intro h0
    have hz := Number.zero_div_eq (fun hc => hpne (by rw [hc, Number.toRat_zero])) (Number.eq_zero_of_toRat hnumN h0) h
    exact hf (by rw [hz, Number.toRat_zero])
  have h1e : 0 < 1 - ε := by linarith
  have hrr0 : 0 ≤ rr.toRat := le_trans (by positivity) hrrge
  have hnumge := (Number.mul_near _ _ _ hrate hrrN hnum).ge hnumne (by positivity)
  have hnum0 : 0 ≤ num.toRat := le_trans (by positivity) hnumge
  have hfge := (Number.div_near _ _ _ hnumN hpN h).ge hf (div_nonneg hnum0 hp0)
  -- `f ≥ rate·(1 + pmo)/pmo · (1 − ε)^3`
  have hkey : rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 / pmo.toRat ≤ f.toRat := by
    calc rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 / pmo.toRat
        = (rate.toRat * ((1 + pmo.toRat) * (1 - ε)) * (1 - ε)) / pmo.toRat * (1 - ε) := by ring
      _ ≤ (rate.toRat * rr.toRat * (1 - ε)) / pmo.toRat * (1 - ε) := by gcongr
      _ ≤ num.toRat / pmo.toRat * (1 - ε) := by gcongr
      _ ≤ f.toRat := hfge
  have hNpos : (0 : ℚ) < pr.toNat := by linarith
  have h3 : 0 ≤ (1 - ε) ^ 3 := by positivity
  refine le_trans ?_ hkey
  rw [div_le_div_iff₀ (by positivity) hp]
  by_cases hs : (pr.toNat : ℚ) * rate.toRat ≤ 1 / 2
  · have hle := computePowerMinusOneHybrid_le_three rate pr pmo hrate hlow hs hpmo
    calc (1 - ε) ^ 3 * pmo.toRat ≤ (1 - ε) ^ 3 * (3 * pr.toNat * rate.toRat) := by gcongr
      _ = rate.toRat * (1 - ε) ^ 3 * (3 * pr.toNat) := by ring
      _ ≤ rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 * (3 * pr.toNat) := by
          gcongr
          nlinarith [mul_nonneg hr0.le hp0]
  · -- the factor is at least the rate, which is above `1/(2·n)`
    push Not at hs
    have e : rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 * (3 * pr.toNat) =
        (1 - ε) ^ 3 * pmo.toRat * (3 * (pr.toNat * rate.toRat)) + (1 - ε) ^ 3 * (3 * (pr.toNat * rate.toRat)) := by
      ring
    rw [e]
    have : (1 - ε) ^ 3 * pmo.toRat * 1 ≤ (1 - ε) ^ 3 * pmo.toRat * (3 * (pr.toNat * rate.toRat)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

end XRPL.Model.Lending
