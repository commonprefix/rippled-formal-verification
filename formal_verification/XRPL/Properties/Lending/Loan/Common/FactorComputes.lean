import XRPL.Properties.Lending.Loan.Common.FactorGapLoan
import XRPL.Properties.Lending.Loan.Common.NumberTotal
import XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal

/-! # The theoretical principal of any count of payments computes

A loan's periodic rate times the payments that fit the 32-bit clock is below `137`, so `(1 + rate)^k` stays below
`10^66`. Every step of the payment factor then stays inside the `Number` range, with divisors above `10^-82`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_ge rn_nonneg Number.ofInt64_one_toRat Number.power_ge_one
  from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.power_le Number.cancellationThreshold Number.ofInt64_nat
  from XRPL.Properties.Lending.Loan.Common.PaymentFactor
open private Number.power_ge_base from XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal
open private one_add_pow_le_exp from XRPL.Properties.Lending.Loan.Common.FactorGapLoan

local notation "ε" => Number.nearestError

/-- A power by squaring computes while the exact power times two roundings per step stays below `10^199`. -/
private lemma Number.power_computes (base : Number) (hb : base.isNormalized) (h1 : 1 ≤ base.toRat) :
    ∀ k : Nat, base.toRat ^ k * (1 + ε) ^ (2 * k) < 10 ^ 199 → ∃ r, base.power k = .ok r := by
  have he : 0 < ε := Number.nearestError_pos
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih with
    | 0, _ => exact ⟨_, by rw [Number.power]⟩
    | 1, _ => exact ⟨base, by rw [Number.power]⟩
    | j + 2, ih =>
      have hm : 1 ≤ (j + 2) / 2 := by omega
      have hmono : base.toRat ^ ((j + 2) / 2) * (1 + ε) ^ (2 * ((j + 2) / 2)) ≤
          base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by
        gcongr <;> first | exact h1 | omega | linarith
      obtain ⟨half, hh⟩ := ih ((j + 2) / 2) (by omega) (lt_of_le_of_lt hmono hk)
      have hhN := Number.power_isNormalized base hb _ half hh
      have hh1 := Number.power_ge_one base hb h1 _ half hh
      have hhle := Number.power_le base hb h1 _ half hm hh
      have hhalf : half.toRat ≤ base.toRat ^ ((j + 2) / 2) * (1 + ε) ^ (2 * ((j + 2) / 2)) := by nlinarith
      have hhl : |half.toRat| < 10 ^ 200 := by
        rw [abs_of_nonneg (by linarith)]; linarith
      obtain ⟨sq, hsq⟩ := Number.operator_mul_ok_of_abs half half .to_nearest hhN hhN hhl hhl
      rw [Number.power, hh, ok_bind, hsq, ok_bind]
      split
      · rename_i hodd
        have hk' : j + 2 = 2 * ((j + 2) / 2) + 1 := by
          have : (j + 2) % 2 = 1 := by simpa using hodd
          omega
        have hsqN := Number.operator_mul_isNormalized _ _ sq _ hhN hhN hsq
        have hsq0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hhN hhN hsq) (by nlinarith)
        have hsqle := (Number.mul_near _ _ _ hhN hhN hsq).le (by nlinarith)
        set m := (j + 2) / 2 with hmdef
        have hB0 : 0 ≤ base.toRat ^ m * (1 + ε) ^ (2 * m) := by positivity
        have hsq' : sq.toRat ≤ base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by
          calc sq.toRat ≤ half.toRat * half.toRat * (1 + ε) := hsqle
            _ ≤ (base.toRat ^ m * (1 + ε) ^ (2 * m)) * (base.toRat ^ m * (1 + ε) ^ (2 * m)) * (1 + ε) := by
                gcongr
            _ = base.toRat ^ (2 * m) * (1 + ε) ^ (4 * m + 1) := by ring
            _ ≤ base.toRat ^ (2 * m + 1) * (1 + ε) ^ (4 * m + 2) := by
                gcongr <;> first | exact h1 | omega | linarith
            _ = base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by
                rw [hk']; ring
        have hbl : base.toRat ≤ base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by
          calc base.toRat = base.toRat ^ 1 * 1 := by ring
            _ ≤ base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by
                gcongr <;> first | exact h1 | omega | linarith | exact one_le_pow₀ (by linarith)
        exact Number.operator_mul_ok_of_abs sq base .to_nearest hsqN hb
          (by rw [abs_of_nonneg hsq0]; linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
      · exact ⟨sq, rfl⟩

/-- The running sum with the rest of the series does not grow from one term to the next. -/
private lemma loop_rest_le (rs ct c3 ns e : ℚ) (d : ℕ) (he : 0 ≤ e) (hc3 : 0 ≤ c3)
    (hterm : c3 ≤ ct / 10 ^ 9) (u4 : ns ≤ (rs + c3) * (1 + e)) :
    (ns + c3 / (10 ^ 9 - 1)) * (1 + e) ^ d ≤ (rs + ct / (10 ^ 9 - 1)) * (1 + e) ^ (d + 1) := by
  have hq : 0 ≤ c3 / (10 ^ 9 - 1) := by positivity
  have hp : 0 ≤ (1 + e) ^ d := by positivity
  calc (ns + c3 / (10 ^ 9 - 1)) * (1 + e) ^ d
      ≤ ((rs + c3) * (1 + e) + c3 / (10 ^ 9 - 1)) * (1 + e) ^ d := by gcongr
    _ ≤ ((rs + c3) * (1 + e) + c3 / (10 ^ 9 - 1) * (1 + e)) * (1 + e) ^ d := by
        gcongr
        exact le_mul_of_one_le_right hq (by linarith)
    _ = (rs + c3 * (10 ^ 9 / (10 ^ 9 - 1))) * (1 + e) ^ (d + 1) := by ring
    _ ≤ (rs + ct / (10 ^ 9 - 1)) * (1 + e) ^ (d + 1) := by
        gcongr
        calc c3 * (10 ^ 9 / (10 ^ 9 - 1)) ≤ ct / 10 ^ 9 * (10 ^ 9 / (10 ^ 9 - 1)) := by gcongr
          _ = ct / (10 ^ 9 - 1) := by field_simp

/-- The binomial series computes while the payment count times the rate is below `10^-9`. Each term is at most
`10^-9` times the one before it, so the running sum and the rest of the series stay at most `2`. -/
private lemma powerMinusOneLoop_computes (rate : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (pr : Nat) (hpr : pr < 2 ^ 32) (hsmall : (pr : ℚ) * rate.toRat < 1 / 10 ^ 9) :
    ∀ (d index : Nat) (ct rs : Number), pr - index = d → 1 ≤ index → ct.isNormalized → rs.isNormalized →
      0 ≤ ct.toRat → 0 ≤ rs.toRat → (rs.toRat + ct.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ d ≤ 2 →
      ∃ r, powerMinusOneLoop rate pr index ct rs = .ok r ∧ rs.toRat ≤ r.toRat ∧ r.toRat ≤ 2 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index ct rs hd hi hc hs hc0 hs0 hB
    have hpow1 : (1 : ℚ) ≤ (1 + ε) ^ d := one_le_pow₀ (by linarith)
    have hq : 0 ≤ ct.toRat / (10 ^ 9 - 1) := by positivity
    have hsum : rs.toRat + ct.toRat / (10 ^ 9 - 1) ≤ 2 :=
      le_trans (le_mul_of_one_le_right (by positivity) hpow1) hB
    have hrs2 : rs.toRat ≤ 2 := by linarith
    have hct2 : ct.toRat ≤ 2 * (10 ^ 9 - 1) := by
      have : ct.toRat / (10 ^ 9 - 1) ≤ 2 := by linarith
      rwa [div_le_iff₀ (by norm_num)] at this
    rw [powerMinusOneLoop]
    split
    · rename_i hlt
      have hpr1 : (1 : ℚ) ≤ pr := by exact_mod_cast (by omega : 1 ≤ pr)
      have hr1 : rate.toRat < 1 := by
        have : rate.toRat ≤ pr * rate.toRat := le_mul_of_one_le_left hr0 hpr1
        linarith
      have hk1 := Number.ofInt64_nat (pr - index) (by omega)
      have hk2 := Number.ofInt64_nat (index + 1) (by omega)
      have hk1l : ((pr - index : ℕ) : ℚ) ≤ 2 ^ 32 := by
        have : pr - index ≤ 2 ^ 32 := by omega
        exact_mod_cast this
      have hk2g : (1 : ℚ) ≤ ((index + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ index + 1)
      obtain ⟨c1, h1⟩ := Number.operator_mul_ok_of_abs ct rate .to_nearest hc hrate
        (by rw [abs_of_nonneg hc0]; linarith) (by rw [abs_of_nonneg hr0]; linarith)
      have hc1 := Number.operator_mul_isNormalized _ _ c1 _ hc hrate h1
      have hc10 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc hrate h1) (mul_nonneg hc0 hr0)
      have u1 := (Number.mul_near _ _ _ hc hrate h1).le (mul_nonneg hc0 hr0)
      have hc1l : c1.toRat ≤ 4 * 10 ^ 9 := by
        calc c1.toRat ≤ ct.toRat * rate.toRat * (1 + ε) := u1
          _ ≤ (2 * (10 ^ 9 - 1)) * 1 * 2 := by gcongr; linarith
          _ ≤ 4 * 10 ^ 9 := by norm_num
      obtain ⟨c2, h2⟩ := Number.operator_mul_ok_of_abs c1 _ .to_nearest hc1 (Number.ofInt64_isNormalized _)
        (by rw [abs_of_nonneg hc10]; linarith) (by rw [hk1, abs_of_nonneg (by positivity)]; linarith)
      have hc2 := Number.operator_mul_isNormalized _ _ c2 _ hc1 (Number.ofInt64_isNormalized _) h2
      have hc20 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc1 (Number.ofInt64_isNormalized _) h2)
        (mul_nonneg hc10 (by rw [hk1]; positivity))
      have u2 := (Number.mul_near _ _ _ hc1 (Number.ofInt64_isNormalized _) h2).le
        (mul_nonneg hc10 (by rw [hk1]; positivity))
      rw [hk1] at u2
      have hc2l : c2.toRat ≤ 4 * 10 ^ 9 * 2 ^ 32 * 2 := by
        calc c2.toRat ≤ c1.toRat * ((pr - index : ℕ) : ℚ) * (1 + ε) := u2
          _ ≤ 4 * 10 ^ 9 * 2 ^ 32 * 2 := by gcongr; linarith
      obtain ⟨c3, h3⟩ := Number.operator_div_ok_of_abs c2 _ .to_nearest hc2 (Number.ofInt64_isNormalized _)
        (by rw [abs_of_nonneg hc20]; linarith)
        (by
          rw [hk2, abs_of_nonneg (by positivity)]
          exact le_trans (by norm_num) hk2g)
      have hc3 := Number.operator_div_isNormalized _ _ c3 _ hc2 (Number.ofInt64_isNormalized _) h3
      have hc30 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hc2 (Number.ofInt64_isNormalized _) h3)
        (div_nonneg hc20 (by rw [hk2]; positivity))
      have u3 := (Number.div_near _ _ _ hc2 (Number.ofInt64_isNormalized _) h3).le
        (div_nonneg hc20 (by rw [hk2]; positivity))
      rw [hk2] at u3
      have hc3l : c3.toRat ≤ 4 * 10 ^ 9 * 2 ^ 32 * 2 * 2 := by
        calc c3.toRat ≤ c2.toRat / ((index + 1 : ℕ) : ℚ) * (1 + ε) := u3
          _ ≤ c2.toRat / 1 * 2 := by gcongr; linarith
          _ ≤ _ := by rw [div_one]; linarith
      obtain ⟨ns, h4⟩ := Number.operator_add_ok_of_abs rs c3 .to_nearest hs hc3
        (by rw [abs_of_nonneg hs0]; linarith) (by rw [abs_of_nonneg hc30]; linarith)
      have hns := operator_add_isNormalized_to_nearest_sz _ _ ns hs hc3 h4
      have hns0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) (add_nonneg hs0 hc30)
      have hrsns : rs.toRat ≤ ns.toRat :=
        rn_ge (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) rs hs (by linarith)
      -- each term is at most `10^-9` times the one before it
      have hidx : ((pr - index : ℕ) : ℚ) / ((index + 1 : ℕ) : ℚ) ≤ pr / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : ((pr - index : ℕ) : ℚ) ≤ pr := by exact_mod_cast Nat.sub_le pr index
        have : (2 : ℚ) ≤ ((index + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 ≤ index + 1)
        nlinarith
      have hterm : c3.toRat ≤ ct.toRat / 10 ^ 9 := by
        have hb3 : (1 + ε) ^ 3 ≤ 2 := by
          have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
          push_cast at this; linarith
        have e1 : c3.toRat ≤ ct.toRat * rate.toRat * (((pr - index : ℕ) : ℚ) / ((index + 1 : ℕ) : ℚ)) *
            (1 + ε) ^ 3 := by
          have hd1 : (0 : ℚ) < ((index + 1 : ℕ) : ℚ) := by positivity
          calc c3.toRat ≤ c2.toRat / ((index + 1 : ℕ) : ℚ) * (1 + ε) := u3
            _ ≤ c1.toRat * ((pr - index : ℕ) : ℚ) * (1 + ε) / ((index + 1 : ℕ) : ℚ) * (1 + ε) := by
                gcongr
            _ ≤ ct.toRat * rate.toRat * (1 + ε) * ((pr - index : ℕ) : ℚ) * (1 + ε) /
                ((index + 1 : ℕ) : ℚ) * (1 + ε) := by gcongr
            _ = _ := by ring
        have e2 : ct.toRat * rate.toRat * (((pr - index : ℕ) : ℚ) / ((index + 1 : ℕ) : ℚ)) * (1 + ε) ^ 3 ≤
            ct.toRat * rate.toRat * (pr / 2) * 2 := by
          gcongr
        have e3 : ct.toRat * rate.toRat * (pr / 2) * 2 ≤ ct.toRat / 10 ^ 9 := by
          have : rate.toRat * pr ≤ 1 / 10 ^ 9 := by linarith
          calc ct.toRat * rate.toRat * (pr / 2) * 2 = ct.toRat * (rate.toRat * pr) := by ring
            _ ≤ ct.toRat * (1 / 10 ^ 9) := mul_le_mul_of_nonneg_left this hc0
            _ = ct.toRat / 10 ^ 9 := by ring
        linarith
      have u4 := (Number.add_near _ _ _ hs hc3 h4).le (add_nonneg hs0 hc30)
      rw [h1, ok_bind, Nat.toInt64Checked_of_lt (n := pr - index) (by omega), ok_bind, h2, ok_bind,
        Nat.toInt64Checked_of_lt (n := index + 1) (by omega), ok_bind, h3, ok_bind, h4, ok_bind]
      split
      · exact ⟨rs, rfl, le_rfl, hrs2⟩
      · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have hB' : (ns.toRat + c3.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ d' ≤ 2 :=
          le_trans (loop_rest_le _ _ _ _ _ d' he.le hc30 hterm u4) hB
        obtain ⟨r, hr, hnsr, hr2⟩ := ih d' (by omega) (index + 1) c3 ns (by omega) (by omega) hc3 hns hc30 hns0 hB'
        exact ⟨r, hr, le_trans hrsns hnsr, hr2⟩
    · exact ⟨rs, rfl, le_rfl, hrs2⟩

/-- `10^-12` and `1 + 10^-12` as normalized `Number`s. -/
private lemma Number.tenth12 : (∃ w : Number, w.isNormalized ∧ w.toRat = 1 / 10 ^ 12) ∧
    ∃ w : Number, w.isNormalized ∧ w.toRat = 1 + 1 / 10 ^ 12 := by
  have hs : minExponent + 18 ≤ (-12 : ℤ) ∧ (-12 : ℤ) ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; norm_num
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (-12) (by norm_num) hs
  obtain ⟨w', hw', hwv'⟩ := Number.exists_normalized_int_mul_pow (10 ^ 12 + 1) (-12) (by norm_num) hs
  exact ⟨⟨w, hw, by rw [hwv]; norm_num⟩, ⟨w', hw', by rw [hwv']; norm_num⟩⟩

/-- The count `k ≠ 0` and a rate above zero pass the zero checks of the payment factor. -/
private lemma zero_checks (rate : Number) (k : UInt32) (hrate : rate.isNormalized) (hr : 0 < rate.toRat)
    (hk0 : k ≠ 0) : (k == 0) = false ∧ rate.operator_eq Number.zero = false := by
  refine ⟨by simpa using hk0, ?_⟩
  cases h : rate.operator_eq Number.zero
  · rfl
  · have := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp h
    rw [Number.toRat_zero] at this
    linarith

/-- `(1 + rate)^k − 1` computes for a rate of at least `10^-12` with `k` times the rate at most `137`. It is
at least `10^-12` and below `10^70`. -/
private lemma computePowerMinusOneHybrid_computes (rate : Number) (k : UInt32) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hk0 : k ≠ 0) (hkr : (k.toNat : ℚ) * rate.toRat ≤ 137) :
    ∃ pm, computePowerMinusOneHybrid rate (Number.ofInt64 k.toInt64) k = .ok pm ∧
      pm.isNormalized ∧ 1 / 10 ^ 12 ≤ pm.toRat ∧ pm.toRat < 10 ^ 70 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  have hone := Number.ofInt64_isNormalized 1
  have hk32 : (k.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast k.toNat_lt
  have hk1 : (1 : ℚ) ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h0 => hk0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hr0 : 0 ≤ rate.toRat := le_trans (by positivity) hlow
  have hr137 : rate.toRat ≤ 137 := le_trans (le_mul_of_one_le_left hr0 hk1) hkr
  obtain ⟨⟨w12, hw12N, hw12⟩, ⟨w1, hw1N, hw1⟩⟩ := Number.tenth12
  obtain ⟨hk', hz⟩ := zero_checks rate k hrate (lt_of_lt_of_le (by positivity) hlow) hk0
  have hcond : (k == 0 || rate.operator_eq Number.zero) = false := by rw [hk', hz]; rfl
  obtain ⟨nr, hnr⟩ := Number.operator_mul_ok_of_abs _ rate .to_nearest hN hrate
    (by rw [hNv, abs_of_nonneg (by positivity)]; linarith) (by rw [abs_of_nonneg hr0]; linarith)
  have hnrN := Number.operator_mul_isNormalized _ _ nr _ hN hrate hnr
  have hnrR := operator_mul_rounded_to_nearest _ _ _ hN hrate hnr
  obtain ⟨w, hw, hwN, hwv⟩ := Number.cancellationThreshold
  unfold computePowerMinusOneHybrid
  rw [hcond, if_neg (by decide)]
  dsimp only
  rw [pure_bind, hnr, ok_bind, hw, ok_bind]
  by_cases hge : nr.operator_ge w = true
  · -- the closed form: `(1 + rate)^k` by squaring, less one
    rw [if_pos hge]
    obtain ⟨b, hb⟩ := Number.operator_add_ok_of_abs (Number.ofInt64 1) rate .to_nearest hone hrate
      (by rw [Number.ofInt64_one_toRat]; norm_num) (by rw [abs_of_nonneg hr0]; linarith)
    have hbN := operator_add_isNormalized_to_nearest_sz _ _ b hone hrate hb
    have hbR := operator_add_rounded_to_nearest _ _ _ hone hrate hb
    rw [Number.ofInt64_one_toRat] at hbR
    have hb1 : 1 ≤ b.toRat := by
      have := rn_ge hbR _ hone (by rw [Number.ofInt64_one_toRat]; linarith)
      rwa [Number.ofInt64_one_toRat] at this
    have hblo : 1 + 1 / 10 ^ 12 ≤ b.toRat := by
      have := rn_ge hbR w1 hw1N (by rw [hw1]; linarith)
      rwa [hw1] at this
    have hble := (Number.add_near _ _ _ hone hrate hb).le (by rw [Number.ofInt64_one_toRat]; linarith)
    rw [Number.ofInt64_one_toRat] at hble
    -- `b^k (1 + ε)^(2k) ≤ (1 + rate)^k (1 + ε)^(3k) ≤ 3^137 · 2`
    have hexp : (1 + rate.toRat) ^ k.toNat ≤ 3 ^ 137 := by
      have h := one_add_pow_le_exp rate.toRat 0 k.toNat 137 hr0 le_rfl (by norm_num) (by rw [add_zero]; exact hkr)
      rw [sub_zero, div_one] at h
      exact le_trans h (pow_le_pow_left₀ (by norm_num) (by norm_num) 137)
    have hlin := one_add_pow_le_lin ε (3 * k.toNat) he.le (by
      push_cast
      calc (3 : ℚ) * k.toNat * ε ≤ 3 * 2 ^ 32 * (1 / 10 ^ 18) := by gcongr
        _ ≤ 1 / 2 := by norm_num)
    have he3 : (1 + ε) ^ (3 * k.toNat) ≤ 2 := by
      refine le_trans hlin ?_
      push_cast
      calc 1 + 2 * (3 * (k.toNat : ℚ)) * ε ≤ 1 + 2 * (3 * 2 ^ 32) * (1 / 10 ^ 18) := by gcongr
        _ ≤ 2 := by norm_num
    have hbig : b.toRat ^ k.toNat * (1 + ε) ^ (2 * k.toNat) ≤ 3 ^ 137 * 2 := by
      have hbk : b.toRat ^ k.toNat ≤ (1 + rate.toRat) ^ k.toNat * (1 + ε) ^ k.toNat := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hble _
      have hpow3 : (1 + ε) ^ k.toNat * (1 + ε) ^ (2 * k.toNat) = (1 + ε) ^ (3 * k.toNat) := by
        rw [← pow_add]; ring_nf
      calc b.toRat ^ k.toNat * (1 + ε) ^ (2 * k.toNat)
          ≤ (1 + rate.toRat) ^ k.toNat * (1 + ε) ^ k.toNat * (1 + ε) ^ (2 * k.toNat) := by gcongr
        _ = (1 + rate.toRat) ^ k.toNat * (1 + ε) ^ (3 * k.toNat) := by rw [mul_assoc, hpow3]
        _ ≤ 3 ^ 137 * 2 := by gcongr
    obtain ⟨raised, hraised⟩ := Number.power_computes b hbN hb1 k.toNat (by
      have : (3 : ℚ) ^ 137 * 2 < 10 ^ 199 := by norm_num
      linarith)
    have hk1' : 1 ≤ k.toNat := by exact_mod_cast hk1
    have hrN := Number.power_isNormalized b hbN _ raised hraised
    have hrb := Number.power_ge_base b hbN hb1 _ raised hk1' hraised
    have hrle := Number.power_le b hbN hb1 _ raised hk1' hraised
    have hrl : raised.toRat ≤ 3 ^ 137 * 2 := by nlinarith
    obtain ⟨pm, hpm⟩ := Number.operator_sub_ok_of_abs raised (Number.ofInt64 1) .to_nearest hrN hone
      (by rw [abs_of_nonneg (by linarith)]; linarith [show (3 : ℚ) ^ 137 * 2 < 10 ^ 200 by norm_num])
      (by rw [Number.ofInt64_one_toRat]; norm_num)
    refine ⟨pm, ?_, operator_sub_isNormalized_to_nearest_sz _ _ pm hrN hone hpm, ?_, ?_⟩
    · rw [hb, ok_bind, hraised, ok_bind, hpm]
    · have := rn_ge (operator_sub_rounded_to_nearest _ _ _ hrN hone hpm) w12 hw12N
        (by rw [hw12, Number.ofInt64_one_toRat]; linarith)
      rwa [hw12] at this
    · have := (Number.sub_near _ _ _ hrN hone hpm).le (by rw [Number.ofInt64_one_toRat]; linarith)
      rw [Number.ofInt64_one_toRat] at this
      have : (raised.toRat - 1) * (1 + ε) ≤ 3 ^ 137 * 2 * 2 := by gcongr <;> linarith
      linarith [show (3 : ℚ) ^ 137 * 2 * 2 < 10 ^ 70 by norm_num]
  · -- the binomial series, for `k·rate` below `10^-9`
    rw [if_neg hge]
    have hsm : (k.toNat : ℚ) * rate.toRat < 1 / 10 ^ 9 := by
      by_contra hc
      push Not at hc
      have := rn_ge hnrR w hwN (by rw [hwv, hNv]; exact hc)
      exact hge ((operator_ge_iff nr w hnrN hwN).mpr this)
    have hnr0 := rn_nonneg hnrR (by rw [hNv]; positivity)
    have hnrle := (Number.mul_near _ _ _ hN hrate hnr).le (by rw [hNv]; positivity)
    rw [hNv] at hnrle
    have hnrlo : 1 / 10 ^ 12 ≤ nr.toRat := by
      have := rn_ge hnrR w12 hw12N (by rw [hw12, hNv]; linarith [le_mul_of_one_le_left hr0 hk1])
      rwa [hw12] at this
    have hpowk : (1 + ε) ^ (k.toNat - 1) ≤ 2 := by
      have hlin := one_add_pow_le_lin ε (k.toNat - 1) he.le (by
        calc ((k.toNat - 1 : ℕ) : ℚ) * ε ≤ 2 ^ 32 * (1 / 10 ^ 18) := by
              gcongr
              exact le_trans (by exact_mod_cast Nat.sub_le _ _) hk32.le
          _ ≤ 1 / 2 := by norm_num)
      refine le_trans hlin ?_
      have : ((k.toNat - 1 : ℕ) : ℚ) * ε ≤ 2 ^ 32 * (1 / 10 ^ 18) := by
        gcongr
        exact le_trans (by exact_mod_cast Nat.sub_le _ _) hk32.le
      linarith [show (2 : ℚ) * (2 ^ 32 * (1 / 10 ^ 18)) ≤ 1 by norm_num]
    have hB : (nr.toRat + nr.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ (k.toNat - 1) ≤ 2 := by
      have hn1 : nr.toRat ≤ 2 / 10 ^ 9 := by
        calc nr.toRat ≤ k.toNat * rate.toRat * (1 + ε) := hnrle
          _ ≤ 1 / 10 ^ 9 * 2 := by gcongr; linarith
          _ = 2 / 10 ^ 9 := by ring
      calc (nr.toRat + nr.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ (k.toNat - 1)
          ≤ (2 / 10 ^ 9 + 2 / 10 ^ 9 / (10 ^ 9 - 1)) * 2 := by gcongr
        _ ≤ 2 := by norm_num
    obtain ⟨pm, hloop, hnrpm, hpm2⟩ := powerMinusOneLoop_computes rate hrate hr0 k.toNat k.toNat_lt hsm
      (k.toNat - 1) 1 nr nr rfl le_rfl hnrN hnrN hnr0 hnr0 hB
    refine ⟨pm, ?_, ?_, le_trans hnrlo hnrpm, by linarith [show (2 : ℚ) < 10 ^ 70 by norm_num]⟩
    · unfold computePowerMinusOne
      rw [hcond, if_neg (by decide)]
      dsimp only
      rw [pure_bind, hnr, ok_bind, hloop]
    · have h : computePowerMinusOneHybrid rate (Number.ofInt64 k.toInt64) k = .ok pm := by
        unfold computePowerMinusOneHybrid
        rw [hcond, if_neg (by decide)]
        dsimp only
        rw [pure_bind, hnr, ok_bind, hw, ok_bind, if_neg hge]
        unfold computePowerMinusOne
        rw [hcond, if_neg (by decide)]
        dsimp only
        rw [pure_bind, hnr, ok_bind, hloop]
      exact computePowerMinusOneHybrid_isNormalized rate _ k pm hrate hN h

/-- The payment factor computes for a rate of at least `10^-12` with `k` times the rate at most `137`. It is at
least `10^-82`. -/
private lemma computePaymentFactor_computes (rate : Number) (k : UInt32) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat) (hk0 : k ≠ 0) (hkr : (k.toNat : ℚ) * rate.toRat ≤ 137) :
    ∃ f, computePaymentFactor rate (Number.ofInt64 k.toInt64) k = .ok f ∧ f.isNormalized ∧
      1 / 10 ^ 82 ≤ f.toRat := by
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
  have hpm0 : 0 ≤ pm.toRat := le_trans (by positivity) hpmlo
  obtain ⟨rr, hrr⟩ := Number.operator_add_ok_of_abs (Number.ofInt64 1) pm .to_nearest hone hpmN
    (by rw [Number.ofInt64_one_toRat]; norm_num)
    (by rw [abs_of_nonneg hpm0]; linarith [show (10 : ℚ) ^ 70 < 10 ^ 200 by norm_num])
  have hrrN := operator_add_isNormalized_to_nearest_sz _ _ rr hone hpmN hrr
  have hrrR := operator_add_rounded_to_nearest _ _ _ hone hpmN hrr
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
  obtain ⟨num, hnum⟩ := Number.operator_mul_ok_of_abs rate rr .to_nearest hrate hrrN
    (by rw [abs_of_nonneg hr0]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 71 < 10 ^ 200 by norm_num])
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
  have hnumR := operator_mul_rounded_to_nearest _ _ _ hrate hrrN hnum
  have hnumlo : 1 / 10 ^ 12 ≤ num.toRat := by
    have := rn_ge hnumR w12 hw12N (by rw [hw12]; nlinarith)
    rwa [hw12] at this
  have hnumle := (Number.mul_near _ _ _ hrate hrrN hnum).le (by nlinarith)
  have hnuml : num.toRat ≤ 10 ^ 75 := by
    calc num.toRat ≤ rate.toRat * rr.toRat * (1 + ε) := hnumle
      _ ≤ 137 * 10 ^ 71 * 2 := by gcongr; linarith
      _ ≤ 10 ^ 75 := by norm_num
  obtain ⟨f, hf⟩ := Number.operator_div_ok_of_abs num pm .to_nearest hnumN hpmN
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 75 < 10 ^ 200 by norm_num])
    (by
      rw [abs_of_nonneg hpm0]
      refine le_trans ?_ hpmlo
      rw [zpow_neg]; norm_num)
  have hfN := Number.operator_div_isNormalized _ _ f _ hnumN hpmN hf
  obtain ⟨w82, hw82N, hw82⟩ := Number.exists_normalized_int_mul_pow 1 (-82) (by norm_num)
    (by unfold minExponent maxExponent; norm_num)
  have hflo : 1 / 10 ^ 82 ≤ f.toRat := by
    have hq : (1 : ℚ) / 10 ^ 82 ≤ num.toRat / pm.toRat := by
      rw [le_div_iff₀ (lt_of_lt_of_le (by positivity) hpmlo)]
      calc 1 / 10 ^ 82 * pm.toRat ≤ 1 / 10 ^ 82 * 10 ^ 70 := by gcongr
        _ ≤ 1 / 10 ^ 12 := by norm_num
        _ ≤ num.toRat := hnumlo
    have := rn_ge (operator_div_rounded_to_nearest _ _ _ hnumN hpmN hf) w82 hw82N
      (by rw [hw82]; norm_num at hq ⊢; linarith)
    rw [hw82] at this
    norm_num at this ⊢
    linarith
  refine ⟨f, ?_, hfN, hflo⟩
  unfold computePaymentFactor
  rw [hk', if_neg (by decide)]
  dsimp only
  rw [pure_bind, hz, if_neg (by decide), hpm, ok_bind, hrr, ok_bind, hnum, ok_bind, hf]

/-- The theoretical principal of `k` payments computes for the periodic rate of a loan's terms and a PeriodicPayment
from zero up to `10^100`, while `k` payment intervals fit the 32-bit clock. -/
lemma loanPrincipalFromPeriodicPayment_computes (pp rate : Number) (ir : TenthBips32) (interval k : UInt32)
    (hrate : loanPeriodicRate ir interval = .ok rate) (hir : ir.toNat ≤ 100000) (hiv : 60 ≤ interval.toNat)
    (hk : k.toNat * interval.toNat < 2 ^ 32) (hpp : pp.isNormalized) (hpp0 : 0 ≤ pp.toRat)
    (hppl : pp.toRat < 10 ^ 100) :
    ∃ tpo, loanPrincipalFromPeriodicPayment pp rate k = .ok tpo := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hrN := loanPeriodicRate_isNormalized ir interval rate hrate
  have hr0 := loanPeriodicRate_nonneg ir interval rate hrate
  obtain ⟨hup, -⟩ := loanPeriodicRate_bounds ir interval rate hrate
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  have hk32 : (k.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast k.toNat_lt
  by_cases hk0 : k = 0
  · subst hk0
    exact ⟨Number.zero, rfl⟩
  have hk' : (k == 0) = false := by simpa using hk0
  unfold loanPrincipalFromPeriodicPayment
  rw [hk', if_neg (by decide)]
  dsimp only
  rw [pure_bind]
  by_cases hz : rate.operator_eq Number.zero = true
  · rw [if_pos hz]
    exact Number.operator_mul_ok_of_abs pp _ .to_nearest hpp hN
      (by rw [abs_of_nonneg hpp0]; linarith [show (10 : ℚ) ^ 100 < 10 ^ 200 by norm_num])
      (by rw [hNv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num])
  rw [if_neg hz]
  have hr00 : rate.toRat ≠ 0 := fun h0 =>
    hz ((operator_eq_iff rate Number.zero hrN Number.zero_isNormalized).mpr (by rw [h0, Number.toRat_zero]))
  have hlow := loanPeriodicRate_ge ir interval rate hiv hrate hr00
  -- `k` intervals fit the clock, so `k` times the rate is at most `137`
  have hkr : (k.toNat : ℚ) * rate.toRat ≤ 137 := by
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
  obtain ⟨f, hf, hfN, hflo⟩ := computePaymentFactor_computes rate k hrN hlow hk0 hkr
  rw [hf, ok_bind]
  exact Number.operator_div_ok_of_abs pp f .to_nearest hpp hfN
    (by rw [abs_of_nonneg hpp0]; linarith [show (10 : ℚ) ^ 100 < 10 ^ 200 by norm_num])
    (by
      rw [abs_of_nonneg (le_trans (by positivity) hflo)]
      refine le_trans ?_ hflo
      rw [zpow_neg]; norm_num)

end XRPL.Model.Lending
