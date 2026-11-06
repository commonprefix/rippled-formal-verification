import XRPL.Properties.Lending.Loan.Common.RoundingError
import XRPL.Properties.Lending.Loan.Common.SetLawful

/-! # How small the payment factor can be

The payment factor of a positive rate over `n` payments is at least the rate, and at least `1/(64·n)` while `n`
times the rate is at most one half. So the principal a periodic payment implies is at most `70·n` payments. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Number.power_ge_one computePowerMinusOneHybrid_nonneg rn_ge rn_nonneg Number.ofInt64_one_toRat
  from XRPL.Properties.Lending.Loan.Common.SetLawful

local notation "ε" => Number.nearestError

private lemma eps_pos : 0 < ε := Number.nearestError_pos

private lemma eps_le : ε ≤ 1 / 10 ^ 18 := Number.nearestError_le

/-- A power by squaring is at most the exact power, times `(1 + ε)^(2k)` over `1 + ε`. Each squaring
doubles the error of the half power and adds one rounding, each multiplication by the base adds one. -/
private lemma Number.power_le (base : Number) (hb : base.isNormalized) (h1 : 1 ≤ base.toRat) :
    ∀ (k : Nat) (r : Number), 1 ≤ k → base.power k = .ok r →
      r.toRat * (1 + ε) ≤ base.toRat ^ k * (1 + ε) ^ (2 * k) := by
  have he := eps_pos
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hk h
    match k, ih with
    | 0, _ => omega
    | 1, _ =>
      rw [Number.power] at h
      cases h
      have h0 : 0 ≤ base.toRat * (1 + ε) := by nlinarith
      have : base.toRat * (1 + ε) * 1 ≤ base.toRat * (1 + ε) * (1 + ε) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
      calc base.toRat * (1 + ε) = base.toRat * (1 + ε) * 1 := by ring
        _ ≤ base.toRat * (1 + ε) * (1 + ε) := this
        _ = base.toRat ^ 1 * (1 + ε) ^ (2 * 1) := by ring
    | j + 2, ih =>
      rw [Number.power] at h
      obtain ⟨half, hh, h⟩ := bind_ok_peel _ _ _ h
      have hhalfN := Number.power_isNormalized base hb _ half hh
      have hhalf1 := Number.power_ge_one base hb h1 _ half hh
      have hhalf := ih ((j + 2) / 2) (by omega) half (by omega) hh
      obtain ⟨sq, hs, h⟩ := bind_ok_peel _ _ _ h
      have hsqN := Number.operator_mul_isNormalized _ _ sq _ hhalfN hhalfN hs
      have hsq := (Number.mul_near _ _ _ hhalfN hhalfN hs).le (by nlinarith)
      have hsq' : sq.toRat * (1 + ε) ≤ base.toRat ^ (2 * ((j + 2) / 2)) * (1 + ε) ^ (2 * (2 * ((j + 2) / 2))) := by
        have h2 : (half.toRat * (1 + ε)) ^ 2 ≤ (base.toRat ^ ((j + 2) / 2) * (1 + ε) ^ (2 * ((j + 2) / 2))) ^ 2 :=
          pow_le_pow_left₀ (by nlinarith) hhalf 2
        have e1 : (base.toRat ^ ((j + 2) / 2) * (1 + ε) ^ (2 * ((j + 2) / 2))) ^ 2 =
            base.toRat ^ (2 * ((j + 2) / 2)) * (1 + ε) ^ (2 * (2 * ((j + 2) / 2))) := by ring
        rw [e1] at h2
        calc sq.toRat * (1 + ε) ≤ half.toRat * half.toRat * (1 + ε) * (1 + ε) :=
              mul_le_mul_of_nonneg_right hsq (by linarith)
          _ = (half.toRat * (1 + ε)) ^ 2 := by ring
          _ ≤ _ := h2
      have hsq1 : 1 ≤ sq.toRat := by
        have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hhalfN hhalfN hs) _ (Number.ofInt64_isNormalized 1)
          (by rw [Number.ofInt64_one_toRat]; nlinarith)
        rwa [Number.ofInt64_one_toRat] at this
      split at h
      · rename_i hodd
        have hk : j + 2 = 2 * ((j + 2) / 2) + 1 := by
          have : (j + 2) % 2 = 1 := by simpa using hodd
          omega
        have hr := (Number.mul_near _ _ _ hsqN hb h).le (by nlinarith)
        have hb0 : 0 ≤ base.toRat := by linarith
        have hpow : (1 + ε) ^ (2 * (2 * ((j + 2) / 2))) * (1 + ε) ≤ (1 + ε) ^ (2 * (j + 2)) := by
          rw [← pow_succ]
          exact pow_le_pow_right₀ (by linarith) (by omega)
        calc r.toRat * (1 + ε) ≤ sq.toRat * base.toRat * (1 + ε) * (1 + ε) :=
              mul_le_mul_of_nonneg_right hr (by linarith)
          _ = (sq.toRat * (1 + ε)) * base.toRat * (1 + ε) := by ring
          _ ≤ (base.toRat ^ (2 * ((j + 2) / 2)) * (1 + ε) ^ (2 * (2 * ((j + 2) / 2)))) * base.toRat * (1 + ε) := by
              gcongr
          _ = base.toRat ^ (2 * ((j + 2) / 2) + 1) * ((1 + ε) ^ (2 * (2 * ((j + 2) / 2))) * (1 + ε)) := by ring
          _ ≤ base.toRat ^ (2 * ((j + 2) / 2) + 1) * (1 + ε) ^ (2 * (j + 2)) := by gcongr
          _ = base.toRat ^ (j + 2) * (1 + ε) ^ (2 * (j + 2)) := by rw [← hk]
      · rename_i heven
        have hk : j + 2 = 2 * ((j + 2) / 2) := by
          have : (j + 2) % 2 ≠ 1 := by simpa using heven
          omega
        cases h
        rw [hk]
        exact hsq'

/-- A count below `2^63` converts to a `Number` of the same value. -/
private lemma Number.ofInt64_nat (k : ℕ) (hk : k < 2 ^ 63) : (Number.ofInt64 k.toInt64).toRat = k := by
  have hv : (k.toInt64).toInt = k := Int64.toInt_ofNat_of_lt hk
  have hne : k.toInt64 ≠ Int64.minValue := by
    intro h
    have := congrArg Int64.toInt h
    rw [hv, show Int64.minValue.toInt = -2 ^ 63 from by decide] at this
    omega
  rw [Number.ofInt64_toRat_of_ne _ hne, hv]
  push_cast; rfl

/-- `10^-9` as a `Number`. -/
private lemma Number.cancellationThreshold :
    ∃ w : Number, Number.from_rep 1 (-9) largeRange.min largeRange.max .to_nearest = .ok w ∧ w.isNormalized ∧
      w.toRat = 1 / 10 ^ 9 := by
  obtain ⟨w, hw, hv, hn⟩ := Number.from_rep_exact (1 : Int64) (-9) .to_nearest (by decide)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  refine ⟨w, hw, hn, ?_⟩
  rw [hv, show (1 : Int64).toInt = 1 from by decide]
  norm_num

/-- The binomial series stays within `(1 + ε)` per step of its first term over `1 − 10^-9`. While `n` times
the rate is below `10^-9`, each term is at most `10^-9` times the one before it. -/
private lemma powerMinusOneLoop_le (rate : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (pr : Nat)
    (hpr : pr < 2 ^ 32) (hsmall : (pr : ℚ) * rate.toRat < 1 / 10 ^ 9) :
    ∀ (d index : Nat) (ct rs r : Number), pr - index = d → 1 ≤ index → ct.isNormalized → rs.isNormalized →
      0 ≤ ct.toRat → 0 ≤ rs.toRat → powerMinusOneLoop rate pr index ct rs = .ok r →
      r.toRat ≤ (rs.toRat + ct.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ d := by
  have he := eps_pos
  have he' := eps_le
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index ct rs r hd hi hc hs hc0 hs0 h
    have hpow1 : (1 : ℚ) ≤ (1 + ε) ^ d := one_le_pow₀ (by linarith)
    have hq : 0 ≤ ct.toRat / (10 ^ 9 - 1) := by positivity
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
      have hk1 := Number.ofInt64_nat (pr - index) (by omega)
      have hk2 := Number.ofInt64_nat (index + 1) (by omega)
      have hc1 := Number.operator_mul_isNormalized _ _ c1 _ hc hrate h1
      have hc2 := Number.operator_mul_isNormalized _ _ c2 _ hc1 (Number.ofInt64_isNormalized _) h2
      have hc3 := Number.operator_div_isNormalized _ _ c3 _ hc2 (Number.ofInt64_isNormalized _) h3
      have hns := operator_add_isNormalized_to_nearest_sz _ _ ns hs hc3 h4
      have hc10 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc hrate h1) (mul_nonneg hc0 hr0)
      have hc20 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc1 (Number.ofInt64_isNormalized _) h2)
        (mul_nonneg hc10 (by rw [hk1]; positivity))
      have hc30 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hc2 (Number.ofInt64_isNormalized _) h3)
        (div_nonneg hc20 (by rw [hk2]; positivity))
      have hns0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) (add_nonneg hs0 hc30)
      -- each term is at most `10^-9` times the one before it
      have u1 := (Number.mul_near _ _ _ hc hrate h1).le (mul_nonneg hc0 hr0)
      have u2 := (Number.mul_near _ _ _ hc1 (Number.ofInt64_isNormalized _) h2).le
        (mul_nonneg hc10 (by rw [hk1]; positivity))
      have u3 := (Number.div_near _ _ _ hc2 (Number.ofInt64_isNormalized _) h3).le
        (div_nonneg hc20 (by rw [hk2]; positivity))
      rw [hk1] at u2
      rw [hk2] at u3
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
      split at h
      · cases h
        nlinarith
      · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have := ih d' (by omega) (index + 1) c3 ns r (by omega) (by omega) hc3 hns hc30 hns0 h
        calc r.toRat ≤ (ns.toRat + c3.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ d' := this
          _ ≤ ((rs.toRat + c3.toRat) * (1 + ε) + c3.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ d' := by gcongr
          _ ≤ ((rs.toRat + c3.toRat) * (1 + ε) + c3.toRat / (10 ^ 9 - 1) * (1 + ε)) * (1 + ε) ^ d' := by
              gcongr
              have : 0 ≤ c3.toRat / (10 ^ 9 - 1) := by positivity
              nlinarith
          _ = (rs.toRat + c3.toRat * (10 ^ 9 / (10 ^ 9 - 1))) * (1 + ε) ^ (d' + 1) := by ring
          _ ≤ (rs.toRat + ct.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ (d' + 1) := by
              gcongr
              calc c3.toRat * (10 ^ 9 / (10 ^ 9 - 1)) ≤ ct.toRat / 10 ^ 9 * (10 ^ 9 / (10 ^ 9 - 1)) := by
                    gcongr
                _ = ct.toRat / (10 ^ 9 - 1) := by field_simp
    · cases h
      nlinarith

/-- `(1 + rate)^n − 1` is at most `64·n·rate` while `n` times the rate is at most one half. The closed form
loses at most `12·n·ε` to rounding, which is small next to `n·rate` at or above `10^-9`. -/
private lemma computePowerMinusOneHybrid_le (rate : Number) (pr : UInt32) (pm : Number)
    (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (hsmall : (pr.toNat : ℚ) * rate.toRat ≤ 1 / 2)
    (h : computePowerMinusOneHybrid rate (Number.ofInt64 pr.toInt64) pr = .ok pm) :
    pm.toRat ≤ 64 * pr.toNat * rate.toRat := by
  have he := eps_pos
  have he' := eps_le
  have hN := Number.ofInt64_isNormalized pr.toInt64
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
    rename_i hge
    have hth : (1 : ℚ) / 10 ^ 9 ≤ nr.toRat := by
      rw [← hwv]; exact (operator_ge_iff nr w hnrN hwN).mp hge
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
    -- the rounding error `12·n·ε` is at most `60·n·rate`, as `n·rate·(1 + ε)` is at least `10^-9`
    have hx : (1 : ℚ) / 10 ^ 9 ≤ pr.toNat * rate.toRat * (1 + ε) := le_trans hth hnrle
    have hNe : 12 * (pr.toNat : ℚ) * ε ≤ 60 * (pr.toNat * rate.toRat) := by
      have h1 : 12 * (pr.toNat : ℚ) * ε * (1 + ε) ≤ 60 * (pr.toNat * rate.toRat) * (1 + ε) := by
        calc 12 * (pr.toNat : ℚ) * ε * (1 + ε) ≤ 12 * 2 ^ 32 * (1 / 10 ^ 18) * (1 + 1 / 10 ^ 18) := by gcongr
          _ ≤ 60 * (1 / 10 ^ 9) := by norm_num
          _ ≤ 60 * (pr.toNat * rate.toRat * (1 + ε)) := by gcongr
          _ = 60 * (pr.toNat * rate.toRat) * (1 + ε) := by ring
      exact le_of_mul_le_mul_right h1 (by linarith)
    have hxe : 12 * (pr.toNat : ℚ) * rate.toRat * pr.toNat * ε ≤ 6 * pr.toNat * ε := by
      have : 12 * (pr.toNat : ℚ) * rate.toRat * pr.toNat * ε = 12 * (pr.toNat * rate.toRat) * (pr.toNat * ε) := by
        ring
      rw [this]
      have : 0 ≤ (pr.toNat : ℚ) * ε := by positivity
      nlinarith
    calc pm.toRat ≤ (raised.toRat - 1) * (1 + ε) := hpm
      _ ≤ ((1 + 2 * pr.toNat * rate.toRat) * (1 + 6 * pr.toNat * ε) - 1) * (1 + ε) := by gcongr
      _ = (2 * pr.toNat * rate.toRat + 6 * pr.toNat * ε + 12 * pr.toNat * rate.toRat * pr.toNat * ε) *
          (1 + ε) := by ring
      _ ≤ (62 * (pr.toNat * rate.toRat)) * (1 + ε) := by gcongr; linarith
      _ ≤ 64 * pr.toNat * rate.toRat := by nlinarith
  · -- the binomial series, for `n·rate` below `10^-9`
    rename_i hlt
    have hlt' : nr.toRat < 1 / 10 ^ 9 := by
      rw [← hwv]
      have : ¬ (w.toRat ≤ nr.toRat) := fun hle => hlt ((operator_ge_iff nr w hnrN hwN).mpr hle)
      exact lt_of_not_ge this
    have hsm : (pr.toNat : ℚ) * rate.toRat < 1 / 10 ^ 9 := by
      by_contra hc
      push Not at hc
      have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hN hrate hnr) w hwN (by rw [hwv, hNv]; exact hc)
      rw [hwv] at this
      linarith
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
      _ ≤ 64 * pr.toNat * rate.toRat := by
          have : (1 : ℚ) + ε ≤ 1 + 1 / 10 ^ 18 := by linarith
          have hx' : 0 ≤ (pr.toNat : ℚ) * rate.toRat := hx0
          calc (pr.toNat * rate.toRat * (1 + ε) + pr.toNat * rate.toRat * (1 + ε) / (10 ^ 9 - 1)) *
                (1 + 1 / 10 ^ 8) = pr.toNat * rate.toRat * ((1 + ε) * (1 + 1 / (10 ^ 9 - 1)) *
                (1 + 1 / 10 ^ 8)) := by ring
            _ ≤ pr.toNat * rate.toRat * ((1 + 1 / 10 ^ 18) * (1 + 1 / (10 ^ 9 - 1)) * (1 + 1 / 10 ^ 8)) := by
                gcongr
            _ ≤ pr.toNat * rate.toRat * 64 := by
                gcongr
                norm_num
            _ = 64 * pr.toNat * rate.toRat := by ring

/-- A normalized `Number` of value zero is `Number.zero`. -/
private lemma Number.eq_zero_of_toRat {x : Number} (hx : x.isNormalized) (h : x.toRat = 0) : x = Number.zero :=
  Number.eq_zero_of_mantissa_zero x hx (Number.toRat_eq_zero_iff.mp h)

/-- A to-nearest quotient by zero fails. -/
private lemma Number.div_zero_error {x y r : Number} (hy : y = Number.zero)
    (h : x.operator_div y .to_nearest = .ok r) : False := by
  unfold Number.operator_div at h
  rw [if_pos (by rw [hy]; decide)] at h
  cases h

/-- A quotient of zero is zero. -/
private lemma Number.zero_div_eq {x y r : Number} (hy : y ≠ Number.zero) (hx : x = Number.zero)
    (h : x.operator_div y .to_nearest = .ok r) : r = Number.zero := by
  unfold Number.operator_div at h
  have hy' : y.operator_eq Number.zero = false := by
    cases hb : y.operator_eq Number.zero
    · rfl
    · exact absurd ((Number.operator_eq_iff_eq _ _).mp hb) hy
  rw [if_neg (by rw [hy']; decide), if_pos (by rw [hx]; decide)] at h
  rw [hx] at h
  exact (Except.ok.inj h).symm

/-- A nonzero payment factor of a positive rate is at least the rate, and at least `1 / (64·n)` while `n` times the
rate is at most one half, each less three roundings. -/
private lemma computePaymentFactor_ge (rate : Number) (pr : UInt32) (f : Number) (hrate : rate.isNormalized)
    (hr0 : 0 < rate.toRat) (h : computePaymentFactor rate (Number.ofInt64 pr.toInt64) pr = .ok f)
    (hf : f.toRat ≠ 0) :
    rate.toRat * (1 - ε) ^ 3 ≤ f.toRat ∧
      ((pr.toNat : ℚ) * rate.toRat ≤ 1 / 2 → (1 - ε) ^ 3 / (64 * pr.toNat) ≤ f.toRat) := by
  have he := eps_pos
  have he' := eps_le
  have hN := Number.ofInt64_isNormalized pr.toInt64
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
  have hrr1 : 1 ≤ rr.toRat := by
    have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hpN hrr) _ hone
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rwa [Number.ofInt64_one_toRat] at this
  have hrrge := (Number.add_near _ _ _ hone hpN hrr).ge (by linarith) (by rw [Number.ofInt64_one_toRat]; linarith)
  rw [Number.ofInt64_one_toRat] at hrrge
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
  have hnumne : num.toRat ≠ 0 := by
    intro h0
    have hz := Number.zero_div_eq (fun hc => hpne (by rw [hc, Number.toRat_zero])) (Number.eq_zero_of_toRat hnumN h0) h
    exact hf (by rw [hz, Number.toRat_zero])
  have hnumge := (Number.mul_near _ _ _ hrate hrrN hnum).ge hnumne (by positivity)
  have h1e : 0 < 1 - ε := by linarith
  have hnum0 : 0 ≤ num.toRat := le_trans (by positivity) hnumge
  have hfge := (Number.div_near _ _ _ hnumN hpN h).ge hf (div_nonneg hnum0 hp0)
  have hkey : rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 / pmo.toRat ≤ f.toRat := by
    calc rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 / pmo.toRat
        = (rate.toRat * ((1 + pmo.toRat) * (1 - ε)) * (1 - ε)) / pmo.toRat * (1 - ε) := by ring
      _ ≤ (rate.toRat * rr.toRat * (1 - ε)) / pmo.toRat * (1 - ε) := by gcongr
      _ ≤ num.toRat / pmo.toRat * (1 - ε) := by gcongr
      _ ≤ f.toRat := hfge
  refine ⟨?_, fun hsmall => ?_⟩
  · refine le_trans ?_ hkey
    rw [le_div_iff₀ hp]
    have : 0 ≤ rate.toRat * (1 - ε) ^ 3 := by positivity
    nlinarith
  · have hle := computePowerMinusOneHybrid_le rate pr pmo hrate hr0.le hsmall hpmo
    refine le_trans ?_ hkey
    rw [div_le_div_iff₀ (by positivity) hp]
    have h3 : 0 ≤ (1 - ε) ^ 3 := by positivity
    calc (1 - ε) ^ 3 * pmo.toRat ≤ (1 - ε) ^ 3 * (64 * pr.toNat * rate.toRat) := by gcongr
      _ = rate.toRat * (1 - ε) ^ 3 * (64 * pr.toNat) := by ring
      _ ≤ rate.toRat * (1 + pmo.toRat) * (1 - ε) ^ 3 * (64 * pr.toNat) := by
          gcongr
          nlinarith [mul_nonneg hr0.le hp0]

/-- The principal a periodic payment implies is at most `70·n` payments, and its interest per period at
most two payments. -/
lemma loanPrincipalFromPeriodicPayment_le_payments (pp rate : Number) (pr : UInt32) (tpo : Number)
    (hpp : pp.isNormalized) (hpp0 : 0 ≤ pp.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (h : loanPrincipalFromPeriodicPayment pp rate pr = .ok tpo) :
    0 ≤ tpo.toRat ∧ tpo.toRat ≤ 70 * pr.toNat * pp.toRat ∧ tpo.toRat * rate.toRat ≤ 2 * pp.toRat := by
  have he := eps_pos
  have he' := eps_le
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  have hN0 : (0 : ℚ) ≤ pr.toNat := by positivity
  have h1e : 0 < 1 - ε := by linarith
  have h1e3 : (1 - 1 / 10 ^ 18 : ℚ) ^ 3 ≤ (1 - ε) ^ 3 := by gcongr
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    rw [Number.toRat_zero]; refine ⟨le_rfl, by positivity, by linarith⟩
  rename_i hpr
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have hpr0 : pr ≠ 0 := by intro h0; apply hpr; simp [h0]
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · -- no interest: `n` payments
    rename_i hz
    have hr := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp hz
    rw [Number.toRat_zero] at hr
    have h0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hpp hN h) (by rw [hNv]; positivity)
    have hle := (Number.mul_near _ _ _ hpp hN h).le (by rw [hNv]; positivity)
    rw [hNv] at hle
    refine ⟨h0, ?_, by rw [hr, mul_zero]; linarith⟩
    calc tpo.toRat ≤ pp.toRat * pr.toNat * (1 + ε) := hle
      _ ≤ pp.toRat * pr.toNat * 70 := by gcongr; linarith
      _ = 70 * pr.toNat * pp.toRat := by ring
  rename_i hz
  have hr : 0 < rate.toRat := by
    rcases lt_or_eq_of_le hr0 with h' | h'
    · exact h'
    · exact absurd ((operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mpr
        (by rw [Number.toRat_zero]; exact h'.symm)) hz
  obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
  have hfN := computePaymentFactor_isNormalized rate _ pr f hrate hN hf
  have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) h
  obtain ⟨hf1, hf2⟩ := computePaymentFactor_ge rate pr f hrate hr hf hfne
  have hfpos : 0 < f.toRat := lt_of_lt_of_le (by positivity) hf1
  have h0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpp hfN h) (div_nonneg hpp0 hfpos.le)
  have hle := (Number.div_near _ _ _ hpp hfN h).le (div_nonneg hpp0 hfpos.le)
  refine ⟨h0, ?_, ?_⟩
  · -- `f` is at least `1/(64·n)` or at least the rate, which is then above `1/(2·n)`
    have hfn : (1 - ε) ^ 3 / (64 * pr.toNat) ≤ f.toRat := by
      by_cases hs : (pr.toNat : ℚ) * rate.toRat ≤ 1 / 2
      · exact hf2 hs
      · push Not at hs
        have hNpos : (0 : ℚ) < pr.toNat := by linarith
        refine le_trans ?_ hf1
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℚ) ≤ (1 - ε) ^ 3 := by positivity
        nlinarith
    have hNpos : (0 : ℚ) < pr.toNat := by linarith
    calc tpo.toRat ≤ pp.toRat / f.toRat * (1 + ε) := hle
      _ ≤ pp.toRat / ((1 - ε) ^ 3 / (64 * pr.toNat)) * (1 + ε) := by gcongr
      _ = pp.toRat * pr.toNat * (64 * (1 + ε) / (1 - ε) ^ 3) := by field_simp
      _ ≤ pp.toRat * pr.toNat * 70 := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith
      _ = 70 * pr.toNat * pp.toRat := by ring
  · calc tpo.toRat * rate.toRat ≤ pp.toRat / f.toRat * (1 + ε) * rate.toRat := by gcongr
      _ ≤ pp.toRat / (rate.toRat * (1 - ε) ^ 3) * (1 + ε) * rate.toRat := by gcongr
      _ = pp.toRat * ((1 + ε) / (1 - ε) ^ 3) := by field_simp
      _ ≤ pp.toRat * 2 := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith
      _ = 2 * pp.toRat := by ring

end XRPL.Model.Lending
