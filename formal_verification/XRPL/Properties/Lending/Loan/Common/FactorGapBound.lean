import XRPL.Properties.Lending.Loan.Common.FactorGap
import XRPL.Properties.Lending.Loan.Common.PowerError

/-! # When the payment factor falls by at least four roundings

The exact factor of `k` payments is below the factor of `k − 1` payments by a fraction of at least
`rate / (1 + rate)^k`. So the computed factors stay four roundings apart while that covers their rounding errors. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_ge rn_nonneg Number.ofInt64_one_toRat Number.power_ge_one computePowerMinusOneHybrid_nonneg
  from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.cancellationThreshold powerMinusOneLoop_le Number.eq_zero_of_toRat Number.div_zero_error
  Number.ofInt64_nat from XRPL.Properties.Lending.Loan.Common.PaymentFactor

local notation "ε" => Number.nearestError
local notation "μ" => Number.mulError

/-- `10^-13` as a `Number`. -/
private lemma Number.tiny : ∃ w : Number, w.isNormalized ∧ w.toRat = 1 / 10 ^ 13 := by
  obtain ⟨w, -, hv, hn⟩ := Number.from_rep_exact (1 : Int64) (-13) .to_nearest (by decide)
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  refine ⟨w, hn, ?_⟩
  rw [hv, show (1 : Int64).toInt = 1 from by decide]
  norm_num

/-- The steps of the payment factor of a positive rate over at least one payment. -/
private lemma computePaymentFactor_steps (rate : Number) (k : UInt32) (f : Number) (hrate : rate.isNormalized)
    (hr0 : 0 < rate.toRat) (hk : k ≠ 0)
    (h : computePaymentFactor rate (Number.ofInt64 k.toInt64) k = .ok f) :
    ∃ pm R num : Number, computePowerMinusOneHybrid rate (Number.ofInt64 k.toInt64) k = .ok pm ∧
      (Number.ofInt64 1).operator_add pm .to_nearest = .ok R ∧ rate.operator_mul R .to_nearest = .ok num ∧
      num.operator_div pm .to_nearest = .ok f := by
  unfold computePaymentFactor at h
  dsimp only at h
  split at h
  · rename_i hz; exact absurd (by simpa using hz) hk
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · rename_i hz
    have := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp hz
    rw [Number.toRat_zero] at this; linarith
  obtain ⟨pm, hpm, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨R, hR, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨num, hnum, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨pm, R, num, hpm, hR, hnum, h⟩

/-- The two ways `(1 + rate)^k − 1` is computed. The closed form `round(1 + rate)^k − 1` when `k·rate` rounds
to `10^-9` or more, else the binomial series, and then `k·rate` is below `10^-9`. -/
private lemma computePowerMinusOneHybrid_cases (rate : Number) (k : UInt32) (pm : Number)
    (hrate : rate.isNormalized) (hr0 : 0 < rate.toRat) (hk : k ≠ 0)
    (h : computePowerMinusOneHybrid rate (Number.ofInt64 k.toInt64) k = .ok pm) :
    (∃ b p : Number, (Number.ofInt64 1).operator_add rate .to_nearest = .ok b ∧ b.power k.toNat = .ok p ∧
        p.operator_sub (Number.ofInt64 1) .to_nearest = .ok pm ∧
        1 / 10 ^ 9 ≤ (k.toNat : ℚ) * rate.toRat * (1 + ε)) ∨
      ((k.toNat : ℚ) * rate.toRat < 1 / 10 ^ 9 ∧
        computePowerMinusOne rate (Number.ofInt64 k.toInt64) k = .ok pm) := by
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  unfold computePowerMinusOneHybrid at h
  dsimp only at h
  split at h
  · rename_i hz
    exfalso
    rcases Bool.or_eq_true_iff.mp hz with hz | hz
    · exact hk (by simpa using hz)
    · have := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp hz
      rw [Number.toRat_zero] at this; linarith
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨nr, hnr, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨th, hth, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨w, hw, hwN, hwv⟩ := Number.cancellationThreshold
  rw [hw, Except.ok.injEq] at hth
  subst hth
  have hnrN := Number.operator_mul_isNormalized _ _ nr _ hN hrate hnr
  have hnrle := (Number.mul_near _ _ _ hN hrate hnr).le (by rw [hNv]; positivity)
  rw [hNv] at hnrle
  split at h
  · rename_i hge
    left
    have hth : (1 : ℚ) / 10 ^ 9 ≤ nr.toRat := by
      rw [← hwv]; exact (operator_ge_iff nr w hnrN hwN).mp hge
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
    exact ⟨b, p, hb, hp, h, le_trans hth hnrle⟩
  · rename_i hlt
    right
    refine ⟨?_, h⟩
    by_contra hc
    push Not at hc
    have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hN hrate hnr) w hwN (by rw [hwv, hNv]; exact hc)
    exact hlt ((operator_ge_iff nr w hnrN hwN).mpr this)

/-- The rounded base `1 + rate` is at least one and within one rounding of `1 + rate`. -/
private lemma base_bounds (rate b : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hb : (Number.ofInt64 1).operator_add rate .to_nearest = .ok b) :
    b.isNormalized ∧ 1 ≤ b.toRat ∧ (1 + rate.toRat) * (1 - ε) ≤ b.toRat ∧ b.toRat ≤ (1 + rate.toRat) * (1 + ε) := by
  have hone := Number.ofInt64_isNormalized 1
  have hbN := operator_add_isNormalized_to_nearest_sz _ _ b hone hrate hb
  have hb1 : 1 ≤ b.toRat := by
    have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hrate hb) _ hone
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rwa [Number.ofInt64_one_toRat] at this
  have hnear := Number.add_near _ _ _ hone hrate hb
  rw [Number.ofInt64_one_toRat] at hnear
  exact ⟨hbN, hb1, hnear.ge (by linarith) (by linarith), hnear.le (by linarith)⟩

/-- The closed form is within its roundings of `b^k − 1`: `k − 1` product errors for the power and one rounding
for the subtraction. -/
private lemma closed_bounds (b p pm : Number) (k : ℕ) (hbN : b.isNormalized) (hb1 : 1 ≤ b.toRat) (hk : 1 ≤ k)
    (hp : b.power k = .ok p) (hs : p.operator_sub (Number.ofInt64 1) .to_nearest = .ok pm) :
    pm.toRat ≤ (b.toRat ^ k * (1 + μ) ^ (k - 1) - 1) * (1 + ε) ∧
      (pm.toRat ≠ 0 → (b.toRat ^ k * (1 - μ) ^ (k - 1) - 1) * (1 - ε) ≤ pm.toRat) := by
  have hone := Number.ofInt64_isNormalized 1
  have hpN := Number.power_isNormalized b hbN _ p hp
  have hp1 := Number.power_ge_one b hbN hb1 _ p hp
  obtain ⟨hlo, hhi⟩ := Number.power_bounds b hbN hb1 k p hk hp
  have hnear := Number.sub_near _ _ _ hpN hone hs
  rw [Number.ofInt64_one_toRat] at hnear
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  refine ⟨?_, fun h0 => ?_⟩
  · calc pm.toRat ≤ (p.toRat - 1) * (1 + ε) := hnear.le (by linarith)
      _ ≤ (b.toRat ^ k * (1 + μ) ^ (k - 1) - 1) * (1 + ε) := by gcongr
  · calc (b.toRat ^ k * (1 - μ) ^ (k - 1) - 1) * (1 - ε) ≤ (p.toRat - 1) * (1 - ε) := by
          gcongr; linarith
      _ ≤ pm.toRat := hnear.ge h0 (by linarith)

/-- The binomial series never drops below its running sum. Each new term is at least zero, so each rounded
partial sum is at least the one before it. -/
private lemma powerMinusOneLoop_ge (rate : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (pr : Nat)
    (hpr : pr < 2 ^ 32) :
    ∀ (d index : Nat) (ct rs r : Number), pr - index = d → ct.isNormalized → rs.isNormalized →
      0 ≤ ct.toRat → 0 ≤ rs.toRat → powerMinusOneLoop rate pr index ct rs = .ok r → rs.toRat ≤ r.toRat := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index ct rs r hd hc hs hc0 hs0 h
    rw [powerMinusOneLoop] at h
    split at h
    · obtain ⟨c1, h1, h⟩ := bind_ok_peel _ _ _ h
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
      have hns1 := rn_ge (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) rs hs (by linarith)
      split at h
      · cases h; exact le_rfl
      · exact le_trans hns1
          (ih (pr - (index + 1)) (by omega) (index + 1) c3 ns r rfl hc3 hns hc30 (le_trans hs0 hns1) h)
    · cases h; exact le_rfl

/-- The binomial series is at least `k·rate`, less one rounding. -/
private lemma computePowerMinusOne_ge (rate : Number) (k : UInt32) (pm : Number) (hrate : rate.isNormalized)
    (hr0 : 0 < rate.toRat) (hk : k ≠ 0)
    (h : computePowerMinusOne rate (Number.ofInt64 k.toInt64) k = .ok pm) :
    (k.toNat : ℚ) * rate.toRat * (1 - ε) ≤ pm.toRat := by
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  have hk1 : (1 : ℚ) ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h0 => hk (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  unfold computePowerMinusOne at h
  dsimp only at h
  split at h
  · rename_i hz
    exfalso
    rcases Bool.or_eq_true_iff.mp hz with hz | hz
    · exact hk (by simpa using hz)
    · have := (operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mp hz
      rw [Number.toRat_zero] at this; linarith
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
  have hcN := Number.operator_mul_isNormalized _ _ c _ hN hrate hc
  -- the first term is at least the rate, so it is not zero
  have hc1 := rn_ge (operator_mul_rounded_to_nearest _ _ _ hN hrate hc) rate hrate (by rw [hNv]; nlinarith)
  have hcge := (Number.mul_near _ _ _ hN hrate hc).ge (by linarith) (by rw [hNv]; positivity)
  rw [hNv] at hcge
  have hloop := powerMinusOneLoop_ge rate hrate hr0.le k.toNat k.toNat_lt _ 1 c c pm rfl hcN hcN (by linarith)
    (by linarith) h
  linarith

/-- The binomial series is at most `k·rate` over `1 − 10^-9`, plus its roundings. -/
private lemma computePowerMinusOne_le (rate : Number) (k : UInt32) (pm : Number) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (hsm : (k.toNat : ℚ) * rate.toRat < 1 / 10 ^ 9)
    (h : computePowerMinusOne rate (Number.ofInt64 k.toInt64) k = .ok pm) :
    pm.toRat ≤ (k.toNat * rate.toRat * (1 + ε) + k.toNat * rate.toRat * (1 + ε) / (10 ^ 9 - 1)) *
      (1 + ε) ^ (k.toNat - 1) := by
  have he := Number.nearestError_pos
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  have hx0 : 0 ≤ (k.toNat : ℚ) * rate.toRat := by positivity
  unfold computePowerMinusOne at h
  dsimp only at h
  split at h
  · cases h; rw [Number.toRat_zero]; positivity
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
  have hcN := Number.operator_mul_isNormalized _ _ c _ hN hrate hc
  have hc0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hN hrate hc) (by rw [hNv]; exact hx0)
  have hcle := (Number.mul_near _ _ _ hN hrate hc).le (by rw [hNv]; exact hx0)
  rw [hNv] at hcle
  have hloop := powerMinusOneLoop_le rate hrate hr0 k.toNat k.toNat_lt hsm _ 1 c c pm rfl le_rfl hcN hcN
    hc0 hc0 h
  calc pm.toRat ≤ (c.toRat + c.toRat / (10 ^ 9 - 1)) * (1 + ε) ^ (k.toNat - 1) := hloop
    _ ≤ _ := by gcongr

private lemma eps_small : ε ≤ 7 / 10 ^ 19 := by unfold Number.nearestError; norm_num

private lemma mu_small : μ ≤ 6 / 10 ^ 19 := by unfold Number.mulError; norm_num

/-- The gap `pm − pm'` covers eleven roundings of `pm'·(1 + pm)` once a lower bound on `pm` and an upper bound
on `pm'` have that gap. -/
private lemma gap_of_bounds (pm pm' L U : ℚ) (hL : L ≤ pm) (hU : pm' ≤ U) (hL0 : 0 ≤ L)
    (hc : 11 * ε * U ≤ 1) (h : U * (1 + 11 * ε) + 11 * ε * L * U ≤ L) : 11 * ε * pm' * (1 + pm) ≤ pm - pm' := by
  have he := Number.nearestError_pos
  have hpm : 0 ≤ pm := le_trans hL0 hL
  have h1 : pm * (1 - 11 * ε * U) ≤ pm * (1 - 11 * ε * pm') :=
    mul_le_mul_of_nonneg_left (by nlinarith) hpm
  have h2 : L * (1 - 11 * ε * U) ≤ pm * (1 - 11 * ε * U) := mul_le_mul_of_nonneg_right hL (by linarith)
  have h3 : pm' * (1 + 11 * ε) ≤ U * (1 + 11 * ε) := mul_le_mul_of_nonneg_right hU (by linarith)
  nlinarith

/-- The closed-form gap in one variable `D`, which is `B^(k−1)/(1 − t)` with `t` the power errors. The bounds
`(B·D·(1 − t)^2 − 1)(1 − ε)` and `(D − 1)(1 + ε)` have the gap once `B − 1` covers the errors. -/
private lemma closed_gap (B D t : ℚ) (hB : 1 ≤ B) (hD : 1 ≤ D) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (h : B * (2 * t + ε) + ε + 11 * ε * (1 + ε) * B * D ≤ B - 1) :
    0 ≤ (B * D * (1 - t) ^ 2 - 1) * (1 - ε) ∧ 11 * ε * ((D - 1) * (1 + ε)) ≤ 1 ∧
      (D - 1) * (1 + ε) * (1 + 11 * ε) + 11 * ε * ((B * D * (1 - t) ^ 2 - 1) * (1 - ε)) * ((D - 1) * (1 + ε)) ≤
        (B * D * (1 - t) ^ 2 - 1) * (1 - ε) := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hBD : 1 ≤ B * D := by nlinarith
  have hq : 1 - 2 * t - ε ≤ (1 - t) ^ 2 * (1 - ε) := by
    nlinarith [mul_nonneg ht0 he.le, mul_nonneg (sq_nonneg t) (by linarith : (0 : ℚ) ≤ 1 - ε)]
  have hq1 : (1 - t) ^ 2 * (1 - ε) ≤ 1 := by
    have : (1 - t) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  -- `G` is the gap per unit of `D`
  set G := B * (1 - t) ^ 2 * (1 - ε) - (1 + ε) with hG
  have hGge : 11 * ε * (1 + ε) * B * D ≤ G := by
    have : B * (1 - 2 * t - ε) ≤ B * ((1 - t) ^ 2 * (1 - ε)) := mul_le_mul_of_nonneg_left hq (by linarith)
    nlinarith
  have hG0 : 0 ≤ G := le_trans (by positivity) hGge
  have hGB : G ≤ B := by
    have : B * ((1 - t) ^ 2 * (1 - ε)) ≤ B * 1 := mul_le_mul_of_nonneg_left hq1 (by linarith)
    nlinarith
  have hB1 : 1 ≤ B * (1 - t) ^ 2 := by nlinarith
  have hBDt : 1 ≤ B * D * (1 - t) ^ 2 := by nlinarith
  have hL0 : 0 ≤ (B * D * (1 - t) ^ 2 - 1) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  have hLle : (B * D * (1 - t) ^ 2 - 1) * (1 - ε) ≤ B * D - 1 := by
    have : B * D * (1 - t) ^ 2 ≤ B * D := by
      have : (1 - t) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  have hU0 : 0 ≤ (D - 1) * (1 + ε) := mul_nonneg (by linarith) (by linarith)
  have hUle : (D - 1) * (1 + ε) ≤ D * (1 + ε) := by nlinarith
  refine ⟨hL0, ?_, ?_⟩
  · -- `11·ε·(1 + ε)·D ≤ G / B ≤ 1`
    have : 11 * ε * (1 + ε) * D ≤ 1 := by
      by_contra hc
      push Not at hc
      have : B * 1 < B * (11 * ε * (1 + ε) * D) := mul_lt_mul_of_pos_left hc (by linarith)
      nlinarith
    nlinarith
  · -- the gap `L − U` is at least `D·G`, and the rounding term at most `D` times `11·ε·(1 + ε)·B·D`
    have hgap : D * G ≤ (B * D * (1 - t) ^ 2 - 1) * (1 - ε) - (D - 1) * (1 + ε) := by
      rw [hG]; nlinarith
    have hround : 11 * ε * ((D - 1) * (1 + ε)) * (1 + (B * D * (1 - t) ^ 2 - 1) * (1 - ε)) ≤
        D * (11 * ε * (1 + ε) * B * D) := by
      have h1 : 1 + (B * D * (1 - t) ^ 2 - 1) * (1 - ε) ≤ B * D := by linarith
      have h2 : 0 ≤ 1 + (B * D * (1 - t) ^ 2 - 1) * (1 - ε) := by linarith
      calc 11 * ε * ((D - 1) * (1 + ε)) * (1 + (B * D * (1 - t) ^ 2 - 1) * (1 - ε))
          ≤ 11 * ε * (D * (1 + ε)) * (B * D) := by gcongr
        _ = D * (11 * ε * (1 + ε) * B * D) := by ring
    have : D * (11 * ε * (1 + ε) * B * D) ≤ D * G := mul_le_mul_of_nonneg_left hGge (by linarith)
    nlinarith

/-- The closed form for `k` and `k − 1` payments has the gap while the rate covers `2·k` product errors and
`16·(1 + rate)^k` roundings. Both counts use the same rounded base `B`. -/
private lemma closed_closed_gap (r B pm pm' : ℚ) (k : ℕ) (hk : 2 ≤ k) (hk32 : k ≤ 2 ^ 32) (hr0 : 0 ≤ r)
    (hB1 : 1 ≤ B) (hBlo : (1 + r) * (1 - ε) ≤ B) (hBhi : B ≤ (1 + r) * (1 + ε))
    (hpm : (B ^ k * (1 - μ) ^ (k - 1) - 1) * (1 - ε) ≤ pm)
    (hpm' : pm' ≤ (B ^ (k - 1) * (1 + μ) ^ (k - 1 - 1) - 1) * (1 + ε))
    (hb : 2 * k * μ * (1 + r) + 16 * ε * (1 + r) ^ k ≤ r) :
    11 * ε * pm' * (1 + pm) ≤ pm - pm' := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hm := Number.mulError_pos
  have hm' := mu_small
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hpm hpm'
  push_cast at hb
  have hj32 : (j : ℚ) ≤ 2 ^ 32 := by exact_mod_cast (by omega : j ≤ 2 ^ 32)
  have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  -- `t` is the error count of the power of `k`, at most `10^-8`
  set t : ℚ := j * μ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 10 ^ 8 := by
    calc t = j * μ := rfl
      _ ≤ 2 ^ 32 * (6 / 10 ^ 19) := by gcongr
      _ ≤ 1 / 10 ^ 8 := by norm_num
  have h1t : 0 < 1 - t := by linarith
  set Y := B ^ j with hY
  have hY1 : 1 ≤ Y := one_le_pow₀ hB1
  set D := Y / (1 - t) with hDdef
  have hDY : D * (1 - t) = Y := by rw [hDdef]; field_simp
  have hD1 : 1 ≤ D := by rw [hDdef, le_div_iff₀ h1t]; linarith
  -- the power of `k` is at least `B·D·(1 − t)^2`, the power of `k − 1` at most `D`
  have hlow : 1 - t ≤ (1 - μ) ^ j := by
    have := one_add_mul_le_pow (a := -μ) (by linarith) j
    rw [← sub_eq_add_neg] at this
    rw [ht]; linarith
  have hup : (1 + μ) ^ (j - 1) ≤ 1 / (1 - t) :=
    le_trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))
      (one_add_pow_le_inv μ j hm.le (by rw [← ht]; linarith))
  have hL : (B * D * (1 - t) ^ 2 - 1) * (1 - ε) ≤ pm := by
    refine le_trans ?_ hpm
    have : B * D * (1 - t) ^ 2 ≤ B ^ (j + 1) * (1 - μ) ^ j := by
      have e1 : B * D * (1 - t) ^ 2 = B * Y * (1 - t) := by rw [← hDY]; ring
      have e2 : B ^ (j + 1) = B * Y := by rw [hY]; ring
      rw [e1, e2]
      gcongr
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hU : pm' ≤ (D - 1) * (1 + ε) := by
    refine le_trans hpm' ?_
    have : B ^ j * (1 + μ) ^ (j - 1) ≤ D := by
      calc B ^ j * (1 + μ) ^ (j - 1) ≤ Y * (1 / (1 - t)) := by gcongr
        _ = D := by rw [hDdef]; ring
    gcongr
  -- the rounding term `11·ε·(1 + ε)·B·D` is at most `12·ε·(1 + r)^k`
  have hP1 : 1 + r ≤ (1 + r) ^ (j + 1) := le_self_pow₀ (by linarith) (by omega)
  have hBk : B * D ≤ (1 + r) ^ (j + 1) * (1 + ε) ^ (j + 1) * (1 / (1 - t)) := by
    have : B * Y ≤ ((1 + r) * (1 + ε)) ^ (j + 1) := by
      rw [hY, ← pow_succ']; exact pow_le_pow_left₀ (by linarith) hBhi _
    calc B * D = B * Y * (1 / (1 - t)) := by rw [hDdef]; ring
      _ ≤ ((1 + r) * (1 + ε)) ^ (j + 1) * (1 / (1 - t)) := by gcongr
      _ = _ := by rw [mul_pow]
  have hE : (1 + ε) ^ (j + 2) ≤ 1 + 1 / 10 ^ 8 := by
    have := one_add_pow_le_lin ε (j + 2) he.le (by
      push_cast
      calc ((j : ℚ) + 2) * ε ≤ (2 ^ 32 + 2) * (7 / 10 ^ 19) := by gcongr
        _ ≤ 1 / 2 := by norm_num)
    push_cast at this
    have : 2 * ((j : ℚ) + 2) * ε ≤ 2 * (2 ^ 32 + 2) * (7 / 10 ^ 19) := by gcongr
    have : (2 : ℚ) * (2 ^ 32 + 2) * (7 / 10 ^ 19) ≤ 1 / 10 ^ 8 := by norm_num
    linarith
  have hT : 1 / (1 - t) ≤ 1 + 1 / 10 ^ 7 := by
    rw [div_le_iff₀ h1t]; nlinarith
  have hround : 11 * ε * (1 + ε) * B * D ≤ 12 * ε * (1 + r) ^ (j + 1) := by
    have hPpos : 0 ≤ (1 + r) ^ (j + 1) := by positivity
    calc 11 * ε * (1 + ε) * B * D = 11 * ε * (1 + ε) * (B * D) := by ring
      _ ≤ 11 * ε * (1 + ε) * ((1 + r) ^ (j + 1) * (1 + ε) ^ (j + 1) * (1 / (1 - t))) := by gcongr
      _ = 11 * ε * (1 + r) ^ (j + 1) * ((1 + ε) ^ (j + 2) * (1 / (1 - t))) := by ring
      _ ≤ 11 * ε * (1 + r) ^ (j + 1) * ((1 + 1 / 10 ^ 8) * (1 + 1 / 10 ^ 7)) := by gcongr
      _ ≤ 12 * ε * (1 + r) ^ (j + 1) := by
          have : (1 + 1 / 10 ^ 8 : ℚ) * (1 + 1 / 10 ^ 7) ≤ 12 / 11 := by norm_num
          have h0 : 0 ≤ 11 * ε * (1 + r) ^ (j + 1) := by positivity
          calc 11 * ε * (1 + r) ^ (j + 1) * ((1 + 1 / 10 ^ 8) * (1 + 1 / 10 ^ 7))
              ≤ 11 * ε * (1 + r) ^ (j + 1) * (12 / 11) := mul_le_mul_of_nonneg_left this h0
            _ = 12 * ε * (1 + r) ^ (j + 1) := by ring
  -- the product errors of the base and the cross terms fit in the rest of the margin
  have htε : t * ε ≤ μ := by
    have : (j : ℚ) * ε ≤ 1 := by
      calc (j : ℚ) * ε ≤ 2 ^ 32 * (7 / 10 ^ 19) := by gcongr
        _ ≤ 1 := by norm_num
    calc t * ε = μ * (j * ε) := by rw [ht]; ring
      _ ≤ μ * 1 := mul_le_mul_of_nonneg_left this hm.le
      _ = μ := mul_one μ
  have hstar : B * (2 * t + ε) + ε + 11 * ε * (1 + ε) * B * D ≤ B - 1 := by
    have h1 : B * (2 * t + ε) ≤ (1 + r) * (1 + ε) * (2 * t + ε) := mul_le_mul_of_nonneg_right hBhi (by positivity)
    have h2 : (1 + r) * (2 * (t * ε)) ≤ (1 + r) * (2 * μ) := by gcongr
    have h3 : ε * ε ≤ ε := by nlinarith
    have h4 : (1 + r) * (ε * ε) ≤ (1 + r) * ε := by gcongr
    have h5 : ε * (1 + r) ≤ ε * (1 + r) ^ (j + 1) := by gcongr
    have hbk : 2 * ((j : ℚ) + 1) * μ * (1 + r) = 2 * t * (1 + r) + 2 * μ * (1 + r) := by rw [ht]; ring
    nlinarith
  obtain ⟨hL0, hc, hg⟩ := closed_gap B D t hB1 hD1 ht0 (by linarith) hstar
  exact gap_of_bounds pm pm' _ _ hL hU hL0 hc hg

/-- The gap while `(k − 1)·rate` is below `10^-9`. Then the gap is about the rate, far above the roundings. -/
private lemma small_gap (r pm pm' : ℚ) (k : ℕ) (hk : 2 ≤ k) (hlow : 1 / 10 ^ 12 ≤ r)
    (hsm : ((k : ℚ) - 1) * r < 1 / 10 ^ 9) (hpm : k * r * (1 - 1 / 10 ^ 14) - 3 / 10 ^ 15 ≤ pm)
    (hpm' : pm' ≤ ((k : ℚ) - 1) * r * (1 + 2 / 10 ^ 9)) :
    11 * ε * pm' * (1 + pm) ≤ pm - pm' := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast hk
  set x := ((k : ℚ) - 1) * r with hx
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hlow
  have hxr : r ≤ x := by rw [hx]; nlinarith
  have hkr : (k : ℚ) * r = x + r := by rw [hx]; ring
  have hr9 : r < 1 / 10 ^ 9 := lt_of_le_of_lt hxr hsm
  rw [hkr] at hpm
  set L := (x + r) * (1 - 1 / 10 ^ 14) - 3 / 10 ^ 15 with hL
  set U := x * (1 + 2 / 10 ^ 9) with hU
  have hL0 : 0 ≤ L := by rw [hL]; nlinarith
  have hLle : L ≤ 2 / 10 ^ 9 := by rw [hL]; nlinarith
  have hU0 : 0 ≤ U := by rw [hU]; exact mul_nonneg (by linarith) (by norm_num)
  have hUle : U ≤ 2 / 10 ^ 9 := by rw [hU]; nlinarith
  have hc : 11 * ε * U ≤ 1 := by
    calc 11 * ε * U ≤ 11 * (7 / 10 ^ 19) * (2 / 10 ^ 9) := by gcongr
      _ ≤ 1 := by norm_num
  refine gap_of_bounds pm pm' L U hpm hpm' hL0 hc ?_
  have ha : U * (1 + 11 * ε) ≤ x + x * (3 / 10 ^ 9) := by
    have : (1 + 2 / 10 ^ 9) * (1 + 11 * ε) ≤ 1 + 3 / 10 ^ 9 := by
      have : (1 + 2 / 10 ^ 9 : ℚ) * (1 + 11 * ε) ≤ (1 + 2 / 10 ^ 9) * (1 + 11 * (7 / 10 ^ 19)) := by gcongr
      have h2 : (1 + 2 / 10 ^ 9 : ℚ) * (1 + 11 * (7 / 10 ^ 19)) ≤ 1 + 3 / 10 ^ 9 := by norm_num
      linarith
    have hx0 : 0 ≤ x := by linarith
    calc U * (1 + 11 * ε) = x * ((1 + 2 / 10 ^ 9) * (1 + 11 * ε)) := by rw [hU]; ring
      _ ≤ x * (1 + 3 / 10 ^ 9) := mul_le_mul_of_nonneg_left this hx0
      _ = x + x * (3 / 10 ^ 9) := by ring
  have hb : 11 * ε * L * U ≤ 1 / 10 ^ 30 := by
    calc 11 * ε * L * U ≤ 11 * (7 / 10 ^ 19) * (2 / 10 ^ 9) * (2 / 10 ^ 9) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num
  have hc' : x * (3 / 10 ^ 9) ≤ 3 / 10 ^ 18 := by nlinarith
  have hd : x + r - 1 / 10 ^ 14 * (2 / 10 ^ 9) - 3 / 10 ^ 15 ≤ L := by rw [hL]; nlinarith
  linarith

/-- The closed form is at least `k·rate`, less its roundings, while `(k − 1)·rate` is below `10^-9`. -/
private lemma small_closed_lower (r B pm : ℚ) (k : ℕ) (hk : 2 ≤ k) (hlow : 1 / 10 ^ 12 ≤ r)
    (hsm : ((k : ℚ) - 1) * r < 1 / 10 ^ 9) (hB1 : 1 ≤ B) (hBlo : (1 + r) * (1 - ε) ≤ B)
    (hBhi : B ≤ (1 + r) * (1 + ε)) (hpm : (B ^ k * (1 - μ) ^ (k - 1) - 1) * (1 - ε) ≤ pm) :
    k * r * (1 - 1 / 10 ^ 14) - 3 / 10 ^ 15 ≤ pm := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hm := Number.mulError_pos
  have hm' := mu_small
  have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hlow
  have hk1000 : (k : ℚ) - 1 ≤ 1000 := by
    by_contra hc
    push Not at hc
    have : 1000 * (1 / 10 ^ 12 : ℚ) < ((k : ℚ) - 1) * r := by
      calc 1000 * (1 / 10 ^ 12 : ℚ) < ((k : ℚ) - 1) * (1 / 10 ^ 12) := by gcongr
        _ ≤ ((k : ℚ) - 1) * r := by gcongr
    norm_num at this
    linarith
  have hr9 : r < 1 / 10 ^ 9 := by nlinarith
  have hkm1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  -- `B^k ≥ 1 + k·(B − 1)` and `(1 − μ)^(k − 1) ≥ 1 − (k − 1)·μ`
  have hBk : 1 + k * (B - 1) ≤ B ^ k := by
    have := one_add_mul_le_pow (a := B - 1) (by linarith) k
    rwa [add_sub_cancel] at this
  have hmk : 1 - ((k : ℚ) - 1) * μ ≤ (1 - μ) ^ (k - 1) := by
    have := one_add_mul_le_pow (a := -μ) (by linarith) (k - 1)
    rw [← sub_eq_add_neg, hkm1] at this
    linarith
  have hmk0 : 0 ≤ 1 - ((k : ℚ) - 1) * μ := by nlinarith
  have hs0 : 0 ≤ B - 1 := by linarith
  have hs1 : B - 1 ≤ 2 / 10 ^ 9 := by nlinarith
  have hprod : (1 + k * (B - 1)) * (1 - ((k : ℚ) - 1) * μ) ≤ B ^ k * (1 - μ) ^ (k - 1) :=
    mul_le_mul hBk hmk hmk0 (by positivity)
  -- the cross term and the roundings of the base are below `3·10^-15`
  have hk' : (k : ℚ) ≤ 1001 := by linarith
  have hkm : ((k : ℚ) - 1) * μ ≤ 1000 * (6 / 10 ^ 19) := mul_le_mul hk1000 hm' hm.le (by norm_num)
  have hkm0 : 0 ≤ ((k : ℚ) - 1) * μ := mul_nonneg (by linarith) hm.le
  have hcross : k * (B - 1) * (((k : ℚ) - 1) * μ) ≤ 1 / 10 ^ 18 := by
    calc k * (B - 1) * (((k : ℚ) - 1) * μ) ≤ 1001 * (2 / 10 ^ 9) * (1000 * (6 / 10 ^ 19)) :=
          mul_le_mul (mul_le_mul hk' hs1 hs0 (by norm_num)) hkm hkm0 (by norm_num)
      _ ≤ 1 / 10 ^ 18 := by norm_num
  have hkB : k * r - 1001 * (2 * (7 / 10 ^ 19)) ≤ k * (B - 1) := by
    have h0 : r - (1 + r) * ε ≤ B - 1 := by linarith
    have h1 : (1 + r) * ε ≤ 2 * (7 / 10 ^ 19) := mul_le_mul (by linarith) he' he.le (by norm_num)
    have h2 : (k : ℚ) * ((1 + r) * ε) ≤ 1001 * (2 * (7 / 10 ^ 19)) :=
      mul_le_mul hk' h1 (by positivity) (by norm_num)
    have h3 : (k : ℚ) * (r - (1 + r) * ε) ≤ k * (B - 1) := mul_le_mul_of_nonneg_left h0 (by linarith)
    linarith
  have hX : k * r - 3 / 10 ^ 15 ≤ B ^ k * (1 - μ) ^ (k - 1) - 1 := by
    have : (1 + k * (B - 1)) * (1 - ((k : ℚ) - 1) * μ) - 1 =
        k * (B - 1) - ((k : ℚ) - 1) * μ - k * (B - 1) * (((k : ℚ) - 1) * μ) := by ring
    have h3 : (1001 * (2 * (7 / 10 ^ 19)) + 1000 * (6 / 10 ^ 19) + 1 / 10 ^ 18 : ℚ) ≤ 3 / 10 ^ 15 := by norm_num
    linarith
  have hkr : (k : ℚ) * r ≤ 2 / 10 ^ 9 := by nlinarith
  have hkε : (k : ℚ) * r * ε ≤ k * r * (1 / 10 ^ 14) := by gcongr; linarith
  calc k * r * (1 - 1 / 10 ^ 14) - 3 / 10 ^ 15 ≤ (k * r - 3 / 10 ^ 15) * (1 - ε) := by nlinarith
    _ ≤ (B ^ k * (1 - μ) ^ (k - 1) - 1) * (1 - ε) := mul_le_mul_of_nonneg_right hX (by linarith)
    _ ≤ pm := hpm

/-- The binomial series for `k − 1` payments is at most `(k − 1)·rate·(1 + 2·10^-9)`. -/
private lemma small_binomial_upper (r pm' : ℚ) (n : ℕ) (hn : n ≤ 1000) (hr0 : 0 ≤ r)
    (h : pm' ≤ (n * r * (1 + ε) + n * r * (1 + ε) / (10 ^ 9 - 1)) * (1 + ε) ^ (n - 1)) :
    pm' ≤ n * r * (1 + 2 / 10 ^ 9) := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hpow : (1 + ε) ^ (n - 1) ≤ 1 + 2 / 10 ^ 15 := by
    have hn1 : ((n - 1 : ℕ) : ℚ) ≤ 1000 := by exact_mod_cast (by omega : n - 1 ≤ 1000)
    have := one_add_pow_le_lin ε (n - 1) he.le (by
      calc ((n - 1 : ℕ) : ℚ) * ε ≤ 1000 * (7 / 10 ^ 19) := by gcongr
        _ ≤ 1 / 2 := by norm_num)
    have : 2 * ((n - 1 : ℕ) : ℚ) * ε ≤ 2 * 1000 * (7 / 10 ^ 19) := by gcongr
    have : (2 * 1000 * (7 / 10 ^ 19) : ℚ) ≤ 2 / 10 ^ 15 := by norm_num
    linarith
  have hx : 0 ≤ (n : ℚ) * r := by positivity
  calc pm' ≤ (n * r * (1 + ε) + n * r * (1 + ε) / (10 ^ 9 - 1)) * (1 + ε) ^ (n - 1) := h
    _ ≤ (n * r * (1 + ε) + n * r * (1 + ε) / (10 ^ 9 - 1)) * (1 + 2 / 10 ^ 15) := by gcongr
    _ = n * r * ((1 + ε) * (1 + 1 / (10 ^ 9 - 1)) * (1 + 2 / 10 ^ 15)) := by ring
    _ ≤ n * r * ((1 + 7 / 10 ^ 19) * (1 + 1 / (10 ^ 9 - 1)) * (1 + 2 / 10 ^ 15)) := by gcongr
    _ ≤ n * r * (1 + 2 / 10 ^ 9) := by gcongr; norm_num

/-- The payment factor is within three roundings of `rate·(1 + pm)/pm`, stated times `pm`. -/
private lemma factor_bounds (rate pm R num f : Number) (hrate : rate.isNormalized) (hlow : 1 / 10 ^ 12 ≤ rate.toRat)
    (hpmN : pm.isNormalized) (hpm0 : 0 ≤ pm.toRat) (hR : (Number.ofInt64 1).operator_add pm .to_nearest = .ok R)
    (hnum : rate.operator_mul R .to_nearest = .ok num) (hf : num.operator_div pm .to_nearest = .ok f) :
    0 < pm.toRat ∧ f.toRat * pm.toRat ≤ rate.toRat * (1 + pm.toRat) * (1 + ε) ^ 3 ∧
      rate.toRat * (1 + pm.toRat) * (1 - ε) ^ 3 ≤ f.toRat * pm.toRat := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hone := Number.ofInt64_isNormalized 1
  have hr0 : 0 < rate.toRat := lt_of_lt_of_le (by norm_num) hlow
  have hpm : 0 < pm.toRat := by
    rcases hpm0.lt_or_eq with h | h
    · exact h
    · exact absurd hf (fun hf => Number.div_zero_error (Number.eq_zero_of_toRat hpmN h.symm) hf)
  -- `R` rounds `1 + pm` and is at least one
  have hRN := operator_add_isNormalized_to_nearest_sz _ _ R hone hpmN hR
  have hR1 : 1 ≤ R.toRat := by
    have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hpmN hR) _ hone
      (by rw [Number.ofInt64_one_toRat]; linarith)
    rwa [Number.ofInt64_one_toRat] at this
  have nR := Number.add_near _ _ _ hone hpmN hR
  rw [Number.ofInt64_one_toRat] at nR
  have hRle := nR.le (by linarith)
  have hRge := nR.ge (by linarith) (by linarith)
  -- `num` rounds `rate·R` and is at least the rate
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hRN hnum
  have hnum1 : rate.toRat ≤ num.toRat :=
    rn_ge (operator_mul_rounded_to_nearest _ _ _ hrate hRN hnum) rate hrate (by nlinarith)
  have nnum := Number.mul_near _ _ _ hrate hRN hnum
  have hnumle := nnum.le (by positivity)
  have hnumge := nnum.ge (by linarith) (by positivity)
  -- `f` rounds `num / pm`, which is above `10^-13`
  have nf := Number.div_near _ _ _ hnumN hpmN hf
  have hq0 : 0 ≤ num.toRat / pm.toRat := div_nonneg (by linarith) hpm.le
  have hfle := nf.le hq0
  have hqge : rate.toRat * (1 - ε) ^ 2 ≤ num.toRat / pm.toRat := by
    rw [le_div_iff₀ hpm]
    have h1 : rate.toRat * ((1 + pm.toRat) * (1 - ε)) * (1 - ε) ≤ num.toRat := by
      calc rate.toRat * ((1 + pm.toRat) * (1 - ε)) * (1 - ε) ≤ rate.toRat * R.toRat * (1 - ε) := by
            gcongr; linarith
        _ ≤ num.toRat := hnumge
    have h2 : rate.toRat * (1 - ε) ^ 2 * pm.toRat ≤ rate.toRat * ((1 + pm.toRat) * (1 - ε)) * (1 - ε) := by
      have : 0 ≤ rate.toRat * (1 - ε) ^ 2 := by positivity
      nlinarith
    linarith
  obtain ⟨w, hwN, hwv⟩ := Number.tiny
  have hf0 : f.toRat ≠ 0 := by
    have hw := rn_ge (operator_div_rounded_to_nearest _ _ _ hnumN hpmN hf) w hwN (by
      rw [hwv]
      refine le_trans ?_ hqge
      have : (1 - 1 / 10 ^ 18 : ℚ) ^ 2 ≤ (1 - ε) ^ 2 := by gcongr; linarith
      calc (1 : ℚ) / 10 ^ 13 ≤ 1 / 10 ^ 12 * (1 - 1 / 10 ^ 18) ^ 2 := by norm_num
        _ ≤ rate.toRat * (1 - ε) ^ 2 := by gcongr)
    rw [hwv] at hw
    intro h0; rw [h0] at hw; norm_num at hw
  have hfge := nf.ge hf0 hq0
  have hpmne : pm.toRat ≠ 0 := hpm.ne'
  refine ⟨hpm, ?_, ?_⟩
  · calc f.toRat * pm.toRat ≤ num.toRat / pm.toRat * (1 + ε) * pm.toRat := by gcongr
      _ = num.toRat * (1 + ε) := by field_simp
      _ ≤ rate.toRat * R.toRat * (1 + ε) * (1 + ε) := by gcongr
      _ ≤ rate.toRat * ((1 + pm.toRat) * (1 + ε)) * (1 + ε) * (1 + ε) := by gcongr
      _ = rate.toRat * (1 + pm.toRat) * (1 + ε) ^ 3 := by ring
  · calc rate.toRat * (1 + pm.toRat) * (1 - ε) ^ 3
        = rate.toRat * ((1 + pm.toRat) * (1 - ε)) * (1 - ε) * (1 - ε) := by ring
      _ ≤ rate.toRat * R.toRat * (1 - ε) * (1 - ε) := by gcongr <;> linarith
      _ ≤ num.toRat * (1 - ε) := by gcongr; linarith
      _ = num.toRat / pm.toRat * (1 - ε) * pm.toRat := by field_simp
      _ ≤ f.toRat * pm.toRat := by gcongr

/-- Seven roundings up are at most three roundings down plus eleven errors. -/
private lemma seven_le_three : (1 + ε) ^ 7 ≤ (1 - ε) ^ 3 * (1 + 11 * ε) := by
  unfold Number.nearestError; norm_num

/-- `k − 1` payments of a count of at least two, as a count and as a rational. -/
private lemma pred_count (k : UInt32) (hk : 2 ≤ k.toNat) :
    (k - 1).toNat = k.toNat - 1 ∧ k - 1 ≠ 0 ∧ (((k - 1).toNat : ℕ) : ℚ) = (k.toNat : ℚ) - 1 := by
  have h1 : (k - 1).toNat = k.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)
  refine ⟨h1, fun h0 => ?_, ?_⟩
  · have := congrArg UInt32.toNat h0
    rw [h1] at this
    simp at this
    omega
  · rw [h1, Nat.cast_sub (by omega)]; norm_num

/-- The payment factor of `k` payments is at least four roundings below the factor of `k − 1` payments while the
rate covers `2·k` product errors and `16·(1 + rate)^k` roundings. A nonzero loan rate is at least `10^-12`. -/
lemma FactorGap.of_bound (rate : Number) (k : UInt32) (hrate : rate.isNormalized) (hlow : 1 / 10 ^ 12 ≤ rate.toRat)
    (hk : 2 ≤ k.toNat)
    (hb : 2 * k.toNat * Number.mulError * (1 + rate.toRat) +
      16 * Number.nearestError * (1 + rate.toRat) ^ k.toNat ≤ rate.toRat) :
    FactorGap rate k := by
  intro f f' hf hf'
  have he := Number.nearestError_pos
  have he' := eps_small
  have hr0 : 0 < rate.toRat := lt_of_lt_of_le (by norm_num) hlow
  have hk0 : k ≠ 0 := by intro h0; rw [h0] at hk; simp at hk
  obtain ⟨hk1v, hk10, hk1q⟩ := pred_count k hk
  have hk32 : k.toNat ≤ 2 ^ 32 := k.toNat_lt.le
  have hk2 : (2 : ℚ) ≤ k.toNat := by exact_mod_cast hk
  obtain ⟨pm, R, num, hpm, hR, hnum, hdiv⟩ := computePaymentFactor_steps rate k f hrate hr0 hk0 hf
  obtain ⟨pm', R', num', hpm', hR', hnum', hdiv'⟩ := computePaymentFactor_steps rate (k - 1) f' hrate hr0 hk10 hf'
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hN' := Number.ofInt64_isNormalized (k - 1).toInt64
  have hpmN := computePowerMinusOneHybrid_isNormalized rate _ k pm hrate hN hpm
  have hpmN' := computePowerMinusOneHybrid_isNormalized rate _ (k - 1) pm' hrate hN' hpm'
  have hpm0 := computePowerMinusOneHybrid_nonneg rate _ k pm hrate hr0.le hN
    (by rw [Number.ofInt64_count]; positivity) hpm
  have hpm0' := computePowerMinusOneHybrid_nonneg rate _ (k - 1) pm' hrate hr0.le hN'
    (by rw [Number.ofInt64_count]; positivity) hpm'
  obtain ⟨hP, hfle, -⟩ := factor_bounds rate pm R num f hrate hlow hpmN hpm0 hR hnum hdiv
  obtain ⟨hP', -, hfge'⟩ := factor_bounds rate pm' R' num' f' hrate hlow hpmN' hpm0' hR' hnum' hdiv'
  -- `k − 1` is at most `1000` while `(k − 1)·rate` is below `10^-9`
  have hsmall : ((k.toNat : ℚ) - 1) * rate.toRat < 1 / 10 ^ 9 → (k - 1).toNat ≤ 1000 := by
    intro hsm
    have : ((k.toNat : ℚ) - 1) ≤ 1000 := by
      by_contra hc
      push Not at hc
      have : 1000 * (1 / 10 ^ 12 : ℚ) < ((k.toNat : ℚ) - 1) * rate.toRat := by
        calc 1000 * (1 / 10 ^ 12 : ℚ) < ((k.toNat : ℚ) - 1) * (1 / 10 ^ 12) := by gcongr
          _ ≤ ((k.toNat : ℚ) - 1) * rate.toRat := by gcongr
      norm_num at this
      linarith
    rw [← hk1q] at this
    exact_mod_cast this
  have key : 11 * ε * pm'.toRat * (1 + pm.toRat) ≤ pm.toRat - pm'.toRat := by
    rcases computePowerMinusOneHybrid_cases rate k pm hrate hr0 hk0 hpm with
      ⟨b, p, hb1, hp, hs, -⟩ | ⟨hlt, hbin⟩ <;>
    rcases computePowerMinusOneHybrid_cases rate (k - 1) pm' hrate hr0 hk10 hpm' with
      ⟨b', p', hb1', hp', hs', hge'⟩ | ⟨hlt', hbin'⟩
    · -- both closed forms, with the same rounded base
      have hbb : b' = b := by rw [hb1] at hb1'; exact (Except.ok.inj hb1').symm
      subst hbb
      obtain ⟨hbN, hbge1, hblo, hbhi⟩ := base_bounds rate b' hrate hr0.le hb1
      have hlo := (closed_bounds b' p pm k.toNat hbN hbge1 (by omega) hp hs).2 hP.ne'
      have hhi := (closed_bounds b' p' pm' (k - 1).toNat hbN hbge1 (by omega) hp' hs').1
      rw [hk1v] at hhi
      exact closed_closed_gap _ _ _ _ k.toNat hk hk32 hr0.le hbge1 hblo hbhi hlo hhi hb
    · -- the closed form for `k`, the series for `k − 1`
      rw [hk1q] at hlt'
      obtain ⟨hbN, hbge1, hblo, hbhi⟩ := base_bounds rate b hrate hr0.le hb1
      have hlo := (closed_bounds b p pm k.toNat hbN hbge1 (by omega) hp hs).2 hP.ne'
      have hlo' := small_closed_lower _ _ _ k.toNat hk hlow hlt' hbge1 hblo hbhi hlo
      have hhi := computePowerMinusOne_le rate (k - 1) pm' hrate hr0.le (by rw [hk1q]; exact hlt') hbin'
      have hhi' := small_binomial_upper _ _ (k - 1).toNat (hsmall hlt') hr0.le hhi
      rw [hk1q] at hhi'
      exact small_gap _ _ _ k.toNat hk hlow hlt' hlo' hhi'
    · -- the series for `k` and the closed form for `k − 1` would need a rate below `10^-12`
      exfalso
      rw [hk1q] at hge'
      have : ((k.toNat : ℚ) - 1) * rate.toRat < 1 / 10 ^ 9 - rate.toRat := by linarith
      have h1 : (1 / 10 ^ 9 : ℚ) ≤ (1 / 10 ^ 9 - rate.toRat) * (1 + ε) := by
        calc (1 / 10 ^ 9 : ℚ) ≤ ((k.toNat : ℚ) - 1) * rate.toRat * (1 + ε) := hge'
          _ ≤ (1 / 10 ^ 9 - rate.toRat) * (1 + ε) := by gcongr
      nlinarith
    · -- both series
      rw [hk1q] at hlt'
      have hlo := computePowerMinusOne_ge rate k pm hrate hr0 hk0 hbin
      have hlo' : k.toNat * rate.toRat * (1 - 1 / 10 ^ 14) - 3 / 10 ^ 15 ≤ pm.toRat := by
        have : (k.toNat : ℚ) * rate.toRat * ε ≤ k.toNat * rate.toRat * (1 / 10 ^ 14) := by
          gcongr; linarith
        nlinarith
      have hhi := computePowerMinusOne_le rate (k - 1) pm' hrate hr0.le (by rw [hk1q]; exact hlt') hbin'
      have hhi' := small_binomial_upper _ _ (k - 1).toNat (hsmall hlt') hr0.le hhi
      rw [hk1q] at hhi'
      exact small_gap _ _ _ k.toNat hk hlow hlt' hlo' hhi'
  -- seven roundings of the gap fit: `(1 + ε)^7·(1 + pm)·pm' ≤ (1 − ε)^3·(1 + pm')·pm`
  have hkey : (1 + 11 * ε) * (1 + pm.toRat) * pm'.toRat ≤ (1 + pm'.toRat) * pm.toRat := by nlinarith
  have h1e : 0 ≤ rate.toRat * (1 - ε) ^ 3 := mul_nonneg hr0.le (pow_nonneg (by linarith) _)
  have hPP : 0 < pm.toRat * pm'.toRat := mul_pos hP hP'
  have hmain : f.toRat * (1 + ε) ^ 4 * (pm.toRat * pm'.toRat) ≤ f'.toRat * (pm.toRat * pm'.toRat) := by
    calc f.toRat * (1 + ε) ^ 4 * (pm.toRat * pm'.toRat)
        = f.toRat * pm.toRat * ((1 + ε) ^ 4 * pm'.toRat) := by ring
      _ ≤ rate.toRat * (1 + pm.toRat) * (1 + ε) ^ 3 * ((1 + ε) ^ 4 * pm'.toRat) :=
          mul_le_mul_of_nonneg_right hfle (by positivity)
      _ = rate.toRat * (1 + ε) ^ 7 * ((1 + pm.toRat) * pm'.toRat) := by ring
      _ ≤ rate.toRat * ((1 - ε) ^ 3 * (1 + 11 * ε)) * ((1 + pm.toRat) * pm'.toRat) := by
          gcongr; exact seven_le_three
      _ = rate.toRat * (1 - ε) ^ 3 * ((1 + 11 * ε) * (1 + pm.toRat) * pm'.toRat) := by ring
      _ ≤ rate.toRat * (1 - ε) ^ 3 * ((1 + pm'.toRat) * pm.toRat) := mul_le_mul_of_nonneg_left hkey h1e
      _ = rate.toRat * (1 + pm'.toRat) * (1 - ε) ^ 3 * pm.toRat := by ring
      _ ≤ f'.toRat * pm'.toRat * pm.toRat := mul_le_mul_of_nonneg_right hfge' hP.le
      _ = f'.toRat * (pm.toRat * pm'.toRat) := by ring
  exact le_of_mul_le_mul_right hmain hPP

/-- The bound at `N` payments gives the payment factor gap at every count from `2` to `N`. The bound only
grows with the count. -/
lemma FactorGap.of_bound_le (rate : Number) (N : UInt32) (hrate : rate.isNormalized)
    (hlow : 1 / 10 ^ 12 ≤ rate.toRat)
    (hb : 2 * N.toNat * Number.mulError * (1 + rate.toRat) +
      16 * Number.nearestError * (1 + rate.toRat) ^ N.toNat ≤ rate.toRat) :
    ∀ k : UInt32, 2 ≤ k.toNat → k ≤ N → FactorGap rate k := by
  intro k hk hkN
  have hkN' : k.toNat ≤ N.toNat := UInt32.le_iff_toNat_le.mp hkN
  have hr0 : 0 ≤ rate.toRat := le_trans (by norm_num) hlow
  have hm := Number.mulError_pos
  have he := Number.nearestError_pos
  refine FactorGap.of_bound rate k hrate hlow hk (le_trans ?_ hb)
  have h1 : (k.toNat : ℚ) ≤ N.toNat := by exact_mod_cast hkN'
  have h2 : (1 + rate.toRat) ^ k.toNat ≤ (1 + rate.toRat) ^ N.toNat := pow_le_pow_right₀ (by linarith) hkN'
  gcongr

end XRPL.Model.Lending
