import Mathlib.Analysis.Complex.ExponentialBounds
import XRPL.Model.Vault.Vault
import XRPL.Properties.Lending.Loan.Common.FactorBound
import XRPL.Properties.Lending.Loan.Common.FactorGapBound

/-! # Loan terms with a payment factor that falls with each payment

A loan of at most 30 years at a nonzero rate with a PaymentInterval of at least 60 seconds has the payment factor gap
at every count for a rate up to 80%, or up to 100% with intervals of two hours or more or a term of 25 years or less. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful

local notation "ε" => Number.nearestError
local notation "μ" => Number.mulError

private lemma eps_small : ε ≤ 7 / 10 ^ 19 := by unfold Number.nearestError; norm_num

/-- A periodic rate is within three roundings of the interest rate prorated to the interval. -/
lemma loanPeriodicRate_bounds (ir : TenthBips32) (interval : UInt32) (rate : Number)
    (h : loanPeriodicRate ir interval = .ok rate) :
    rate.toRat ≤ interval.toNat * ir.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 ∧
      (rate.toRat ≠ 0 → interval.toNat * ir.toNat / (10 ^ 5 * 31536000) * (1 - ε) ^ 3 ≤ rate.toRat) := by
  have he := Number.nearestError_pos
  have he' := eps_small
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
  have nr := Number.div_near _ _ _ htN hY h
  have nt := Number.div_near _ _ _ hpN hU ht
  have np := Number.mul_near _ _ _ hI hB hp
  rw [hYv] at nr
  rw [hUv] at nt
  rw [hIv, hBv] at np
  have hi0 : (0 : ℚ) ≤ interval.toNat := by positivity
  have hb0 : (0 : ℚ) ≤ ir.toNat := by positivity
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hI hB hp) (by rw [hIv, hBv]; positivity)
  have ht0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpN hU ht) (by rw [hUv]; positivity)
  have e3 : interval.toNat * ir.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 =
      interval.toNat * ir.toNat * (1 + ε) / 100000 * (1 + ε) / 31536000 * (1 + ε) := by ring
  constructor
  · rw [e3]
    calc rate.toRat ≤ t.toRat / 31536000 * (1 + ε) := nr.le (by positivity)
      _ ≤ p.toRat / 100000 * (1 + ε) / 31536000 * (1 + ε) := by gcongr; exact nt.le (by positivity)
      _ ≤ interval.toNat * ir.toNat * (1 + ε) / 100000 * (1 + ε) / 31536000 * (1 + ε) := by
          gcongr; exact np.le (by positivity)
  · intro hr
    -- every step before the rate is nonzero, or the rate would be zero
    have ht' : t.toRat ≠ 0 := by
      intro h0
      have := nr.le (by rw [h0]; norm_num)
      rw [h0] at this
      exact hr (le_antisymm (by linarith) (rn_nonneg (operator_div_rounded_to_nearest _ _ _ htN hY h)
        (by rw [hYv]; positivity)))
    have hp' : p.toRat ≠ 0 := by
      intro h0
      have := nt.le (by rw [h0]; norm_num)
      rw [h0] at this
      exact ht' (le_antisymm (by linarith) ht0)
    have h1e : (0 : ℚ) ≤ 1 - ε := by linarith
    calc interval.toNat * ir.toNat / (10 ^ 5 * 31536000) * (1 - ε) ^ 3
        = interval.toNat * ir.toNat * (1 - ε) / 100000 * (1 - ε) / 31536000 * (1 - ε) := by ring
      _ ≤ p.toRat / 100000 * (1 - ε) / 31536000 * (1 - ε) := by gcongr; exact np.ge hp' (by positivity)
      _ ≤ t.toRat / 31536000 * (1 - ε) := by gcongr; exact nt.ge ht' (by positivity)
      _ ≤ rate.toRat := nr.ge hr (by positivity)

/-- `(1 + r)^N` is at most `2.7182818286^k / (1 − d)` while `N·r ≤ k + d`, as `2.7182818286` is above `e`. -/
private lemma one_add_pow_le_exp (r d : ℚ) (N k : ℕ) (hr : 0 ≤ r) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (h : N * r ≤ k + d) : (1 + r) ^ N ≤ (27182818286 / 10 ^ 10) ^ k / (1 - d) := by
  have hR : ((1 + r : ℚ) : ℝ) ^ N ≤ (((27182818286 / 10 ^ 10 : ℚ) : ℝ)) ^ k / (1 - (d : ℝ)) := by
    have h1 : (1 + (r : ℝ)) ^ N ≤ Real.exp r ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (r : ℝ)]) N
    have h2 : Real.exp r ^ N ≤ Real.exp (k + d) := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by exact_mod_cast h)
    have h3 : Real.exp (k + d) ≤ Real.exp 1 ^ k * (1 / (1 - d)) := by
      rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
      gcongr
      exact Real.exp_bound_div_one_sub_of_interval (by exact_mod_cast hd0) (by exact_mod_cast hd1)
    have h4 : Real.exp 1 ^ k ≤ (((27182818286 / 10 ^ 10 : ℚ) : ℝ)) ^ k := by
      gcongr
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    have hd' : (0 : ℝ) < 1 - d := by
      have : (d : ℝ) < 1 := by exact_mod_cast hd1
      linarith
    push_cast
    calc (1 + (r : ℝ)) ^ N ≤ Real.exp 1 ^ k * (1 / (1 - d)) := le_trans h1 (le_trans h2 h3)
      _ ≤ (((27182818286 / 10 ^ 10 : ℚ) : ℝ)) ^ k * (1 / (1 - d)) := by gcongr
      _ = _ := by push_cast; ring
  exact_mod_cast hR

/-- One block of loan terms meets the gap bound. Interest rates from `lo` to `hi` tenth bips, intervals of
at least `T0` seconds and loans of at most `P` seconds, once the numbers check at the low end of the block. -/
private lemma gap_bound_block (r d : ℚ) (I T N k lo hi T0 P : ℕ) (hlo : lo ≤ I) (hhi : I ≤ hi) (hT : T0 ≤ T)
    (hT0 : 1 ≤ T0) (hNT : N * T ≤ P)
    (hrlo : T * I / (10 ^ 5 * 31536000) * (1 - ε) ^ 3 ≤ r) (hrhi : r ≤ T * I / (10 ^ 5 * 31536000) * (1 + ε) ^ 3)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hx : (P : ℚ) * hi / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 ≤ k + d)
    (hcheck : 2 * μ * (P : ℚ) + T0 * (2 * μ * (k + d) + 16 * ε * ((27182818286 / 10 ^ 10) ^ k / (1 - d))) ≤
      T0 * T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000)) :
    2 * N * μ * (1 + r) + 16 * ε * (1 + r) ^ N ≤ r := by
  have he := Number.nearestError_pos
  have he' := eps_small
  have hm := Number.mulError_pos
  have hT0q : (1 : ℚ) ≤ T0 := by exact_mod_cast hT0
  have hTq : (T0 : ℚ) ≤ T := by exact_mod_cast hT
  have hloq : (lo : ℚ) ≤ I := by exact_mod_cast hlo
  have hhiq : (I : ℚ) ≤ hi := by exact_mod_cast hhi
  have hNTq : (N : ℚ) * T ≤ P := by exact_mod_cast hNT
  have hT1 : (0 : ℚ) < T := by linarith
  have h1e : (0 : ℚ) ≤ (1 + ε) ^ 3 := by positivity
  have h1e' : (0 : ℚ) ≤ (1 - ε) ^ 3 := pow_nonneg (by linarith) 3
  have hr0 : 0 ≤ r := le_trans (by positivity) hrlo
  have hNr : N * r ≤ k + d := by
    have : (N : ℚ) * r ≤ N * T * I / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 := by
      calc (N : ℚ) * r ≤ N * (T * I / (10 ^ 5 * 31536000) * (1 + ε) ^ 3) := by gcongr
        _ = N * T * I / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 := by ring
    refine le_trans this (le_trans ?_ hx)
    have : (N : ℚ) * T * I ≤ P * hi := mul_le_mul hNTq hhiq (by positivity) (by norm_num)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this (by norm_num)) h1e
  have hE := one_add_pow_le_exp r d N k hr0 hd0 hd1 hNr
  set E := (27182818286 / 10 ^ 10 : ℚ) ^ k / (1 - d) with hEdef
  -- times `T`, the bound is at most `T·T0·lo·(1 − ε)^3 / (10^5·31536000)`, which is at most `T·r`
  have hβ : 2 * μ * P ≤
      T0 * (T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) - (2 * μ * (k + d) + 16 * ε * E)) := by
    have : T0 * (T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) - (2 * μ * (k + d) + 16 * ε * E)) =
        T0 * T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) - T0 * (2 * μ * (k + d) + 16 * ε * E) := by ring
    linarith
  have hβ0 : 0 ≤ T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) - (2 * μ * (k + d) + 16 * ε * E) := by
    by_contra hc
    push Not at hc
    have : (T0 : ℚ) * (T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) - (2 * μ * (k + d) + 16 * ε * E)) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hc
    have : 0 ≤ 2 * μ * (P : ℚ) := by positivity
    linarith
  have hTβ := mul_le_mul_of_nonneg_right hTq hβ0
  have hrT : T * (T0 * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000)) ≤ T * r := by
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hrlo) hT1.le
    have : (T0 : ℚ) * lo ≤ T * I := mul_le_mul hTq hloq (by positivity) hT1.le
    calc (T0 : ℚ) * lo * (1 - ε) ^ 3 / (10 ^ 5 * 31536000) = T0 * lo / (10 ^ 5 * 31536000) * (1 - ε) ^ 3 := by
          ring
      _ ≤ T * I / (10 ^ 5 * 31536000) * (1 - ε) ^ 3 :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this (by norm_num)) h1e'
  have hlhs : T * (2 * N * μ * (1 + r) + 16 * ε * (1 + r) ^ N) ≤
      2 * μ * P + T * (2 * μ * (k + d) + 16 * ε * E) := by
    have h1 : T * (2 * N * μ) ≤ 2 * μ * P := by nlinarith
    have h2 : T * (2 * μ * (N * r)) ≤ T * (2 * μ * (k + d)) := by gcongr
    have h3 : T * (16 * ε * (1 + r) ^ N) ≤ T * (16 * ε * E) := by gcongr
    nlinarith
  have : T * (2 * N * μ * (1 + r) + 16 * ε * (1 + r) ^ N) ≤ T * r := by nlinarith
  exact le_of_mul_le_mul_left this hT1

/-- A nonzero periodic rate over at least 60 seconds is normalized, at least `10^-12`, within three roundings of
the prorated interest rate, and its interest rate is at least one tenth bip. -/
private lemma loanRate_facts (ir : TenthBips32) (T : UInt32) (rate : Number) (h : loanPeriodicRate ir T = .ok rate)
    (hr : rate.toRat ≠ 0) (hT : 60 ≤ T.toNat) :
    rate.isNormalized ∧ 1 / 10 ^ 12 ≤ rate.toRat ∧ 1 ≤ ir.toNat ∧
      (T.toNat : ℚ) * ir.toNat / (10 ^ 5 * 31536000) * (1 - ε) ^ 3 ≤ rate.toRat ∧
      rate.toRat ≤ (T.toNat : ℚ) * ir.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3 := by
  obtain ⟨hhi, hlo⟩ := loanPeriodicRate_bounds ir T rate h
  refine ⟨loanPeriodicRate_isNormalized ir T rate h, loanPeriodicRate_ge ir T rate hT h hr, ?_, hlo hr, hhi⟩
  by_contra hc
  push Not at hc
  have h0 : ir.toNat = 0 := by omega
  rw [h0] at hhi
  push_cast at hhi
  have := loanPeriodicRate_nonneg ir T rate h
  exact hr (le_antisymm (by linarith) this)

/-- A loan of at most 30 years at a nonzero interest rate of at most 80% has the payment factor gap at every count
of payments from `2` to `N`, with a payment interval of at least 60 seconds. -/
lemma FactorGap.of_rate_le (ir : TenthBips32) (T N : UInt32) (rate : Number) (h : loanPeriodicRate ir T = .ok rate)
    (hr : rate.toRat ≠ 0) (hT : 60 ≤ T.toNat) (hir : ir.toNat ≤ 80000)
    (hNT : N.toNat * T.toNat ≤ SingleAssetVault.maxInvestmentPeriod) :
    ∀ k : UInt32, 2 ≤ k.toNat → k ≤ N → FactorGap rate k := by
  obtain ⟨hrate, hlow, hI1, hrlo, hrhi⟩ := loanRate_facts ir T rate h hr hT
  have hNT' : N.toNat * T.toNat ≤ 946708560 := hNT
  refine FactorGap.of_bound_le rate N hrate hlow ?_
  rcases le_or_gt ir.toNat 20000 with h1 | h1
  · exact gap_bound_block _ (1 / 100) ir.toNat T.toNat N.toNat 6 1 20000 60 946708560 hI1 h1 hT (by norm_num) hNT'
      hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)
  rcases le_or_gt ir.toNat 60000 with h2 | h2
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 18 20000 60000 60 946708560 h1.le h2 hT (by norm_num)
      hNT' hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 24 60000 80000 60 946708560 h2.le hir hT (by norm_num)
      hNT' hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)

/-- A loan of at most 30 years at a nonzero interest rate of at most 100% has the payment factor gap at every count
of payments from `2` to `N`, with a payment interval of at least two hours. -/
lemma FactorGap.of_interval_ge (ir : TenthBips32) (T N : UInt32) (rate : Number)
    (h : loanPeriodicRate ir T = .ok rate) (hr : rate.toRat ≠ 0) (hT : 7200 ≤ T.toNat) (hir : ir.toNat ≤ 100000)
    (hNT : N.toNat * T.toNat ≤ SingleAssetVault.maxInvestmentPeriod) :
    ∀ k : UInt32, 2 ≤ k.toNat → k ≤ N → FactorGap rate k := by
  obtain ⟨hrate, hlow, hI1, hrlo, hrhi⟩ := loanRate_facts ir T rate h hr (by omega)
  have hNT' : N.toNat * T.toNat ≤ 946708560 := hNT
  refine FactorGap.of_bound_le rate N hrate hlow ?_
  rcases le_or_gt ir.toNat 60000 with h1 | h1
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 18 1 60000 7200 946708560 hI1 h1 hT (by norm_num)
      hNT' hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 30 60000 100000 7200 946708560 h1.le hir hT
      (by norm_num) hNT' hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)

/-- A loan of at most 25 years at a nonzero interest rate of at most 100% has the payment factor gap at every count
of payments from `2` to `N`, with a payment interval of at least 60 seconds. -/
lemma FactorGap.of_term_le (ir : TenthBips32) (T N : UInt32) (rate : Number) (h : loanPeriodicRate ir T = .ok rate)
    (hr : rate.toRat ≠ 0) (hT : 60 ≤ T.toNat) (hir : ir.toNat ≤ 100000)
    (hNT : N.toNat * T.toNat ≤ 25 * 31556952) :
    ∀ k : UInt32, 2 ≤ k.toNat → k ≤ N → FactorGap rate k := by
  obtain ⟨hrate, hlow, hI1, hrlo, hrhi⟩ := loanRate_facts ir T rate h hr hT
  refine FactorGap.of_bound_le rate N hrate hlow ?_
  rcases le_or_gt ir.toNat 20000 with h1 | h1
  · exact gap_bound_block _ (1 / 100) ir.toNat T.toNat N.toNat 5 1 20000 60 (25 * 31556952) hI1 h1 hT
      (by norm_num) hNT hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)
  rcases le_or_gt ir.toNat 60000 with h2 | h2
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 15 20000 60000 60 (25 * 31556952) h1.le h2 hT
      (by norm_num) hNT hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)
  · exact gap_bound_block _ (2 / 100) ir.toNat T.toNat N.toNat 25 60000 100000 60 (25 * 31556952) h2.le hir hT
      (by norm_num) hNT hrlo hrhi (by norm_num) (by norm_num) (by unfold Number.nearestError; norm_num)
      (by unfold Number.nearestError Number.mulError; norm_num)

end XRPL.Model.Lending
