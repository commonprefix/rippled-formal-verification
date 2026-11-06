import XRPL.Properties.Lending.Loan.Common.FactorGap
import XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal

/-! # The theoretical principal when the payment factor falls

When the payment factor falls by at least four roundings per payment, one payment less never raises the theoretical
principal. After a re-amortization of `x`, the theoretical principal after the next payment is at most `x`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_nonneg loanPeriodicPayment_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.eq_zero_of_toRat Number.div_zero_error from XRPL.Properties.Lending.Loan.Common.PaymentFactor

local notation "ε" => Number.nearestError

/-- One payment less of `k ≠ 0` payments is `k − 1` of them. -/
private lemma UInt32.toNat_pred (k : UInt32) (hk : k ≠ 0) : (k - 1).toNat = k.toNat - 1 := by
  have h0 : k.toNat ≠ 0 := fun h' => hk (UInt32.toNat_inj.mp (by simpa using h'))
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp

/-- Taking a payment off never raises the theoretical principal of a PeriodicPayment of at least `10^-40`, when
the payment factor falls by at least four roundings. -/
lemma loanPrincipalFromPeriodicPayment_pred_le (pp rate : Number) (k : UInt32) (t t' : Number)
    (hpp : pp.isNormalized) (hppL : 1 / 10 ^ 40 ≤ pp.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hlow : rate.toRat ≠ 0 → 1 / 10 ^ 12 ≤ rate.toRat) (hhigh : rate.toRat ≤ 200) (hk : k ≠ 0)
    (hgap : 2 ≤ k.toNat → FactorGap rate k)
    (h : loanPrincipalFromPeriodicPayment pp rate k = .ok t)
    (h' : loanPrincipalFromPeriodicPayment pp rate (k - 1) = .ok t') : t'.toRat ≤ t.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have ht := loanPrincipalFromPeriodicPayment_ge pp rate k t hpp hppL hrate hr0 hlow hhigh hk h
  have ht0 : 0 < t.toRat := lt_of_lt_of_le (by norm_num) ht
  by_cases hk1 : k - 1 = 0
  · rw [hk1, loanPrincipalFromPeriodicPayment_zero, Except.ok.injEq] at h'
    rw [← h', Number.toRat_zero]
    exact ht0.le
  have hkp := UInt32.toNat_pred k hk
  have hk1' : (k - 1).toNat ≠ 0 := fun h0 => hk1 (UInt32.toNat_inj.mp (by simpa using h0))
  have hk2 : 2 ≤ k.toNat := by omega
  have hk32 : (k.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast k.toNat_lt.le
  have hkq : ((k - 1).toNat : ℚ) = k.toNat - 1 := by
    rw [hkp]; push_cast [show 1 ≤ k.toNat by omega]; ring
  have hN := Number.ofInt64_isNormalized k.toInt64
  have hNv := Number.ofInt64_count k
  have hN' := Number.ofInt64_isNormalized (k - 1).toInt64
  have hNv' := Number.ofInt64_count (k - 1)
  have hppm : pp.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_iff.mpr h0] at hppL; norm_num at hppL
  unfold loanPrincipalFromPeriodicPayment at h h'
  dsimp only at h h'
  split at h
  · rename_i h0; exact absurd (by simpa using h0) hk
  split at h'
  · rename_i h0; exact absurd (by simpa using h0) hk1
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h'⟩ := bind_ok_peel _ _ _ h'
  split at h
  · -- no interest: `pp·(k − 1)` against `pp·k`
    rename_i hz
    split at h'
    swap
    · rename_i hz'; exact absurd hz hz'
    have hle := (Number.mul_near _ _ _ hpp hN' h').le (by rw [hNv']; positivity)
    have hge := (Number.mul_near _ _ _ hpp hN h).ge (ne_of_gt ht0) (by rw [hNv]; positivity)
    rw [hNv', hkq] at hle
    rw [hNv] at hge
    have hpp0 : 0 ≤ pp.toRat := le_trans (by norm_num) hppL
    have hkk : ((k.toNat : ℚ) - 1) * (1 + ε) ≤ k.toNat * (1 - ε) := by nlinarith
    calc t'.toRat ≤ pp.toRat * ((k.toNat : ℚ) - 1) * (1 + ε) := hle
      _ = pp.toRat * (((k.toNat : ℚ) - 1) * (1 + ε)) := by ring
      _ ≤ pp.toRat * (k.toNat * (1 - ε)) := mul_le_mul_of_nonneg_left hkk hpp0
      _ = pp.toRat * k.toNat * (1 - ε) := by ring
      _ ≤ t.toRat := hge
  · -- interest: `pp/f'` against `pp/f` with `f·(1 + ε)^4 ≤ f'`
    rename_i hz
    split at h'
    · rename_i hz'; exact absurd hz' hz
    obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨f', hf', h'⟩ := bind_ok_peel _ _ _ h'
    have hg := hgap hk2 f f' hf hf'
    have hfN := computePaymentFactor_isNormalized rate _ k f hrate hN hf
    have hfN' := computePaymentFactor_isNormalized rate _ (k - 1) f' hrate hN' hf'
    have hf0 := computePaymentFactor_nonneg rate _ k f hrate hr0 hN (by rw [hNv]; positivity) hf
    have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) h
    have hfne' : f'.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN' h0) h'
    have hfpos : 0 < f.toRat := lt_of_le_of_ne hf0 (Ne.symm hfne)
    have hpp0 : 0 ≤ pp.toRat := le_trans (by norm_num) hppL
    have he4 : 1 ≤ (1 + ε) ^ 4 := one_le_pow₀ (by linarith)
    have hfpos' : 0 < f'.toRat := lt_of_lt_of_le (by nlinarith) hg
    have hle := (Number.div_near _ _ _ hpp hfN' h').le (div_nonneg hpp0 hfpos'.le)
    have hge := (Number.div_near _ _ _ hpp hfN h).ge (ne_of_gt ht0) (div_nonneg hpp0 hfpos.le)
    have h3 : 1 ≤ (1 + ε) ^ 3 * (1 - ε) := by nlinarith [sq_nonneg ε, mul_pos he he]
    calc t'.toRat ≤ pp.toRat / f'.toRat * (1 + ε) := hle
      _ ≤ pp.toRat / (f.toRat * (1 + ε) ^ 4) * (1 + ε) := by gcongr
      _ = pp.toRat / f.toRat / (1 + ε) ^ 3 := by field_simp
      _ ≤ pp.toRat / f.toRat * (1 - ε) := by
          rw [div_le_iff₀ (by positivity)]
          have : 0 ≤ pp.toRat / f.toRat := div_nonneg hpp0 hfpos.le
          nlinarith
      _ ≤ t.toRat := hge

/-- A re-amortization never schedules more principal than it re-amortized. The theoretical principal after the
next payment of the PeriodicPayment of `x` over `n` payments is at most `x`, when the payment factor falls. -/
lemma loanPrincipalFromPeriodicPayment_reamortized_le (x rate : Number) (n : UInt32) (pp t : Number)
    (hx : x.isNormalized) (hx0 : 0 ≤ x.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hgap : 2 ≤ n.toNat → FactorGap rate n) (hpp : loanPeriodicPayment x rate n = .ok pp)
    (h : loanPrincipalFromPeriodicPayment pp rate (n - 1) = .ok t) : t.toRat ≤ x.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  by_cases hn1 : n - 1 = 0
  · rw [hn1, loanPrincipalFromPeriodicPayment_zero, Except.ok.injEq] at h
    rw [← h, Number.toRat_zero]
    exact hx0
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hx hrate hpp
  have hpp0 := loanPeriodicPayment_nonneg _ _ _ _ hx hx0 hrate hr0 hpp
  have hN' := Number.ofInt64_isNormalized (n - 1).toInt64
  have hNv' := Number.ofInt64_count (n - 1)
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · rename_i h0; exact absurd (by simpa using h0) hn1
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  unfold loanPeriodicPayment at hpp
  dsimp only at hpp
  split at hpp
  · -- no principal: the PeriodicPayment is zero, so the theoretical principal is at most zero
    simp only [pure, Except.pure, Except.ok.injEq] at hpp
    subst hpp
    split at h
    · have := (Number.mul_near _ _ _ Number.zero_isNormalized hN' h).le
        (by rw [Number.toRat_zero, zero_mul])
      rw [Number.toRat_zero, zero_mul, zero_mul] at this
      linarith
    · obtain ⟨f', hf', h⟩ := bind_ok_peel _ _ _ h
      have hfN' := computePaymentFactor_isNormalized rate _ (n - 1) f' hrate hN' hf'
      have := (Number.div_near _ _ _ Number.zero_isNormalized hfN' h).le (by rw [Number.toRat_zero, zero_div])
      rw [Number.toRat_zero, zero_div, zero_mul] at this
      linarith
  rename_i hz0
  have hn0 : n ≠ 0 := by intro h0; apply hz0; simp [h0]
  have hnp := UInt32.toNat_pred n hn0
  have hn1' : (n - 1).toNat ≠ 0 := fun h0 => hn1 (UInt32.toNat_inj.mp (by simpa using h0))
  have hn2 : 2 ≤ n.toNat := by omega
  have hn32 : (n.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast n.toNat_lt.le
  have hnq : ((n - 1).toNat : ℚ) = n.toNat - 1 := by
    rw [hnp]; push_cast [show 1 ≤ n.toNat by omega]; ring
  have hn2q : (2 : ℚ) ≤ n.toNat := by exact_mod_cast hn2
  have hnpos : (0 : ℚ) < n.toNat := by linarith
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  obtain ⟨_, -, hpp⟩ := bind_ok_peel _ _ _ hpp
  split at hpp
  · -- no interest: `x/n` times `n − 1`
    rename_i hz
    split at h
    swap
    · rename_i hz'; exact absurd hz hz'
    have hpple := (Number.div_near _ _ _ hx hN hpp).le (by rw [hNv]; positivity)
    have hle := (Number.mul_near _ _ _ hppN hN' h).le (by rw [hNv']; positivity)
    rw [hNv] at hpple
    rw [hNv', hnq] at hle
    have hn1q : (0 : ℚ) ≤ n.toNat - 1 := by linarith
    have hkk : ((n.toNat : ℚ) - 1) * ((1 + ε) * (1 + ε)) ≤ n.toNat := by
      have hsq : (1 + ε) * (1 + ε) ≤ 1 + 3 * ε := by nlinarith
      have h1 := mul_le_mul_of_nonneg_left hsq hn1q
      have h2 : ((n.toNat : ℚ) - 1) * (3 * ε) ≤ 1 := by nlinarith
      nlinarith
    calc t.toRat ≤ pp.toRat * ((n.toNat : ℚ) - 1) * (1 + ε) := hle
      _ ≤ x.toRat / n.toNat * (1 + ε) * ((n.toNat : ℚ) - 1) * (1 + ε) := by gcongr
      _ = x.toRat * ((((n.toNat : ℚ) - 1) * ((1 + ε) * (1 + ε))) / n.toNat) := by field_simp
      _ ≤ x.toRat * (n.toNat / n.toNat) := by gcongr
      _ = x.toRat := by rw [div_self (ne_of_gt hnpos), mul_one]
  · -- interest: `x·f` over `f' ≥ f·(1 + ε)^4`
    rename_i hz
    split at h
    · rename_i hz'; exact absurd hz' hz
    obtain ⟨f, hf, hpp⟩ := bind_ok_peel _ _ _ hpp
    obtain ⟨f', hf', h⟩ := bind_ok_peel _ _ _ h
    have hg := hgap hn2 f f' hf hf'
    have hfN := computePaymentFactor_isNormalized rate _ n f hrate hN hf
    have hfN' := computePaymentFactor_isNormalized rate _ (n - 1) f' hrate hN' hf'
    have hf0 := computePaymentFactor_nonneg rate _ n f hrate hr0 hN (by rw [hNv]; positivity) hf
    have hfne' : f'.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN' h0) h
    have he4 : 1 ≤ (1 + ε) ^ 4 := one_le_pow₀ (by linarith)
    have hf0' : 0 ≤ f'.toRat := le_trans (by nlinarith) hg
    have hfpos' : 0 < f'.toRat := lt_of_le_of_ne hf0' (Ne.symm hfne')
    have hpple := (Number.mul_near _ _ _ hx hfN hpp).le (mul_nonneg hx0 hf0)
    have hle := (Number.div_near _ _ _ hppN hfN' h).le (div_nonneg hpp0 hfpos'.le)
    have h24 : (1 + ε) * (1 + ε) ≤ (1 + ε) ^ 4 := by nlinarith
    have hff : f.toRat * ((1 + ε) * (1 + ε)) ≤ f'.toRat :=
      le_trans (mul_le_mul_of_nonneg_left h24 hf0) hg
    calc t.toRat ≤ pp.toRat / f'.toRat * (1 + ε) := hle
      _ ≤ x.toRat * f.toRat * (1 + ε) / f'.toRat * (1 + ε) := by gcongr
      _ = x.toRat * (f.toRat * ((1 + ε) * (1 + ε))) / f'.toRat := by ring
      _ ≤ x.toRat * f'.toRat / f'.toRat := by gcongr
      _ = x.toRat := by rw [mul_div_assoc, div_self (ne_of_gt hfpos'), mul_one]

end XRPL.Model.Lending
