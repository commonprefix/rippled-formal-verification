import XRPL.Properties.Lending.Ledger.Common.LoanStarts
import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.NextTarget
import XRPL.Properties.Lending.Loan.Common.FactorGapLoan

/-! # A loan on a reachable ledger keeps principal while payments are left

A loan of a reachable ledger starts after SubscriptionDate and ends before RedemptionDate, so its term is at most the
vault's 30-year investment period. Its payment factor then drops by at least four roundings for each extra payment
left when the interest rate is at most 80%, the interval at least two hours, or the term at most 25 years, and always
at a zero rate. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

open private rn_nonneg Number.ofInt64_one_toRat from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.eq_zero_of_toRat Number.div_zero_error from XRPL.Properties.Lending.Loan.Common.PaymentFactor

local notation "ε" => Number.nearestError

/-- At a zero periodic rate the factor of `k` payments is `1/k` rounded, at least four roundings below the factor of
`k − 1` payments. -/
lemma FactorGap.of_zero_rate (rate : Number) (hrate : rate.isNormalized) (h0 : rate.toRat = 0) (k : UInt32)
    (hk : 2 ≤ k.toNat) : FactorGap rate k := by
  intro f f' hf hf'
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hz : rate.operator_eq Number.zero = true := by rw [Number.eq_zero_of_toRat hrate h0]; rfl
  have hk0 : k ≠ 0 := fun h' => by rw [h'] at hk; simp at hk
  have hkp : (k - 1).toNat = k.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp
  have hk1 : k - 1 ≠ 0 := fun h' => by
    have := congrArg UInt32.toNat h'
    rw [hkp] at this
    simp at this; omega
  have hone := Number.ofInt64_isNormalized 1
  have hN := Number.ofInt64_isNormalized k.toUInt64.toInt64
  have hNv := Number.ofInt64_count k
  have hN' := Number.ofInt64_isNormalized (k - 1).toUInt64.toInt64
  have hNv' := Number.ofInt64_count (k - 1)
  have hkq : ((k - 1).toNat : ℚ) = k.toNat - 1 := by
    rw [hkp]; push_cast [show 1 ≤ k.toNat by omega]; ring
  have hk2 : (2 : ℚ) ≤ k.toNat := by exact_mod_cast hk
  have hk32 : (k.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast k.toNat_lt.le
  unfold computePaymentFactor at hf hf'
  dsimp only at hf hf'
  split at hf
  · rename_i h; exact absurd (by simpa using h) hk0
  split at hf'
  · rename_i h; exact absurd (by simpa using h) hk1
  obtain ⟨_, -, hf⟩ := bind_ok_peel _ _ _ hf
  obtain ⟨_, -, hf'⟩ := bind_ok_peel _ _ _ hf'
  -- `f ≤ (1 + ε)/k` and `f' ≥ (1 − ε)/(k − 1)`, the latter not lost to underflow
  have hle := (Number.div_near _ _ _ hone hN hf).le (by rw [Number.ofInt64_one_toRat, hNv]; positivity)
  rw [Number.ofInt64_one_toRat, hNv] at hle
  have hm1 : (Number.ofInt64 1).mantissa_ ≠ 0 := fun h' => by
    have := Number.toRat_eq_zero_iff.mpr h'; rw [Number.ofInt64_one_toRat] at this; norm_num at this
  have hmN' : (Number.ofInt64 (k - 1).toUInt64.toInt64).mantissa_ ≠ 0 := fun h' => by
    have := Number.toRat_eq_zero_iff.mpr h'; rw [hNv', hkq] at this; linarith
  have hkm1 : (1 : ℚ) ≤ k.toNat - 1 := by linarith
  have hf'ne : f'.toRat ≠ 0 := by
    intro h'
    have hu := operator_div_underflow_truth_small _ _ _ _ hone hN' hm1 hmN' hf' (Number.toRat_eq_zero_iff.mp h')
    rw [Number.ofInt64_one_toRat, hNv', hkq, abs_of_nonneg (by positivity)] at hu
    have hmin : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-200 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
    have h1 : (1 : ℚ) / 2 ^ 32 ≤ 1 / ((k.toNat : ℚ) - 1) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]; linarith
    have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (minExponent : ℤ) ≤ 10 ^ (18 : ℕ) * 10 ^ (-200 : ℤ) := by gcongr
    have h3 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (-200 : ℤ) < 1 / 2 ^ 32 := by norm_num
    exact absurd (lt_of_lt_of_le hu h2) (not_lt.mpr (le_trans h3.le h1))
  have hge := (Number.div_near _ _ _ hone hN' hf').ge hf'ne (by rw [Number.ofInt64_one_toRat, hNv', hkq]; positivity)
  rw [Number.ofInt64_one_toRat, hNv', hkq] at hge
  have hf0 : 0 ≤ f.toRat := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hone hN hf)
    (by rw [Number.ofInt64_one_toRat, hNv]; positivity)
  -- `(k − 1)·(1 + ε)^5 ≤ k·(1 − ε)`
  have h5 : (1 + ε) ^ 5 ≤ 1 + 10 * ε := by
    have := one_add_pow_le_lin ε 5 he.le (by push_cast; linarith)
    push_cast at this; linarith
  have hkk : ((k.toNat : ℚ) - 1) * (1 + ε) ^ 5 ≤ k.toNat * (1 - ε) := by
    have := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℚ) ≤ k.toNat - 1)
    nlinarith
  have hkpos : (0 : ℚ) < k.toNat := by linarith
  calc f.toRat * (1 + ε) ^ 4 ≤ 1 / k.toNat * (1 + ε) * (1 + ε) ^ 4 := by gcongr
    _ = (1 + ε) ^ 5 / k.toNat := by ring
    _ ≤ (1 - ε) / ((k.toNat : ℚ) - 1) := by
        rw [div_le_div_iff₀ hkpos (by linarith)]; linarith
    _ = 1 / ((k.toNat : ℚ) - 1) * (1 - ε) := by ring
    _ ≤ f'.toRat := hge

/-- A loan of a reachable ledger runs for at most the vault's investment period. It starts after SubscriptionDate
and its last payment is due before RedemptionDate. -/
lemma LendingLedger.Reachable.loanAt_term_le {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    loan.schedule.paymentTotal.toNat * loan.schedule.paymentInterval.toNat ≤
      XRPL.Model.SingleAssetVault.maxInvestmentPeriod := by
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hsch : loan.schedule = e.loan.schedule := (congrArg RawLoan.schedule (RawLoan.to_lawful_ok hw).1 :)
  obtain ⟨s, hs⟩ := hr.startsInv
  have hm := LendingLedger.loans_mature_proof l hr s hs.schedule i e he
  have hst := hs.starts i e he
  have hgap : s.hasValidGap = true := l.vault.valid.schedule_gap s (by simp [hs.schedule])
  unfold XRPL.Model.SingleAssetVault.VaultSchedule.hasValidGap at hgap
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgap
  rw [hsch, Nat.mul_comm]
  omega

/-- A loan of a reachable ledger with payments left has principal left, when its interest rate is at most 80%, its
interval at least two hours, or its term at most 25 years. -/
lemma Loan.principal_left_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan)
    (hterms : loan.rates.interestRate.toNat ≤ 80000 ∨ 7200 ≤ loan.schedule.paymentInterval.toNat ∨
      loan.schedule.paymentTotal.toNat * loan.schedule.paymentInterval.toNat ≤ 25 * 31556952)
    (hn : loan.paymentRemaining ≠ 0) : loan.principalOutstanding ≠ Number.zero := by
  obtain ⟨t, -, hre⟩ := hr.loanAt_reachable hat
  have hNT := hr.loanAt_term_le hat
  have hT : 60 ≤ loan.schedule.paymentInterval.toNat := by
    have := (UInt32.le_iff_toNat_le).mp loan.valid.paymentInterval_min
    have h60 : minPaymentInterval.toNat = 60 := rfl
    omega
  have hir : loan.rates.interestRate.toNat ≤ 100000 := by
    have := (UInt32.le_iff_toNat_le).mp loan.valid.interestRate_cap
    have h100 : maxLoanRate.toNat = 100000 := rfl
    omega
  refine Loan.Reachable.principal_left_of_factorGap hre (fun rate hrate k hk2 hk => ?_) hn
  have hrate' : loanPeriodicRate loan.rates.interestRate loan.schedule.paymentInterval = .ok rate := hrate
  by_cases h0 : rate.toRat = 0
  · exact FactorGap.of_zero_rate rate (loanPeriodicRate_isNormalized _ _ _ hrate') h0 k hk2
  · rcases hterms with h1 | h1 | h1
    · exact FactorGap.of_rate_le _ _ _ rate hrate' h0 hT h1 hNT k hk2 hk
    · exact FactorGap.of_interval_ge _ _ _ rate hrate' h0 h1 hir hNT k hk2 hk
    · exact FactorGap.of_term_le _ _ _ rate hrate' h0 hT hir h1 k hk2 hk

end XRPL.Model.Lending
