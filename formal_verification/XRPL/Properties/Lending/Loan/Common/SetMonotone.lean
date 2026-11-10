import XRPL.Properties.Lending.Loan.Common.Amortization
import XRPL.Properties.Lending.Loan.Common.SetUpdates
import XRPL.Properties.Vault.Common.RoundMonotoneSat
import XRPL.Properties.Vault.Common.RoundMonotoneSatDiv

/-! # How the terms of a new loan move its PeriodicPayment

A larger principal never lowers the payment: the payment is the principal over the count, or the
principal times a factor that does not depend on it, and both roundings keep the order. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- `operator_mul` keeps the order of its first factor at `.to_nearest`, for a fixed positive second
factor. -/
private lemma operator_mul_right_mono (x₁ x₂ y r₁ r₂ : Number) (hx₁ : x₁.isNormalized) (hx₂ : x₂.isNormalized)
    (hy : y.isNormalized) (hok₁ : Number.operator_mul x₁ y .to_nearest = .ok r₁)
    (hok₂ : Number.operator_mul x₂ y .to_nearest = .ok r₂)
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat) (hy0 : 0 < y.toRat) (hx₁pos : 0 < x₁.toRat)
    (hle : x₁.toRat ≤ x₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  have hx₂pos : 0 < x₂.toRat := lt_of_lt_of_le hx₁pos hle
  have hm : ∀ n : Number, 0 < n.toRat → n.mantissa_ ≠ 0 := fun n hn h => by
    rw [Number.toRat_eq_zero_iff.mpr h] at hn; exact lt_irrefl _ hn
  have hn₁ := operator_mul_roundsCuspAware x₁ y r₁ hx₁ hy (hm _ hx₁pos) (hm _ hy0) hok₁ (hm _ hr₁pos)
    (by positivity)
  have hn₂ := operator_mul_roundsCuspAware x₂ y r₂ hx₂ hy (hm _ hx₂pos) (hm _ hy0) hok₂ (hm _ hr₂pos)
    (by positivity)
  refine roundsCuspAware_mono _ _ r₁ r₂ hn₁ hn₂ hr₁pos hr₂pos (by positivity)
    (mul_le_mul_of_nonneg_right hle (le_of_lt hy0)) ?_ ?_
  · intro hlt
    have hx_lt : x₁.toRat < x₂.toRat := lt_of_mul_lt_mul_right hlt (le_of_lt hy0)
    have hgap := normalized_gap_bound x₁ x₂ hx₁ hx₂ hx₁pos hx_lt
    calc x₁.toRat * y.toRat
        ≤ ((maxRepNat : ℚ) * (x₂.toRat - x₁.toRat)) * y.toRat :=
          mul_le_mul_of_nonneg_right hgap (le_of_lt hy0)
      _ = (maxRepNat : ℚ) * (x₂.toRat * y.toRat - x₁.toRat * y.toRat) := by ring
  · intro heq
    have hxx : x₁ = x₂ := hx₁.toRat_inj hx₂ (mul_right_cancel₀ (ne_of_gt hy0) heq)
    subst hxx
    rw [hok₁] at hok₂
    cases hok₂
    rfl

/-- The stored payment of the loan is the periodic payment of its principal at its periodic rate. -/
private lemma computeLoanProperties_periodicPayment (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (props : LoanProperties)
    (h : computeLoanProperties principal ir interval n mgmt nt minScale = .ok props) :
    ∃ rate, loanPeriodicRate ir interval = .ok rate ∧
      loanPeriodicPayment principal rate n = .ok props.periodicPayment := by
  unfold computeLoanProperties at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  refine ⟨rate, hrate, ?_⟩
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [← h]; exact hpp

/-- A successful create stores the periodic payment of its principal, and that payment is positive. -/
private lemma Loan.create_periodicPayment (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ rate, loanPeriodicRate rates.interestRate schedule.paymentInterval = .ok rate ∧
      loanPeriodicPayment principal rate schedule.paymentTotal = .ok r.loan'.periodicPayment ∧
      0 < r.loan'.periodicPayment.toRat := by
  obtain ⟨props, _, _, _, _, hchecks, -, -, -, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  have hpp : r.loan'.periodicPayment = props.periodicPayment :=
    (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok hloan).1 :)
  obtain ⟨rate, hrate, hpay⟩ := computeLoanProperties_periodicPayment _ _ _ _ _ _ _ _ hchecks.properties_ok
  exact ⟨rate, hrate, hpp ▸ hpay, r.loan'.exact.periodicPayment_pos⟩

/-- Proof body of `create_periodicPayment_principal_monotone`. -/
lemma Loan.create_periodicPayment_principal_monotone_proof (broker : LoanBroker) (v : Vault)
    (principal₁ principal₂ : Number) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule)
    (allowsOverpayment pending : Bool) (r₁ r₂ : LoanWithDisbursement Vault)
    (hp₁ : principal₁.isNormalized) (hp₂ : principal₂.isNormalized) (hpos : 0 < principal₁.toRat)
    (hok₁ : (Loan.create broker v principal₁ rates fees schedule allowsOverpayment pending).run = .ok (.ok r₁))
    (hok₂ : (Loan.create broker v principal₂ rates fees schedule allowsOverpayment pending).run = .ok (.ok r₂))
    (hle : principal₁.toRat ≤ principal₂.toRat) :
    r₁.loan'.toExact.periodicPayment ≤ r₂.loan'.toExact.periodicPayment := by
  obtain ⟨rate, hrate, hpay₁, hpos₁⟩ :=
    Loan.create_periodicPayment broker v principal₁ rates fees schedule allowsOverpayment pending r₁ hok₁
  obtain ⟨rate', hrate', hpay₂, hpos₂⟩ :=
    Loan.create_periodicPayment broker v principal₂ rates fees schedule allowsOverpayment pending r₂ hok₂
  rw [hrate, Except.ok.injEq] at hrate'
  subst hrate'
  show r₁.loan'.periodicPayment.toRat ≤ r₂.loan'.periodicPayment.toRat
  have hne : ∀ n : Number, 0 < n.toRat → n ≠ Number.zero := fun n hn h => by
    rw [h, Number.toRat_zero] at hn; exact lt_irrefl _ hn
  have hm : ∀ n : Number, 0 < n.toRat → n.mantissa_ ≠ 0 := fun n hn h => by
    rw [Number.toRat_eq_zero_iff.mpr h] at hn; exact lt_irrefl _ hn
  have hpos₂' : 0 < principal₂.toRat := lt_of_lt_of_le hpos hle
  have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toInt64
  rcases loanPeriodicPayment_cases _ _ _ _ hpay₁ (hne _ hpos₁) with ⟨hz, hd₁⟩ | ⟨hz, f, hf, hm₁⟩ <;>
    rcases loanPeriodicPayment_cases _ _ _ _ hpay₂ (hne _ hpos₂) with ⟨hz', hd₂⟩ | ⟨hz', f', hf', hm₂⟩
  · -- a zero rate: the principal over the count
    have ht := Number.pos_of_roundsToRepresentable _ _
      (operator_div_rounded_to_nearest _ _ _ hp₁ hN hd₁) hpos₁
    have hNpos : 0 < (Number.ofInt64 schedule.paymentTotal.toInt64).toRat := by
      by_contra hc
      push Not at hc
      exact absurd ht (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hpos.le hc))
    exact operator_div_num_mono_of_cuspAware _ _ _ _ _ hp₁ hp₂ hd₁ hd₂
      (operator_div_roundsCuspAware _ _ _ hp₁ hN (hm _ hpos) (hm _ hNpos) hd₁ (hm _ hpos₁) (by positivity))
      (operator_div_roundsCuspAware _ _ _ hp₂ hN (hm _ hpos₂') (hm _ hNpos) hd₂ (hm _ hpos₂)
        (by positivity))
      hpos₁ hpos₂ hNpos hpos hle
  · rw [hz] at hz'; exact absurd hz' (by decide)
  · rw [hz] at hz'; exact absurd hz' (by decide)
  · -- a nonzero rate: the principal times the payment factor
    rw [hf, Except.ok.injEq] at hf'
    subst hf'
    have hrateN := loanPeriodicRate_isNormalized _ _ rate hrate
    have hfN := computePaymentFactor_isNormalized rate _ _ f hrateN hN hf
    have ht := Number.pos_of_roundsToRepresentable _ _
      (operator_mul_rounded_to_nearest _ _ _ hp₁ hfN hm₁) hpos₁
    have hfpos : 0 < f.toRat := by
      by_contra hc
      push Not at hc
      exact absurd ht (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hpos.le hc))
    exact operator_mul_right_mono _ _ _ _ _ hp₁ hp₂ hfN hm₁ hm₂ hpos₁ hpos₂ hfpos hpos hle

end XRPL.Model.Lending
