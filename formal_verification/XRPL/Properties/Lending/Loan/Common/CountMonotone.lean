import XRPL.Properties.Lending.Loan.Common.SetMonotone
import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Lending.Loan.Common.RoundingError
import XRPL.Properties.Vault.Common.RoundMonotoneCusp

/-! # One more payment never raises PeriodicPayment

The guard on the first payment's principal of a LoanSet with `n + 1` payments compares the principal of `n + 1`
payments with that of `n`, so it passes only when the payment factor of `n + 1` is below the one of `n`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

local notation "ε" => Number.nearestError

open private Loan.create_periodicPayment from XRPL.Properties.Lending.Loan.Common.SetMonotone

/-- What the loan properties computed for the first payment. The principal of the full schedule and of one
payment fewer, both from the periodic payment, and their difference. -/
private lemma computeLoanProperties_first (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (props : LoanProperties)
    (h : computeLoanProperties principal ir interval n mgmt nt minScale = .ok props) :
    ∃ rate sp np, loanPeriodicRate ir interval = .ok rate ∧
      loanPeriodicPayment principal rate n = .ok props.periodicPayment ∧
      loanPrincipalFromPeriodicPayment props.periodicPayment rate n = .ok sp ∧
      loanPrincipalFromPeriodicPayment props.periodicPayment rate (n - 1) = .ok np ∧
      sp.operator_sub np .to_nearest = .ok props.firstPaymentPrincipal := by
  unfold computeLoanProperties at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sp, hsp, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨np, hnp, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨fp, hfp, h⟩ := bind_ok_peel _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rate, sp, np, hrate, hpp, hsp, hnp, hfp⟩

/-- A nonzero result of a division near a positive quotient is positive. -/
private lemma Number.div_pos_of_ne (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_div y .to_nearest = .ok r) (hr : r.mantissa_ ≠ 0) (ht : 0 < x.toRat / y.toRat) :
    0 < r.toRat := by
  have he := Number.nearestError_le
  have hne : r.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero r hr
  have := (Number.div_near x y r hx hy hok).ge hne ht.le
  have h1 : (0 : ℚ) < 1 - ε := by linarith
  nlinarith

/-- `operator_div` never rises with a larger divisor at `.to_nearest`, for a fixed positive numerator and
results that are not zero. -/
private lemma operator_div_den_antitone (x y₁ y₂ r₁ r₂ : Number) (hx : x.isNormalized) (hy₁ : y₁.isNormalized)
    (hy₂ : y₂.isNormalized) (hok₁ : x.operator_div y₁ .to_nearest = .ok r₁)
    (hok₂ : x.operator_div y₂ .to_nearest = .ok r₂) (hr₁ : r₁.mantissa_ ≠ 0) (hr₂ : r₂.mantissa_ ≠ 0)
    (hx0 : 0 < x.toRat) (hy0 : 0 < y₁.toRat) (hle : y₁.toRat ≤ y₂.toRat) :
    r₂.toRat ≤ r₁.toRat := by
  have hy0' : 0 < y₂.toRat := lt_of_lt_of_le hy0 hle
  have hm : ∀ n : Number, 0 < n.toRat → n.mantissa_ ≠ 0 := fun n hn h => by
    rw [Number.toRat_eq_zero_iff.mpr h] at hn; exact lt_irrefl _ hn
  have ht₁ : 0 < x.toRat / y₁.toRat := div_pos hx0 hy0
  have ht₂ : 0 < x.toRat / y₂.toRat := div_pos hx0 hy0'
  have hc₁ := operator_div_roundsCuspAware x y₁ r₁ hx hy₁ (hm _ hx0) (hm _ hy0) hok₁ hr₁ ht₁
  have hc₂ := operator_div_roundsCuspAware x y₂ r₂ hx hy₂ (hm _ hx0) (hm _ hy0') hok₂ hr₂ ht₂
  refine roundsCuspAware_mono _ _ r₂ r₁ hc₂ hc₁ (Number.div_pos_of_ne x y₂ r₂ hx hy₂ hok₂ hr₂ ht₂)
    (Number.div_pos_of_ne x y₁ r₁ hx hy₁ hok₁ hr₁ ht₁) ht₂ (div_le_div_of_nonneg_left hx0.le hy0 hle) ?_ ?_
  · intro hlt
    have hy_lt : y₁.toRat < y₂.toRat := by
      by_contra hc
      push Not at hc
      have : x.toRat / y₁.toRat ≤ x.toRat / y₂.toRat := div_le_div_of_nonneg_left hx0.le hy0' hc
      linarith
    have hgap := normalized_gap_bound y₁ y₂ hy₁ hy₂ hy0 hy_lt
    have hM : (0 : ℚ) ≤ maxRepNat := Nat.cast_nonneg _
    calc x.toRat / y₂.toRat = x.toRat * y₁.toRat / (y₁.toRat * y₂.toRat) := by field_simp
      _ ≤ x.toRat * ((maxRepNat : ℚ) * (y₂.toRat - y₁.toRat)) / (y₁.toRat * y₂.toRat) := by gcongr
      _ = (maxRepNat : ℚ) * (x.toRat / y₁.toRat - x.toRat / y₂.toRat) := by field_simp
  · intro heq
    have hyy : y₁.toRat = y₂.toRat := by
      have h1 : x.toRat / y₂.toRat = x.toRat / y₁.toRat := heq
      field_simp at h1
      linarith
    have : y₁ = y₂ := hy₁.toRat_inj hy₂ hyy
    subst this
    rw [hok₁] at hok₂
    cases hok₂
    rfl

/-- An amount above zero that the asset stores exactly is at least `10^-81`. -/
private lemma STAmount.representable_ge (nt : NumericType) (x : Number) (hx : x.isNormalized) (h0 : 0 < x.toRat)
    (hst : STAmount.isRounded nt x = false) : (1 : ℚ) / 10 ^ 81 ≤ x.toRat := by
  rcases (STAmount.isRounded_eq_false_iff nt x hx h0.le).mp hst with hz | hrep
  · linarith
  · cases nt with
    | integral mv mo ms msh =>
      obtain ⟨-, k, -, -, hk⟩ := hrep
      have hk1 : (1 : ℚ) ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hk; simp at hk; linarith
        · exact_mod_cast h
      rw [hk]
      linarith [show (1 : ℚ) / 10 ^ 81 ≤ 1 by norm_num]
    | fractional =>
      obtain ⟨m, e, hm, -, he, -, hv⟩ := hrep
      rw [hv]
      have hm' : (10 : ℚ) ^ 15 ≤ m := by exact_mod_cast hm
      have he' : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) he
      calc (1 : ℚ) / 10 ^ 81 = 10 ^ 15 * (10 : ℚ) ^ (-96 : ℤ) := by norm_num
        _ ≤ (m : ℚ) * 10 ^ e := mul_le_mul hm' he' (by positivity) (by positivity)

/-- With a periodic rate and some payments left, the principal of a periodic payment is the payment over the
payment factor. -/
private lemma loanPrincipalFromPeriodicPayment_div (pp rate f tpo : Number) (k : UInt32) (hk : k ≠ 0)
    (hz : rate.operator_eq Number.zero = false)
    (hf : computePaymentFactor rate (Number.ofInt64 k.toUInt64.toInt64) k = .ok f)
    (h : loanPrincipalFromPeriodicPayment pp rate k = .ok tpo) : pp.operator_div f .to_nearest = .ok tpo := by
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  rw [if_neg (by simp [hk])] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  rw [if_neg (by rw [hz]; decide)] at h
  obtain ⟨f', hf', h⟩ := bind_ok_peel _ _ _ h
  rw [hf, Except.ok.injEq] at hf'
  subst hf'
  exact h

/-- Proof body of `Lending.create_periodicPayment_monotone`. -/
lemma Loan.create_periodicPayment_count_antitone_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule schedule₂ : LoanSchedule) (allowsOverpayment pending : Bool)
    (r₁ r₂ : LoanWithPool Vault) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hs : schedule₂ = { schedule with paymentTotal := schedule₂.paymentTotal })
    (hlt : schedule.paymentTotal < schedule₂.paymentTotal)
    (hstep : schedule₂.paymentTotal = schedule.paymentTotal + 1)
    (hok₁ : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r₁))
    (hok₂ : (Loan.create broker v principal rates fees schedule₂ allowsOverpayment pending).run = .ok (.ok r₂)) :
    r₂.loan'.toExact.periodicPayment ≤ r₁.loan'.toExact.periodicPayment := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨props, _, _, _, _, hchecks, -, -, -, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule₂ allowsOverpayment pending r₂ hok₂
  have hpp₂ : r₂.loan'.periodicPayment = props.periodicPayment :=
    (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok hloan).1 :)
  obtain ⟨_, -, -, -, hfirst, -, -, -⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  obtain ⟨rate, sp, np, hrate, hpay₂, hsp, hnp, hfp⟩ := computeLoanProperties_first _ _ _ _ _ _ _ _
    hchecks.properties_ok
  obtain ⟨rate₁, hrate₁, hpay₁, hpos₁⟩ :=
    Loan.create_periodicPayment broker v principal rates fees schedule allowsOverpayment pending r₁ hok₁
  have hint : schedule₂.paymentInterval = schedule.paymentInterval := by rw [hs]
  rw [hint, hrate₁, Except.ok.injEq] at hrate
  subst hrate
  have hpos₂ : 0 < props.periodicPayment.toRat := by rw [← hpp₂]; exact r₂.loan'.exact.periodicPayment_pos
  set n := schedule.paymentTotal with hn
  rw [hstep] at hpay₂ hsp hnp hlt
  have hn1 : n + 1 - 1 = n := by simp
  rw [hn1] at hnp
  show r₂.loan'.periodicPayment.toRat ≤ r₁.loan'.periodicPayment.toRat
  rw [hpp₂]
  have hne : ∀ x : Number, 0 < x.toRat → x ≠ Number.zero := fun x hx h => by
    rw [h, Number.toRat_zero] at hx; exact lt_irrefl _ hx
  have hm : ∀ x : Number, 0 < x.toRat → x.mantissa_ ≠ 0 := fun x hx h => by
    rw [Number.toRat_eq_zero_iff.mpr h] at hx; exact lt_irrefl _ hx
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0] at hpay₁; unfold loanPeriodicPayment at hpay₁
    simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hpay₁
    rw [← hpay₁, Number.toRat_zero] at hpos₁; exact lt_irrefl _ hpos₁
  have hNn : (n + 1).toNat = n.toNat + 1 := by
    have h1 := UInt32.lt_iff_toNat_lt.mp hlt
    rw [UInt32.toNat_add, UInt32.toNat_one] at h1 ⊢
    have h2 := n.toNat_lt
    rcases Nat.lt_or_ge (n.toNat + 1) (2 ^ 32) with h3 | h3
    · exact Nat.mod_eq_of_lt h3
    · have : (n.toNat + 1) % 2 ^ 32 = 0 := by
        have : n.toNat + 1 = 2 ^ 32 := by omega
        rw [this]; rfl
      omega
  have hN0 : n + 1 ≠ 0 := by
    intro h0
    have := congrArg UInt32.toNat h0
    rw [hNn] at this
    simp at this
  have hrN := loanPeriodicRate_isNormalized _ _ rate₁ hrate₁
  have hNn' := Number.ofInt64_isNormalized n.toUInt64.toInt64
  have hNN' := Number.ofInt64_isNormalized (n + 1).toUInt64.toInt64
  rcases loanPeriodicPayment_cases _ _ _ _ hpay₁ (hne _ hpos₁) with ⟨hz, hd₁⟩ | ⟨hz, f, hf, hm₁⟩ <;>
    rcases loanPeriodicPayment_cases _ _ _ _ hpay₂ (hne _ hpos₂) with ⟨hz', hd₂⟩ | ⟨hz', f', hf', hm₂⟩
  · -- no interest: the principal over the count
    have hcn := Number.ofInt64_count n
    have hcN := Number.ofInt64_count (n + 1)
    have hnpos : (0 : ℚ) < (Number.ofInt64 n.toUInt64.toInt64).toRat := by
      rw [hcn]; have : n.toNat ≠ 0 := fun h => hn0 (UInt32.toNat_inj.mp (by simpa using h)); positivity
    exact operator_div_den_antitone _ _ _ _ _ hp hNn' hNN' hd₁ hd₂ (hm _ hpos₁) (hm _ hpos₂) hpos hnpos
      (by rw [hcn, hcN, hNn]; push_cast; linarith)
  · rw [hz] at hz'; exact absurd hz' (by decide)
  · rw [hz] at hz'; exact absurd hz' (by decide)
  · -- a periodic rate: the principal times the payment factor, which one more payment lowers
    have hfN := computePaymentFactor_isNormalized rate₁ _ _ f hrN hNn' hf
    have hfN' := computePaymentFactor_isNormalized rate₁ _ _ f' hrN hNN' hf'
    have hfpos : 0 < f.toRat := by
      have ht := Number.pos_of_roundsToRepresentable _ _ (operator_mul_rounded_to_nearest _ _ _ hp hfN hm₁) hpos₁
      by_contra hc; push Not at hc
      exact absurd ht (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hpos.le hc))
    have hfpos' : 0 < f'.toRat := by
      have ht := Number.pos_of_roundsToRepresentable _ _ (operator_mul_rounded_to_nearest _ _ _ hp hfN' hm₂) hpos₂
      by_contra hc; push Not at hc
      exact absurd ht (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hpos.le hc))
    have hspd := loanPrincipalFromPeriodicPayment_div _ _ _ _ _ hN0 hz' hf' hsp
    have hnpd := loanPrincipalFromPeriodicPayment_div _ _ _ _ _ hn0 hz hf hnp
    have hppN := Number.operator_mul_isNormalized _ _ _ _ hp hfN' hm₂
    have hspN := Number.operator_div_isNormalized _ _ _ _ hppN hfN' hspd
    have hnpN := Number.operator_div_isNormalized _ _ _ _ hppN hfN hnpd
    -- the guard: the principal of `n + 1` payments is above the principal of `n`
    have hfpN := operator_sub_isNormalized_to_nearest_sz _ _ _ hspN hnpN hfp
    have hfp0 : 0 < props.firstPaymentPrincipal.toRat := (Number.signum_pos_iff_toRat hfpN).mp hfirst
    have hgt : np.toRat < sp.toRat := by
      by_contra hc; push Not at hc
      have := (Number.sub_near _ _ _ hspN hnpN hfp).nonpos (by linarith)
      linarith
    have hnp0 : 0 ≤ np.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg np _
      (operator_div_rounded_to_nearest _ _ _ hppN hfN hnpd) (div_nonneg hpos₂.le hfpos.le)
    have hflt : f'.toRat < f.toRat := by
      by_contra hc; push Not at hc
      -- the principal of `n` payments is far above the smallest Number, so it is not zero
      have hPge := STAmount.representable_ge _ _ hp hpos hst
      have hpp_ge : principal.toRat * f'.toRat * (1 - ε) ≤ props.periodicPayment.toRat :=
        (Number.mul_near _ _ _ hp hfN' hm₂).ge (ne_of_gt hpos₂) (by positivity)
      have hnpm : np.mantissa_ ≠ 0 := by
        intro h0
        have hsmall := operator_div_underflow_truth_small _ _ _ .to_nearest hppN hfN (hm _ hpos₂) (hm _ hfpos)
          hnpd h0
        have hq : principal.toRat * (1 - ε) ≤ props.periodicPayment.toRat / f.toRat := by
          rw [le_div_iff₀ hfpos]
          calc principal.toRat * (1 - ε) * f.toRat ≤ principal.toRat * f'.toRat * (1 - ε) := by
                have : principal.toRat * f.toRat ≤ principal.toRat * f'.toRat :=
                  mul_le_mul_of_nonneg_left hc hpos.le
                nlinarith
            _ ≤ props.periodicPayment.toRat := hpp_ge
        rw [abs_of_pos (div_pos hpos₂ hfpos)] at hsmall
        have h1 : (1 : ℚ) / 10 ^ 81 * (1 - 1 / 10 ^ 18) ≤ principal.toRat * (1 - ε) := by
          have : (1 : ℚ) - 1 / 10 ^ 18 ≤ 1 - ε := by linarith
          exact mul_le_mul hPge this (by norm_num) hpos.le
        have h2 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) < (1 : ℚ) / 10 ^ 81 * (1 - 1 / 10 ^ 18) := by
          have hmin : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-200 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)
          calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (18 : ℕ) * 10 ^ (-200 : ℤ) :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ < (1 : ℚ) / 10 ^ 81 * (1 - 1 / 10 ^ 18) := by norm_num
        linarith
      have hspm : sp.mantissa_ ≠ 0 := hm _ (lt_of_le_of_lt hnp0 hgt)
      have := operator_div_den_antitone _ _ _ _ _ hppN hfN hfN' hnpd hspd hnpm hspm hpos₂ hfpos hc
      linarith
    exact operator_mul_left_mono_of_cuspAware _ _ _ _ _ hfN' hfN hm₂ hm₁
      (operator_mul_roundsCuspAware _ _ _ hp hfN' (hm _ hpos) (hm _ hfpos') hm₂ (hm _ hpos₂) (by positivity))
      (operator_mul_roundsCuspAware _ _ _ hp hfN (hm _ hpos) (hm _ hfpos) hm₁ (hm _ hpos₁) (by positivity))
      hpos₂ hpos₁ hpos hfpos' hflt.le

end XRPL.Model.Lending
