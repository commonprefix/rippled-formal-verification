import XRPL.Properties.Lending.Loan.Common.RoundToNearest
import XRPL.Properties.Lending.Loan.Common.SetInterest
import XRPL.Properties.Lending.Loan.Common.SetScale
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar
import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.AlgorithmicFacts

/-! # The management fee of a new loan, from above

When the 19-digit product of the interest and ManagementFeeRate is exact, the fee over `10^5` rounded down is at
most its share. -/

namespace XRPL.Model.Protocol

/-- A positive normalized `Number` of at least `10^t` has an exponent above `t - 19`. -/
private lemma Number.exponent_gt_of_le (y : Number) (hy : y.isNormalized) (hneg : y.negative_ = false) (t : ℤ)
    (h : (10 : ℚ) ^ t ≤ y.toRat) : t - 19 < y.exponent_ := by
  have hpos : 0 < y.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) h
  have hm : y.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero y h0] at hpos; exact lt_irrefl _ hpos
  have hmax : (y.mantissa_.toNat : ℚ) < 10 ^ 19 := by
    rcases hy with hz | ⟨h1, h2, -⟩
    · exact absurd (by rw [hz]; rfl) hm
    · exact_mod_cast (mantissaBounds_nat_of ⟨h1, h2⟩).2
  rw [Number.toRat_of_nonneg y hneg] at h
  have h1 : (10 : ℚ) ^ t < 10 ^ (19 + y.exponent_) := by
    calc (10 : ℚ) ^ t ≤ (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_ := h
      _ < 10 ^ 19 * 10 ^ y.exponent_ := mul_lt_mul_of_pos_right hmax (zpow_pos (by norm_num) _)
      _ = 10 ^ (19 + y.exponent_) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
  omega

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private STAmount.isNormalized_of_isRounded_false Loan.create_principal_pos
  from XRPL.Properties.Lending.Loan.Common.SetInterest

/-- Dividing a nonnegative `Number` by `10^5` to nearest gives at most the exact quotient, given room in the
exponent. -/
lemma operator_div_unity_le (y q : Number) (hy : y.isNormalized) (hy0 : 0 ≤ y.toRat)
    (hexp : y.mantissa_ ≠ 0 → minExponent + 5 ≤ y.exponent_)
    (hq : y.operator_div kTenthBipsPerUnity.toNumber .to_nearest = .ok q) :
    q.toRat ≤ y.toRat / 100000 := by
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toInt64
  have hUv : (Number.ofInt64 kTenthBipsPerUnity.toInt64).toRat = 100000 := by
    rw [Number.ofInt64_count]; rfl
  have hR := operator_div_rounded_to_nearest _ _ q hy hU hq
  rw [hUv] at hR
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  by_cases hm : y.mantissa_ = 0
  · have hy00 : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y hm
    have h := hR.le_of_ge hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero, hy00]; norm_num)
    rw [Number.toRat_zero] at h
    rw [hy00]
    linarith
  have hneg := Number.negative_false_of_nonneg y hy hy0
  set w : Number := { y with exponent_ := y.exponent_ - 5 } with hw
  have hwN : w.isNormalized := by
    rcases hy with hz | ⟨h1, h2, h3, h4, h5⟩
    · exact absurd (by rw [hz]; rfl) hm
    · have := hexp hm
      exact Or.inr ⟨h1, h2, h3, by simp only [hw]; omega, by simp only [hw]; omega⟩
  have hwv : w.toRat = y.toRat / 100000 := by
    rw [Number.toRat_of_nonneg w hneg, Number.toRat_of_nonneg y hneg]
    show (y.mantissa_.toNat : ℚ) * 10 ^ (y.exponent_ - 5) = _
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
    norm_num
    ring
  have h := hR.le_of_ge hmode w hwN (by rw [hwv])
  rwa [hwv] at h

/-- Proof body of `create_managementFee_upper_bound`. -/
lemma Loan.create_managementFee_upper_bound_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault) (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hfit : (r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.principalOutstanding) *
      (r.loan'.broker.managementFeeRate.toNat : ℚ) < 2 ^ 63 * 10 ^ r.loan'.toExact.loanScale) :
    r.loan'.toExact.managementFeeOutstanding - (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.principalOutstanding) ≤ 0 := by
  have hp := STAmount.isNormalized_of_isRounded_false _ _ hst
  have hpos := Loan.create_principal_pos broker v principal rates fees schedule allowsOverpayment pending r hp hok
  have hPT := Loan.create_principal_le_value broker v principal rates fees schedule allowsOverpayment pending r hp
    hst hok
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨_, _, _, ti, -, -, -, -, -, -, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hFR : r.loan'.broker.managementFeeRate = broker.managementFeeRate := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.managementFeeRate = _; rw [hl]
    show broker'.toRawLoanBroker.managementFeeRate = _; rw [hb]
  show r.loan'.managementFeeOutstanding.toRat - (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat) ≤ 0
  rw [hFR, hTV, hPO, hMF]
  have hfit' : (r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat) *
      (r.loan'.broker.managementFeeRate.toNat : ℚ) < 2 ^ 63 * 10 ^ r.loan'.loanScale := hfit
  rw [hFR, hTV, hPO, hLS] at hfit'

  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props _ _ hchecks
    hrange.2
  set ls := props.loanScale with hlsdef
  have hls10 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _
  have hsl : minExponent + 18 ≤ ls ∧ ls ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal ls hp hpos.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  obtain ⟨aT, haT, haTv⟩ := hexg.totalValueOutstanding_atExponent
  simp only [RawLoan.toExact] at haT haTv
  rw [hTV, hLS] at haTv
  rw [hNT] at haT
  have hbound := NumericType.mantissaBound_le broker.numericType
  have hjaT : j ≤ aT := by
    have : (j : ℚ) * 10 ^ ls ≤ (aT : ℚ) * 10 ^ ls := by
      rw [← hj, ← haTv]; simp only [RawLoan.toExact] at hPT; rw [hTV] at hPT; exact hPT
    exact_mod_cast le_of_mul_le_mul_right this hls10

  -- the stored principal is PrincipalRequested, so the interest is `K` units
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest ls hp
      hpos.le (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj
      (fun hf => by rw [hf] at haT; exact lt_of_le_of_lt hjaT haT) hpo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  set K := aT - j with hK
  have hKq : (aT : ℚ) * 10 ^ ls - (j : ℚ) * 10 ^ ls = (K : ℚ) * 10 ^ ls := by
    rw [hK]; push_cast [Nat.cast_sub hjaT]; ring
  have htiv : ti.toRat = (K : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j ls htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hsl hti, hK]
    push_cast [Nat.cast_sub hjaT]; ring
  have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti
  set R := broker.managementFeeRate.toNat with hRdef

  -- the interest times the rate is below `2^63` units
  have hKR63 : K * R < 2 ^ 63 := by
    rw [haTv, hpov, hj, hKq] at hfit'
    have h : ((K * R : ℕ) : ℚ) * 10 ^ ls < 2 ^ 63 * 10 ^ ls := by
      have e : ((K * R : ℕ) : ℚ) * 10 ^ ls = (K : ℚ) * 10 ^ ls * R := by push_cast; ring
      rw [e]; exact hfit'
    exact_mod_cast lt_of_mul_lt_mul_right h hls10.le

  -- the fee is the product, over `10^5`, rounded down at LoanScale
  have heq : computeManagementFee broker.numericType ti broker.managementFeeRate ls =
      (ti.operator_mul broker.managementFeeRate.toTenthBips32.toNumber .to_nearest >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some ls)) := rfl
  rw [heq] at hmfo
  obtain ⟨raw, hraw, hmfo⟩ := bind_ok_peel _ _ _ hmfo
  obtain ⟨y, hy, hraw⟩ := bind_ok_peel _ _ _ hraw
  have hRB := Number.ofInt64_isNormalized broker.managementFeeRate.toTenthBips32.toInt64
  have hRBv : (Number.ofInt64 broker.managementFeeRate.toTenthBips32.toInt64).toRat = (R : ℚ) := by
    rw [Number.ofInt64_count]
    show ((broker.managementFeeRate.toUInt32.toNat : ℕ) : ℚ) = _
    rw [UInt16.toNat_toUInt32]
  have hyN := Number.operator_mul_isNormalized _ _ y _ htiN hRB hy
  have hR1 := operator_mul_rounded_to_nearest _ _ y htiN hRB hy
  rw [htiv, hRBv] at hR1
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl

  -- below `2^63` units the product is held exactly, so rounding it to nearest never raises it
  have hyA : y.toRat ≤ (K : ℚ) * 10 ^ ls * R := by
    have hP : ((K * R : ℕ) : ℤ) < 2 ^ 63 := by exact_mod_cast hKR63
    have hP0 : (0 : ℤ) ≤ ((K * R : ℕ) : ℤ) := Int.natCast_nonneg _
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((K * R : ℕ) : ℤ) ls ⟨by linarith, hP⟩ hsl
    have hwv' : w.toRat = (K : ℚ) * 10 ^ ls * R := by rw [hwv]; push_cast; ring
    have h := hR1.le_of_ge hmode w hw hwv'.ge
    rw [hwv'] at h
    exact h

  -- a nonzero product is at least one LoanScale unit, so it has the exponent room to divide by `10^5`
  have hy0 : 0 ≤ y.toRat := by
    have h := hR1.ge_of_le hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; positivity)
    rwa [Number.toRat_zero] at h
  have hexp : y.mantissa_ ≠ 0 → minExponent + 5 ≤ y.exponent_ := by
    intro hm
    have hneg := Number.negative_false_of_nonneg y hyN hy0
    have hypos : 0 < y.toRat := lt_of_le_of_ne hy0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero y hm))
    have hKR : 1 ≤ (K : ℚ) * R := by
      by_contra hc
      push Not at hc
      have hKR0 : K * R = 0 := by
        have : K * R < 1 := by exact_mod_cast hc
        omega
      have h := hR1.le_of_ge hmode Number.zero Number.zero_isNormalized (by
        rw [Number.toRat_zero]
        have : (K : ℚ) * R = 0 := by exact_mod_cast hKR0
        nlinarith)
      rw [Number.toRat_zero] at h
      linarith
    obtain ⟨w1, hw1, hw1v⟩ := Number.exists_normalized_int_mul_pow 1 ls (by norm_num) hsl
    have hy1 := hR1.ge_of_le hmode w1 hw1 (by rw [hw1v]; push_cast; nlinarith)
    rw [hw1v] at hy1
    push_cast at hy1
    have := Number.exponent_gt_of_le y hyN hneg ls (by linarith)
    unfold minExponent
    omega
  have hrawB := operator_div_unity_le y raw hyN hy0 hexp hraw

  -- rounding down at LoanScale never raises the quotient
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toInt64
  have hUv : (Number.ofInt64 kTenthBipsPerUnity.toInt64).toRat = 100000 := by
    rw [Number.ofInt64_count]; rfl
  have hrawN := Number.operator_div_isNormalized _ _ raw _ hyN hU hraw
  have hraw0 : 0 ≤ raw.toRat := by
    have h := (operator_div_rounded_to_nearest _ _ raw hyN hU hraw).ge_of_le hmode Number.zero
      Number.zero_isNormalized (by rw [Number.toRat_zero, hUv]; positivity)
    rwa [Number.toRat_zero] at h
  have hmfC : props.managementFeeOutstanding.toRat ≤ raw.toRat := by
    cases hnt : broker.numericType with
    | fractional =>
      rw [hnt] at hmfo
      exact STAmount.roundToNumericType_frac_downward_le raw _ ls hrawN hraw0 ⟨by omega, hhi⟩ hmfo
    | integral mv mo ms msh =>
      rw [hnt] at hmfo
      exact (STAmount.roundToNumericType_int_grid _ rfl raw _ .downward _ hrawN hraw0 (Or.inr (Or.inr rfl))
        hmfo).2.2.2 rfl

  -- the fee is at most its share
  rw [haTv, hpov, hj, hKq]
  have hdiv : y.toRat / 100000 ≤ (K : ℚ) * 10 ^ ls * R / 100000 :=
    div_le_div_of_nonneg_right hyA (by norm_num)
  have h1 : (K : ℚ) * 10 ^ ls * R / 100000 = (R : ℚ) / 100000 * ((K : ℚ) * 10 ^ ls) := by ring
  linarith

end XRPL.Model.Lending
