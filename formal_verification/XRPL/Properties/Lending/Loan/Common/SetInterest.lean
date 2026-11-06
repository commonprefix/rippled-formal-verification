import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Lending.Loan.Common.ReachableDefs

/-! # The interest of a new loan

A new loan stores TotalValueOutstanding at least PrincipalOutstanding plus ManagementFeeOutstanding, because
the fee is a share of at most 10% of the interest, rounded down. -/

namespace XRPL.Model.Protocol

/-- A value that `isRounded` keeps equals the `Number` its amount converts back to, so it is normalized. -/
private lemma STAmount.isNormalized_of_isRounded_false (nt : NumericType) (x : Number)
    (h : STAmount.isRounded nt x = false) : x.isNormalized := by
  unfold STAmount.isRounded at h
  cases hconv : STAmount.equalAfterNumberConvert nt x with
  | error e => rw [hconv] at h; exact absurd h (by simp)
  | ok b =>
    rw [hconv] at h
    have hb : b = true := by cases b <;> simp at h ⊢
    subst hb
    unfold STAmount.equalAfterNumberConvert at hconv
    obtain ⟨st, -, hconv⟩ := bind_ok_peel _ _ _ hconv
    obtain ⟨n, hnum, hconv⟩ := bind_ok_peel _ _ _ hconv
    have heq : n.operator_eq x = true :=
      Except.ok.inj (show (Except.ok (n.operator_eq x) : Except Error Bool) = .ok true from hconv)
    have hnN := STAmount.toNumber_isNormalized st _ n hnum
    have hnx : n = x := by
      unfold Number.operator_eq at heq
      simp only [Bool.and_eq_true, beq_iff_eq] at heq
      obtain ⟨⟨h1, h2⟩, h3⟩ := heq
      cases n
      cases x
      simp_all
    exact hnx ▸ hnN

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)
open private checkPrecisionFields canFundLoan from XRPL.Model.Lending.Loan.LoanSet

/-- The periodic payment of a nonpositive principal at a nonnegative rate is nonpositive. -/
private lemma loanPeriodicPayment_nonpos (principal rate : Number) (pr : UInt32) (r : Number)
    (hp : principal.isNormalized) (hp0 : principal.toRat ≤ 0) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (h : loanPeriodicPayment principal rate pr = .ok r) : r.toRat ≤ 0 := by
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hN0 : 0 ≤ (Number.ofInt64 pr.toInt64).toRat := by rw [Number.ofInt64_count]; positivity
  unfold loanPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rw [Number.toRat_zero]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact Number.roundsToRepresentable_nonpos _ _ (operator_div_rounded_to_nearest _ _ _ hp hN h)
        (div_nonpos_of_nonpos_of_nonneg hp0 hN0)
    · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
      have hfN := computePaymentFactor_isNormalized rate _ pr f hrate hN hf
      have hf0 := computePaymentFactor_nonneg rate _ pr f hrate hr0 hN hN0 hf
      exact Number.roundsToRepresentable_nonpos _ _ (operator_mul_rounded_to_nearest _ _ _ hp hfN h)
        (mul_nonpos_of_nonpos_of_nonneg hp0 hf0)

/-- A successful create lends a positive amount. A nonpositive principal would give a nonpositive
PeriodicPayment, which the sanity check rejects. -/
private lemma Loan.create_principal_pos (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    0 < principal.toRat := by
  obtain ⟨props, _, _, _, _, _, _, _, _, _, hchecks, -⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨rate, _, _, _, hrt, hpp, -⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  obtain ⟨_, -, -, -, -, -, -, hpp0⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrt
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hp hrN hpp
  by_contra hc
  push Not at hc
  have h1 := loanPeriodicPayment_nonpos _ _ _ _ hp hc hrN (loanPeriodicRate_nonneg _ _ rate hrt) hpp
  have h2 := (Number.signum_pos_iff_toRat hppN).mp hpp0
  linarith

/-- A new loan has nonnegative interestDue. PrincipalOutstanding is PrincipalRequested, at most the total
value, and the fee is at most the interest. -/
private lemma Loan.create_interestDue_nonneg (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    0 ≤ r.loan'.toExact.interestDue := by
  have hp := STAmount.isNormalized_of_isRounded_false _ _ hst
  have hpos := Loan.create_principal_pos broker v principal rates fees schedule allowsOverpayment pending r hp hok
  have hPT := Loan.create_principal_le_value broker v principal rates fees schedule allowsOverpayment pending r hp hst
    hok
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
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
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props _
    _ hchecks hrange.2
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
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest ls hp
      hpos.le (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj
      (fun hf => by rw [hf] at haT; exact lt_of_le_of_lt hjaT haT) hpo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j ls htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hsl hti]
    push_cast [Nat.cast_sub hjaT]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := by
    intro hf
    rw [hf] at haT
    exact lt_of_le_of_lt (Nat.sub_le _ _) haT
  obtain ⟨-, hmf_hi, -, -⟩ := computeManagementFee_bounds broker.numericType ti _ (aT - j)
    broker.managementFeeRate ls (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) htiv
    (by omega) hR10 ⟨hlo, hhi⟩ hint hfr hmfo
  have hC : ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 ≤ aT - j := by
    have : (aT - j) * broker.managementFeeRate.toNat ≤ (aT - j) * 10000 := Nat.mul_le_mul_left _ hR10
    omega
  have hmf : props.managementFeeOutstanding.toRat ≤ ((aT - j : ℕ) : ℚ) * 10 ^ ls :=
    hmf_hi.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hC) hls10.le)
  show 0 ≤ r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat -
    r.loan'.managementFeeOutstanding.toRat
  rw [hTV, hPO, hMF, hpov, haTv, hj]
  have : ((aT - j : ℕ) : ℚ) * 10 ^ ls = (aT : ℚ) * 10 ^ ls - (j : ℚ) * 10 ^ ls := by
    push_cast [Nat.cast_sub hjaT]; ring
  linarith

/-- `canCreate` passes only for a PrincipalRequested an STAmount holds exactly. -/
private lemma Loan.canCreate_principal_exact (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (hok : Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS) :
    STAmount.isRounded broker.numericType p = false := by
  have hst : schedule.checkTimeAvailability = .ok .tecKILLED ∨ schedule.checkTimeAvailability = .ok .tesSUCCESS := by
    rw [LoanSchedule.checkTimeAvailability_eq]; split <;> simp
  unfold Loan.canCreate at hok
  rcases hst with h | h <;> rw [h] at hok
  · simp only [bind, Except.bind, pure, Except.pure, show TER.tecKILLED.isTesSuccess = false from rfl,
      Bool.not_false, ↓reduceIte, Except.ok.injEq] at hok
    exact absurd hok (by decide)
  · simp only [bind, Except.bind, pure, Except.pure, show TER.tesSUCCESS.isTesSuccess = true from rfl,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
    by_cases hexp : (twoStep && decide (t ≥ schedule.startDate)) = true
    · simp only [hexp, ↓reduceIte, Except.ok.injEq] at hok
      exact absurd hok (by decide)
    · simp only [hexp, Bool.false_eq_true, ↓reduceIte] at hok
      cases hf : canFundLoan v schedule t broker.numericType with
      | error err => rw [hf] at hok; exact absurd hok (by simp)
      | ok vt =>
        rw [hf] at hok
        simp only [checkPrecisionFields_pure] at hok
        by_cases hvt : vt.isTesSuccess = true
        · simp only [hvt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
          by_cases hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = true
          · simpa using List.all_eq_true.mp hall p List.mem_cons_self
          · simp only [hall, Bool.false_eq_true, ↓reduceIte, show TER.tecPRECISION_LOSS.isTesSuccess = false from rfl,
              Bool.not_false, Except.ok.injEq] at hok
            exact absurd hok (by decide)
        · simp only [hvt, Bool.not_false, ↓reduceIte, Except.ok.injEq] at hok
          exact absurd (hok ▸ rfl : vt.isTesSuccess = true) hvt

/-- Every loan a LoanSet creates has nonnegative interestDue. -/
lemma Loan.Created.interestDue_nonneg {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    0 ≤ start.toExact.interestDue := by
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, hcan, hok, hr⟩ := h
  rw [← hr]
  exact Loan.create_interestDue_nonneg broker v principal rates fees _ allowsOverpayment twoStep r
    (Loan.canCreate_principal_exact broker v principal fees _ t₀ twoStep hcan) hok

end XRPL.Model.Lending
