import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.Common.SetDefs

/-! # Proof bodies for the `Loan.create` exits

One proof per exit, in the order the create runs its checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet

/-- The precision check passes on terms exact at LoanScale. -/
private lemma Loan.CreateTerms.precision {broker v principal rates fees schedule properties}
    (h : Loan.CreateTerms broker v principal rates fees schedule properties) :
    checkPrecisionFields principal fees (fun value => isRounded value properties.loanScale broker.numericType) =
      .ok .tesSUCCESS := by
  rw [checkPrecisionFields_ok principal fees _ (fun _ => true) h.exact]
  simp

variable (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates) (fees : LoanFees)
  (schedule : LoanSchedule) (allowsOverpayment pending : Bool)

/-- Proof body of the AssetsAvailable line of `Loan.create_exits`. -/
lemma Loan.create_insufficient_funds_proof (hfunds : v.assetsAvailable.operator_lt principal = true) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecINSUFFICIENT_FUNDS) := by
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hfunds]

/-- Proof body of the LoanScale precision line of `Loan.create_exits`. -/
lemma Loan.create_precision_loss_proof (properties : LoanProperties)
    (hfunds : v.assetsAvailable.operator_lt principal = false)
    (hprops : computeLoanProperties principal rates.interestRate schedule.paymentInterval schedule.paymentTotal
      broker.managementFeeRate broker.numericType v.baseExponent = .ok properties)
    (hchecks : ∀ x ∈ principal :: fees.amountFields, ∃ b, isRounded x properties.loanScale broker.numericType = .ok b)
    (hround : ∃ x ∈ principal :: fees.amountFields, isRounded x properties.loanScale broker.numericType = .ok false) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) := by
  classical
  let g : Number → Bool := fun x =>
    if h : ∃ b, isRounded x properties.loanScale broker.numericType = .ok b then h.choose else true
  have hg : ∀ x ∈ principal :: fees.amountFields, isRounded x properties.loanScale broker.numericType = .ok (g x) := by
    intro x hx
    have h := hchecks x hx
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hall : (principal :: fees.amountFields).all g = false := by
    obtain ⟨x, hx, hf⟩ := hround
    rw [Bool.eq_false_iff]
    intro h
    have h1 := List.all_eq_true.mp h x hx
    have h2 := hg x hx
    rw [hf, h1] at h2
    exact absurd h2 (by decide)
  have hp := checkPrecisionFields_ok principal fees _ g hg
  rw [hall] at hp
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hfunds, Vault.pool_baseExponent, hprops, hp]
  rfl

/-- A create whose amortization guards return tecPRECISION_LOSS is rejected with it. -/
lemma Loan.create_cannot_amortize_proof (properties : LoanProperties)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hguard : properties.amortizationGuards principal (rates.interestRate != 0) schedule.paymentTotal
      broker.numericType = .ok .tecPRECISION_LOSS) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) := by
  have hg : properties.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType =
      .ok .tecPRECISION_LOSS := by
    unfold LoanProperties.checkGuards
    rw [hguard]
    rfl
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hterms.funds, Vault.pool_baseExponent, hterms.properties_ok, hterms.precision, hg]
  rfl

/-- Guard 1 rejects a loan with an interest rate but no interest. -/
private lemma LoanProperties.guards_no_interest (properties : LoanProperties) (principal totalInterest : Number)
    (paymentsRemaining : UInt32) (nt : NumericType)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hnone : totalInterest.signum ≤ 0) :
    properties.amortizationGuards principal true paymentsRemaining nt = .ok .tecPRECISION_LOSS := by
  unfold LoanProperties.amortizationGuards
  simp [hti, hnone]

/-- Guard 2 rejects a loan whose first payment pays no principal, once guard 1 passed. -/
private lemma LoanProperties.guards_no_principal (properties : LoanProperties) (principal totalInterest : Number)
    (expectInterest : Bool) (paymentsRemaining : UInt32) (nt : NumericType)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ expectInterest = true)
    (hfirst : properties.firstPaymentPrincipal.signum ≤ 0) :
    properties.amortizationGuards principal expectInterest paymentsRemaining nt = .ok .tecPRECISION_LOSS := by
  unfold LoanProperties.amortizationGuards
  cases expectInterest <;> simp at hinterest <;> simp [hti, hinterest, hfirst]

/-- Guard 3 rejects a loan whose rounded payment is zero, once guard 1 passed. -/
private lemma LoanProperties.guards_zero_payment (properties : LoanProperties)
    (principal totalInterest roundedPayment : Number) (expectInterest : Bool) (paymentsRemaining : UInt32)
    (nt : NumericType)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ expectInterest = true)
    (hround : STAmount.roundToNumericType nt properties.periodicPayment .upward (some properties.loanScale) =
      .ok roundedPayment)
    (hzero : roundedPayment.operator_eq Number.zero = true) :
    properties.amortizationGuards principal expectInterest paymentsRemaining nt = .ok .tecPRECISION_LOSS := by
  unfold LoanProperties.amortizationGuards
  cases expectInterest <;> simp at hinterest <;> simp [hti, hinterest, hround, hzero]

/-- Guard 4 rejects a loan whose rounded payments need another count, once guard 1 passed. -/
private lemma LoanProperties.guards_payment_count (properties : LoanProperties)
    (principal totalInterest roundedPayment ratio : Number) (computedPayments : Int64) (expectInterest : Bool)
    (paymentsRemaining : UInt32) (nt : NumericType)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ expectInterest = true)
    (hround : STAmount.roundToNumericType nt properties.periodicPayment .upward (some properties.loanScale) =
      .ok roundedPayment)
    (hnz : roundedPayment.operator_eq Number.zero = false)
    (hratio : properties.totalValueOutstanding.operator_div roundedPayment .upward = .ok ratio)
    (hcount : ratio.to_rep .upward = .ok computedPayments)
    (hne : computedPayments ≠ paymentsRemaining.toInt64) :
    properties.amortizationGuards principal expectInterest paymentsRemaining nt = .ok .tecPRECISION_LOSS := by
  unfold LoanProperties.amortizationGuards
  cases expectInterest <;> simp at hinterest <;> simp [hti, hinterest, hround, hnz, hratio, hcount, hne]

/-- The loan has interest exactly when InterestRate ≠ 0, in the guards' Bool form. -/
private lemma interest_iff_bne {totalInterest : Number} {rate : TenthBips32}
    (h : 0 < totalInterest.signum ↔ rate ≠ 0) : 0 < totalInterest.signum ↔ (rate != 0) = true := by
  rw [h, bne_iff_ne]

/-- Proof body of the no interest line of `Loan.create_exits`. -/
lemma Loan.create_no_interest_proof (properties : LoanProperties) (totalInterest : Number)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties) (hrate : rates.interestRate ≠ 0)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hnone : totalInterest.signum ≤ 0) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) := by
  have hb : (rates.interestRate != 0) = true := bne_iff_ne.mpr hrate
  refine Loan.create_cannot_amortize_proof broker v principal rates fees schedule allowsOverpayment pending
    properties hterms ?_
  rw [hb]
  exact LoanProperties.guards_no_interest properties principal totalInterest _ _ hti hnone

/-- Proof body of the no principal line of `Loan.create_exits`. -/
lemma Loan.create_no_principal_proof (properties : LoanProperties) (totalInterest : Number)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ rates.interestRate ≠ 0)
    (hfirst : properties.firstPaymentPrincipal.signum ≤ 0) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) :=
  Loan.create_cannot_amortize_proof broker v principal rates fees schedule allowsOverpayment pending properties
    hterms (LoanProperties.guards_no_principal properties principal totalInterest _ _ _ hti
      (interest_iff_bne hinterest) hfirst)

/-- Proof body of the zero PeriodicPayment line of `Loan.create_exits`. -/
lemma Loan.create_zero_payment_proof (properties : LoanProperties) (totalInterest roundedPayment : Number)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ rates.interestRate ≠ 0)
    (hround : STAmount.roundToNumericType broker.numericType properties.periodicPayment .upward
      (some properties.loanScale) = .ok roundedPayment)
    (hzero : roundedPayment.operator_eq Number.zero = true) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) :=
  Loan.create_cannot_amortize_proof broker v principal rates fees schedule allowsOverpayment pending properties
    hterms (LoanProperties.guards_zero_payment properties principal totalInterest roundedPayment _ _ _ hti
      (interest_iff_bne hinterest) hround hzero)

/-- Proof body of the payment count line of `Loan.create_exits`. -/
lemma Loan.create_payment_count_proof (properties : LoanProperties) (totalInterest roundedPayment ratio : Number)
    (computedPayments : Int64) (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hti : properties.totalValueOutstanding.operator_sub principal .to_nearest = .ok totalInterest)
    (hinterest : 0 < totalInterest.signum ↔ rates.interestRate ≠ 0)
    (hround : STAmount.roundToNumericType broker.numericType properties.periodicPayment .upward
      (some properties.loanScale) = .ok roundedPayment)
    (hnz : roundedPayment.operator_eq Number.zero = false)
    (hratio : properties.totalValueOutstanding.operator_div roundedPayment .upward = .ok ratio)
    (hcount : ratio.to_rep .upward = .ok computedPayments)
    (hne : computedPayments ≠ schedule.paymentTotal.toInt64) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecPRECISION_LOSS) :=
  Loan.create_cannot_amortize_proof broker v principal rates fees schedule allowsOverpayment pending properties
    hterms (LoanProperties.guards_payment_count properties principal totalInterest roundedPayment ratio
      computedPayments _ _ _ hti (interest_iff_bne hinterest) hround hnz hratio hcount hne)

/-- Proof body of the Open limit line of `Loan.create_exits`. -/
lemma Loan.create_open_zone_proof (properties : LoanProperties) (loanState : LoanState)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hguards : properties.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType =
      .ok .tesSUCCESS)
    (hstate : LoanState.build properties.totalValueOutstanding principal properties.managementFeeOutstanding =
      .ok loanState)
    (hopen : v.exceedsOpenLimit loanState.interestDue = .ok true) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecLIMIT_EXCEEDED) := by
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hterms.funds, Vault.pool_baseExponent, hterms.properties_ok, hterms.precision, hguards,
    hstate,
    Vault.pool_exceedsOpenLimit, hopen]
  rfl

/-- Proof body of the DebtMaximum line of `Loan.create_exits`. -/
lemma Loan.create_limit_exceeded_proof (properties : LoanProperties) (loanState : LoanState) (debtTotal' : Number)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hguards : properties.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType =
      .ok .tesSUCCESS)
    (hstate : LoanState.build properties.totalValueOutstanding principal properties.managementFeeOutstanding =
      .ok loanState)
    (hopen : v.exceedsOpenLimit loanState.interestDue = .ok false)
    (hdebt : broker.debtTotal.operator_add principal .to_nearest = .ok debtTotal')
    (hmax : (broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt debtTotal') = true) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecLIMIT_EXCEEDED) := by
  have hl : broker.checkLimits debtTotal' v.baseExponent = .ok .tecLIMIT_EXCEEDED := by
    unfold LoanBroker.checkLimits; rw [if_pos hmax]; rfl
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hterms.funds, Vault.pool_baseExponent, hterms.properties_ok, hterms.precision, hguards,
    hstate,
    Vault.pool_exceedsOpenLimit, hopen, hdebt, hl]
  rfl

/-- Proof body of the minCover line of `Loan.create_exits`. -/
lemma Loan.create_below_minCover_proof (properties : LoanProperties) (loanState : LoanState) (debtTotal' : Number)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule properties)
    (hguards : properties.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType =
      .ok .tesSUCCESS)
    (hstate : LoanState.build properties.totalValueOutstanding principal properties.managementFeeOutstanding =
      .ok loanState)
    (hopen : v.exceedsOpenLimit loanState.interestDue = .ok false)
    (hdebt : broker.debtTotal.operator_add principal .to_nearest = .ok debtTotal')
    (hmax : (broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt debtTotal') = false)
    (hcover : ({ broker.toRawLoanBroker with debtTotal := debtTotal' } : RawLoanBroker).hasMinimumCover
      v.baseExponent = .ok false) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error .tecINSUFFICIENT_FUNDS) := by
  have hl : broker.checkLimits debtTotal' v.baseExponent = .ok .tecINSUFFICIENT_FUNDS := by
    unfold LoanBroker.checkLimits; rw [if_neg (by rw [hmax]; decide)]
    simp only [bind, Except.bind, hcover]; rfl
  simp only [Loan.create]
  unfold_ter
  simp [Vault.pool_amounts, hterms.funds, Vault.pool_baseExponent, hterms.properties_ok, hterms.precision, hguards,
    hstate,
    Vault.pool_exceedsOpenLimit, hopen, hdebt, hl]
  rfl

/-- The create once every check passes: the vault and broker updates, then the re-check of the
new loan. -/
lemma Loan.create_run_of_checks (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      (match (RawLoan.build principal properties rates fees schedule broker' allowsOverpayment pending
        (schedule.startDate + schedule.paymentInterval)).to_lawful with
       | .error e => .error e
       | .ok loan => match Loan.createAmountToBorrower principal fees pending with
         | .error e => .error e
         | .ok a => .ok (.ok { loan' := loan, pool' := v', amountToBorrower := a })) := by
  have hpool := Vault.poolAdjust_ok v _ raw v' hadj hv'
  simp only [Loan.createChange] at hpool
  simp only [Loan.create]
  unfold_ter
  simp only at hbroker
  simp [Vault.pool_amounts, hchecks.funds, Vault.pool_baseExponent, hchecks.properties_ok, hchecks.precision,
    hchecks.guards,
    hchecks.state, Vault.pool_exceedsOpenLimit, hchecks.open_zone, hchecks.debt, hchecks.limits, hround, hpool, hbroker,
    show TER.tesSUCCESS.isTesSuccess = true from rfl,
    UInt32.addChecked_of_lt (b := 1) hcount, UInt32.addChecked_of_lt hdue, Loan.createAmountToBorrower]
  cases (RawLoan.build principal properties rates fees schedule broker' allowsOverpayment pending
    (schedule.startDate + schedule.paymentInterval)).to_lawful <;> try rfl
  cases pending <;> try rfl
  cases principal.operator_sub fees.originationFee .to_nearest <;> rfl

/-- A create with a rate, OverpaymentFee or fee out of range builds a loan that isn't lawful. -/
lemma Loan.create_terms_out_of_range_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : maxLoanRate < rates.interestRate ∨ maxLoanRate < rates.lateInterestRate ∨
      maxLoanRate < rates.closeInterestRate ∨ maxLoanRate < rates.overpaymentInterestRate ∨
      maxLoanRate < rates.overpaymentFee ∨ ∃ fee ∈ fees.amountFields, Number.zero.operator_le fee = false) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful := by
  rw [Loan.create_run_of_checks broker v principal rates fees schedule allowsOverpayment pending properties
    loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue,
    RawLoan.to_lawful_not_lawful]
  rintro ⟨-, hv⟩
  simp only [RawLoan.build] at hv
  rcases hbad with h | h | h | h | h | ⟨fee, hfee, h⟩
  · exact UInt32.not_le.mpr h hv.interestRate_cap
  · exact UInt32.not_le.mpr h hv.lateInterestRate_cap
  · exact UInt32.not_le.mpr h hv.closeInterestRate_cap
  · exact UInt32.not_le.mpr h hv.overpaymentInterestRate_cap
  · exact UInt32.not_le.mpr h hv.overpaymentFee_cap
  · simp only [LoanFees.amountFields, List.mem_cons, List.not_mem_nil, or_false] at hfee
    rcases hfee with rfl | rfl | rfl | rfl
    · rw [hv.originationFee_nonneg] at h; exact absurd h (by decide)
    · rw [hv.serviceFee_nonneg] at h; exact absurd h (by decide)
    · rw [hv.latePaymentFee_nonneg] at h; exact absurd h (by decide)
    · rw [hv.closePaymentFee_nonneg] at h; exact absurd h (by decide)

/-- A create with a schedule out of range builds a loan that isn't lawful. -/
lemma Loan.create_schedule_out_of_range_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : schedule.paymentTotal = 0 ∨ schedule.paymentInterval < minPaymentInterval ∨
      schedule.gracePeriod < defaultGracePeriod ∨ schedule.paymentInterval < schedule.gracePeriod) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful := by
  rw [Loan.create_run_of_checks broker v principal rates fees schedule allowsOverpayment pending properties
    loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue,
    RawLoan.to_lawful_not_lawful]
  rintro ⟨-, hv⟩
  simp only [RawLoan.build] at hv
  rcases hbad with h | h | h | h
  · have := hv.paymentTotal_pos; rw [h] at this; exact absurd this (by decide)
  · exact UInt32.not_le.mpr h hv.paymentInterval_min
  · exact UInt32.not_le.mpr h hv.gracePeriod_range.1
  · exact UInt32.not_le.mpr h hv.gracePeriod_range.2

/-- Proof body of the rate line of `Loan.create_not_lawful`. -/
lemma Loan.create_rate_out_of_range_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : maxLoanRate < rates.interestRate ∨ maxLoanRate < rates.lateInterestRate ∨
      maxLoanRate < rates.closeInterestRate ∨ maxLoanRate < rates.overpaymentInterestRate) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful :=
  Loan.create_terms_out_of_range_proof broker v principal rates fees schedule allowsOverpayment pending
    properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue
    (by rcases hbad with h | h | h | h <;> simp [h])

/-- Proof body of the OverpaymentFee line of `Loan.create_not_lawful`. -/
lemma Loan.create_overpaymentFee_out_of_range_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : maxLoanRate < rates.overpaymentFee) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful :=
  Loan.create_terms_out_of_range_proof broker v principal rates fees schedule allowsOverpayment pending
    properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbad)))))

/-- Proof body of the negative fee line of `Loan.create_not_lawful`. -/
lemma Loan.create_fee_negative_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : ∃ fee ∈ fees.amountFields, Number.zero.operator_le fee = false) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful :=
  Loan.create_terms_out_of_range_proof broker v principal rates fees schedule allowsOverpayment pending
    properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbad)))))

/-- Proof body of the PaymentInterval line of `Loan.create_not_lawful`. -/
lemma Loan.create_interval_too_short_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : schedule.paymentInterval < minPaymentInterval) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful :=
  Loan.create_schedule_out_of_range_proof broker v principal rates fees schedule allowsOverpayment pending
    properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue
    (Or.inr (Or.inl hbad))

/-- Proof body of the GracePeriod line of `Loan.create_not_lawful`. -/
lemma Loan.create_grace_out_of_range_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hbad : schedule.gracePeriod < defaultGracePeriod ∨ schedule.paymentInterval < schedule.gracePeriod) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .error .notLawful :=
  Loan.create_schedule_out_of_range_proof broker v principal rates fees schedule allowsOverpayment pending
    properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue
    (Or.inr (Or.inr hbad))

/-- Proof body of the success line of `Loan.create_exits`. -/
lemma Loan.create_success_proof (properties : LoanProperties) (loanState : LoanState)
    (debtTotal' principal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker) (loan : Loan)
    (amountToBorrower : Number)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal')
    (hround : STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal')
    (hadj : (v.adjustBalances (Loan.createChange principal principal' loanState.interestDue pending)).run =
      .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker')
    (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32)
    (hloan : (RawLoan.build principal properties rates fees schedule broker' allowsOverpayment pending
      (schedule.startDate + schedule.paymentInterval)).to_lawful = .ok loan)
    (hamount : Loan.createAmountToBorrower principal fees pending = .ok amountToBorrower) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.ok { loan' := loan, pool' := v', amountToBorrower := amountToBorrower }) := by
  rw [Loan.create_run_of_checks broker v principal rates fees schedule allowsOverpayment pending properties
    loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker hcount hdue, hloan]
  simp only [hamount]

end XRPL.Model.Lending
