import XRPL.Properties.Lending.Loan.Common.SetExits
import XRPL.Properties.Lending.LoanBroker.Defs
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Lending.Loan.Common.SetPhase

/-! # What a successful `Loan.create` writes

A successful create passed every check, so its result is the loan built from the computed
properties, on the broker with the new debt, and the vault after the principal moved. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet

/-- A precision check that passes passed every amount. -/
lemma checkPrecisionFields_success_inv (principal : Number) (fees : LoanFees) (f : Number → Except Error Bool)
    (h : checkPrecisionFields principal fees f = .ok .tesSUCCESS) :
    ∀ x ∈ principal :: fees.amountFields, f x = .ok true := by
  unfold checkPrecisionFields LoanFees.amountFields at h
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at h
  intro x hx
  simp only [LoanFees.amountFields, List.mem_cons, List.not_mem_nil, or_false] at hx
  cases h1 : f principal with
  | error e => rw [h1] at h; simp at h
  | ok b1 =>
    cases b1
    · rw [h1] at h; simp at h
    cases h2 : f fees.originationFee with
    | error e => rw [h1, h2] at h; simp at h
    | ok b2 =>
      cases b2
      · rw [h1, h2] at h; simp at h
      cases h3 : f fees.serviceFee with
      | error e => rw [h1, h2, h3] at h; simp at h
      | ok b3 =>
        cases b3
        · rw [h1, h2, h3] at h; simp at h
        cases h4 : f fees.latePaymentFee with
        | error e => rw [h1, h2, h3, h4] at h; simp at h
        | ok b4 =>
          cases b4
          · rw [h1, h2, h3, h4] at h; simp at h
          cases h5 : f fees.closePaymentFee with
          | error e => rw [h1, h2, h3, h4, h5] at h; simp at h
          | ok b5 =>
            cases b5
            · rw [h1, h2, h3, h4, h5] at h; simp at h
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A passing LoanSet check means PrincipalRequested and every fee fit an amount of the broker's asset. -/
lemma Loan.canCreate_exact (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (h : Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS) :
    ∀ x ∈ p :: fees.amountFields, STAmount.isRounded broker.numericType x = false := by
  have hfund := Loan.canCreate_canFundLoan broker v p fees schedule t twoStep h
  unfold Loan.canCreate at h
  generalize schedule.checkTimeAvailability = st at h
  obtain ⟨st, rfl⟩ : ∃ t, st = .ok t := by
    cases st with
    | error e => simp [bind, Except.bind] at h
    | ok t => exact ⟨t, rfl⟩
  rw [hfund] at h
  generalize hc : checkPrecisionFields p fees
    (fun value => pure !(STAmount.isRounded broker.numericType value)) = c at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; exact absurd ‹_› (by decide)
  · split at h
    · cases h
    · rw [if_neg (by rw [show TER.tesSUCCESS.isTesSuccess = true from rfl]; decide)] at h
      cases c with
      | error e => cases h
      | ok pt =>
        dsimp only at h
        split at h
        · cases h; exact absurd ‹_› (by decide)
        · rename_i hpt
          have hpt' : pt = .tesSUCCESS := (TER.isTesSuccess_iff pt).mp (by simpa using hpt)
          subst hpt'
          intro x hx
          have := checkPrecisionFields_success_inv p fees _ hc x hx
          simpa [pure, Except.pure] using this

/-- A successful create passed every check. It returns the loan built from the computed
properties on the broker with the new debt, and the vault after the balance change. -/
lemma Loan.create_ok_inv (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ properties loanState debtTotal' principal' broker',
      Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal' ∧
      STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal' ∧
      AssetPool.adjustBalances v (Loan.createChange principal principal' loanState.interestDue pending) =
        .ok (.ok r.pool') ∧
      ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
        : RawLoanBroker).to_lawful = .ok broker' ∧
      (RawLoan.build properties rates fees schedule broker' allowsOverpayment pending
        (schedule.startDate + schedule.paymentInterval)).to_lawful = .ok r.loan' := by
  simp only [Loan.create] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    have hfunds := ‹¬ (AssetPool.amounts v).assetsAvailable.operator_lt principal = true›
    have hprops := ‹computeLoanProperties _ _ _ _ _ _ _ = Except.ok _›
    have hprec := ‹checkPrecisionFields _ _ _ = Except.ok _›
    have hguards := ‹LoanProperties.checkGuards _ _ _ _ _ = Except.ok _›
    have hstate := ‹LoanState.build _ _ _ = Except.ok _›
    have hopen := ‹AssetPool.exceedsOpenLimit _ _ = Except.ok _›
    have hdebt := ‹broker.debtTotal.operator_add principal _ = Except.ok _›
    have hlimits := ‹broker.checkLimits _ _ = Except.ok _›
    have hround := ‹STAmount.roundToNumericType broker.numericType principal _ = Except.ok _›
    have hbroker := ‹RawLoanBroker.to_lawful _ = Except.ok _›
    have hloan := ‹RawLoan.to_lawful _ = Except.ok _›
    have hpool := ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true] at *
    simp only [Bool.not_eq_false, TER.isTesSuccess_iff] at *
    subst_vars
    refine ⟨_, _, _, _, _, ⟨⟨by simpa [Vault.pool_amounts] using hfunds, hprops,
      checkPrecisionFields_success_inv _ _ _ hprec⟩, hguards, hstate, hopen, hdebt, hlimits⟩, hround, ?_, hbroker,
      hloan⟩
    simp [Loan.createChange, *] at hpool ⊢

/-- A successful create counted one more loan and set the first due date without wrapping. -/
lemma Loan.create_ok_fits (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    broker.loanCount.toNat + 1 < 2 ^ 32 ∧ schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32 := by
  simp only [Loan.create] at hok
  unfold_ter at hok
  constructor
  · by_contra hc
    have hbad : broker.loanCount.addChecked 1 = .error .wrap := by
      unfold UInt32.addChecked; rw [if_neg (by simpa using hc)]
    simp only [hbad] at hok
    walk_ok
  · by_contra hc
    have hbad : schedule.startDate.addChecked schedule.paymentInterval = .error .wrap := by
      unfold UInt32.addChecked; rw [if_neg (by simpa using hc)]
    simp only [hbad] at hok
    walk_ok

/-- The new loan sits on the broker with the new debt, and that broker is the old one with DebtTotal
and LoanCount updated. -/
lemma Loan.create_ok_broker (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ properties loanState debtTotal',
      Loan.CreateChecks broker v principal rates fees schedule properties loanState debtTotal' ∧
      r.loan'.broker.toRawLoanBroker =
        { broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 } := by
  obtain ⟨properties, loanState, debtTotal', _, broker', hchecks, -, -, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨hl, -, -⟩ := RawLoan.to_lawful_ok hloan
  obtain ⟨hb, -, -⟩ := RawLoanBroker.to_lawful_ok hbroker
  refine ⟨properties, loanState, debtTotal', hchecks, ?_⟩
  have : r.loan'.broker = broker' := (congrArg RawLoan.broker hl).trans rfl
  rw [this, hb]

/-- Proof body of the DebtMaximum part of `Lending.create_updates`. -/
lemma Loan.create_within_debtMaximum_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault)
    (_hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hmax : r.loan'.broker.toExact.debtMaximum ≠ 0) :
    r.loan'.broker.toExact.debtTotal ≤ r.loan'.broker.toExact.debtMaximum :=
  r.loan'.broker.exact.debt_within_cap hmax

/-- Proof body of the minCover part of `Lending.create_updates`. -/
lemma Loan.create_meets_minCover_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.loan'.broker.HasMinimumCover v.baseExponent := by
  obtain ⟨_, _, debtTotal', hchecks, hb⟩ :=
    Loan.create_ok_broker broker v principal rates fees schedule allowsOverpayment pending r hok
  have hl := hchecks.limits
  unfold LoanBroker.checkLimits at hl
  unfold LoanBroker.HasMinimumCover
  have hcover : r.loan'.broker.hasMinimumCover v.baseExponent =
      ({ broker.toRawLoanBroker with debtTotal := debtTotal' } : RawLoanBroker).hasMinimumCover v.baseExponent := by
    show r.loan'.broker.toRawLoanBroker.hasMinimumCover v.baseExponent = _
    rw [hb]
    rfl
  rw [hcover]
  split at hl
  · exact absurd hl (by decide)
  · cases hm : ({ broker.toRawLoanBroker with debtTotal := debtTotal' } : RawLoanBroker).hasMinimumCover
        v.baseExponent with
    | error e => simp only [bind, Except.bind, hm] at hl; exact absurd hl (by simp)
    | ok b =>
      cases b
      · simp only [bind, Except.bind, hm] at hl; exact absurd hl (by decide)
      · rfl

end XRPL.Model.Lending
