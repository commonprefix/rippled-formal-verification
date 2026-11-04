import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.SetExits
import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Lending.Loan.Common.SetReachable

/-! # `LoanSet` exits

The exits of `canCreate` and `create`, one line per exit. Each line assumes the checks that run before it
passed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultSchedule RawVault)

variable (broker : LoanBroker) (v : Vault) (principalRequested : Number) (fees : LoanFees)
  (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)

/-- The exits of `canCreate`, one line per exit. Each line assumes the checks that run before it passed. -/
theorem Loan.canCreate_exits :
    (maxTime.toNat < schedule.startDate.toNat + schedule.gracePeriod.toNat +
        schedule.paymentTotal.toNat * schedule.paymentInterval.toNat →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecKILLED) ∧
    (schedule.Fits → schedule.startDate ≤ t →
      Loan.canCreate broker v principalRequested fees schedule t true = .ok .tecEXPIRED) ∧
    (schedule.Fits → (twoStep = false ∨ t < schedule.startDate) → v.phase t = .subscription →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecTOO_SOON) ∧
    (schedule.Fits → (twoStep = false ∨ t < schedule.startDate) → v.phase t = .redemption →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecEXPIRED) ∧
    (∀ s : VaultSchedule, schedule.Fits → (twoStep = false ∨ t < schedule.startDate) → v.phase t = .investment →
      v.schedule = some s →
      s.redemptionDate.toNat <
        schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat + loanRedemptionBuffer →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecNO_PERMISSION) ∧
    -- `e` - the current vault scale, the exponent of AssetsTotal
    (∀ (assetsTotal : Number) (e : Int), schedule.Fits → (twoStep = false ∨ t < schedule.startDate) →
      schedule.FitsVault v t → v.assetsTotal = .ok assetsTotal →
      numberExponent assetsTotal v.baseExponent broker.numericType = .ok e → v.baseExponent < e →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecLIMIT_EXCEEDED) ∧
    (∀ assetsTotal : Number, schedule.Fits → (twoStep = false ∨ t < schedule.startDate) →
      schedule.FitsVault v t → v.assetsTotal = .ok assetsTotal →
      numberExponent assetsTotal v.baseExponent broker.numericType = .ok v.baseExponent →
      (∃ x ∈ principalRequested :: fees.amountFields, STAmount.isRounded broker.numericType x = true) →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tecPRECISION_LOSS) ∧
    (∀ assetsTotal : Number, schedule.Fits → (twoStep = false ∨ t < schedule.startDate) →
      schedule.FitsVault v t → v.assetsTotal = .ok assetsTotal →
      numberExponent assetsTotal v.baseExponent broker.numericType = .ok v.baseExponent →
      (∀ x ∈ principalRequested :: fees.amountFields, STAmount.isRounded broker.numericType x = false) →
      Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tesSUCCESS) :=
  ⟨Loan.canCreate_schedule_too_long_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_start_passed_proof broker v principalRequested fees schedule t,
    Loan.canCreate_subscription_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_redemption_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_ends_late_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_base_scale_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_precision_loss_proof broker v principalRequested fees schedule t twoStep,
    Loan.canCreate_success_proof broker v principalRequested fees schedule t twoStep⟩

/-- Error codes: success, tecKILLED, tecTOO_SOON, tecEXPIRED, tecNO_PERMISSION, tecLIMIT_EXCEEDED or
tecPRECISION_LOSS. -/
theorem Loan.canCreate_error_codes (ter : TER)
    (hok : Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecKILLED ∨ ter = .tecTOO_SOON ∨ ter = .tecEXPIRED ∨
      ter = .tecNO_PERMISSION ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS :=
  Loan.canCreate_error_codes_proof broker v principalRequested fees schedule t twoStep ter hok

/-- Success ⟺ the schedule fits the ledger clock and the vault's phases, now < StartDate for a pending loan, the current
vault scale = the initial vault scale, and PrincipalRequested and the fees fit an STAmount exactly. -/
theorem Loan.canCreate_lawful_iff (assetsTotal : Number) (e : Int)
    (hn : 0 < schedule.paymentTotal) (hi : 0 < schedule.paymentInterval) -- LoanSet preflight
    (hat : v.assetsTotal = .ok assetsTotal)
    (hexp : numberExponent assetsTotal v.baseExponent broker.numericType = .ok e) :
    Loan.canCreate broker v principalRequested fees schedule t twoStep = .ok .tesSUCCESS ↔
      schedule.Fits ∧ (twoStep = false ∨ t < schedule.startDate) ∧ schedule.FitsVault v t ∧
        e = v.baseExponent ∧
        ∀ x ∈ principalRequested :: fees.amountFields, STAmount.isRounded broker.numericType x = false :=
  Loan.canCreate_lawful_iff_proof broker v principalRequested fees schedule t twoStep assetsTotal e hn hi hat hexp

/-! ## `Loan.create` -/

variable (rates : LoanRates) (allowsOverpayment pending : Bool)

/-- The exits of `create`, one line per exit. Each line assumes the checks that run before it passed. -/
theorem Loan.create_exits :
    (v.assetsAvailable.operator_lt principalRequested = true →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    -- `properties` - the loan computed from the terms, LoanScale is `properties.loanScale`
    (∀ properties : LoanProperties, v.assetsAvailable.operator_lt principalRequested = false →
      computeLoanProperties principalRequested rates.interestRate schedule.paymentInterval
        schedule.paymentTotal broker.managementFeeRate broker.numericType v.baseExponent = .ok properties →
      (∀ x ∈ principalRequested :: fees.amountFields,
        ∃ b, isRounded x properties.loanScale broker.numericType = .ok b) →
      (∃ x ∈ principalRequested :: fees.amountFields,
        isRounded x properties.loanScale broker.numericType = .ok false) →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecPRECISION_LOSS)) ∧
    -- `totalInterest` - TotalValueOutstanding − PrincipalRequested
    (∀ (properties : LoanProperties) (totalInterest : Number),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties → rates.interestRate ≠ 0 →
      properties.totalValueOutstanding.operator_sub principalRequested .to_nearest = .ok totalInterest →
      totalInterest.signum ≤ 0 →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecPRECISION_LOSS)) ∧
    -- the loan has interest exactly when InterestRate ≠ 0, the check before this one
    (∀ (properties : LoanProperties) (totalInterest : Number),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.totalValueOutstanding.operator_sub principalRequested .to_nearest = .ok totalInterest →
      (0 < totalInterest.signum ↔ rates.interestRate ≠ 0) →
      properties.firstPaymentPrincipal.signum ≤ 0 →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecPRECISION_LOSS)) ∧
    -- the loan has interest exactly when InterestRate ≠ 0, the first check
    (∀ (properties : LoanProperties) (totalInterest roundedPayment : Number),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.totalValueOutstanding.operator_sub principalRequested .to_nearest = .ok totalInterest →
      (0 < totalInterest.signum ↔ rates.interestRate ≠ 0) →
      STAmount.roundToNumericType broker.numericType properties.periodicPayment .upward
        (some properties.loanScale) = .ok roundedPayment →
      roundedPayment.operator_eq Number.zero = true →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecPRECISION_LOSS)) ∧
    -- `computedPayments` - TotalValueOutstanding / roundedPayment, rounded up
    (∀ (properties : LoanProperties) (totalInterest roundedPayment ratio : Number) (computedPayments : Int64),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.totalValueOutstanding.operator_sub principalRequested .to_nearest = .ok totalInterest →
      (0 < totalInterest.signum ↔ rates.interestRate ≠ 0) →
      STAmount.roundToNumericType broker.numericType properties.periodicPayment .upward
        (some properties.loanScale) = .ok roundedPayment →
      roundedPayment.operator_eq Number.zero = false →
      properties.totalValueOutstanding.operator_div roundedPayment .upward = .ok ratio →
      ratio.to_rep .upward = .ok computedPayments →
      computedPayments ≠ schedule.paymentTotal.toUInt64.toInt64 →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecPRECISION_LOSS)) ∧
    -- `loanState` - the state of the new loan, its interestDue is `loanState.interestDue`
    (∀ (properties : LoanProperties) (loanState : LoanState),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.checkGuards principalRequested rates.interestRate schedule.paymentTotal
        broker.numericType = .ok .tesSUCCESS →
      LoanState.build properties.totalValueOutstanding principalRequested
        properties.managementFeeOutstanding = .ok loanState →
      v.exceedsOpenLimit loanState.interestDue = .ok true →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- `debtTotal'` - the new DebtTotal
    (∀ (properties : LoanProperties) (loanState : LoanState) (debtTotal' : Number),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.checkGuards principalRequested rates.interestRate schedule.paymentTotal
        broker.numericType = .ok .tesSUCCESS →
      LoanState.build properties.totalValueOutstanding principalRequested
        properties.managementFeeOutstanding = .ok loanState →
      v.exceedsOpenLimit loanState.interestDue = .ok false →
      broker.debtTotal.operator_add principalRequested .to_nearest = .ok debtTotal' →
      (broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt debtTotal') = true →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecLIMIT_EXCEEDED)) ∧
    (∀ (properties : LoanProperties) (loanState : LoanState) (debtTotal' : Number),
      Loan.CreateTerms broker v principalRequested rates fees schedule properties →
      properties.checkGuards principalRequested rates.interestRate schedule.paymentTotal
        broker.numericType = .ok .tesSUCCESS →
      LoanState.build properties.totalValueOutstanding principalRequested
        properties.managementFeeOutstanding = .ok loanState →
      v.exceedsOpenLimit loanState.interestDue = .ok false →
      broker.debtTotal.operator_add principalRequested .to_nearest = .ok debtTotal' →
      (broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt debtTotal') = false →
      ({ broker.toRawLoanBroker with debtTotal := debtTotal' } : RawLoanBroker).hasMinimumCover
        v.baseExponent = .ok false →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    (∀ (properties : LoanProperties) (loanState : LoanState) (debtTotal' principal' : Number) (raw : RawVault)
      (v' : Vault) (broker' : LoanBroker) (loan : Loan),
      Loan.CreateChecks broker v principalRequested rates fees schedule properties loanState debtTotal' →
      STAmount.roundToNumericType broker.numericType principalRequested .to_nearest = .ok principal' →
      (v.adjustBalances (Loan.createChange principalRequested principal' loanState.interestDue
        pending)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
        : RawLoanBroker).to_lawful = .ok broker' →
      (RawLoan.build properties rates fees schedule broker' allowsOverpayment pending).to_lawful = .ok loan →
      (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
        .ok (.ok { loan' := loan, pool' := v' })) :=
  ⟨Loan.create_insufficient_funds_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_precision_loss_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_no_interest_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_no_principal_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_zero_payment_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_payment_count_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_open_zone_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_limit_exceeded_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_below_minCover_proof broker v principalRequested rates fees schedule allowsOverpayment pending,
    Loan.create_success_proof broker v principalRequested rates fees schedule allowsOverpayment pending⟩

/-- All checks pass but a term is out of range -> `create` returns notLawful, one line per term. -/
theorem Loan.create_not_lawful :
    ∀ (properties : LoanProperties) (loanState : LoanState) (debtTotal' principal' : Number) (raw : RawVault)
      (v' : Vault) (broker' : LoanBroker),
      Loan.CreateChecks broker v principalRequested rates fees schedule properties loanState debtTotal' →
      STAmount.roundToNumericType broker.numericType principalRequested .to_nearest = .ok principal' →
      (v.adjustBalances (Loan.createChange principalRequested principal' loanState.interestDue
        pending)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
        : RawLoanBroker).to_lawful = .ok broker' →
      (maxLoanRate < rates.interestRate ∨ maxLoanRate < rates.lateInterestRate ∨
          maxLoanRate < rates.closeInterestRate ∨ maxLoanRate < rates.overpaymentInterestRate →
        (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
          .error .notLawful) ∧
      (maxLoanRate < rates.overpaymentFee →
        (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
          .error .notLawful) ∧
      ((∃ fee ∈ fees.amountFields, Number.zero.operator_le fee = false) →
        (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
          .error .notLawful) ∧
      (schedule.paymentInterval < minPaymentInterval →
        (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
          .error .notLawful) ∧
      (schedule.gracePeriod < defaultGracePeriod ∨ schedule.paymentInterval < schedule.gracePeriod →
        (Loan.create broker v principalRequested rates fees schedule allowsOverpayment pending).run =
          .error .notLawful) :=
  fun properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker =>
    ⟨Loan.create_rate_out_of_range_proof broker v principalRequested rates fees schedule allowsOverpayment pending
        properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker,
      Loan.create_overpaymentFee_out_of_range_proof broker v principalRequested rates fees schedule
        allowsOverpayment pending properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv'
        hbroker,
      Loan.create_fee_negative_proof broker v principalRequested rates fees schedule allowsOverpayment pending
        properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker,
      Loan.create_interval_too_short_proof broker v principalRequested rates fees schedule allowsOverpayment pending
        properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker,
      Loan.create_grace_out_of_range_proof broker v principalRequested rates fees schedule allowsOverpayment pending
        properties loanState debtTotal' principal' raw v' broker' hchecks hround hadj hv' hbroker⟩

/-- The only create rejections on a reachable ledger are tecINSUFFICIENT_FUNDS, tecPRECISION_LOSS or
tecLIMIT_EXCEEDED. The guards never reject with tecINTERNAL, and the vault update never with tefBAD_LEDGER. -/
theorem Loan.create_error_codes (l : LendingLedger) (hr : l.Reachable) (j : Nat) (hb : l.broker? j = some broker)
    (ter : TER)
    (hpre : Loan.CreatePreflight broker principalRequested rates fees schedule) -- LoanSet preflight and preclaim
    (hc : Loan.canCreate broker l.vault principalRequested fees schedule l.now twoStep = .ok .tesSUCCESS)
    -- the range of the proof: an XRP or MPT vault holds less than `10^16` units
    (hroom : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hcount : broker.loanCount + 1 ≠ 0) -- LoanCount does not overflow
    (hok : (Loan.create broker l.vault principalRequested rates fees schedule allowsOverpayment pending).run =
      .ok (.error ter)) :
    ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED :=
  Loan.create_error_codes_reachable_proof l hr j broker hb principalRequested rates fees schedule twoStep
    allowsOverpayment pending ter hpre hc hroom hcount hok

end XRPL.Model.Lending
