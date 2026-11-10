import XRPL.Properties.Lending.Loan.Common.PayBounds
import XRPL.Model.Lending1_1.AssetPool

/-! # Witnesses for the LoanPay bounds

Concrete creates and payments on closed-ended IOU vaults, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

open private Loan.scheduledComponents from XRPL.Model.Lending.Loan.LoanPay

/-- A closed-ended schedule that never ends during the witnesses' payments. -/
private def pbSchedule : VaultSchedule := { subscriptionDate := 900, redemptionDate := 900000900 }

/-- A closed-ended IOU vault at the given scale holding `assets`, with nothing lent out. -/
private def pbVault (scale : UInt8) (assets : Number) : RawVault :=
  { assetsAvailable := assets, assetsDeployed := Number.zero
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := scale
  , sharesTotal := ⟨false, 1000000000000000000, -15⟩, lossUnrealized := Number.zero
  , yieldUnrealized := Number.zero, schedule := some pbSchedule, earlyExitFeeRate := none
  , ownerCanBlockDeposit := false, depositBlocked := false }

/-- An IOU broker with no loans and no cover requirement. -/
private def pbBroker (managementFeeRate : TenthBips16) : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := managementFeeRate, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := Number.zero, loanCount := 0 }

/-- No fees. -/
private def pbFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
  , closePaymentFee := Number.zero }

/-- The given InterestRate and LateInterestRate, no other rate. -/
private def pbRates (interestRate lateInterestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := lateInterestRate, closeInterestRate := 0
  , overpaymentInterestRate := 0, overpaymentFee := 0 }

/-- `count` payments 30 days apart. -/
private def pbMonthly (count : UInt32) : LoanSchedule :=
  { paymentInterval := 2592000, paymentTotal := count, gracePeriod := 60, startDate := 1000 }

/-- Pay the next scheduled payment `n` times, each with its totalDue at its due date. -/
private def pbPayDue : Nat → Loan → Vault → Option (Loan × Vault)
  | 0, loan, v => some (loan, v)
  | n + 1, loan, v =>
    match loan.paymentComponents .regular loan.nextPaymentDueDate with
    | .ok pc =>
      match pc.totalDue with
      | .ok due =>
        match (loan.regularPayment v due loan.nextPaymentDueDate).run with
        | .ok (.ok r) => pbPayDue n r.loan' r.pool'
        | _ => none
      | .error _ => none
    | .error _ => none

/-- A vault at scale `10^-8` holding `10^6`. -/
private def pbLastVault : Vault := ⟨pbVault 8 ⟨false, 1000000000000000000, -12⟩, by native_decide, by native_decide⟩

/-- The broker with a 0.1% management fee. -/
private def pbLastBroker : LoanBroker := ⟨pbBroker 100, by native_decide, by native_decide⟩

/-- `190.623`. -/
private def pbLastPrincipal : Number := ⟨false, 1906230000000000000, -16⟩

/-- The loan of `190.623` at 12% over 36 monthly payments after its first 35 payments, and its vault. -/
private def pbLastRun : Option (Loan × Vault) :=
  match (Loan.create pbLastBroker pbLastVault pbLastPrincipal (pbRates 12000 0) pbFees (pbMonthly 36) false
      false).run with
  | .ok (.ok r) => pbPayDue 35 r.loan' r.pool'
  | _ => none

/-- The last payment costs more than ⌈PeriodicPayment⌉ + LoanServiceFee, and a regular payment of it passes. -/
private def lastPaymentCheck : Bool :=
  match pbLastRun with
  | some (loan, v) =>
    match loan.paymentComponents .regular loan.nextPaymentDueDate,
        STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) with
    | .ok pc, .ok pp' =>
      match pc.totalDue with
      | .ok due =>
        match (loan.regularPayment v due loan.nextPaymentDueDate).run with
        | .ok (.ok _) => decide (pp'.toRat + loan.fees.serviceFee.toRat < due.toRat)
        | _ => false
      | .error _ => false
    | _, _ => false
  | none => false

private lemma lastPaymentCheck_true : lastPaymentCheck = true := by native_decide

/-- **The last scheduled payment can cost more than ⌈PeriodicPayment⌉ + LoanServiceFee.** A loan of `190.623` at
12% over 36 monthly payments with a 0.1% fee owes `6.31645547` after 35 payments, ⌈PeriodicPayment⌉ is `6.31645546`. -/
lemma Loan.regularPayment_amount_witness :
    ∃ (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) (pc : PaymentComponents) (due pp' : Number)
      (r : LoanWithAmounts Vault),
      loan.paymentComponents .regular now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧
      (loan.regularPayment v amount now).run = .ok (.ok r) ∧ amount = due ∧
      pp'.toRat + loan.fees.serviceFee.toRat < due.toRat := by
  have h := lastPaymentCheck_true
  unfold lastPaymentCheck at h
  split at h
  · rename_i loan v _
    split at h
    · rename_i pc pp' hpc hpp
      split at h
      · rename_i due hdue
        split at h
        · rename_i r hr
          exact ⟨loan, v, due, _, pc, due, pp', r, hpc, hdue, hpp, hr, rfl, of_decide_eq_true h⟩
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)


/-- A vault at scale `10^-6` holding `10^6`. -/
private def pbBaseVault : Vault := ⟨pbVault 6 ⟨false, 1000000000000000000, -12⟩, by native_decide, by native_decide⟩

/-- The broker without a management fee. -/
private def pbNoFeeBroker : LoanBroker := ⟨pbBroker 0, by native_decide, by native_decide⟩

/-- `1000`. -/
private def pbThousand : Number := ⟨false, 1000000000000000000, -15⟩

/-- The loan of `1000` at 12% over 12 monthly payments, and its vault. -/
private def pbBaseRun : Option (Loan × Vault) :=
  match (Loan.create pbNoFeeBroker pbBaseVault pbThousand (pbRates 12000 0) pbFees (pbMonthly 12) false false).run with
  | .ok (.ok r) => some (r.loan', r.pool')
  | _ => none

/-- An IOU broker that needs cover for all of its debt, holding `cover`. -/
private def pbCoverBroker (managementFeeRate : TenthBips16) (cover : Number) : RawLoanBroker :=
  { pbBroker managementFeeRate with
    coverRateMinimum := 100000
    coverRateLiquidation := 100000
    coverAvailable := cover }

/-- The loan with its broker's cover replaced, as when another loan's default takes from the cover. -/
private def pbWithCover (loan : Loan) (cover : Number) : Option Loan :=
  match ({ loan.broker.toRawLoanBroker with coverAvailable := cover } : RawLoanBroker).to_lawful with
  | .ok broker =>
    match ({ loan.toRawLoan with broker := broker } : RawLoan).to_lawful with
    | .ok l => some l
    | .error _ => none
  | .error _ => none

/-- The checks a cover witness makes: the vault and the broker share the asset, the broker is below minCover and
the fee is not negative. -/
private def pbCoverChecks (loan : Loan) (v : Vault) (payment : UnsettledPayment Vault) : Bool :=
  decide (loan.broker.numericType = v.numericType) && !loan.broker.numericType.isIntegral &&
    decide (loan.broker.hasMinimumCover v.baseExponent = .ok false) && decide (0 ≤ payment.amounts.feePaid.toRat)

private lemma pbCoverChecks_spec (loan : Loan) (v : Vault) (payment : UnsettledPayment Vault)
    (h : pbCoverChecks loan v payment = true) :
    loan.broker.numericType = v.numericType ∧ loan.broker.hasMinimumCover v.baseExponent = .ok false ∧
      0 ≤ payment.amounts.feePaid.toRat ∧
      (loan.broker.numericType.isIntegral = true → ∃ w : Number, w.isNormalized ∧
        w.toRat = loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat) := by
  unfold pbCoverChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h3, h4, fun hi => absurd hi (by rw [h2]; decide)⟩

/-- The base loan on a broker with a 1% management fee that needs cover for its debt, holding `1000`. -/
private def pbCoverRun : Option (Loan × Vault) :=
  match (pbCoverBroker 1000 pbThousand).to_lawful with
  | .ok broker =>
    match (Loan.create broker pbBaseVault pbThousand (pbRates 12000 0) pbFees (pbMonthly 12) false false).run with
    | .ok (.ok r) => (pbWithCover r.loan' Number.zero).map (·, r.pool')
    | _ => none
  | .error _ => none

/-- With the cover emptied, the first payment of exactly totalDue adds exactly the fee to the cover. -/
private def coverEqualCheck : Bool :=
  match pbCoverRun with
  | some (loan, v) =>
    match loan.paymentComponents .regular loan.nextPaymentDueDate with
    | .ok pc =>
      match pc.totalDue with
      | .ok due =>
        match (loan.payInstalments v .regular due loan.nextPaymentDueDate).run,
            (loan.pay v .regular due loan.nextPaymentDueDate).run with
        | .ok (.ok payment), .ok (.ok r) =>
          pbCoverChecks loan v payment && decide (0 < payment.amounts.feePaid.toRat) &&
            decide ((r.loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) -
              payment.amounts.feePaid.toRat = 0)
        | _, _ => false
      | .error _ => false
    | .error _ => false
  | none => false

private lemma coverEqualCheck_true : coverEqualCheck = true := by native_decide

/-- **A payment can add exactly feePaid to the cover of a broker below minCover.** The first payment of the base
loan, with a 1% management fee, on a broker whose cover a default emptied. -/
lemma Loan.payment_fees_upper_bound_witness :
    ∃ (loan : Loan) (v : Vault) (paymentType : LoanPaymentType) (amount : Number) (now : UInt32)
      (r : LoanWithAmounts Vault) (payment : UnsettledPayment Vault),
      loan.broker.hasMinimumCover v.baseExponent = .ok false ∧
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) ∧
      (loan.pay v paymentType amount now).run = .ok (.ok r) ∧
      (loan.broker.numericType.isIntegral = true → ∃ w : Number, w.isNormalized ∧
        w.toRat = loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat) ∧
      (r.loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat = 0 := by
  have h := coverEqualCheck_true
  unfold coverEqualCheck at h
  split at h
  · rename_i loan v _
    split at h
    · split at h
      · rename_i due _
        split at h
        · rename_i payment r hp hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hc, -⟩, he⟩ := h
          obtain ⟨-, h2, -, h4⟩ := pbCoverChecks_spec loan v payment hc
          exact ⟨loan, v, .regular, due, _, r, payment, h2, hp, hr, h4, he⟩
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The base loan, and its vault with AssetsAvailable set to `12345678901.23456`, above `10^16` base units at
scale `10^-6`. -/
private def pbSplitRun : Option (Loan × Vault) :=
  match pbBaseRun with
  | some (loan, v) =>
    match ({ v.toRawVault with assetsAvailable := ⟨false, 1234567890123456000, -8⟩ } : RawVault).to_lawful with
    | .ok v' => some (loan, v')
    | .error _ => none
  | none => none

/-- Two scheduled payments in one regular payment leave the loan of two separate regular payments, but not their
vault. -/
private def splitCheck : Bool :=
  match pbSplitRun with
  | some (loan, v) =>
    match loan.paymentComponents .regular loan.nextPaymentDueDate with
    | .ok pc₁ =>
      match pc₁.totalDue with
      | .ok due₁ =>
        match (loan.regularPayment v due₁ loan.nextPaymentDueDate).run with
        | .ok (.ok r₁) =>
          match r₁.loan'.paymentComponents .regular loan.nextPaymentDueDate with
          | .ok pc₂ =>
            match pc₂.totalDue with
            | .ok due₂ =>
              match due₁.operator_add due₂ .to_nearest with
              | .ok amount =>
                match (r₁.loan'.regularPayment r₁.pool' due₂ loan.nextPaymentDueDate).run,
                    (loan.payInstalments v .regular amount loan.nextPaymentDueDate).run,
                    (loan.regularPayment v amount loan.nextPaymentDueDate).run with
                | .ok (.ok r₂), .ok (.ok payment), .ok (.ok r) =>
                  decide (payment.count = 2) &&
                    decide (r.loan'.totalValueOutstanding = r₂.loan'.totalValueOutstanding) &&
                    decide (r.loan'.principalOutstanding = r₂.loan'.principalOutstanding) &&
                    decide (r.loan'.managementFeeOutstanding = r₂.loan'.managementFeeOutstanding) &&
                    decide (r.loan'.paymentRemaining = r₂.loan'.paymentRemaining) &&
                    decide (r.pool'.assetsAvailable.toRat ≠ r₂.pool'.assetsAvailable.toRat)
                | _, _, _ => false
              | .error _ => false
            | .error _ => false
          | .error _ => false
        | _ => false
      | .error _ => false
    | .error _ => false
  | none => false

private lemma splitCheck_true : splitCheck = true := by native_decide

/-- **Two scheduled payments paid together can leave a different vault than paid one at a time.** Above `10^16`
base units each credit is floored to `10^-5`, so two credits lose more than one. The loan ends the same. -/
lemma Loan.regularPayment_split_witness :
    ∃ (loan : Loan) (v : Vault) (now : UInt32) (amount₁ amount₂ amount : Number)
      (r₁ r₂ r : LoanWithAmounts Vault) (payment : UnsettledPayment Vault),
      (loan.regularPayment v amount₁ now).run = .ok (.ok r₁) ∧
      (r₁.loan'.regularPayment r₁.pool' amount₂ now).run = .ok (.ok r₂) ∧
      amount₁.operator_add amount₂ .to_nearest = .ok amount ∧
      (loan.payInstalments v .regular amount now).run = .ok (.ok payment) ∧ payment.count = 2 ∧
      (loan.regularPayment v amount now).run = .ok (.ok r) ∧
      r.loan'.totalValueOutstanding = r₂.loan'.totalValueOutstanding ∧
      r.loan'.principalOutstanding = r₂.loan'.principalOutstanding ∧
      r.loan'.managementFeeOutstanding = r₂.loan'.managementFeeOutstanding ∧
      r.loan'.paymentRemaining = r₂.loan'.paymentRemaining ∧
      r.pool'.assetsAvailable.toRat ≠ r₂.pool'.assetsAvailable.toRat := by
  have h := splitCheck_true
  unfold splitCheck at h
  split at h
  · rename_i loan v _
    split at h
    · split at h
      · rename_i due₁ _
        split at h
        · rename_i r₁ hr₁
          split at h
          · split at h
            · rename_i due₂ _
              split at h
              · rename_i amount hamount
                split at h
                · rename_i r₂ payment r hr₂ hp hr
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
                  exact ⟨loan, v, _, due₁, due₂, amount, r₁, r₂, r, payment, hr₁, hr₂, hamount, hp, h1, hr, h2, h3, h4,
                    h5, h6⟩
                · exact absurd h (by decide)
              · exact absurd h (by decide)
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
