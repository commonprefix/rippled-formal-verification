import XRPL.Properties.Lending.Loan.Common.SetLedger
import XRPL.Properties.Lending.Loan.Common.SetLedgerWitness

/-! # `LoanSet`

What a new loan stores, and what it changes in the vault and the broker. "Create" is a successful LoanSet on
broker `j` of the ledger `l`, the primed values are the ones after it. The new loan is the last one on `l'`. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

variable (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
  (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32) (twoStep allowsOverpayment : Bool)
  (loan' : Loan)

/-- Create with a larger PrincipalRequested, other terms equal -> PeriodicPayment never decreases. -/
theorem Lending.create_periodicPayment_principal_monotone (l₁ l₂ : LendingLedger) (principal₁ principal₂ : Number)
    (h₁ : (l.apply (.loanSet j principal₁ rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₁))
    (h₂ : (l.apply (.loanSet j principal₂ rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₂))
    (loan₁ loan₂ : Loan) (hat₁ : l₁.LoanAt l.loans.length loan₁) (hat₂ : l₂.LoanAt l.loans.length loan₂)
    (hle : principal₁.toRat ≤ principal₂.toRat) :
    loan₁.toExact.periodicPayment ≤ loan₂.toExact.periodicPayment :=
  LendingLedger.create_periodicPayment_principal_monotone_proof h₁ h₂ hat₁ hat₂ hle

/-- Create with other terms equal -> a larger PaymentTotal never raises PeriodicPayment. The InterestRate line has
only a witness, a larger InterestRate can lower PeriodicPayment. -/
theorem Lending.create_periodicPayment_monotone (l₁ l₂ : LendingLedger)
    (paymentTotal₁ paymentTotal₂ : Option UInt32)
    (h₁ : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₁ gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₁))
    (h₂ : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₂ gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₂))
    (loan₁ loan₂ : Loan) (hat₁ : l₁.LoanAt l.loans.length loan₁) (hat₂ : l₂.LoanAt l.loans.length loan₂)
    (hlt : paymentTotal₁.getD defaultPaymentTotal < paymentTotal₂.getD defaultPaymentTotal)
    -- the larger PaymentTotal is one more
    (hstep : paymentTotal₂.getD defaultPaymentTotal = paymentTotal₁.getD defaultPaymentTotal + 1) :
    loan₂.toExact.periodicPayment ≤ loan₁.toExact.periodicPayment :=
  LendingLedger.create_periodicPayment_count_antitone_proof h₁ h₂ hat₁ hat₂ hlt hstep

/-- Witness: a run where a higher InterestRate lowers PeriodicPayment. Ten payments 60 seconds apart
on `10^6`: InterestRate 14 gives a lower payment than InterestRate 13. -/
theorem Lending.create_periodicPayment_monotone_rate_attained :
    ∃ (l l₁ l₂ : LendingLedger) (j : Nat) (principal : Number) (rates₁ rates₂ : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan₁ loan₂ : Loan),
      l.Reachable ∧ rates₂ = { rates₁ with interestRate := rates₂.interestRate } ∧
      rates₁.interestRate < rates₂.interestRate ∧
      (l.apply (.loanSet j principal rates₁ fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₁) ∧
      (l.apply (.loanSet j principal rates₂ fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₂) ∧
      l₁.LoanAt l.loans.length loan₁ ∧ l₂.LoanAt l.loans.length loan₂ ∧
      loan₂.toExact.periodicPayment < loan₁.toExact.periodicPayment :=
  LendingLedger.create_periodicPayment_rate_monotone_witness

/-- Witness: a run where two more payments raise PeriodicPayment. At InterestRate 100% and 15396294 payments 60
seconds apart, 15396296 payments raise it by one unit in its 19th digit. -/
theorem Lending.create_periodicPayment_monotone_count_attained :
    ∃ (l l₁ l₂ : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal₁ paymentTotal₂ gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan₁ loan₂ : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₁ gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₁) ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₂ gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l₂) ∧
      l₁.LoanAt l.loans.length loan₁ ∧ l₂.LoanAt l.loans.length loan₂ ∧
      paymentTotal₁.getD defaultPaymentTotal < paymentTotal₂.getD defaultPaymentTotal ∧
      loan₁.toExact.periodicPayment < loan₂.toExact.periodicPayment :=
  LendingLedger.create_periodicPayment_count_antitone_witness

/-- Create -> with InterestRate ≠ 0 the scheduled payments sum above PrincipalRequested and TotalValueOutstanding is
less than 1 ULP above that sum, never below it. With InterestRate = 0 TotalValueOutstanding = PrincipalRequested. -/
theorem Lending.create_value
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    (rates.interestRate ≠ 0 →
      principal.toRat < loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat ∧
      loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat - loan'.toExact.totalValueOutstanding ≤ 0 ∧
      loan'.toExact.totalValueOutstanding - loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat <
        10 ^ loan'.toExact.loanScale) ∧
    (rates.interestRate = 0 → loan'.toExact.totalValueOutstanding = principal.toRat) :=
  ⟨fun hrate => ⟨LendingLedger.create_covers_principal_proof h hat' hrate,
      LendingLedger.create_value_lower_bound_proof h hat' hrate,
      LendingLedger.create_value_upper_bound_proof h hat' hrate⟩,
    LendingLedger.create_zero_rate_proof h hat'⟩

/-- Witness: a run where they are equal. One payment after a year at 10% on `10`: both are `11`. -/
theorem Lending.create_value_lower_bound_attained :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧ rates.interestRate ≠ 0 ∧
      loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat - loan'.toExact.totalValueOutstanding = 0 :=
  LendingLedger.create_value_lower_bound_witness

/-- Witness: a run where the difference is just under 1 ULP, above `1 − 10^-10` ULP. One payment after
60 seconds at InterestRate 1 on one base unit. -/
theorem Lending.create_value_upper_bound_attained :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧ rates.interestRate ≠ 0 ∧
      (1 - 1 / 10 ^ 10 : ℚ) * 10 ^ loan'.toExact.loanScale <
        loan'.toExact.totalValueOutstanding - loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat :=
  LendingLedger.create_value_upper_bound_witness

/-- Create -> ManagementFeeOutstanding − ManagementFeeRate × (TotalValueOutstanding − PrincipalOutstanding) ≤ 0.
`hfit` - interest in LoanScale units × ManagementFeeRate in tenth bips below `2^63`, so the 19-digit product is exact -/
theorem Lending.create_managementFee_upper_bound
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan')
    (hfit : (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) *
      (loan'.broker.managementFeeRate.toNat : ℚ) < 2 ^ 63 * 10 ^ loan'.toExact.loanScale) :
    loan'.toExact.managementFeeOutstanding - (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) ≤ 0 :=
  LendingLedger.create_managementFee_upper_bound_proof h hat' hfit

/-- Witness: a run where ManagementFeeOutstanding is larger. One payment after fifteen years at 100% on
`615000000.00667` with a 9.999% fee: the fee share `922407750.0100039995` rounds up to `922407750.010004`. -/
theorem Lending.create_managementFee_upper_bound_attained :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧
      0 < loan'.toExact.managementFeeOutstanding - (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
        (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) :=
  LendingLedger.create_managementFee_upper_bound_witness

/-- Create -> ManagementFeeRate × (TotalValueOutstanding − PrincipalOutstanding) − ManagementFeeOutstanding
< 1 ULP at LoanScale. -/
theorem Lending.create_managementFee_lower_bound
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) -
      loan'.toExact.managementFeeOutstanding < 10 ^ loan'.toExact.loanScale :=
  LendingLedger.create_managementFee_lower_bound_proof h hat'

/-- Witness: a run where the difference is just under 1 ULP, 0.99999 ULP. One payment after a year at 10% on
`0.10001` with a 9.999% fee: the interest is 10001 units and its fee share 999.99999 units. -/
theorem Lending.create_managementFee_lower_bound_attained :
    ∃ (l l' : LendingLedger) (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool) (loan' : Loan),
      l.Reachable ∧
      (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .ok (.ok l') ∧ l'.LoanAt l.loans.length loan' ∧
      (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
        (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) -
        loan'.toExact.managementFeeOutstanding = 99999 / 100000 * 10 ^ loan'.toExact.loanScale :=
  LendingLedger.create_managementFee_lower_bound_witness

/-- A new loan -> AssetsTotal and LossUnrealized unchanged, the principal leaves AssetsAvailable for AssetsDeployed and
DebtTotal, an active loan pays it out as amountToBorrower + OriginationFee, LoanScale = base scale, broker in limits. -/
theorem Lending.create_updates (hr : l.Reachable) (broker : LoanBroker) (hb : l.broker? j = some broker)
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan')
    -- `r` - the create the LoanSet runs, `r.amountToBorrower` is what the vault sends the borrower
    (r : LoanWithDisbursement Vault)
    (hc : (Loan.create broker l.vault principal rates fees
      (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep) allowsOverpayment
      twoStep).run = .ok (.ok r)) :
    (l'.vault.toExact.assetsTotal = l.vault.toExact.assetsTotal ∧
      l'.vault.toExact.lossUnrealized = l.vault.toExact.lossUnrealized) ∧
    (l.vault.toExact.assetsAvailable - l'.vault.toExact.assetsAvailable = principal.toRat ∧
      l'.vault.toExact.assetsDeployed - l.vault.toExact.assetsDeployed = principal.toRat ∧
      loan'.broker.toExact.debtTotal - broker.toExact.debtTotal = principal.toRat ∧
      l'.vault.toExact.assetsReserved - l.vault.toExact.assetsReserved = if twoStep then principal.toRat else 0) ∧
    ((twoStep = false →
      r.amountToBorrower.toRat + fees.originationFee.toRat = principal.toRat ∧
        l.vault.toExact.assetsAvailable - l'.vault.toExact.assetsAvailable =
          r.amountToBorrower.toRat + fees.originationFee.toRat) ∧
      (twoStep = true → r.amountToBorrower = Number.zero)) ∧
    loan'.toExact.loanScale = l.vault.baseExponent ∧
    (loan'.broker.toExact.debtMaximum ≠ 0 → loan'.broker.toExact.debtTotal ≤ loan'.broker.toExact.debtMaximum) ∧
    loan'.broker.HasMinimumCover l.vault.baseExponent :=
  ⟨LendingLedger.create_assetsTotal_unchanged_proof hr h, LendingLedger.create_principal_proof hr hb h hat',
    LendingLedger.create_amountToBorrower_proof hr hb h hat' r hc, LendingLedger.create_loanScale_proof hr h hat',
    LendingLedger.create_within_debtMaximum_proof h hat',
    LendingLedger.create_meets_minCover_proof h hat'⟩

end XRPL.Model
