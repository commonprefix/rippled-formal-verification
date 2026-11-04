import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Loan.Common.CountMonotone
import XRPL.Properties.Lending.Loan.Common.SetFeeBound
import XRPL.Properties.Lending.Loan.Common.SetVault

/-! # Proof bodies for LoanSet on a ledger

A successful LoanSet on broker `j` ran `Loan.create` on the ledger's copy of that broker, with a principal its
preflight and checks accepted. The ledger after holds the created vault and reads the created loan at the end of
the loan list. Each proof below reaches that create and reuses the proof for `Loan.create`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {l l' : LendingLedger} {j : Nat} {principal : Number} {rates : LoanRates} {fees : LoanFees}
  {paymentInterval paymentTotal gracePeriod : Option UInt32} {startDate : UInt32} {twoStep allowsOverpayment : Bool}
  {loan' : Loan}

/-- A successful LoanSet on broker `j` created its loan on the stored broker, with a principal that is normalized,
above zero and stored exactly. The ledger after holds the created vault and reads the created loan. -/
private lemma LendingLedger.loanSet_create
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l')) :
    ∃ broker r, l.broker? j = some broker ∧ principal.isNormalized ∧ 0 < principal.toRat ∧
      STAmount.isRounded broker.numericType principal = false ∧
      (Loan.create broker l.vault principal rates fees
        (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep) allowsOverpayment
        twoStep).run = .ok (.ok r) ∧
      l'.LoanAt l.loans.length r.loan' ∧ l'.vault = r.pool' := by
  obtain ⟨broker, r, hb, hpre, -, hc, hcr, -, hv, hat, -, -⟩ := LendingLedger.loanSet_ok h
  obtain ⟨hp, hpos⟩ := LendingTx.preflight_loanSet_principal l j principal rates fees paymentInterval paymentTotal
    gracePeriod startDate twoStep allowsOverpayment (by rw [hpre]; rfl)
  exact ⟨broker, r, hb, hp, hpos, Loan.canCreate_exact broker l.vault principal fees _ _ _ hc principal
    List.mem_cons_self, hcr, hat, hv⟩

/-- Proof body of `create_periodicPayment_principal_monotone`. -/
lemma LendingLedger.create_periodicPayment_principal_monotone_proof {l₁ l₂ : LendingLedger}
    {principal₁ principal₂ : Number} {loan₁ loan₂ : Loan}
    (h₁ : (l.apply (.loanSet j principal₁ rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₁))
    (h₂ : (l.apply (.loanSet j principal₂ rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₂))
    (hat₁ : l₁.LoanAt l.loans.length loan₁) (hat₂ : l₂.LoanAt l.loans.length loan₂)
    (hle : principal₁.toRat ≤ principal₂.toRat) :
    loan₁.toExact.periodicPayment ≤ loan₂.toExact.periodicPayment := by
  obtain ⟨b, r₁, hb, hp₁, hpos, -, hc₁, hr₁, -⟩ := LendingLedger.loanSet_create h₁
  obtain ⟨b₂, r₂, hb₂, hp₂, -, -, hc₂, hr₂, -⟩ := LendingLedger.loanSet_create h₂
  obtain rfl := Option.some.inj (hb.symm.trans hb₂)
  obtain rfl := hr₁.eq hat₁
  obtain rfl := hr₂.eq hat₂
  exact Loan.create_periodicPayment_principal_monotone_proof b l.vault principal₁ principal₂ rates fees _
    allowsOverpayment twoStep r₁ r₂ hp₁ hp₂ hpos hc₁ hc₂ hle

/-- Proof body of `Lending.create_periodicPayment_monotone`. -/
lemma LendingLedger.create_periodicPayment_count_antitone_proof {l₁ l₂ : LendingLedger}
    {paymentTotal₁ paymentTotal₂ : Option UInt32} {loan₁ loan₂ : Loan}
    (h₁ : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₁ gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₁))
    (h₂ : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal₂ gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l₂))
    (hat₁ : l₁.LoanAt l.loans.length loan₁) (hat₂ : l₂.LoanAt l.loans.length loan₂)
    (hlt : paymentTotal₁.getD defaultPaymentTotal < paymentTotal₂.getD defaultPaymentTotal)
    (hstep : paymentTotal₂.getD defaultPaymentTotal = paymentTotal₁.getD defaultPaymentTotal + 1) :
    loan₂.toExact.periodicPayment ≤ loan₁.toExact.periodicPayment := by
  obtain ⟨b, r₁, hb, hp, hpos, hst, hc₁, hr₁, -⟩ := LendingLedger.loanSet_create h₁
  obtain ⟨b₂, r₂, hb₂, -, -, -, hc₂, hr₂, -⟩ := LendingLedger.loanSet_create h₂
  obtain rfl := Option.some.inj (hb.symm.trans hb₂)
  obtain rfl := hr₁.eq hat₁
  obtain rfl := hr₂.eq hat₂
  exact Loan.create_periodicPayment_count_antitone_proof b l.vault principal rates fees _ _ allowsOverpayment
    twoStep r₁ r₂ hp hpos hst rfl hlt hstep hc₁ hc₂

/-- Proof body of the PrincipalRequested part of `Lending.create_value`. -/
lemma LendingLedger.create_covers_principal_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') (hrate : rates.interestRate ≠ 0) :
    principal.toRat < loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat := by
  obtain ⟨b, r, -, hp, -, hst, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_covers_principal_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hp hst hc
    hrate

/-- Proof body of `create_managementFee_upper_bound`. -/
lemma LendingLedger.create_managementFee_upper_bound_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan')
    (hfit : (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) *
      (loan'.broker.managementFeeRate.toNat : ℚ) < 2 ^ 63 * 10 ^ loan'.toExact.loanScale) :
    loan'.toExact.managementFeeOutstanding - (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) ≤ 0 := by
  obtain ⟨b, r, -, -, -, hst, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_managementFee_upper_bound_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hst
    hc hfit

/-- Proof body of `create_managementFee_lower_bound`. -/
lemma LendingLedger.create_managementFee_lower_bound_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    (loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (loan'.toExact.totalValueOutstanding - loan'.toExact.principalOutstanding) -
      loan'.toExact.managementFeeOutstanding < 10 ^ loan'.toExact.loanScale := by
  obtain ⟨b, r, -, -, -, -, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_managementFee_lower_bound_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hc

/-- Proof body of the upper bound part of `Lending.create_value`. -/
lemma LendingLedger.create_value_upper_bound_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') (hrate : rates.interestRate ≠ 0) :
    loan'.toExact.totalValueOutstanding - loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat <
      10 ^ loan'.toExact.loanScale := by
  obtain ⟨b, r, -, -, -, -, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_value_upper_bound_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hc hrate

/-- Proof body of the lower bound part of `Lending.create_value`. -/
lemma LendingLedger.create_value_lower_bound_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') (hrate : rates.interestRate ≠ 0) :
    loan'.toExact.periodicPayment * loan'.toExact.paymentTotal.toNat - loan'.toExact.totalValueOutstanding ≤ 0 := by
  obtain ⟨b, r, -, -, -, -, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_value_lower_bound_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hc hrate

/-- Proof body of the zero InterestRate line of `Lending.create_value`. -/
lemma LendingLedger.create_zero_rate_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') (hrate : rates.interestRate = 0) :
    loan'.toExact.totalValueOutstanding = principal.toRat := by
  obtain ⟨b, r, -, hp, -, hst, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_zero_rate_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hp hst hc hrate

/-- Proof body of the DebtMaximum part of `Lending.create_updates`. -/
lemma LendingLedger.create_within_debtMaximum_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') (hmax : loan'.broker.toExact.debtMaximum ≠ 0) :
    loan'.broker.toExact.debtTotal ≤ loan'.broker.toExact.debtMaximum := by
  obtain ⟨b, r, -, -, -, -, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_within_debtMaximum_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hc hmax

/-- Proof body of the minCover part of `Lending.create_updates`. -/
lemma LendingLedger.create_meets_minCover_proof
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    loan'.broker.HasMinimumCover l.vault.baseExponent := by
  obtain ⟨b, r, -, -, -, -, hc, hr, -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr.eq hat'
  exact Loan.create_meets_minCover_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hc

/-- Proof body of the LoanScale line of `Lending.create_updates`. -/
lemma LendingLedger.create_loanScale_proof (hr : l.Reachable)
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    loan'.toExact.loanScale = l.vault.baseExponent := by
  obtain ⟨b, r, hb, hp, hpos, hst, hc, hr', -⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr'.eq hat'
  exact Loan.create_loanScale_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hp hpos hst
    (hr.scaleInv.brokers j b hb) hc

/-- Proof body of the AssetsTotal line of `Lending.create_updates`. -/
lemma LendingLedger.create_assetsTotal_unchanged_proof (hr : l.Reachable)
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l')) :
    l'.vault.toExact.assetsTotal = l.vault.toExact.assetsTotal ∧
      l'.vault.toExact.lossUnrealized = l.vault.toExact.lossUnrealized := by
  obtain ⟨b, r, hb, hp, hpos, hst, hc, -, hv⟩ := LendingLedger.loanSet_create h
  rw [hv]
  exact Loan.create_assetsTotal_unchanged_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hp
    hpos hst (hr.createGrid hb hp hpos hst hc) hc

/-- Proof body of the PrincipalRequested line of `Lending.create_updates`. -/
lemma LendingLedger.create_principal_proof (hr : l.Reachable) {broker : LoanBroker}
    (hb : l.broker? j = some broker)
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    l.vault.toExact.assetsAvailable - l'.vault.toExact.assetsAvailable = principal.toRat ∧
      l'.vault.toExact.assetsDeployed - l.vault.toExact.assetsDeployed = principal.toRat ∧
      loan'.broker.toExact.debtTotal - broker.toExact.debtTotal = principal.toRat ∧
      l'.vault.toExact.assetsReserved - l.vault.toExact.assetsReserved = if twoStep then principal.toRat else 0 := by
  obtain ⟨b, r, hb', hp, hpos, hst, hc, hr', hv⟩ := LendingLedger.loanSet_create h
  obtain rfl := Option.some.inj (hb.symm.trans hb')
  obtain rfl := hr'.eq hat'
  rw [hv]
  exact Loan.create_principal_proof broker l.vault principal rates fees _ allowsOverpayment twoStep r hp hpos hst
    (hr.createGrid hb hp hpos hst hc) hc

/-- A LoanSet -> YieldUnrealized' = YieldUnrealized + interestDue when the new loan is active, unchanged when it is
pending. -/
lemma LendingLedger.create_yield_proof (hr : l.Reachable)
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l'))
    (hat' : l'.LoanAt l.loans.length loan') :
    l'.vault.toExact.yieldUnrealized =
      l.vault.toExact.yieldUnrealized + if twoStep then 0 else loan'.toExact.interestDue := by
  obtain ⟨b, r, hb, hp, hpos, hst, hc, hr', hv⟩ := LendingLedger.loanSet_create h
  obtain rfl := hr'.eq hat'
  rw [hv]
  exact Loan.create_yield_proof b l.vault principal rates fees _ allowsOverpayment twoStep r hp hpos hst
    (hr.createGrid hb hp hpos hst hc) hc

end XRPL.Model.Lending
