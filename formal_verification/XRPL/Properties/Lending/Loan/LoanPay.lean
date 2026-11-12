import XRPL.Properties.Lending.Loan.Common.PayLedgerLoan
import XRPL.Properties.Lending.Loan.Common.PayLedgerFunds
import XRPL.Properties.Lending.Loan.Common.PayLedgerDue
import XRPL.Properties.Lending.Loan.Common.PayLedgerWitness
import XRPL.Properties.Lending.Loan.Common.PayLedgerDueWitness
import XRPL.Properties.Lending.Loan.Common.OverpaymentFees
import XRPL.Properties.Lending.Loan.Common.VaultCredit
import XRPL.Properties.Lending.Loan.Common.VaultCreditWitness
import XRPL.Properties.Lending.Loan.Common.FullPaymentBeforeStartWitness

/-! # `LoanPay`

What a LoanPay transaction pays and what it changes in the loan, the vault and the broker. "Payment" is a successful
LoanPay of any type from ledger `l` to `l'`, a scheduled payment is one instalment of `Loan.payInstalments`, primed
values are the ones after it, read from `l'`. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

variable (l : LendingLedger)

/-- Now ≤ NextPaymentDueDate -> regular, full and overpayments pass the date check and a late payment
fails, otherwise only a late payment passes. `hpre` - the LoanPay preflight, which reads only the amount -/
theorem Lending.payment_lateness (hr : l.Reachable) (i : Nat) (amount : Number) (loan : Loan) (hat : l.LoanAt i loan)
    (hc : loan.canPay .regular = .tesSUCCESS) -- LoanPay preclaim: the loan is accepted and not paid off
    (hpre : (LendingTx.loanPay i .regular amount).preflight l = .tesSUCCESS) :
    (l.now ≤ loan.nextPaymentDueDate →
      (l.apply (.loanPay i .regular amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .full amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .overpayment amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .late amount)).run = .ok (.error .tecTOO_SOON)) ∧
    (loan.nextPaymentDueDate < l.now →
      (l.apply (.loanPay i .regular amount)).run = .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .full amount)).run = .ok (.error .tecEXPIRED) ∧
        (loan.allowsOverpayment = true →
          (l.apply (.loanPay i .overpayment amount)).run = .ok (.error .tecEXPIRED)) ∧
        (l.apply (.loanPay i .late amount)).run ≠ .ok (.error .tecTOO_SOON)) :=
  LendingLedger.payment_lateness_proof l hr i amount loan hat hc hpre

/-- Payment -> principalPaid + interestPaid + feePaid ≤ requestedAmount, and each scheduled payment charges exactly
its totalDue: the value it takes off the loan plus LoanServiceFee, and LatePaymentFee and ⌊late interest⌉ when late. -/
theorem Lending.payment_charge (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok p)) :
    -- the amount due fits 16 digits at LoanScale
    (p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale →
      p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ≤ amount.toRat) ∧
    -- a scheduled payment the LoanPay pays: the loan `lk` it starts from, its instalment `pc` and its charge `q`
    (∀ (lk : Loan) (pc : PaymentComponents) (q : UnsettledPayment Vault),
      loan.PaysInstalment l.vault amount l.now paymentType lk pc q →
      q.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale →
      q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat = q.totalPaid.toRat ∧
        (paymentType = .regular → q.totalPaid.toRat = lk.totalValueOutstanding.toRat -
          q.loan.totalValueOutstanding.toRat + lk.fees.serviceFee.toRat) ∧
        (paymentType = .late → ∃ li lr, loanLatePaymentInterest lk.principalOutstanding lk.rates.lateInterestRate
            l.now lk.nextPaymentDueDate = .ok li ∧
          STAmount.roundToNumericType lk.broker.numericType li .to_nearest (some lk.loanScale) = .ok lr ∧
          q.totalPaid.toRat = lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat +
            lk.fees.serviceFee.toRat + lk.fees.latePaymentFee.toRat + lr.toRat)) :=
  ⟨LendingLedger.payment_charge_le_amount_proof l hr l' i paymentType amount h loan hat p hp,
    LendingLedger.payment_split_proof l hr l' i paymentType amount h loan hat⟩

/-- Witness: a run where principalPaid + interestPaid + feePaid > requestedAmount. A LoanSet with LoanServiceFee
`10^30`, then a regular payment of exactly its totalDue, which drops the instalment's value. -/
theorem Lending.payment_charge_le_amount_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧
      amount.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat :=
  LendingLedger.payment_charge_le_amount_witness

/-- Witness: a run for a regular payment where principalPaid + interestPaid + feePaid > totalDue. A LoanSet with
LoanServiceFee `10^30`, then one instalment of exactly its totalDue, which drops the instalment's value. -/
theorem Lending.payment_charge_split_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧
      q.totalPaid.toRat < q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat :=
  LendingLedger.payment_split_witness

/-- Witness: a run for a late payment where principalPaid + interestPaid + feePaid > totalDue. A LoanSet with
LatePaymentFee `10^30`, then a late payment of exactly its totalDue, which drops the instalment's value. -/
theorem Lending.payment_charge_late_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (li lr : Number),
      l.Reachable ∧ (l.apply (.loanPay i .late amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .late amount l.now).run = .ok (.ok p) ∧
      loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate l.now loan.nextPaymentDueDate =
        .ok li ∧ STAmount.roundToNumericType loan.broker.numericType li .to_nearest (some loan.loanScale) = .ok lr ∧
      p.totalPaid.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ∧
      p.totalPaid.toRat < loan.totalValueOutstanding.toRat - p.loan.totalValueOutstanding.toRat +
        loan.fees.serviceFee.toRat + loan.fees.latePaymentFee.toRat + lr.toRat :=
  LendingLedger.latePayment_cost_witness

/-- Successful payment -> PaymentRemaining and TotalValueOutstanding strictly decrease.
`hlate` - the instalment of a late payment takes some value off the loan unless it is the last -/
theorem Lending.payment_decreases (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan')
    (hlate : paymentType = .late → ∀ pc, loan.paymentComponents .late l.now = .ok pc → pc.isFinal = false →
      0 < pc.totalValueDelta.toRat) :
    loan'.paymentRemaining < loan.paymentRemaining ∧
      loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat :=
  LendingLedger.payment_decreases_proof l hr l' i paymentType amount h loan loan' hat hat' hlate

/-- Witness: a run where a late payment leaves TotalValueOutstanding as it was. A loan of 6 at 14.5% in 16 yearly
instalments with a 10% management fee reaches an instalment of value 0, and its late interest alone is paid. -/
theorem Lending.payment_decreases_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan loan' : Loan) (pc : PaymentComponents),
      l.Reachable ∧ (l.apply (.loanPay i .late amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.paymentComponents .late l.now = .ok pc ∧ pc.isFinal = false ∧
      pc.totalValueDelta.toRat = 0 ∧ loan'.paymentRemaining < loan.paymentRemaining ∧
      loan'.principalOutstanding = loan.principalOutstanding ∧
      loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat :=
  LendingLedger.payment_decreases_witness

/-- Payment when the broker is at or above minCover -> CoverAvailable' = CoverAvailable. -/
theorem Lending.payment_cover_unchanged (l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan')
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok true) :
    loan'.broker.coverAvailable = loan.broker.coverAvailable :=
  LendingLedger.payment_fees_proof l l' i paymentType amount h loan loan' hat hat' hcover

/-- Payment when the broker is below minCover -> CoverAvailable' − CoverAvailable is at most feePaid and less than
1 ULP below it at the scale of CoverAvailable', and it is amountToBroker. -/
theorem Lending.payment_fees (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (r : LoanWithAmounts Vault) (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    -- for an XRP or MPT broker, CoverAvailable + feePaid is below `2^63` base units, within the asset's supply
    ((loan.broker.numericType.isIntegral = true → loan.broker.coverAvailable.toRat +
        payment.amounts.feePaid.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) →
      (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat ≤ 0) ∧
    -- the cover is not coarsened: CoverAvailable + feePaid stays a base unit below 10^16 base units (FV_M4_25)
    (loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat ≤
        (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent →
      (∀ e, numberExponent loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType = .ok e →
        payment.amounts.feePaid.toRat - (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) <
          10 ^ e) ∧
        loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat = r.amountToBroker.toRat) :=
  ⟨LendingLedger.payment_fees_upper_bound_proof l hr l' i paymentType amount h loan loan' hat hat' payment hcover
      hpay,
    fun hroom => ⟨fun e he => by
      have := LendingLedger.payment_fees_lower_bound_proof l hr l' i paymentType amount h loan loan' hat hat' payment
        hcover hpay hroom e he
      linarith,
      LendingLedger.payment_cover_amountToBroker_proof l hr l' i paymentType amount h loan loan' hat hat' payment
        hcover hpay r hok hroom⟩⟩

/-- Witness: a run where (CoverAvailable' − CoverAvailable) − feePaid = 0. The large loan paid a minute late with a
10% management fee, after a default left the cover at `0.5`. -/
theorem Lending.payment_fees_upper_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan loan' : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (loan.broker.numericType.isIntegral = true → loan.broker.coverAvailable.toRat +
        payment.amounts.feePaid.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat = 0 :=
  LendingLedger.payment_fees_upper_bound_witness

/-- Witness: a run on a coarsened cover where feePaid − (CoverAvailable' − CoverAvailable) = 1 ULP. A 10% management
fee on a loan paid 32 years late lifts a cover of `0.5` to the scale `10^0`, on a Scale 1 vault. -/
theorem Lending.payment_fees_lower_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan loan' : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      numberExponent loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType = .ok e ∧
      payment.amounts.feePaid.toRat - (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) =
        10 ^ e :=
  let ⟨l, l', i, pt, amount, loan, loan', payment, e, hr, h, hat, hat', hc, hp, he, hd⟩ :=
    LendingLedger.payment_fees_lower_bound_witness
  ⟨l, l', i, pt, amount, loan, loan', payment, e, hr, h, hat, hat', hc, hp, he, by linarith⟩

/-- Regular payment -> every scheduled payment it pays has totalDue ≤ ⌈PeriodicPayment⌉ + LoanServiceFee.
`hlast` - the last scheduled payment takes the rounding the others leave. `hfit` - the amount due fits 16 digits -/
theorem Lending.regularPayment_amount (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p))
    (k : Nat) (hk : k < p.count) (lk : Loan) (hl : loan.ScheduledBefore l.now k lk) (pc : PaymentComponents)
    (due pp' : Number) (hpc : lk.paymentComponents .regular l.now = .ok pc) (hdue : pc.totalDue = .ok due)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp')
    (hlast : lk.paymentRemaining ≠ 1) (hfit : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    due.toRat ≤ pp'.toRat + loan.fees.serviceFee.toRat :=
  LendingLedger.regularPayment_amount_proof l hr l' i amount h loan hat p hp k hk lk hl pc due pp' hpc hdue hpp hlast
    hfit

/-- Witness: a run where the last scheduled payment has a larger totalDue. A loan of `190.623` at 12% over 36 monthly
payments with a 0.1% management fee owes `6.31645547` after 35 payments, ⌈PeriodicPayment⌉ is `6.31645546`. -/
theorem Lending.regularPayment_amount_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (k : Nat)
      (lk : Loan) (pc : PaymentComponents) (due pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore l.now k lk ∧ lk.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale ∧
      pp'.toRat + loan.fees.serviceFee.toRat < due.toRat :=
  LendingLedger.regularPayment_amount_last_witness

/-- Witness: a run where a scheduled payment that is not the last has a larger totalDue. With LoanServiceFee `10^17`
the 19-digit totalDue rounds ⌈PeriodicPayment⌉ `33.37` up to `33.4`. -/
theorem Lending.regularPayment_amount_fee_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (k : Nat)
      (lk : Loan) (pc : PaymentComponents) (due pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore l.now k lk ∧ lk.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ lk.paymentRemaining ≠ 1 ∧ pp'.toRat + loan.fees.serviceFee.toRat < due.toRat :=
  LendingLedger.regularPayment_amount_fee_witness

/-- Regular payment, a scheduled payment that isn't the last -> (TotalValueOutstanding − TotalValueOutstanding') −
PeriodicPayment < 1 ULP at LoanScale. -/
theorem Lending.regularPayment_periodicPayment (hr : l.Reachable) (i : Nat) (amount : Number) (loan : Loan)
    (hat : l.LoanAt i loan) (lk : Loan) (pc : PaymentComponents) (q : UnsettledPayment Vault)
    -- a scheduled payment the LoanPay pays: the loan `lk` it starts from, its instalment `pc` and its charge `q`
    (hq : loan.PaysInstalment l.vault amount l.now .regular lk pc q) (hleft : q.loan.paymentRemaining ≠ 0) :
    lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat - loan.periodicPayment.toRat <
      10 ^ loan.loanScale :=
  LendingLedger.regularPayment_periodicPayment_proof l hr i amount loan hat lk pc q hq hleft

/-- Witness: a run where ⌈principal⌉ and ⌊interest⌋ put a payment 1.33 ULP below PeriodicPayment. A loan of
`0.048832` at 15% over 3 monthly payments: the second takes `0.016679`, PeriodicPayment is `0.0166803315…`. -/
theorem Lending.regularPayment_periodicPayment_below_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining ≠ 0 ∧
      10 ^ loan.loanScale ≤ loan.periodicPayment.toRat -
        (lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat) :=
  LendingLedger.regularPayment_periodicPayment_below_witness

/-- Witness: a run where ⌊management fee⌉ puts the last payment 1 ULP above ⌈PeriodicPayment⌉. A loan of `98763`
at 21% over 2 monthly payments with a 6% fee: the last is `50665`, ⌈PeriodicPayment⌉ is `50664`. -/
theorem Lending.regularPayment_periodicPayment_last_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault) (pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining = 0 ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ 0 < lk.totalValueOutstanding.toRat - pp'.toRat :=
  LendingLedger.regularPayment_periodicPayment_last_witness

/-- Witness: a run where ⌊management fee⌉ puts the last payment 2 ULP below ⌈PeriodicPayment⌉. A loan of `6188`
at 9% over 3 monthly payments with a 3% fee: the last is `2092`, ⌈PeriodicPayment⌉ is `2094`. -/
theorem Lending.regularPayment_periodicPayment_last_below_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault) (pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining = 0 ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ 10 ^ loan.loanScale < pp'.toRat - lk.totalValueOutstanding.toRat :=
  LendingLedger.regularPayment_periodicPayment_last_below_witness

/-- Regular payment -> pays as many whole scheduled payments as requestedAmount covers, at most
min(100, PaymentRemaining), and a final scheduled payment pays exactly TotalValueOutstanding and closes the loan. -/
theorem Lending.regularPayment_schedule (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) :
    -- `payment.count` - the scheduled payments it pays, `payment.totalPaid` - their total due
    (1 ≤ payment.count ∧ payment.count ≤ min 100 loan.paymentRemaining.toNat ∧
      amount.operator_lt payment.totalPaid = false ∧
      (payment.count = 100 ∨ payment.loan.paymentRemaining = 0 ∨
        ∀ pc due s, payment.loan.paymentComponents .regular l.now = .ok pc → pc.totalDue = .ok due →
          payment.totalPaid.operator_add due .to_nearest = .ok s → amount.operator_lt s = true)) ∧
    -- `pp'` - ⌈PeriodicPayment⌉, PeriodicPayment rounded up at LoanScale
    (∀ (pc : PaymentComponents) (pp' : Number),
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' →
      (loan.paymentRemaining = 1 ∨ loan.totalValueOutstanding.operator_le pp' = true) →
      loan.paymentComponents .regular l.now = .ok pc →
      pc.totalValueDelta = loan.totalValueOutstanding ∧ loan'.paymentRemaining = 0) :=
  ⟨LendingLedger.regularPayment_count_proof l l' i amount h loan hat payment hpay,
    LendingLedger.regularPayment_final_proof l l' i amount h loan loan' hat hat'⟩

/-- Regular payment of k scheduled payments -> the same loan and vault as k separate payments. Only the broker's
CoverAvailable can differ, by design. `payment.count` - k. `htotal` - the payment stays at base scale -/
theorem Lending.regularPayment_split (hr : l.Reachable) (l₁ : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁)) (loan loan₁ : Loan) (hat : l.LoanAt i loan)
    (hat₁ : l₁.LoanAt i loan₁) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) (l₂ : LendingLedger)
    (loan₂ : Loan) (hsep : l.SeparatePayments i payment.count l₂) (hat₂ : l₂.LoanAt i loan₂)
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker } ∧
      loan₂.broker.toRawLoanBroker =
        { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable } ∧
      l₂.vault = l₁.vault :=
  LendingLedger.regularPayment_split_proof l hr l₁ i amount h loan loan₁ hat hat₁ payment hpay l₂ loan₂ hsep hat₂
    htotal

/-- Witness: a run where the vaults differ. On a reachable vault that loan A's late interest coarsened, loan D's
two instalments of 1.5 credit 3 to AssetsAvailable paid together and 1 each paid one at a time. -/
theorem Lending.regularPayment_split_attained :
    ∃ (l l₁ : LendingLedger) (i : Nat) (amount : Number) (loan loan₁ : Loan) (payment : UnsettledPayment Vault)
      (l₂ : LendingLedger) (loan₂ : Loan),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁) ∧ l.LoanAt i loan ∧
      l₁.LoanAt i loan₁ ∧ (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      payment.count = 2 ∧ l.SeparatePayments i payment.count l₂ ∧ l₂.LoanAt i loan₂ ∧
      loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker } ∧
      loan₂.broker.toRawLoanBroker =
        { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable } ∧
      l₂.vault ≠ l₁.vault :=
  LendingLedger.regularPayment_split_witness

/-- Late payment -> pays exactly one scheduled payment, with the same result for any requestedAmount ≥ totalDue.
`pc` - the late instalment -/
theorem Lending.latePayment_single (l₁ l₂ : LendingLedger) (i : Nat) (a₁ a₂ : Number)
    (h₁ : (l.apply (.loanPay i .late a₁)).run = .ok (.ok l₁)) (h₂ : (l.apply (.loanPay i .late a₂)).run = .ok (.ok l₂))
    (loan loan₁ : Loan) (hat : l.LoanAt i loan) (hat₁ : l₁.LoanAt i loan₁) (pc : PaymentComponents)
    (totalDue : Number) (hpc : loan.paymentComponents .late l.now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (ha₁ : a₁.operator_lt totalDue = false) (ha₂ : a₂.operator_lt totalDue = false) :
    l₁ = l₂ ∧ loan₁.paymentRemaining = if pc.isFinal then 0 else loan.paymentRemaining - 1 :=
  LendingLedger.latePayment_single_proof l l₁ l₂ i a₁ a₂ h₁ h₂ loan loan₁ hat hat₁ pc totalDue hpc hdue ha₁ ha₂

/-- When CloseInterestRate = 0 and ClosePaymentFee ≤ LoanServiceFee -> a full payment never costs more than the
remaining regular payments. -/
theorem Lending.fullPayment_cheaper (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok p))
    (hclose : loan.rates.closeInterestRate = 0)
    (hfee : loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat)
    -- the interest the loan books covers one period of interest on its theoretical principal
    (hcover : ∀ rate tpo : Number, loan.periodicRate = .ok rate →
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo →
      tpo.toRat * rate.toRat ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat) :
    p.totalPaid.toRat ≤
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat :=
  LendingLedger.fullPayment_cheaper_proof l hr l' i amount h loan hat p hp hclose hfee hcover

/-- Witness: a run where a full payment costs more than the remaining regular payments. At InterestRate 0.001% the
loan books almost no interest, and a full payment at the first due date charges one period of interest. -/
theorem Lending.fullPayment_cheaper_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok p) ∧
      loan.rates.closeInterestRate = 0 ∧ loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat ∧
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat <
        p.totalPaid.toRat :=
  LendingLedger.fullPayment_cheaper_witness

/-- Full payment -> the loan is paid off, principalPaid = PrincipalOutstanding and
interestPaid = ⌊fullInterest⌋ − managementFee. -/
theorem Lending.fullPayment_payoff (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment)) :
    (loan'.paymentRemaining = 0 ∧ loan'.totalValueOutstanding = Number.zero ∧
      loan'.principalOutstanding = Number.zero ∧ loan'.managementFeeOutstanding = Number.zero) ∧
    (∀ rate tpo fullInterest fullInterest' managementFee : Number, loan.periodicRate = .ok rate →
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo →
      -- the interest since StartDate, when the principal is paid out unless LoanAccept comes before it (FV_M4_48)
      computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
        loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest →
      STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
        .ok fullInterest' →
      computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee →
      payment.amounts.principalPaid = loan.principalOutstanding ∧
        payment.amounts.interestPaid.toRat = fullInterest'.toRat - managementFee.toRat) :=
  ⟨LendingLedger.fullPayment_closes_proof l l' i amount h loan' hat',
    fun rate tpo fullInterest fullInterest' managementFee =>
      LendingLedger.fullPayment_vault_proof l hr l' i amount h loan hat payment rate tpo fullInterest fullInterest'
        managementFee hpay⟩

/-- Witness: a run where a loan accepted before StartDate is paid in full with interestPaid = 0. A loan of 100 at 10%
accepted on day 0 with StartDate on day 30 is paid in full on day 29. -/
theorem Lending.fullPayment_payoff_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment) ∧
      loan.rates.interestRate ≠ 0 ∧ 0 < loan.principalOutstanding.toRat ∧ l.now < loan.schedule.startDate ∧
      payment.amounts.interestPaid.toRat = 0 :=
  LendingLedger.fullPayment_before_start_witness

/-- Full payment -> feePaid = ClosePaymentFee + managementFee.
`hsum` - ClosePaymentFee plus managementFee stays below 2^63 LoanScale units -/
theorem Lending.fullPayment_broker (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee)
    (hsum : loan.fees.closePaymentFee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale) :
    payment.amounts.feePaid.toRat = loan.fees.closePaymentFee.toRat + managementFee.toRat :=
  LendingLedger.fullPayment_broker_proof l hr l' i amount h loan hat payment rate tpo fullInterest fullInterest'
    managementFee hpay hrate htpo hfi hfloor hfee hsum

/-- Witness: a reachable run where feePaid ≠ ClosePaymentFee + managementFee. A ClosePaymentFee of `10^25` plus
a management fee of `100.000003` has 32 digits, and the payoff keeps 19 of them. -/
theorem Lending.fullPayment_broker_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault)
      (rate tpo fullInterest fullInterest' managementFee : Number),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment) ∧
      loan.periodicRate = .ok rate ∧
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo ∧
      computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
        loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest ∧
      STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
        .ok fullInterest' ∧
      computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee ∧
      payment.amounts.feePaid.toRat ≠ loan.fees.closePaymentFee.toRat + managementFee.toRat :=
  LendingLedger.fullPayment_broker_witness

/-- The extra amount of an overpayment -> PaymentRemaining and NextPaymentDueDate unchanged, and when not dropped
PrincipalOutstanding, TotalValueOutstanding and PeriodicPayment strictly decrease. -/
theorem Lending.overpayment_extra (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    -- `payment` - the scheduled payments the overpayment pays first
    (∃ payment, (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      loan'.paymentRemaining = payment.loan.paymentRemaining ∧
      loan'.nextPaymentDueDate = payment.loan.nextPaymentDueDate) ∧
    -- not dropped: the result differs from a regular payment of the same requestedAmount
    (∀ payment : UnsettledPayment Vault,
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) →
      (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run →
      loan'.principalOutstanding.toRat < payment.loan.principalOutstanding.toRat ∧
        loan'.totalValueOutstanding.toRat < payment.loan.totalValueOutstanding.toRat ∧
        loan'.periodicPayment.toRat < payment.loan.periodicPayment.toRat) :=
  ⟨LendingLedger.overpayment_schedule_proof l l' i amount h loan loan' hat hat',
    LendingLedger.overpayment_reduces_proof l hr l' i amount h loan loan' hat hat'⟩

/-- Overpayment whose extra part is dropped -> the same result as a regular payment of the same amount. -/
theorem Lending.overpayment_dropped (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (amount' : Number)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount') :
    -- the regular payments within the overpayment pay the loan off, use the whole rounded amount or reach 100 payments
    ((payment.loan.paymentRemaining = 0 ∨ payment.totalPaid.operator_lt amount' = false ∨
        payment.count = maxPaymentsPerTransaction) →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) ∧
    -- the extra part `extra`, capped at TotalValueOutstanding, rounds down to zero at LoanScale
    (∀ unspent extra : Number, amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent →
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra →
      extra.operator_gt Number.zero = false →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) ∧
    -- the extra part pays no principal. `opc` - the fee, interest and principal parts of the extra part
    (∀ (unspent extra : Number) (opc : PaymentComponents),
      amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent →
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra →
      payment.loan.computeOverpaymentComponents extra = .ok opc →
      opc.principalDelta.operator_gt Number.zero = false →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) ∧
    -- the new schedule after the extra part fails its checks: the LoanSet schedule checks, PrincipalOutstanding goes
    -- down, and the interest still owed does not go up
    (∀ (unspent extra : Number) (opc : PaymentComponents),
      amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent →
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra →
      payment.loan.computeOverpaymentComponents extra = .ok opc →
      payment.loan.overpaymentReamortization opc = .ok none →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) :=
  ⟨LendingLedger.overpayment_dropped_paid_off_proof l l' i amount h loan hat payment amount' hpay hamount,
    fun unspent extra => LendingLedger.overpayment_dropped_no_extra_proof l l' i amount h loan hat payment amount'
      unspent extra hpay hamount,
    fun unspent extra opc => LendingLedger.overpayment_dropped_absorbed_proof l l' i amount h loan hat payment
      amount' unspent extra opc hpay hamount,
    fun unspent extra opc => LendingLedger.overpayment_dropped_reamortization_proof l l' i amount h loan hat payment
      amount' unspent extra opc hpay hamount⟩

/-- Overpayment whose extra part isn't dropped -> feePaid = the scheduled payments' feePaid + ⌊OverpaymentFee × extra⌉
+ managementFee. `hsum` - the fees stay below 2^63 LoanScale units -/
theorem Lending.overpayment_fees (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    -- `payment` - the scheduled payments the overpayment pays first, `p` - those and the extra part
    (payment p : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hp : (loan.payInstalments l.vault .overpayment amount l.now).run = .ok (.ok p))
    -- not dropped: the result differs from a regular payment of the same requestedAmount
    (happlied : (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run)
    (amount' unspent extra f fee interest interest' managementFee : Number)
    -- the extra part `extra`, capped at TotalValueOutstanding and rounded down at LoanScale
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    -- `fee` - ⌊OverpaymentFee × extra⌉
    (hf : tenthBipsOfValue extra loan.rates.overpaymentFee .to_nearest = .ok f)
    (hfee : STAmount.roundToNumericType loan.broker.numericType f .to_nearest (some loan.loanScale) = .ok fee)
    -- `managementFee` - the management fee on ⌊OverpaymentInterestRate × extra⌉
    (hi : tenthBipsOfValue extra loan.rates.overpaymentInterestRate .to_nearest = .ok interest)
    (hi' : STAmount.roundToNumericType loan.broker.numericType interest .to_nearest (some loan.loanScale) =
      .ok interest')
    (hmf : computeManagementFee loan.broker.numericType interest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee)
    (hsum : |payment.amounts.feePaid.toRat| + fee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale) :
    p.amounts.feePaid.toRat = payment.amounts.feePaid.toRat + fee.toRat + managementFee.toRat :=
  LendingLedger.overpayment_fees_proof l hr l' i amount h loan hat payment p hpay hp happlied amount' unspent extra f
    fee interest interest' managementFee hamount hunspent hextra hf hfee hi hi' hmf hsum

/-- Witness: a run where a huge LoanServiceFee makes feePaid miss ⌊OverpaymentFee × extra⌉. With LoanServiceFee
`10^25` the fees keep 19 digits, and the fee of about `1.6·10^5` rounds away. -/
theorem Lending.overpayment_fees_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment p : UnsettledPayment Vault)
      (amount' unspent extra f fee interest interest' managementFee : Number),
      l.Reachable ∧ (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      (loan.payInstalments l.vault .overpayment amount l.now).run = .ok (.ok p) ∧
      (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run ∧
      STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) = .ok amount' ∧
      amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent ∧
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra ∧
      tenthBipsOfValue extra loan.rates.overpaymentFee .to_nearest = .ok f ∧
      STAmount.roundToNumericType loan.broker.numericType f .to_nearest (some loan.loanScale) = .ok fee ∧
      tenthBipsOfValue extra loan.rates.overpaymentInterestRate .to_nearest = .ok interest ∧
      STAmount.roundToNumericType loan.broker.numericType interest .to_nearest (some loan.loanScale) =
        .ok interest' ∧
      computeManagementFee loan.broker.numericType interest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee ∧
      p.amounts.feePaid.toRat ≠ payment.amounts.feePaid.toRat + fee.toRat + managementFee.toRat :=
  LendingLedger.overpayment_fees_witness

/-- Payment -> AssetsAvailable' − AssetsAvailable is at most principalPaid + interestPaid and less than 1 ULP below it
at the scale of AssetsAvailable', and it is amountToPool, for a regular payment the drop in TVO − drop in MFO. -/
theorem Lending.payment_vault (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (r : LoanWithAmounts Vault) (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤ 0 ∧
    -- at most `10^16` base units paid, and the range of the proof: AssetsAvailable plus the payment below `2^63`
    -- base units, within the XRP and MPT supply
    (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent →
      ∀ e, numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
        payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
          (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) < 10 ^ e) ∧
    -- the vault is not coarsened: AssetsAvailable plus the payment stays below `10^16` base units (FV_M4_25)
    (l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat = r.amountToPool.toRat ∧
        (paymentType = .regular → r.amountToPool.toRat =
          (loan.totalValueOutstanding.toRat - loan'.totalValueOutstanding.toRat) -
            (loan.managementFeeOutstanding.toRat - loan'.managementFeeOutstanding.toRat))) :=
  ⟨LendingLedger.payment_vault_upper_bound_proof l hr l' i paymentType amount h loan hat payment hpay,
    fun hpaid hfit =>
      LendingLedger.payment_vault_lower_bound_proof l hr l' i paymentType amount h loan hat payment hpay hpaid hfit,
    fun htotal => LendingLedger.payment_vault_credit_proof l hr l' i paymentType amount h loan loan' hat hat' payment
      hpay r hok htotal⟩

/-- Witness: a run where (AssetsAvailable' − AssetsAvailable) − (principalPaid + interestPaid) = 0. The first payment
of the loan of `603946999675283.3` at its due date. -/
theorem Lending.payment_vault_upper_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
        (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) = 0 :=
  LendingLedger.payment_vault_upper_bound_witness

/-- Witness: a run where principalPaid + interestPaid − (AssetsAvailable' − AssetsAvailable) is 1.99 ULP at the
scale of AssetsAvailable'. The loan of `603946999675283.3` paid 32 years late pays over `10^16` base units. -/
theorem Lending.payment_vault_lower_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
        (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) = (199 / 100 : ℚ) * 10 ^ e :=
  LendingLedger.payment_vault_lower_bound_witness

/-- Witness: a run on a coarsened vault where a regular payment credits less than that drop. Loan D's final
instalment takes 1.9 off TotalValueOutstanding, but the vault holding about `1.87·10^15` gets 1. -/
theorem Lending.payment_vault_coarsened_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan loan' : Loan),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧
      l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat <
        (loan.totalValueOutstanding.toRat - loan'.totalValueOutstanding.toRat) -
          (loan.managementFeeOutstanding.toRat - loan'.managementFeeOutstanding.toRat) :=
  LendingLedger.payment_vault_credit_coarsened_witness

/-- Regular payment -> AssetsTotal' − AssetsTotal = YieldUnrealized − YieldUnrealized' = interestPaid. -/
theorem Lending.regularPayment_yield (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) :
    -- the vault is not coarsened after the payment: AssetsAvailable' stays below 10^16 base units (FV_M4_25)
    (l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      l'.vault.toExact.assetsTotal - l.vault.toExact.assetsTotal = payment.amounts.interestPaid.toRat) ∧
    l.vault.toExact.yieldUnrealized - l'.vault.toExact.yieldUnrealized = payment.amounts.interestPaid.toRat :=
  LendingLedger.regularPayment_yield_proof l hr l' i amount h loan hat payment hpay

/-- Witness: a run where AssetsTotal' − AssetsTotal < interestPaid. On the coarsened vault loan D's regular instalment
of 1.9 is credited as 1, so AssetsTotal falls by 0.5 while interestPaid is 0.4. -/
theorem Lending.regularPayment_yield_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      l'.vault.toExact.assetsTotal - l.vault.toExact.assetsTotal < payment.amounts.interestPaid.toRat :=
  LendingLedger.regularPayment_yield_witness

end XRPL.Model
