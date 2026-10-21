import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Lending1_1.AssetPool
import XRPL.FFI.Vault.Vault
import XRPL.FFI.Lending.LoanBroker

open XRPL.Model.Protocol (Number NumericType STAmount TER Error)
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

-- Build a lawful loan from the raw C++ fields and its lawful broker, validating at the boundary.
@[export lean_loan_build]
def lean_loan_build (broker : LoanBroker)
    (interestRate lateInterestRate closeInterestRate overpaymentInterestRate overpaymentFee : UInt32)
    (originationFee serviceFee latePaymentFee closePaymentFee : Number)
    (paymentInterval paymentTotal gracePeriod startDate : UInt32)
    (paymentRemaining : UInt32)
    (periodicPayment principalOutstanding totalValueOutstanding managementFeeOutstanding : Number)
    (loanScale : Int32) (previousPaymentDueDate nextPaymentDueDate : UInt32)
    (isPending isImpaired isDefault allowsOverpayment : UInt8) : Except Error Loan :=
  RawLoan.to_lawful {
    broker
    rates := { interestRate, lateInterestRate, closeInterestRate, overpaymentInterestRate, overpaymentFee }
    fees := { originationFee, serviceFee, latePaymentFee, closePaymentFee }
    schedule := { paymentInterval, paymentTotal, gracePeriod, startDate }
    paymentRemaining, periodicPayment, principalOutstanding, totalValueOutstanding, managementFeeOutstanding
    loanScale := loanScale.toInt
    previousPaymentDueDate, nextPaymentDueDate
    isPending := isPending != 0
    isImpaired := isImpaired != 0
    isDefault := isDefault != 0
    allowsOverpayment := allowsOverpayment != 0 }

@[export lean_loan_broker]
def lean_loan_broker (loan : Loan) : LoanBroker := loan.broker
@[export lean_loan_payment_remaining]
def lean_loan_payment_remaining (loan : Loan) : UInt32 := loan.paymentRemaining
@[export lean_loan_periodic_payment]
def lean_loan_periodic_payment (loan : Loan) : Number := loan.periodicPayment
@[export lean_loan_principal_outstanding]
def lean_loan_principal_outstanding (loan : Loan) : Number := loan.principalOutstanding
@[export lean_loan_total_value_outstanding]
def lean_loan_total_value_outstanding (loan : Loan) : Number := loan.totalValueOutstanding
@[export lean_loan_management_fee_outstanding]
def lean_loan_management_fee_outstanding (loan : Loan) : Number := loan.managementFeeOutstanding
@[export lean_loan_scale]
def lean_loan_scale (loan : Loan) : Int32 := Int32.ofInt loan.loanScale
@[export lean_loan_previous_payment_due_date]
def lean_loan_previous_payment_due_date (loan : Loan) : UInt32 := loan.previousPaymentDueDate
@[export lean_loan_next_payment_due_date]
def lean_loan_next_payment_due_date (loan : Loan) : UInt32 := loan.nextPaymentDueDate
@[export lean_loan_is_pending]
def lean_loan_is_pending (loan : Loan) : UInt8 := if loan.isPending then 1 else 0
@[export lean_loan_is_impaired]
def lean_loan_is_impaired (loan : Loan) : UInt8 := if loan.isImpaired then 1 else 0
@[export lean_loan_is_default]
def lean_loan_is_default (loan : Loan) : UInt8 := if loan.isDefault then 1 else 0
@[export lean_loan_allows_overpayment]
def lean_loan_allows_overpayment (loan : Loan) : UInt8 := if loan.allowsOverpayment then 1 else 0

-- Every fund-moving result reaches C++ as a `LoanWithAmounts`; operations that move nothing report zeros.
def withZeroAmounts (r : LoanWithPool Vault) : LoanWithAmounts Vault :=
  { toLoanWithPool := r, amountToPool := Number.zero, amountToBroker := Number.zero }

-- LoanSet. The schedule fields are the transaction's, with the model filling the defaults; the ledger
-- close time stamps a one-step start date, the parent close time judges expiry and phase.
@[export lean_can_loan_create]
def lean_can_loan_create (broker : LoanBroker) (pool : Vault) (principal : Number)
    (originationFee serviceFee latePaymentFee closePaymentFee : Number)
    (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate ledgerCloseTime parentCloseTime : UInt32)
    (twoStep : UInt8) : Except Error Int32 :=
  let schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate ledgerCloseTime (twoStep != 0)
  (·.code) <$> Loan.canCreate broker pool principal
    { originationFee, serviceFee, latePaymentFee, closePaymentFee } schedule parentCloseTime (twoStep != 0)

@[export lean_loan_create]
def lean_loan_create (broker : LoanBroker) (pool : Vault) (principal : Number)
    (interestRate lateInterestRate closeInterestRate overpaymentInterestRate overpaymentFee : UInt32)
    (originationFee serviceFee latePaymentFee closePaymentFee : Number)
    (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate ledgerCloseTime : UInt32)
    (twoStep allowsOverpayment : UInt8) : Except Error (Except TER (LoanWithAmounts Vault)) :=
  let schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate ledgerCloseTime (twoStep != 0)
  (withZeroAmounts <$> Loan.create broker pool principal
    { interestRate, lateInterestRate, closeInterestRate, overpaymentInterestRate, overpaymentFee }
    { originationFee, serviceFee, latePaymentFee, closePaymentFee }
    schedule (allowsOverpayment != 0) (twoStep != 0)).run

-- LoanAccept
@[export lean_can_loan_accept]
def lean_can_loan_accept (loan : Loan) (pool : Vault) (parentCloseTime : UInt32) : Except Error Int32 :=
  (·.code) <$> loan.canAccept pool parentCloseTime

@[export lean_loan_accept]
def lean_loan_accept (loan : Loan) (pool : Vault) : Except Error (Except TER (LoanWithAmounts Vault)) :=
  (withZeroAmounts <$> loan.accept pool).run

-- LoanPay. Payment type tags: 0 = regular, 1 = late, 2 = full, 3 = overpayment.
def paymentTypeOf : UInt8 → LoanPaymentType
  | 1 => .late
  | 2 => .full
  | 3 => .overpayment
  | _ => .regular

@[export lean_can_loan_pay]
def lean_can_loan_pay (loan : Loan) (paymentType : UInt8) : Except Error Int32 :=
  pure (loan.canPay (paymentTypeOf paymentType)).code

@[export lean_loan_pay]
def lean_loan_pay (loan : Loan) (pool : Vault) (paymentType : UInt8) (amount : Number) (now : UInt32)
    : Except Error (Except TER (LoanWithAmounts Vault)) :=
  (match paymentTypeOf paymentType with
    | .regular => loan.regularPayment pool amount now
    | .late => loan.latePayment pool amount now
    | .full => loan.fullPayment pool amount now
    | .overpayment => loan.overpayment pool amount now).run

-- LoanManage. Action tags: 0 = impair, 1 = unimpair, 2 = default.
def manageActionOf : UInt8 → LoanManageAction
  | 1 => .unimpair
  | 2 => .default
  | _ => .impair

@[export lean_can_loan_manage]
def lean_can_loan_manage (loan : Loan) (action : UInt8) (now : UInt32) : Except Error Int32 :=
  pure (loan.canManage (manageActionOf action) now).code

@[export lean_loan_manage]
def lean_loan_manage (loan : Loan) (pool : Vault) (action : UInt8) (now : UInt32)
    : Except Error (Except TER (LoanWithAmounts Vault)) :=
  (match manageActionOf action with
    | .impair => withZeroAmounts <$> loan.manageImpair pool now
    | .unimpair => withZeroAmounts <$> loan.manageUnimpair pool
    | .default => loan.manageDefault pool).run

-- LoanDelete
@[export lean_can_loan_delete]
def lean_can_loan_delete (loan : Loan) : Except Error Int32 :=
  pure loan.canDelete.code

@[export lean_loan_delete]
def lean_loan_delete (loan : Loan) (pool : Vault) : Except Error (Except TER (LoanBrokerWithPool Vault)) :=
  (loan.delete pool).run

@[export lean_ter_loan_amounts_code]
def lean_ter_loan_amounts_code (r : Except TER (LoanWithAmounts Vault)) : Option Int32 := terCode r
@[export lean_ter_loan_amounts_value]
def lean_ter_loan_amounts_value (r : Except TER (LoanWithAmounts Vault)) : Option (LoanWithAmounts Vault) :=
  terValue r
@[export lean_loan_amounts_loan]
def lean_loan_amounts_loan (r : LoanWithAmounts Vault) : Loan := r.loan'
@[export lean_loan_amounts_pool]
def lean_loan_amounts_pool (r : LoanWithAmounts Vault) : Vault := r.pool'
@[export lean_loan_amounts_to_pool]
def lean_loan_amounts_to_pool (r : LoanWithAmounts Vault) : Number := r.amountToPool
@[export lean_loan_amounts_to_broker]
def lean_loan_amounts_to_broker (r : LoanWithAmounts Vault) : Number := r.amountToBroker

@[export lean_ter_broker_pool_code]
def lean_ter_broker_pool_code (r : Except TER (LoanBrokerWithPool Vault)) : Option Int32 := terCode r
@[export lean_ter_broker_pool_value]
def lean_ter_broker_pool_value (r : Except TER (LoanBrokerWithPool Vault)) : Option (LoanBrokerWithPool Vault) :=
  terValue r
@[export lean_broker_pool_broker]
def lean_broker_pool_broker (r : LoanBrokerWithPool Vault) : LoanBroker := r.broker'
@[export lean_broker_pool_pool]
def lean_broker_pool_pool (r : LoanBrokerWithPool Vault) : Vault := r.pool'
