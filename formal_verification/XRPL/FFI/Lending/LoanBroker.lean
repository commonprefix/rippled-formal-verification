import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete
import XRPL.Model.Lending1_1.AssetPool
import XRPL.FFI.Vault.Vault

open XRPL.Model.Protocol (Number NumericType STAmount TER Error)
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

-- Build a lawful loan broker from the raw C++ fields, validating at the boundary.
@[export lean_loan_broker_build]
def lean_loan_broker_build (numericType : NumericType) (managementFeeRate : UInt16)
    (coverRateMinimum coverRateLiquidation : UInt32) (debtTotal debtMaximum coverAvailable : Number)
    (loanCount : UInt32) : Except Error LoanBroker :=
  RawLoanBroker.to_lawful
    { numericType, managementFeeRate, coverRateMinimum, coverRateLiquidation, debtTotal, debtMaximum,
      coverAvailable, loanCount }

@[export lean_loan_broker_management_fee_rate]
def lean_loan_broker_management_fee_rate (lb : LoanBroker) : UInt16 := lb.managementFeeRate
@[export lean_loan_broker_cover_rate_minimum]
def lean_loan_broker_cover_rate_minimum (lb : LoanBroker) : UInt32 := lb.coverRateMinimum
@[export lean_loan_broker_cover_rate_liquidation]
def lean_loan_broker_cover_rate_liquidation (lb : LoanBroker) : UInt32 := lb.coverRateLiquidation
@[export lean_loan_broker_debt_total]
def lean_loan_broker_debt_total (lb : LoanBroker) : Number := lb.debtTotal
@[export lean_loan_broker_debt_maximum]
def lean_loan_broker_debt_maximum (lb : LoanBroker) : Number := lb.debtMaximum
@[export lean_loan_broker_cover_available]
def lean_loan_broker_cover_available (lb : LoanBroker) : Number := lb.coverAvailable
@[export lean_loan_broker_loan_count]
def lean_loan_broker_loan_count (lb : LoanBroker) : UInt32 := lb.loanCount

-- LoanBrokerSet
@[export lean_can_loan_broker_create]
def lean_can_loan_broker_create (pool : Vault) (debtMaximum : Option Number) (nt : NumericType)
    : Except Error Int32 :=
  (·.code) <$> LoanBroker.canCreate pool debtMaximum nt

@[export lean_loan_broker_create]
def lean_loan_broker_create (debtMaximum : Option Number) (managementFeeRate : Option UInt16)
    (coverRateMinimum coverRateLiquidation : Option UInt32) (nt : NumericType) : Except Error LoanBroker :=
  LoanBroker.create { debtMaximum, managementFeeRate, coverRateMinimum, coverRateLiquidation } nt

@[export lean_can_loan_broker_update]
def lean_can_loan_broker_update (lb : LoanBroker) (pool : Vault) (debtMaximum : Option Number)
    : Except Error Int32 :=
  (·.code) <$> lb.canUpdate pool debtMaximum

@[export lean_loan_broker_update]
def lean_loan_broker_update (lb : LoanBroker) (debtMaximum : Option Number) : Except Error LoanBroker :=
  lb.update debtMaximum

-- Cover transactions. Each `TerExcept` reaches C++ as its `.run`.
@[export lean_can_cover_deposit]
def lean_can_cover_deposit (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Except Error Int32 :=
  (·.code) <$> lb.canCoverDeposit pool amount

@[export lean_cover_deposit]
def lean_cover_deposit (lb : LoanBroker) (pool : Vault) (amount : STAmount)
    : Except Error (Except TER LoanBrokerCoverResult) :=
  (lb.coverDeposit pool amount).run

@[export lean_can_cover_withdraw]
def lean_can_cover_withdraw (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Except Error Int32 :=
  (·.code) <$> lb.canCoverWithdraw pool amount

@[export lean_cover_withdraw]
def lean_cover_withdraw (lb : LoanBroker) (pool : Vault) (amount : STAmount)
    : Except Error (Except TER LoanBrokerCoverResult) :=
  (lb.coverWithdraw pool amount).run

@[export lean_can_cover_clawback]
def lean_can_cover_clawback (lb : LoanBroker) (pool : Vault) (amount : Option STAmount)
    : Except Error Int32 :=
  (·.code) <$> lb.canCoverClawback pool amount

@[export lean_cover_clawback]
def lean_cover_clawback (lb : LoanBroker) (pool : Vault) (amount : Option STAmount)
    : Except Error (Except TER LoanBrokerCoverResult) :=
  (lb.coverClawback pool amount).run

-- LoanBrokerDelete
@[export lean_can_loan_broker_delete]
def lean_can_loan_broker_delete (lb : LoanBroker) (pool : Vault) : Except Error Int32 :=
  (·.code) <$> lb.canDelete pool

@[export lean_loan_broker_rounded_cover]
def lean_loan_broker_rounded_cover (lb : LoanBroker) : Except Error STAmount :=
  lb.roundedCoverAvailable

@[export lean_ter_cover_result_code]
def lean_ter_cover_result_code (r : Except TER LoanBrokerCoverResult) : Option Int32 := terCode r
@[export lean_ter_cover_result_value]
def lean_ter_cover_result_value (r : Except TER LoanBrokerCoverResult) : Option LoanBrokerCoverResult :=
  terValue r

@[export lean_cover_result_amount]
def lean_cover_result_amount (r : LoanBrokerCoverResult) : STAmount := r.amount'
@[export lean_cover_result_broker]
def lean_cover_result_broker (r : LoanBrokerCoverResult) : LoanBroker := r.loanBroker'
