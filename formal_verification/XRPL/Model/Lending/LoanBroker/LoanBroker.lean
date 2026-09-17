import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure RawLoanBroker where
  numericType : NumericType
  managementFeeRate : TenthBips16
  coverRateMinimum : TenthBips32
  coverRateLiquidation : TenthBips32
  -- amounts in the pool's asset
  debtTotal : Number
  debtMaximum : Number
  coverAvailable : Number
  loanCount : UInt32

structure RawLoanBroker.WF (rb : RawLoanBroker) : Prop where
  debtTotal_norm : rb.debtTotal.isNormalized
  debtMaximum_norm : rb.debtMaximum.isNormalized
  coverAvailable_norm : rb.coverAvailable.isNormalized

structure RawLoanBroker.Valid (rb : RawLoanBroker) : Prop where
  debtTotal_nonneg : Number.zero.operator_le rb.debtTotal = true
  coverAvailable_nonneg : Number.zero.operator_le rb.coverAvailable = true

instance RawLoanBroker.decidableWF (rb : RawLoanBroker) : Decidable rb.WF :=
  decidable_of_iff
    (rb.debtTotal.isNormalized ∧ rb.debtMaximum.isNormalized ∧ rb.coverAvailable.isNormalized)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

instance RawLoanBroker.decidableValid (rb : RawLoanBroker) : Decidable rb.Valid :=
  decidable_of_iff
    (Number.zero.operator_le rb.debtTotal = true ∧ Number.zero.operator_le rb.coverAvailable = true)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

structure LoanBroker extends RawLoanBroker where
  wf : toRawLoanBroker.WF
  valid : toRawLoanBroker.Valid

def RawLoanBroker.to_lawful (rb : RawLoanBroker) : Except Error LoanBroker :=
  if h : rb.WF ∧ rb.Valid then .ok { toRawLoanBroker := rb, wf := h.1, valid := h.2 } else .error .notLawful

-- The broker with the pool it draws on, after an operation that changes both
structure LoanBrokerWithPool (α : Type) where
  broker' : LoanBroker
  pool' : α

-- XLS-66 (32): management fee on the interest, rounded down
def computeManagementFee (nt : NumericType) (value : Number) (feeRate : TenthBips16) (exponent : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue value feeRate.toTenthBips32 .to_nearest
  STAmount.roundToNumericType nt raw .downward (some exponent)

end XRPL.Model.Lending
