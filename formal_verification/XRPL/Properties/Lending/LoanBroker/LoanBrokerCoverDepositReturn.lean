import XRPL.Properties.Lending.LoanBroker.Common.DepositExits
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness

/-! # `LoanBrokerCoverDeposit` exits

The exits of the deposit check: an amount that rounds to zero at the cover scale is rejected. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- When the amount rounds down to zero at CoverAvailable's scale -> tecPRECISION_LOSS. -/
theorem LoanBroker.roundedCoverAmount_precision_loss (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hz : r.signum = 0) :
    lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) :=
  LoanBroker.roundedCoverAmount_precision_loss_proof lb amount r hdown hz

/-- Witness: the same deposit passes after a withdraw. A deposit of `10^-15` rounds to zero on a
cover of `10`, and is taken whole on a cover of `9.5`, which is what a withdrawal of `0.5`
leaves. -/
theorem LoanBroker.roundedCoverAmount_precision_loss_attained :
    ∃ (lb lb' : LoanBroker) (amount : STAmount), lb'.numericType = lb.numericType ∧
      lb'.toExact.coverAvailable < lb.toExact.coverAvailable ∧
      lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) ∧
      lb'.roundedCoverAmount amount = .ok (.rounded amount) :=
  LoanBroker.roundedCoverAmount_precision_loss_witness

/-- Otherwise -> success, with the amount rounded down to CoverAvailable's scale. -/
theorem LoanBroker.roundedCoverAmount_rounded (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hnz : r.signum ≠ 0) :
    lb.roundedCoverAmount amount = .ok (.rounded r) :=
  LoanBroker.roundedCoverAmount_rounded_proof lb amount r hdown hnz

/-- The only rounding rejection is tecPRECISION_LOSS. -/
theorem LoanBroker.roundedCoverAmount_rejected_code (amount : STAmount)
    (ter : TER) (hok : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS :=
  LoanBroker.roundedCoverAmount_rejected_code_proof lb amount ter hok

/-- When the amount rounds down to zero -> tecINTERNAL. -/
theorem LoanBroker.coverDeposit_rejected (amount : STAmount) (ter : TER)
    (hrej : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    lb.coverDeposit amount = .ok (.error .tecINTERNAL) :=
  LoanBroker.coverDeposit_rejected_proof lb amount ter hrej

/-- All checks pass -> updated loan broker and roundedAmount.
`c'` - the new CoverAvailable, the rounded sum -/
theorem LoanBroker.coverDeposit_success (amount r : STAmount) (rN c' : Number)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hadd : lb.coverAvailable.operator_add rN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverDeposit amount = .ok (.ok ⟨r, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } :=
  LoanBroker.coverDeposit_success_proof lb amount r rN c' hrounded hc hnn hnum hadd

/-- The only deposit rejection is tecINTERNAL. -/
theorem LoanBroker.coverDeposit_error_codes (amount : STAmount) (ter : TER)
    (hok : lb.coverDeposit amount = .ok (.error ter)) : ter = .tecINTERNAL :=
  LoanBroker.coverDeposit_error_codes_proof lb amount ter hok

end XRPL.Model.Lending
