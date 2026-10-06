import XRPL.Properties.Lending.LoanBroker.Common.DepositExits
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness

/-! # `LoanBrokerCoverDeposit` exits

The exits of the deposit check: an amount that rounds to zero at the cover scale is rejected. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- An amount that rounds down to zero at the scale of `coverAvailable`:
`tecPRECISION_LOSS`. -/
theorem LoanBroker.roundedCoverAmount_precision_loss (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hz : r.signum = 0) :
    lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) :=
  LoanBroker.roundedCoverAmount_precision_loss_proof lb amount r hdown hz

/-- Witness: whether `roundedCoverAmount_precision_loss` fires depends on `coverAvailable`. A deposit
of `10^-15` rounds to zero on a cover of `10`, and is taken whole on a cover of `9.5`, which is what a
withdrawal of `0.5` leaves. -/
theorem LoanBroker.roundedCoverAmount_precision_loss_attained :
    ∃ (lb lb' : LoanBroker) (amount : STAmount), lb'.numericType = lb.numericType ∧
      lb'.toExact.coverAvailable < lb.toExact.coverAvailable ∧
      lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) ∧
      lb'.roundedCoverAmount amount = .ok (.rounded amount) :=
  LoanBroker.roundedCoverAmount_precision_loss_witness

/-- Otherwise the amount passes, rounded down to the scale of `coverAvailable`. -/
theorem LoanBroker.roundedCoverAmount_rounded (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hnz : r.signum ≠ 0) :
    lb.roundedCoverAmount amount = .ok (.rounded r) :=
  LoanBroker.roundedCoverAmount_rounded_proof lb amount r hdown hnz

/-- `tecPRECISION_LOSS` is the only rejection `roundedCoverAmount` can return. -/
theorem LoanBroker.roundedCoverAmount_rejected_code (amount : STAmount)
    (ter : TER) (hok : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS :=
  LoanBroker.roundedCoverAmount_rejected_code_proof lb amount ter hok

/-- An amount that `roundedCoverAmount` rejects makes `coverDeposit` fail with
`tecINTERNAL`: the deposit never runs on such an amount. -/
theorem LoanBroker.coverDeposit_rejected (amount : STAmount) (ter : TER)
    (hrej : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    lb.coverDeposit amount = .ok (.error .tecINTERNAL) :=
  LoanBroker.coverDeposit_rejected_proof lb amount ter hrej

/-- Every check passes: the deposit returns the rounded amount and the exact
updated broker, with `coverAvailable` set to the rounded sum `c'`. The
`to_lawful` re-check succeeds, so the `.notLawful` throw is unreachable. -/
theorem LoanBroker.coverDeposit_success (amount r : STAmount) (rN c' : Number)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hadd : lb.coverAvailable.operator_add rN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverDeposit amount = .ok (.ok ⟨r, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } :=
  LoanBroker.coverDeposit_success_proof lb amount r rN c' hrounded hc hnn hnum hadd

/-- Every outcome of a deposit that runs without a throw: `tecINTERNAL` is the
only rejection `coverDeposit` can return. -/
theorem LoanBroker.coverDeposit_error_codes (amount : STAmount) (ter : TER)
    (hok : lb.coverDeposit amount = .ok (.error ter)) : ter = .tecINTERNAL :=
  LoanBroker.coverDeposit_error_codes_proof lb amount ter hok

end XRPL.Model.Lending
