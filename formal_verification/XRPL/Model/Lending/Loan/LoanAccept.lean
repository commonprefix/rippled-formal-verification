import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanAccept -> preclaim
def Loan.canAccept {α : Type} [AssetPool α] (loan : Loan) (pool : α) (parentCloseTime : UInt32)
    : Except Error TER := do
  if !loan.isPending then return .tecNO_PERMISSION
  let hasExpired : Bool := parentCloseTime ≥ loan.schedule.startDate
  if hasExpired then return .tecEXPIRED

  let phase := AssetPool.phase pool parentCloseTime
  match phase with
  | .subscription => return .tecTOO_SOON
  | .redemption => return .tecEXPIRED
  | .noPhase | .investment => pure ()

  -- the interest of the loan must fit in the vault's Open zone
  let interestDue ← loan.interestDue
  let exceedsOpenLimit ← AssetPool.exceedsOpenLimit pool interestDue
  if exceedsOpenLimit then
    return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

-- LoanAccept -> doApply. The principal leaves the reserved assets, the interest joins the unrealized yield.
def Loan.accept {α : Type} [AssetPool α] (loan : Loan) (pool : α) : TerExcept (LoanWithPool α) := do
  let interestDue ← loan.interestDue
  let change : PoolBalanceChange := {
    yield := interestDue
    reserved := loan.principalOutstanding.operator_neg }
  let pool' ← AssetPool.adjustBalances pool change

  let rawLoan' : RawLoan := { loan.toRawLoan with isPending := false }
  let loan' ← rawLoan'.to_lawful

  return { loan' := loan', pool' := pool' }

end XRPL.Model.Lending
