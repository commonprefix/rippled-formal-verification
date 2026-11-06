import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.PayExits
import XRPL.Properties.Lending.Loan.Common.PayProofs

/-! # The coarsened run before the stuck loan

The coarsened run of `CoarsenedVault.lean` up to loan A's late payment, where the stuck-loan witnesses start. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The coarsened run up to loan A's late payment. -/
def cwCoarsenedTxs : List LendingTx := cwTxs.take 10

end XRPL.Model.Lending
