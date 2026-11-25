import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Lending.Loan.Common.PayFit
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.SettledVault
import XRPL.Properties.Vault.Proofs.Support.IOUTotality

/-! # A downward IOU amount never overflows

Rounding a positive value below `10^96` down to an IOU amount never carries past the IOU ceiling. The
lemma lives in `Vault/Proofs/Support/IOUTotality.lean`, imported here for this module's users. -/
