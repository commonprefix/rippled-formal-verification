import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.AssociateAssetProofs

/-! # The `associateAsset` no-op invariant

Every LoanBroker transactor calls `associateAsset` on the broker SLE after
updating it, which rounds each `kSmdNeedsAsset` field (`debtTotal`,
`debtMaximum`, `coverAvailable`) to the asset's precision. The model does not
round, so `associateAsset` should be a no-op: `LoanBroker.assetsRounded` should
never hold on a stored broker. When it does, C++ stores a different value than
the model. On an IOU broker each cover operation can leave `coverAvailable` off
the grid. On an XRP or MPT broker it stays on the grid while it fits the type. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- **`associateAsset` is not a no-op after a deposit.** Depositing
`9999999999999999` onto `9999999999999999` of IOU cover leaves `coverAvailable`
at `19999999999999998`, 17 significant digits. -/
theorem LoanBroker.coverDeposit_associateAsset_rounds :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverDeposit_associateAsset_witness

/-- **`associateAsset` is not a no-op after a withdrawal.** Withdrawing
`7.6 * 10^-10` from `10^6` of IOU cover passes the checks and leaves a 17-digit
`coverAvailable`. -/
theorem LoanBroker.coverWithdraw_associateAsset_rounds :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverWithdraw_associateAsset_witness

/-- **`associateAsset` is not a no-op after a clawback.** Clawing `7.5` from
`10^16` of IOU cover leaves `coverAvailable` at `9999999999999992.5`, 17
significant digits. -/
theorem LoanBroker.coverClawback_associateAsset_rounds :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      lb.coverClawback pool amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverClawback_associateAsset_witness

variable {α : Type} [AssetPool α]

/-- **`associateAsset` is a no-op after an XRP or MPT deposit.** A whole cover
plus a whole deposit is whole, so the asset stores it exactly while it fits the
type's bounds. -/
theorem LoanBroker.coverDeposit_associateAsset_integral (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverDeposit_associateAsset_integral_proof lb amount res hok hnt hmaxoff hint hsz
    hcint hbound hmax

/-- **`associateAsset` is a no-op after an XRP or MPT withdrawal.** A whole cover
less a whole withdrawal is whole and no larger, so the asset stores it exactly. -/
theorem LoanBroker.coverWithdraw_associateAsset_integral (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverWithdraw_associateAsset_integral_proof lb amount res hok hnt hmaxoff hint hsz
    hnn hcint hbound hmax

/-- **`associateAsset` is a no-op after an XRP or MPT clawback.** A whole cover
less a whole clawed amount is whole and no larger, so the asset stores it
exactly. -/
theorem LoanBroker.coverClawback_associateAsset_integral (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverClawback_associateAsset_integral_proof lb pool amount res hcan hok hreq hnt
    hmaxoff hcint hbound hmax

end XRPL.Model.Lending
