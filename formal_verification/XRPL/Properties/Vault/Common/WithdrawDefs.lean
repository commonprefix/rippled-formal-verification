import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Exact-arithmetic reference values for `Vault.withdraw`

The ideal (unrounded) exchange quantities the `Vault.withdraw` accuracy
headlines are stated against, plus the `WithdrawNavExact` pricing hypothesis. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The withdrawal names an amount of shares, the model's `isByShares`. -/
def WithdrawAmount.isByShares : WithdrawAmount → Bool
  | .vaultShares _ => true
  | .vaultAssets _ => false

/-- The entry checks of a withdrawal pass, read off the code: it is not too soon to withdraw,
the amounts are priced, and a final withdrawal leaves nothing deployed. -/
structure Vault.WithdrawPriced (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (amounts : VaultAmounts) (sharesTotalAmount : STAmount) : Prop where
  soon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false
  priced : (computeWithdraw v amount waive).run = .ok (.ok amounts)
  sharesTotal : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount
  obligations : (amounts.shares.operator_eq sharesTotalAmount && v.assetsDeployed.operator_ne Number.zero) = false

/-- The checks before the fee of a non-final withdrawal pass, read off the code: the entry checks,
the amount converts, the dust check passes, and something is paid. -/
structure Vault.WithdrawNonFinal (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber : Number) : Prop where
  priced : v.WithdrawPriced amount waive t amounts sharesTotalAmount
  nonFinal : amounts.shares.operator_eq sharesTotalAmount = false
  converted : amounts.assets.toNumber .to_nearest = .ok assetsNumber
  netAssetValue : ∃ netAssetValue, v.assetsTotalForWithdrawal waive = .ok netAssetValue
  dust : v.checkDebitNotDust assetsNumber = .ok .tesSUCCESS
  nonzero : amounts.assets.isZero = false

/-- Net asset value backing the shares for withdrawal:
assetsTotal minus lossUnrealized. -/
def RawVault.withdrawNav (rv : RawVault) : ℚ :=
  rv.toExact.assetsTotal - rv.toExact.lossUnrealized

/-- The exact `assets'` for redeeming `shares`, before rounding (XLS-0065): `nav * shares / sharesTotal`, priced
at `depositNav` when the loss is waived and at `withdrawNav` otherwise. -/
def RawVault.idealAssetsWithdraw (rv : RawVault) (waiveUnrealizedLoss : Bool) (shares : ℚ) : ℚ :=
  (if waiveUnrealizedLoss then rv.depositNav else rv.withdrawNav) *
    shares / rv.toExact.sharesTotal

/-- The exact share amount for withdrawing `assets`, before rounding (XLS-0065): `sharesTotal * assets / nav`, with
the same `nav` as `idealAssetsWithdraw`. -/
def RawVault.idealSharesWithdraw (rv : RawVault) (waiveUnrealizedLoss : Bool) (assets : ℚ) : ℚ :=
  rv.toExact.sharesTotal * assets /
    (if waiveUnrealizedLoss then rv.depositNav else rv.withdrawNav)

/-- The exact `assets'` for redeeming `shares` priced at `nav` instead of the exact net asset value. The model
prices at its computed value, which can sit just off the exact one when assets are deployed. -/
def RawVault.idealAssetsWithdrawAt (rv : RawVault) (nav shares : ℚ) : ℚ :=
  nav * shares / rv.toExact.sharesTotal

/-- The exact share amount for withdrawing `assets` priced at the net asset value `nav` rather than
the vault's exact one. -/
def RawVault.idealSharesWithdrawAt (rv : RawVault) (nav assets : ℚ) : ℚ :=
  rv.toExact.sharesTotal * assets / nav

/-- The `Number` subtraction that prices a withdrawal returns exactly `withdrawNav`, or `depositNav` when the loss
is waived. Every reachable vault has it, its loss being zero. -/
def RawVault.WithdrawNavExact (rv : RawVault) (waiveUnrealizedLoss : Bool) : Prop :=
  ∃ assetsTotal netAssetValue : Number,
    rv.assetsTotal = .ok assetsTotal ∧
    assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => rv.lossUnrealized) .to_nearest = .ok netAssetValue ∧
    netAssetValue.toRat = (if waiveUnrealizedLoss then rv.depositNav else rv.withdrawNav)

end XRPL.Model.SingleAssetVault
