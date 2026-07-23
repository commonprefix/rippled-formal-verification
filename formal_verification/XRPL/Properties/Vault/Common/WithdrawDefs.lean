import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Exact-arithmetic reference values for `Vault.withdraw`

The ideal (unrounded) exchange quantities the `Vault.withdraw` accuracy
headlines are stated against, plus the `WithdrawNavExact` pricing hypothesis
and the `navSlack` budget of the two pricing subtractions. Kept in `Common` so
both the headline file and its proof files can see them. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Net asset value backing the shares for withdrawal:
`assetsTotal - interestUnrealized - lossUnrealized`. -/
def Vault.withdrawNav (v : Vault) : ℚ :=
  v.toExact.assetsTotal - v.toExact.interestUnrealized - v.toExact.lossUnrealized

/-- The exact `assets'` for redeeming `shares`, before any rounding. The XLS-0065
exchange formula `nav * shares / sharesTotal`, where the pricing `nav` is
`withdrawNav`, or `depositNav` when `waiveUnrealizedLoss` is `true` and the
unrealized loss is not subtracted. -/
def Vault.idealAssetsWithdraw (v : Vault) (waiveUnrealizedLoss : Bool) (shares : ℚ) : ℚ :=
  (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav) *
    shares / v.toExact.sharesTotal

/-- The exact share amount for withdrawing `assets`, before any rounding. The
XLS-0065 exchange formula `sharesTotal * assets / nav`, with the same pricing
`nav` as `idealAssetsWithdraw`. -/
def Vault.idealSharesWithdraw (v : Vault) (waiveUnrealizedLoss : Bool) (assets : ℚ) : ℚ :=
  v.toExact.sharesTotal * assets /
    (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav)

/-- The stored pricing computation loses nothing: the two `Number`
subtractions producing the withdrawal net asset value return exactly
`withdrawNav` (or `depositNav` when the loss is waived). Holds in particular
whenever `interestUnrealized` and `lossUnrealized` are both zero, the state
every modeled operation preserves. Without it the first subtraction can round
away digits that the second subtraction cancels, and no relative accuracy
bound against the exact stored fields exists. -/
def Vault.WithdrawNavExact (v : Vault) (waiveUnrealizedLoss : Bool) : Prop :=
  ∃ netAssetValue netAssetValue' : Number,
    v.assetsTotal.operator_sub v.interestUnrealized .to_nearest = .ok netAssetValue ∧
    netAssetValue.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue' ∧
    netAssetValue'.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav)

/-- Bound on how far the computed pricing value can sit from the exact
`assetsTotal - interestUnrealized - lossUnrealized`: each of the two
subtractions is correctly rounded, so each contributes at most `depositε`
relative to its exact operand magnitudes. -/
def Vault.navSlack (v : Vault) : ℚ :=
  depositε * (|v.toExact.assetsTotal| +
    |v.toExact.assetsTotal - v.toExact.interestUnrealized|)

end XRPL.Model.SingleAssetVault
