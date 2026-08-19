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
assetsTotal minus lossUnrealized. -/
def Vault.withdrawNav (v : Vault) : ℚ :=
  v.toExact.assetsTotal - v.toExact.lossUnrealized

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

/-- The stored pricing computation loses nothing: the single `Number`
subtraction producing the withdrawal net asset value returns exactly
`withdrawNav` (or `depositNav` when the loss is waived). Holds in particular
whenever `lossUnrealized` is zero, the state every modeled operation preserves.
Without it the subtraction can round away digits, and no relative accuracy
bound against the exact stored fields exists. -/
def Vault.WithdrawNavExact (v : Vault) (waiveUnrealizedLoss : Bool) : Prop :=
  ∃ netAssetValue : Number,
    v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue ∧
    netAssetValue.toRat = (if waiveUnrealizedLoss then v.depositNav else v.withdrawNav)

/-- Bound on how far the computed pricing value can sit from the exact
assetsTotal minus lossUnrealized: the single subtraction is correctly rounded,
contributing at most `depositε` relative to its exact operand magnitude. -/
def Vault.navSlack (v : Vault) : ℚ :=
  depositε * (v.toExact.assetsTotal + v.toExact.assetsTotal)

end XRPL.Model.SingleAssetVault
