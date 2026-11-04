import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical

/-! # Exact-arithmetic reference values for `Vault.deposit`

The ideal (unrounded) exchange quantities and the relative-error budget the
`Vault.deposit` accuracy headlines are stated against. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Relative error budget of the two `.to_nearest` stages (`mul`, then `div`) that price a share count. Each errs by
at most half a step of the coarsest grid, `5 / (2 ^ 63 + 7)`, so two stages stay below `11 / 10 ^ 19`. -/
def sharesε : ℚ := 11 / 10 ^ 19

/-- Relative error of a deposit's share count above the ideal: two exact `.to_nearest`
half-steps, `(1 + 5/(2^63+7))² - 1`, rounded up. -/
def sharesOverε : ℚ := 10842022 / 10 ^ 25

/-- Relative error of a deposit's share count below the ideal, beyond the one share lost to truncation, while the
issuance stays within its `maxRep` cap. -/
def sharesShortε : ℚ := 4879 / 10 ^ 22

/-- The entry checks of a deposit pass: deposits are open in the vault's phase, a donation goes to a vault with
shares, a deposit into an insolvent vault is a donation, and deposits are not blocked. -/
structure Vault.DepositOpen (v : Vault) (isDonation : Bool) (t : UInt32) : Prop where
  phase : (!isDonation && (v.phase t == .investment || v.phase t == .redemption)) = false
  donation : (isDonation && v.sharesTotal.mantissa_ == 0) = false
  insolvent : (v.isInsolvent && !isDonation) = false
  blocked : v.depositBlocked = false

/-- Net asset value used to price a deposit: `assetsTotal`.
Unrealized loss is not subtracted when depositing. -/
def RawVault.depositNav (rv : RawVault) : ℚ :=
  rv.toExact.assetsTotal

/-- The computed total that prices a deposit is exact: the `Number` sum of the cash and the
deployed assets loses no digit. It holds on every reachable vault, where nothing is deployed. -/
def RawVault.DepositNavExact (rv : RawVault) : Prop :=
  ∃ assetsTotal : Number, rv.assetsTotal = .ok assetsTotal ∧ assetsTotal.toRat = rv.depositNav

/-- The exponent of the grid a deposit amount is rounded onto: the post-sum exponent of the vault
total plus the amount, never finer than the vault's base exponent. -/
def Vault.depositExponent (v : Vault) (amountDeposit : STAmount) : Except Error Int := do
  let assetsTotal ← v.assetsTotal
  let amountNumber ← amountDeposit.toNumber .to_nearest
  postSumExponent assetsTotal amountNumber v.baseExponent amountDeposit.numericType

/-- The exact share amount for a deposit, before rounding (XLS-0065): an empty vault issues `amount * 10 ^ scale`
shares, otherwise `sharesTotal * amount / nav`. -/
def RawVault.idealSharesDeposit (rv : RawVault) (amount : ℚ) : ℚ :=
  if rv.toExact.assetsTotal = 0 then amount * (10 : ℚ) ^ rv.scale.toNat
  else rv.toExact.sharesTotal * amount / rv.depositNav

/-- The exact `amountDeposit'` for issuing `shares`, before rounding (XLS-0065): an empty vault takes
`shares / 10 ^ scale`, otherwise `nav * shares / sharesTotal`. -/
def RawVault.idealChargeDeposit (rv : RawVault) (shares : ℚ) : ℚ :=
  if rv.toExact.assetsTotal = 0 then shares / (10 : ℚ) ^ rv.scale.toNat
  else rv.depositNav * shares / rv.toExact.sharesTotal

/-- The exact deposit share amount priced at `nav` instead of the exact total. The model prices at its computed
total, which can sit just below the exact one. -/
def RawVault.idealSharesDepositAt (rv : RawVault) (nav amount : ℚ) : ℚ :=
  if nav = 0 then amount * (10 : ℚ) ^ rv.scale.toNat
  else rv.toExact.sharesTotal * amount / nav

/-- The exact `amountDeposit'` for issuing `shares` priced at the net asset value `nav` rather than
the vault's exact total. -/
def RawVault.idealChargeDepositAt (rv : RawVault) (nav shares : ℚ) : ℚ :=
  if nav = 0 then shares / (10 : ℚ) ^ rv.scale.toNat
  else nav * shares / rv.toExact.sharesTotal

end XRPL.Model.SingleAssetVault
