import XRPL.NewModel.SingleAssetVault.VaultDeposit
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (FFIRoundedDepositResult FFIDepositResult encodeAsset encodeSTAmount encodeNumber decodeMode)
open XRPL.Model.Protocol (Number STAmount Asset)

def encodeRoundedDeposit (r : Except String RoundedDepositResult) : FFIRoundedDepositResult :=
  match r with
  | .error _ => ⟨0, 0, 0, 0, 0, 1⟩                          -- threw: status = 1
  | .ok (.rejected t) => ⟨t.code.toInt64, 0, 0, 0, 0, 0⟩    -- error code set, status = 0
  | .ok (.rounded s) =>
      ⟨0, s.mantissa, s.exponent.toInt64, encodeAsset s.asset, (if s.negative then 1 else 0), 0⟩

@[export lean_rounded_deposit_amount]
def lean_rounded_deposit_amount (vault : Vault) (amountDeposit : STAmount) : FFIRoundedDepositResult :=
  encodeRoundedDeposit (vault.roundedDepositAmount amountDeposit)

-- TEMPORARY (rounding-mode probe): same as above but with the roundToScale mode parameterized.
@[export lean_rounded_deposit_amount_mode]
def lean_rounded_deposit_amount_mode (vault : Vault) (amountDeposit : STAmount) (mode : UInt8)
    : FFIRoundedDepositResult :=
  encodeRoundedDeposit (vault.roundedDepositAmountMode amountDeposit (decodeMode mode))

-- TEMPORARY (rounding-mode probe): both stages parameterized (scale computation, final round).
@[export lean_rounded_deposit_amount_modes]
def lean_rounded_deposit_amount_modes (vault : Vault) (amountDeposit : STAmount)
    (scaleRounding roundMode : UInt8) : FFIRoundedDepositResult :=
  encodeRoundedDeposit
    (vault.roundedDepositAmountModes amountDeposit (decodeMode scaleRounding) (decodeMode roundMode))

def encodeDeposit (r : Except String DepositResult) : FFIDepositResult :=
  match r with
  | .error _ =>
    { amountValue := 0, amountOffset := 0, sharesValue := 0, sharesOffset := 0,
      assetsTotalMantissa := 0, assetsTotalExponent := 0,
      sharesTotalMantissa := 0, sharesTotalExponent := 0,
      errorCode := 0, amountKind := 0, amountNegative := 0,
      sharesKind := 0, sharesNegative := 0, assetsTotalNegative := 0,
      sharesTotalNegative := 0, hasError := 0, status := 1 }
  | .ok d =>
    let a  := encodeSTAmount d.amountDeposit'
    let s  := encodeSTAmount d.sharesIssued
    let atn := encodeNumber d.vault'.assetsTotal
    let stn := encodeNumber d.vault'.sharesTotal
    { amountValue := a.mValue, amountOffset := a.mOffset,
      sharesValue := s.mValue, sharesOffset := s.mOffset,
      assetsTotalMantissa := atn.mantissa, assetsTotalExponent := atn.exponent,
      sharesTotalMantissa := stn.mantissa, sharesTotalExponent := stn.exponent,
      errorCode := match d.error with | some t => t.code.toInt64 | none => 0,
      amountKind := a.assetKind, amountNegative := a.mIsNegative,
      sharesKind := s.assetKind, sharesNegative := s.mIsNegative,
      assetsTotalNegative := atn.negative, sharesTotalNegative := stn.negative,
      hasError := if d.error.isSome then 1 else 0,
      status := 0 }

@[export lean_vault_deposit]
def lean_vault_deposit (vault : Vault) (amountDeposit : STAmount) (isDonation : UInt8)
    : FFIDepositResult :=
  encodeDeposit (vault.deposit amountDeposit (isDonation != 0))

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (asset : Asset) (scale : UInt8)
    (sharesTotal : Number) (sharesAsset : Asset) (interestUnrealized : Number) : Vault :=
  { assetsTotal, asset, scale, sharesTotal, sharesAsset, interestUnrealized }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vs : Vault) : Number := vs.assetsTotal

@[export lean_vault_state_asset]
def lean_vault_state_asset (vs : Vault) : Asset := vs.asset
