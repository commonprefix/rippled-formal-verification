import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (encodeAsset encodeSTAmount encodeNumber decodeMode)
open XRPL.Model.Protocol (Number STAmount Asset)

-- status: 0 = ok, 1 = threw. code: 0 = rounded (STAmount fields valid), else the rejection TER.
-- Only 8-byte and 1-byte fields so the C++ decode offsets are predictable
-- (8-byte group first in decl order: 0, 8, 16; then 1-byte group: 24, 25, 26).
structure FFIRoundedDepositResult where
  code : Int64
  mValue : UInt64
  mOffset : Int64
  assetKind : UInt8
  mIsNegative : UInt8
  status : UInt8

-- status: 0 = ok, 1 = threw. hasError: 1 if error TER present (errorCode valid).
-- Scalar layout: 8-byte group in decl order (0,8,…,80), then 1-byte group (88,89,…,96).
structure FFIDepositResult where
  amountValue : UInt64
  amountOffset : Int64
  sharesValue : UInt64
  sharesOffset : Int64
  assetsTotalMantissa : UInt64
  assetsTotalExponent : Int64
  assetsAvailableMantissa : UInt64
  assetsAvailableExponent : Int64
  sharesTotalMantissa : UInt64
  sharesTotalExponent : Int64
  errorCode : Int64
  amountKind : UInt8
  amountNegative : UInt8
  sharesKind : UInt8
  sharesNegative : UInt8
  assetsTotalNegative : UInt8
  assetsAvailableNegative : UInt8
  sharesTotalNegative : UInt8
  hasError : UInt8
  status : UInt8

def encodeRoundedDeposit (r : Except String RoundedDepositResult) : FFIRoundedDepositResult :=
  match r with
  | .error _ => ⟨0, 0, 0, 0, 0, 1⟩                          -- threw: status = 1
  | .ok (.rejected t) => ⟨t.code.toInt64, 0, 0, 0, 0, 0⟩    -- error code set, status = 0
  | .ok (.rounded s) =>
      ⟨0, s.mantissa, s.exponent.toInt64, encodeAsset s.asset, (if s.negative then 1 else 0), 0⟩

@[export lean_rounded_deposit_amount]
def lean_rounded_deposit_amount (vault : Vault) (amountDeposit : STAmount) : FFIRoundedDepositResult :=
  encodeRoundedDeposit (vault.roundedDepositAmount amountDeposit)

def encodeDeposit (r : Except String DepositResult) : FFIDepositResult :=
  match r with
  | .error _ =>
    { amountValue := 0, amountOffset := 0, sharesValue := 0, sharesOffset := 0,
      assetsTotalMantissa := 0, assetsTotalExponent := 0,
      assetsAvailableMantissa := 0, assetsAvailableExponent := 0,
      sharesTotalMantissa := 0, sharesTotalExponent := 0,
      errorCode := 0, amountKind := 0, amountNegative := 0,
      sharesKind := 0, sharesNegative := 0, assetsTotalNegative := 0, assetsAvailableNegative := 0,
      sharesTotalNegative := 0, hasError := 0, status := 1 }
  | .ok d =>
    let a  := encodeSTAmount d.amountDeposit'
    let s  := encodeSTAmount d.sharesIssued
    let atn := encodeNumber d.vault'.assetsTotal
    let aan := encodeNumber d.vault'.assetsAvailable
    let stn := encodeNumber d.vault'.sharesTotal
    { amountValue := a.mValue, amountOffset := a.mOffset,
      sharesValue := s.mValue, sharesOffset := s.mOffset,
      assetsTotalMantissa := atn.mantissa, assetsTotalExponent := atn.exponent,
      assetsAvailableMantissa := aan.mantissa, assetsAvailableExponent := aan.exponent,
      sharesTotalMantissa := stn.mantissa, sharesTotalExponent := stn.exponent,
      errorCode := match d.error with | some t => t.code.toInt64 | none => 0,
      amountKind := a.assetKind, amountNegative := a.mIsNegative,
      sharesKind := s.assetKind, sharesNegative := s.mIsNegative,
      assetsTotalNegative := atn.negative, assetsAvailableNegative := aan.negative, sharesTotalNegative := stn.negative,
      hasError := if d.error.isSome then 1 else 0,
      status := 0 }

@[export lean_vault_deposit]
def lean_vault_deposit (vault : Vault) (amountDeposit : STAmount) (isDonation : UInt8)
    : FFIDepositResult :=
  encodeDeposit (vault.deposit amountDeposit (isDonation != 0))

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (assetsAvailable : Number) (asset : Asset) (scale : UInt8)
    (sharesTotal : Number) (sharesAsset : Asset) (interestUnrealized : Number) : Vault :=
  { assetsTotal, assetsAvailable, asset, scale, sharesTotal, sharesAsset, interestUnrealized }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vs : Vault) : Number := vs.assetsTotal

@[export lean_vault_state_asset]
def lean_vault_state_asset (vs : Vault) : Asset := vs.asset
