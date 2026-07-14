import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (encodeAsset encodeSTAmount encodeNumber)
open XRPL.Model.Protocol (Number STAmount Asset)
open XRPL.Model.SingleAssetVault

-- Clawback result in C++ primitives. Layout mirrors FFIDepositResult (identical C++ decoder):
-- 8-byte group in decl order (0,8,…,80), then 1-byte group (88,89,…,96).
-- status: 0 = ok, 1 = threw. hasError: 1 if error TER present (errorCode valid).
structure FFIClawbackResult where
  assetsValue : UInt64
  assetsOffset : Int64
  sharesValue : UInt64
  sharesOffset : Int64
  assetsTotalMantissa : UInt64
  assetsTotalExponent : Int64
  assetsAvailableMantissa : UInt64
  assetsAvailableExponent : Int64
  sharesTotalMantissa : UInt64
  sharesTotalExponent : Int64
  errorCode : Int64
  assetsKind : UInt8
  assetsNegative : UInt8
  sharesKind : UInt8
  sharesNegative : UInt8
  assetsTotalNegative : UInt8
  assetsAvailableNegative : UInt8
  sharesTotalNegative : UInt8
  hasError : UInt8
  status : UInt8

def encodeClawback (r : Except String ClawbackResult) : FFIClawbackResult :=
  match r with
  | .error _ =>
    { assetsValue := 0, assetsOffset := 0, sharesValue := 0, sharesOffset := 0,
      assetsTotalMantissa := 0, assetsTotalExponent := 0,
      assetsAvailableMantissa := 0, assetsAvailableExponent := 0,
      sharesTotalMantissa := 0, sharesTotalExponent := 0,
      errorCode := 0, assetsKind := 0, assetsNegative := 0,
      sharesKind := 0, sharesNegative := 0, assetsTotalNegative := 0, assetsAvailableNegative := 0,
      sharesTotalNegative := 0, hasError := 0, status := 1 }
  | .ok d =>
    let a  := encodeSTAmount d.assetsRecovered
    let s  := encodeSTAmount d.sharesDestroyed
    let atn := encodeNumber d.vault'.assetsTotal
    let aan := encodeNumber d.vault'.assetsAvailable
    let stn := encodeNumber d.vault'.sharesTotal
    { assetsValue := a.mValue, assetsOffset := a.mOffset,
      sharesValue := s.mValue, sharesOffset := s.mOffset,
      assetsTotalMantissa := atn.mantissa, assetsTotalExponent := atn.exponent,
      assetsAvailableMantissa := aan.mantissa, assetsAvailableExponent := aan.exponent,
      sharesTotalMantissa := stn.mantissa, sharesTotalExponent := stn.exponent,
      errorCode := match d.error with | some t => t.code.toInt64 | none => 0,
      assetsKind := a.assetKind, assetsNegative := a.mIsNegative,
      sharesKind := s.assetKind, sharesNegative := s.mIsNegative,
      assetsTotalNegative := atn.negative, assetsAvailableNegative := aan.negative,
      sharesTotalNegative := stn.negative,
      hasError := if d.error.isSome then 1 else 0,
      status := 0 }

-- doApply: clawback all shares (byShares != 0) or a specific asset amount (byShares = 0).
@[export lean_vault_clawback]
def lean_vault_clawback (vault : Vault) (amount : STAmount) (byShares : UInt8) : FFIClawbackResult :=
  let clawbackAmount :=
    if byShares != 0 then AmountClawback.vaultShares else AmountClawback.vaultAssets amount
  encodeClawback (clawback vault clawbackAmount)

-- Preclaim check: whether the vault's shares can be clawed back, and if so the full share
-- amount (as an STAmount) that would be recovered. code: 0 = ok (STAmount valid), else the TER.
structure FFICanClawbackResult where
  code : Int64
  mValue : UInt64
  mOffset : Int64
  assetKind : UInt8
  mIsNegative : UInt8
  status : UInt8

def encodeCanClawback (r : Except String CanClawbackVaultSharesResult) : FFICanClawbackResult :=
  match r with
  | .error _ => ⟨0, 0, 0, 0, 0, 1⟩                       -- threw: status = 1
  | .ok (.error t) => ⟨t.code.toInt64, 0, 0, 0, 0, 0⟩    -- error code set, status = 0
  | .ok (.assets s) =>
      ⟨0, s.mantissa, s.exponent.toInt64, encodeAsset s.asset, (if s.negative then 1 else 0), 0⟩

@[export lean_can_clawback_vault_shares]
def lean_can_clawback_vault_shares (vault : Vault) : FFICanClawbackResult :=
  encodeCanClawback (canClawbackVaultShares vault)
