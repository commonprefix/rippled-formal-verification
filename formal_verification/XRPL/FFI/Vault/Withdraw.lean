import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (encodeAsset encodeSTAmount encodeNumber)
open XRPL.Model.Protocol (Number STAmount Asset)
open XRPL.Model.SingleAssetVault

-- Withdraw result in C++ primitives. Layout mirrors FFIDepositResult so the C++ decoder is
-- identical: 8-byte group in decl order (0,8,…,80), then 1-byte group (88,89,…,96).
-- status: 0 = ok, 1 = threw. hasError: 1 if error TER present (errorCode valid).
structure FFIWithdrawResult where
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

def encodeWithdraw (r : Except String WithdrawResult) : FFIWithdrawResult :=
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
    let a  := encodeSTAmount d.assets'
    let s  := encodeSTAmount d.sharesBurned
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

-- doApply: withdraw by assets (byShares = 0) or by shares (byShares != 0).
@[export lean_vault_withdraw]
def lean_vault_withdraw (vault : Vault) (amount : STAmount) (byShares : UInt8) : FFIWithdrawResult :=
  let withdrawAmount :=
    if byShares != 0 then WithdrawAmount.vaultShares amount else WithdrawAmount.vaultAssets amount
  encodeWithdraw (vault.withdraw withdrawAmount)

-- Preclaim arithmetic: the asset equivalent of a share-denominated withdrawal (feeds the
-- withdrawal-limit check). waiveUnrealizedLoss != 0 when the account is the sole shareholder.
@[export lean_shares_to_assets_withdraw]
def lean_shares_to_assets_withdraw (vault : Vault) (shares : STAmount) (waiveUnrealizedLoss : UInt8)
    : XRPL.FFI.FFISTAmountResult :=
  XRPL.FFI.encodeSTAmountResult (vault.sharesToAssetsWithdraw shares (waiveUnrealizedLoss != 0))
