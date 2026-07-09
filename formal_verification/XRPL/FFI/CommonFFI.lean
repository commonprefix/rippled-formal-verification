import XRPL.Model.Protocol.IOUAmount
import XRPL.Model.Protocol.MPTAmount
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.XRPAmount
import XRPL.Model.Protocol.TER

namespace XRPL.FFI

open XRPL.Model.Protocol

structure FFINumberResult where
  mantissa : UInt64
  exponent : Int64
  status : UInt8
  negative : UInt8

structure FFIBoolResult where
  value : UInt8
  status : UInt8

structure FFIMPTResult where
  value : Int64
  status : UInt8

structure FFIXRPResult where
  drops : Int64
  status : UInt8

structure FFIIOUResult where
  mantissa : Int64
  exponent : Int64
  status : UInt8

structure FFITERResult where
  code : Int32
  status : UInt8

-- assetKind: 0 = XRP, 1 = IOU (noIssue), 2 = MPT (ffiMPTIssue).
structure FFISTAmountResult where
  assetKind : UInt8
  mValue : UInt64
  mOffset : Int64
  mIsNegative : UInt8
  status : UInt8

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
-- Scalar layout: 8-byte group in decl order (0,8,…,64), then 1-byte group (72,73,…,79).
structure FFIDepositResult where
  amountValue : UInt64
  amountOffset : Int64
  sharesValue : UInt64
  sharesOffset : Int64
  assetsTotalMantissa : UInt64
  assetsTotalExponent : Int64
  sharesTotalMantissa : UInt64
  sharesTotalExponent : Int64
  errorCode : Int64
  amountKind : UInt8
  amountNegative : UInt8
  sharesKind : UInt8
  sharesNegative : UInt8
  assetsTotalNegative : UInt8
  sharesTotalNegative : UInt8
  hasError : UInt8
  status : UInt8

def ffiMPTIssue : MPTIssue := { mptID := ⟨0⟩ }

def decodeMode (m : UInt8) : rounding_mode := match m.toNat with
  | 0 => .to_nearest | 1 => .towards_zero | 2 => .downward | _ => .upward

def decodeNumber (neg : UInt8) (mant : UInt64) (exp : Int64) : Number :=
  Number.unchecked (neg != 0) mant exp.toInt

def decodeMPT (v : Int64) : MPTAmount := { value_ := v }

def decodeXRP (v : Int64) : XRPAmount := { drops_ := v }

def decodeIOU (m : Int64) (e : Int64) : IOUAmount :=
  { mantissa_ := m, exponent_ := e.toInt }

def decodeAsset (kind : UInt8) : Asset := match kind.toNat with
  | 0 => xrpAsset
  | 1 => .issue noIssue
  | _ => .mptIssue ffiMPTIssue

def decodeSTAmount (kind : UInt8) (mValue : UInt64) (mOffset : Int64)
    (mIsNegative : UInt8) : STAmount :=
  STAmount.unchecked (decodeAsset kind) mValue mOffset.toInt (mIsNegative != 0)

-- `Number.mantissa`/`Number.exponent` apply the C++ transformation
def encodeNumber (n : Number) : FFINumberResult :=
  ⟨n.mantissa.toInt.natAbs.toUInt64, n.exponent.toInt64, 0, if n.negative_ then 1 else 0⟩

def encodeResult (r : Except String Number) : FFINumberResult :=
  match r with
  | .ok n => encodeNumber n
  | .error _ => ⟨0, 0, 1, 0⟩

def encodeMPTResult (r : Except String MPTAmount) : FFIMPTResult :=
  match r with
  | .ok x => ⟨x.value, 0⟩
  | .error _ => ⟨0, 1⟩

def encodeXRPResult (r : Except String XRPAmount) : FFIXRPResult :=
  match r with
  | .ok x => ⟨x.value, 0⟩
  | .error _ => ⟨0, 1⟩

def encodeIOUResult (r : Except String IOUAmount) : FFIIOUResult :=
  match r with
  | .ok x => ⟨x.mantissa, x.exponent.toInt64, 0⟩
  | .error _ => ⟨0, 0, 1⟩

def encodeAsset : Asset → UInt8
  | .issue iss => if iss.isXRP then 0 else 1
  | .mptIssue _ => 2

def encodeSTAmount (s : STAmount) : FFISTAmountResult :=
  let isNegative : UInt8 := if s.negative then 1 else 0
  ⟨encodeAsset s.asset, s.mantissa, s.exponent.toInt64, isNegative, 0⟩

def encodeSTAmountResult (r : Except String STAmount) : FFISTAmountResult :=
  match r with
  | .ok s => encodeSTAmount s
  | .error _ => ⟨0, 0, 0, 0, 1⟩

def encodeBoolResult (r : Except String Bool) : FFIBoolResult :=
  match r with
  | .ok b => ⟨if b then 1 else 0, 0⟩
  | .error _ => ⟨0, 1⟩

def encodeTERResult (r : Except String TER) : FFITERResult :=
  match r with
  | .ok t => ⟨t.code, 0⟩
  | .error _ => ⟨0, 1⟩

end XRPL.FFI
