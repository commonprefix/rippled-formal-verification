import XRPL.Model.Protocol.IntAmount
import XRPL.Model.Protocol.IOUAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType


namespace XRPL.Model.Protocol

def kMinValue : UInt64 := 1000000000000000
def kMaxValue : UInt64 := 9999999999999999

structure STAmount where
  mNumericType : NumericType
  mValue : UInt64
  mOffset : Int
  mIsNegative : Bool
  deriving DecidableEq, Repr

def STAmount.exponent (s : STAmount) : Int := s.mOffset
def STAmount.mantissa (s : STAmount) : UInt64 := s.mValue
def STAmount.integral (s : STAmount) : Bool := s.mNumericType.isIntegral
def STAmount.negative (s : STAmount) : Bool := s.mIsNegative
def STAmount.numericType (s : STAmount) : NumericType := s.mNumericType
def STAmount.isZero (s : STAmount) : Bool := s.mValue == 0

def STAmount.signum (s : STAmount) : Int :=
  if s.mValue == 0 then 0 else if s.mIsNegative then -1 else 1

-- Signed-int64 view of an integral STAmount (`mOffset == 0`).
def STAmount.signedDrops (s : STAmount) : Int :=
  if s.mIsNegative then -(s.mValue.toNat : Int) else (s.mValue.toNat : Int)

-- Two amounts are comparable when they share a representation.
def STAmount.areComparable (lhs rhs : STAmount) : Bool :=
  lhs.mNumericType == rhs.mNumericType

-- Short-circuits `mValue = 0`, mirroring `Number.toRat`'s guard.
def STAmount.toRat (s : STAmount) : ℚ :=
  if s.mValue = 0 then 0
  else
    let sign : Int := if s.mIsNegative then -1 else 1
    let m : Int := s.mValue.toNat
    if s.mOffset ≥ 0 then
      mkRat (sign * m * (10 : Int) ^ s.mOffset.toNat) 1
    else
      mkRat (sign * m) ((10 : Nat) ^ (-s.mOffset).toNat)

-- Integral (XRP/MPT) as a plain int64 amount.
def STAmount.intAmount (s : STAmount) : Except Error IntAmount :=
  if s.integral then do
    let value ← s.signedDrops.toInt64Checked
    return { value }
  else .error .cannotConvert

-- Fractional (IOU).
def STAmount.iou (s : STAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  if s.integral then
    .error .cannotConvert
  else do
    let mantissa ← s.signedDrops.toInt64Checked
    IOUAmount.ofMantissaExp mantissa s.mOffset mode

def STAmount.toNumber (s : STAmount) (mode : rounding_mode) : Except Error Number :=
  if s.integral then
    match s.intAmount with
    | .error e => .error e
    | .ok i => i.toNumber mode
  else
    match s.iou mode with
    | .error e => .error e
    | .ok i => i.toNumber mode

def STAmount.canonicalize (s : STAmount) (mode : rounding_mode) : Except Error STAmount :=
  if s.integral then
    if s.mValue == 0 || s.mOffset ≤ -20 then
      .ok { s with mValue := 0, mOffset := 0, mIsNegative := false }
    else if s.mOffset > s.mNumericType.maxOffset then
      .error .outOfRange
    else
      let num : Number := Number.unchecked s.mIsNegative s.mValue s.mOffset
      match IntAmount.ofNumber num mode with
      | .error e => .error e
      | .ok i =>
        let v : UInt64 := i.value.magnitude
        if v > s.mNumericType.maxValue then .error .outOfRange
        else .ok { s with mValue := v, mOffset := 0, mIsNegative := i.value < 0 }
  else
    match s.iou mode with
    | .error e => .error e
    | .ok i =>
      let neg := i.signum < 0
      .ok { s with mValue := i.mantissa_.magnitude
                 , mOffset := i.exponent_
                 , mIsNegative := neg }

def STAmount.unchecked (mNumericType : NumericType) (mValue : UInt64) (mOffset : Int)
    (mIsNegative : Bool) : STAmount :=
  { mNumericType, mValue, mOffset, mIsNegative }

def STAmount.uncheckedFromInt64 (nt : NumericType) (v : Int64) (offset : Int) : STAmount :=
  if v < 0 then STAmount.unchecked nt v.magnitude offset true
  else STAmount.unchecked nt v.magnitude offset false

def STAmount.checked (nt : NumericType) (mValue : UInt64) (mOffset : Int) (mIsNegative : Bool)
    (mode : rounding_mode) : Except Error STAmount :=
  (STAmount.unchecked nt mValue mOffset mIsNegative).canonicalize mode

-- Zero amount of a numericType (C++ `STAmount(Asset)`), canonicalized. Zero never rounds or overflows.
def STAmount.zero (nt : NumericType) : STAmount :=
  match STAmount.checked nt 0 0 false rounding_mode.to_nearest with
  | .ok s => s
  | .error _ => STAmount.unchecked nt 0 0 false

def STAmount.ofIOUAmount (a : IOUAmount) (mode : rounding_mode) : Except Error STAmount :=
  let neg := a.signum < 0
  (STAmount.unchecked .fractional a.mantissa_.magnitude a.exponent_ neg).canonicalize mode

def STAmount.ofNumber (nt : NumericType) (n : Number) (mode : rounding_mode)
    : Except Error STAmount :=
  let neg : Bool := n.signum < 0
  let working : Number := if neg then n.operator_neg else n
  if nt.isIntegral then
    match working.to_rep mode with
    | .error e => .error e
    | .ok intValue => do
      let value ← intValue.toUInt64Checked
      STAmount.checked nt value 0 neg mode
  else
    match working.normalizeToRange kMinValue kMaxValue mode with
    | .error e => .error e
    | .ok (mantissa, exponent) => do
      let value ← mantissa.toUInt64Checked
      STAmount.checked nt value exponent neg mode

-- C++ `STAmount{asset, value} == value`
def STAmount.equalAfterNumberConvert (nt : NumericType) (value : Number) : Except Error Bool := do
  let stValue ← STAmount.ofNumber nt value .to_nearest
  let numValue ← stValue.toNumber .to_nearest
  return numValue.operator_eq value

-- Checks if Number will be rounded when converted to STAmount
def STAmount.isRounded (nt : NumericType) (value : Number) : Bool :=
  match STAmount.equalAfterNumberConvert nt value with
  | .ok isEqual => !isEqual
  | .error _ => true

def STAmount.operator_eq (lhs rhs : STAmount) : Bool :=
  STAmount.areComparable lhs rhs &&
    lhs.mIsNegative == rhs.mIsNegative &&
    lhs.mOffset == rhs.mOffset &&
    lhs.mValue == rhs.mValue

def STAmount.operator_lt (lhs rhs : STAmount) : Except Error Bool :=
  if !STAmount.areComparable lhs rhs then
    .error .notComparable
  else
    .ok <|
      if lhs.mIsNegative != rhs.mIsNegative then lhs.mIsNegative
      else if lhs.mValue == 0 then
        if rhs.mIsNegative then false else rhs.mValue != 0
      else if rhs.mValue == 0 then false
      else if lhs.mOffset > rhs.mOffset then lhs.mIsNegative
      else if lhs.mOffset < rhs.mOffset then !lhs.mIsNegative
      else if lhs.mValue > rhs.mValue then lhs.mIsNegative
      else if lhs.mValue < rhs.mValue then !lhs.mIsNegative
      else false

def STAmount.operator_le (lhs rhs : STAmount) : Except Error Bool :=
  match STAmount.operator_lt rhs lhs with
  | .error e => .error e
  | .ok lt => .ok (!lt)

def STAmount.operator_gt (lhs rhs : STAmount) : Except Error Bool :=
  STAmount.operator_lt rhs lhs

def STAmount.operator_neg (s : STAmount) : STAmount :=
  if s.mValue == 0 then s else { s with mIsNegative := !s.mIsNegative }

def STAmount.operator_add (v1 v2 : STAmount) (mode : rounding_mode)
    : Except Error STAmount :=
  if !STAmount.areComparable v1 v2 then
    .error .notComparable
  else if v2.mValue == 0 then .ok v1
  else if v1.mValue == 0 then
    STAmount.checked v1.mNumericType v2.mValue v2.mOffset v2.mIsNegative mode
  else if v1.integral then do
    let drops1 ← v1.signedDrops.toInt64Checked
    let drops2 ← v2.signedDrops.toInt64Checked
    let total ← drops1.addChecked drops2
    let sum := STAmount.uncheckedFromInt64 v1.mNumericType total 0
    if v1.mNumericType == .native then .ok sum else sum.canonicalize mode
  else
    match v1.iou mode with
    | .error e => .error e
    | .ok i1 =>
      match v2.iou mode with
      | .error e => .error e
      | .ok i2 =>
        match IOUAmount.operator_add i1 i2 mode with
        | .error e => .error e
        | .ok sumI => STAmount.ofIOUAmount sumI mode

def STAmount.operator_sub (v1 v2 : STAmount) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.operator_add v1 v2.operator_neg mode

def STAmount.roundToExponent (value : STAmount) (exponent : Int) (rounding : rounding_mode)
    : Except Error STAmount :=
  if value.integral then .ok value
  else if value.isZero then .ok value
  else if value.exponent ≥ exponent then .ok value
  else
    match STAmount.checked value.mNumericType kMinValue exponent value.negative rounding with
    | .error e => .error e
    | .ok referenceValue =>
      match STAmount.operator_add value referenceValue rounding with
      | .error e => .error e
      | .ok sum => STAmount.operator_sub sum referenceValue rounding

-- Unifies the two C++ `roundToAsset` overloads: `scale = none` is the in-place
-- 2-arg form (no IOU truncation), `scale = some s` is the 4-arg form.
def STAmount.roundToNumericType (nt : NumericType) (value : Number) (rounding : rounding_mode)
    (scale : Option Int := none) : Except Error Number :=
  match STAmount.ofNumber nt value rounding with
  | .error e => .error e
  | .ok ret =>
    match scale with
    | none => ret.toNumber rounding
    | some s =>
      if ret.integral then ret.toNumber rounding
      else
        match STAmount.roundToExponent ret s rounding with
        | .error e => .error e
        | .ok rounded => rounded.toNumber rounding

def STAmount.isFractionalNonPositive (amount : STAmount) : Except Error Bool :=
  if amount.integral then
    .ok false
  else
    amount.operator_le (STAmount.zero amount.numericType)

end XRPL.Model.Protocol
