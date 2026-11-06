import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.STAmount


namespace XRPL.FFI

open XRPL.Model.Protocol

@[export lean_st_amount_build]
def lean_st_amount_build (numericType : NumericType) (mantissa : UInt64) (offset : Int64)
    (negative : UInt8) : STAmount :=
  STAmount.unchecked numericType mantissa offset.toInt (negative != 0)
@[export lean_st_amount_numeric_type]
def lean_st_amount_numeric_type (s : STAmount) : NumericType := s.numericType
@[export lean_st_amount_mantissa]
def lean_st_amount_mantissa (s : STAmount) : UInt64 := s.mantissa
@[export lean_st_amount_offset]
def lean_st_amount_offset (s : STAmount) : Int64 := s.exponent.toInt64
@[export lean_st_amount_negative]
def lean_st_amount_negative (s : STAmount) : UInt8 := if s.negative then 1 else 0

@[export lean_stamount_are_comparable]
def lean_stamount_are_comparable (a b : STAmount) : UInt8 :=
  if STAmount.areComparable a b then 1 else 0

-- Integral (XRP or MPT) amount as a plain int64.
@[export lean_stamount_int_amount]
def lean_stamount_int_amount (s : STAmount) : Except Error Int64 :=
  s.intAmount.map (·.value)

@[export lean_stamount_iou]
def lean_stamount_iou (s : STAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  s.iou mode

@[export lean_stamount_to_number]
def lean_stamount_to_number (s : STAmount) (mode : rounding_mode) : Except Error Number :=
  s.toNumber mode

@[export lean_stamount_unchecked_from_int64]
def lean_stamount_unchecked_from_int64 (numericType : NumericType) (v : Int64) (offset : Int64)
    : STAmount :=
  STAmount.uncheckedFromInt64 numericType v offset.toInt

@[export lean_stamount_checked]
def lean_stamount_checked (numericType : NumericType) (mValue : UInt64) (mOffset : Int64)
    (mIsNegative : UInt8) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.checked numericType mValue mOffset.toInt (mIsNegative != 0)
    mode

@[export lean_stamount_of_number]
def lean_stamount_of_number (numericType : NumericType) (n : Number) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.ofNumber numericType n mode

@[export lean_stamount_eq]
def lean_stamount_eq (a b : STAmount) : UInt8 :=
  if STAmount.operator_eq a b then 1 else 0

@[export lean_stamount_lt]
def lean_stamount_lt (a b : STAmount) : Except Error Bool :=
  STAmount.operator_lt a b

@[export lean_stamount_le]
def lean_stamount_le (a b : STAmount) : Except Error Bool :=
  STAmount.operator_le a b

@[export lean_stamount_gt]
def lean_stamount_gt (a b : STAmount) : Except Error Bool :=
  STAmount.operator_gt a b

@[export lean_stamount_neg]
def lean_stamount_neg (s : STAmount) : STAmount := s.operator_neg

@[export lean_stamount_add]
def lean_stamount_add (a b : STAmount) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.operator_add a b mode

@[export lean_stamount_sub]
def lean_stamount_sub (a b : STAmount) (mode : rounding_mode) : Except Error STAmount :=
  STAmount.operator_sub a b mode

-- C++ `roundToScale`.
@[export lean_stamount_round_to_exponent]
def lean_stamount_round_to_exponent (s : STAmount) (scale : Int64) (mode : rounding_mode)
    : Except Error STAmount :=
  STAmount.roundToExponent s scale.toInt mode

end XRPL.FFI
