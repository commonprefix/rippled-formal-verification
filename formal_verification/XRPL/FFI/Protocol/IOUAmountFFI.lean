import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.IOUAmount


namespace XRPL.FFI

open XRPL.Model.Protocol (IOUAmount Number rounding_mode Error)

@[export lean_iou_amount_build]
def lean_iou_amount_build (mantissa exponent : Int64) : IOUAmount :=
  { mantissa_ := mantissa, exponent_ := exponent.toInt }
@[export lean_iou_amount_mantissa]
def lean_iou_amount_mantissa (a : IOUAmount) : Int64 := a.mantissa_
@[export lean_iou_amount_exponent]
def lean_iou_amount_exponent (a : IOUAmount) : Int64 := a.exponent_.toInt64

@[export lean_iou_from_number]
def lean_iou_from_number (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.fromNumber n mode

@[export lean_iou_of_mantissa_exp]
def lean_iou_of_mantissa_exp (m : Int64) (e : Int64) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.ofMantissaExp m e.toInt mode

@[export lean_iou_of_number]
def lean_iou_of_number (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.ofNumber n mode

@[export lean_iou_to_number]
def lean_iou_to_number (a : IOUAmount) (mode : rounding_mode) : Except Error Number :=
  a.toNumber mode

@[export lean_iou_add]
def lean_iou_add (a b : IOUAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.operator_add a b mode

end XRPL.FFI
