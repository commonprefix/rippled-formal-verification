import XRPL.FFI.CommonFFI
import XRPL.Model.Protocol.IntAmount


namespace XRPL.FFI

open XRPL.Model.Protocol (IntAmount Number rounding_mode Error)

@[export lean_int_amount_of_number]
def lean_int_amount_of_number (n : Number) (mode : rounding_mode) : Except Error Int64 :=
  (IntAmount.ofNumber n mode).map (·.value)

@[export lean_int_amount_to_number]
def lean_int_amount_to_number (v : Int64) (mode : rounding_mode) : Except Error Number :=
  IntAmount.toNumber { value := v } mode

end XRPL.FFI
