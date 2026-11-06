import XRPL.Model.Protocol.Number


namespace XRPL.Model.Protocol

-- Integer-valued amount (an int64 at offset 0). XRP and MPT share this one representation.
structure IntAmount where
  value : Int64
  deriving DecidableEq, Repr

def IntAmount.toRat (x : IntAmount) : ℚ := (x.value.toInt : ℚ)

def IntAmount.ofNumber (n : Number) (mode : rounding_mode) : Except Error IntAmount :=
  match n.to_rep mode with
  | .ok r => .ok { value := r }
  | .error e => .error e

def IntAmount.toNumber (x : IntAmount) (mode : rounding_mode) : Except Error Number :=
  Number.from_rep x.value 0 largeRange.min largeRange.max mode

end XRPL.Model.Protocol
