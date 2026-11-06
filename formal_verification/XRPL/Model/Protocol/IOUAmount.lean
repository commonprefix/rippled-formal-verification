import XRPL.Model.Protocol.Number


namespace XRPL.Model.Protocol

structure IOUAmount where
  mantissa_ : Int64
  exponent_ : Int
  deriving DecidableEq, Repr

def IOUAmount.zero : IOUAmount := { mantissa_ := 0, exponent_ := -100 }

def IOUAmount.signum (x : IOUAmount) : Int :=
  if x.mantissa_ < 0 then -1 else if x.mantissa_ != 0 then 1 else 0

def IOUAmount.toRat (a : IOUAmount) : ℚ :=
  let sign : Int := if a.mantissa_ < 0 then -1 else 1
  let m : Int := a.mantissa_.toInt.natAbs
  if a.exponent_ ≥ 0 then
    mkRat (sign * m * (10 : Int) ^ a.exponent_.toNat) 1
  else
    mkRat (sign * m) ((10 : Nat) ^ (-a.exponent_).toNat)

def IOUAmount.fromNumber (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  match n.normalizeToRange cMinValue cMaxValue mode with
  | .error e => .error e
  | .ok (m, e) => .ok { mantissa_ := m, exponent_ := e }

def IOUAmount.normalize (a : IOUAmount) (mode : rounding_mode) : Except Error IOUAmount :=
  if a.mantissa_ == 0 then .ok IOUAmount.zero
  else
    -- `Number{mantissa_, exponent_}` ctor normalizes against largeRange (throws on overflow).
    match Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | .error e => .error e
    | .ok v =>
      match IOUAmount.fromNumber v mode with
      | .error e => .error e
      | .ok result =>
        if result.exponent_ > cMaxOffset then .error .overflow
        else if result.exponent_ < cMinOffset then .ok IOUAmount.zero
        else .ok result

-- C++ `IOUAmount(mantissa_type, exponent_type)`
def IOUAmount.ofMantissaExp (m : Int64) (e : Int) (mode : rounding_mode) : Except Error IOUAmount :=
  IOUAmount.normalize ⟨m, e⟩ mode

-- C++ `explicit IOUAmount(Number const&)`
def IOUAmount.ofNumber (n : Number) (mode : rounding_mode) : Except Error IOUAmount :=
  match IOUAmount.fromNumber n mode with
  | .error e => .error e
  | .ok r =>
    if r.exponent_ > cMaxOffset then .error .overflow
    else if r.exponent_ < cMinOffset then .ok IOUAmount.zero
    else .ok r

-- C++ `operator Number()` = `Number{mantissa_, exponent_}`
def IOUAmount.toNumber (a : IOUAmount) (mode : rounding_mode) : Except Error Number :=
  Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode

def IOUAmount.operator_add (x y : IOUAmount) (mode : rounding_mode)
    : Except Error IOUAmount :=
  if y.mantissa_ == 0 then .ok x
  else if x.mantissa_ == 0 then .ok y
  else
    match x.toNumber mode with
    | .error e => .error e
    | .ok xn =>
      match y.toNumber mode with
      | .error e => .error e
      | .ok yn =>
        match Number.operator_add xn yn mode with
        | .error e => .error e
        | .ok sum => IOUAmount.ofNumber sum mode

end XRPL.Model.Protocol
