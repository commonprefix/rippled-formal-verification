namespace XRPL.Model.Protocol

/-- Error conditions surfaced by the model's fallible arithmetic and amount operations.
Replaces the former `String` error payload. -/
inductive Error where
  | overflow
  | divByZero
  | outOfRange
  | normalize1
  | normalize1_5
  | normalize2
  | notComparable
  | cannotConvert
  | notLawful
  | badInput
  | wrap
deriving DecidableEq, Repr, Inhabited

-- Detect an error C++ throws as `std::overflow_error`. Every `Number` failure is one, including division by zero.
def isOverflow (e : Error) : Bool :=
  match e with
  | .overflow | .normalize1 | .normalize1_5 | .normalize2 | .divByZero => true
  | _ => false

end XRPL.Model.Protocol
