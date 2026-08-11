import XRPL.Model.Protocol.Number

namespace XRPL.Model.Protocol

--structure TenthBips32 where
--  value : UInt32
--  deriving DecidableEq, Repr, BEq

abbrev TenthBips32 := UInt32

def kTenthBipsPerUnity : TenthBips32 := ⟨100000⟩

def tenthBipsOfValue (value : Number) (bips : TenthBips32) (mode : rounding_mode)
    : Except Error Number := do
  let rate := Number.ofInt64 bips.value.toUInt64.toInt64
  let unity := Number.ofInt64 kTenthBipsPerUnity.value.toUInt64.toInt64
  (← value.operator_mul rate mode).operator_div unity mode

end XRPL.Model.Protocol
