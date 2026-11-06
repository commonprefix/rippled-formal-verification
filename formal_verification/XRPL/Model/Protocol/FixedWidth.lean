import XRPL.Model.Protocol.Errors

/-! # Fixed-width integers

The model's 128-bit integer, and checked operations on the fixed-width integers. A checked operation
returns `Error.wrap` when its exact result does not fit its type, where C++ wraps around. -/

namespace XRPL.Model.Protocol

abbrev UInt128 := BitVec 128

def toUInt128 (x : UInt64) : UInt128 := x.toBitVec.zeroExtend 128
def toUInt64 (x : UInt128) : UInt64 := ⟨x.truncate 64⟩

def _root_.UInt32.addChecked (a b : UInt32) : Except Error UInt32 :=
  if a.toNat + b.toNat < 2 ^ 32 then .ok (a + b) else .error .wrap

def _root_.UInt32.subChecked (a b : UInt32) : Except Error UInt32 :=
  if b ≤ a then .ok (a - b) else .error .wrap

def _root_.UInt32.toInt64 (a : UInt32) : Int64 := a.toUInt64.toInt64

def _root_.Nat.toInt64Checked (n : Nat) : Except Error Int64 :=
  if n < 2 ^ 63 then .ok n.toInt64 else .error .wrap

def _root_.Int.toInt64Checked (i : Int) : Except Error Int64 :=
  if -9223372036854775808 ≤ i ∧ i ≤ 9223372036854775807 then .ok i.toInt64 else .error .wrap

def _root_.UInt64.toInt64Checked (a : UInt64) : Except Error Int64 :=
  if a.toNat < 2 ^ 63 then .ok a.toInt64 else .error .wrap

def _root_.Int64.toUInt64Checked (a : Int64) : Except Error UInt64 :=
  if 0 ≤ a then .ok a.toUInt64 else .error .wrap

def _root_.Int64.negChecked (a : Int64) : Except Error Int64 :=
  if a ≠ Int64.minValue then .ok (-a) else .error .wrap

def _root_.Int64.addChecked (a b : Int64) : Except Error Int64 :=
  if -9223372036854775808 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ 9223372036854775807 then .ok (a + b)
  else .error .wrap

def _root_.Int64.mulChecked (a b : Int64) : Except Error Int64 :=
  if -9223372036854775808 ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 9223372036854775807 then .ok (a * b)
  else .error .wrap

def _root_.Int64.magnitude (a : Int64) : UInt64 := a.toInt.natAbs.toUInt64

def _root_.UInt64.addChecked (a b : UInt64) : Except Error UInt64 :=
  if a.toNat + b.toNat < 2 ^ 64 then .ok (a + b) else .error .wrap

def _root_.UInt64.subChecked (a b : UInt64) : Except Error UInt64 :=
  if b ≤ a then .ok (a - b) else .error .wrap

def _root_.UInt64.mulChecked (a b : UInt64) : Except Error UInt64 :=
  if a.toNat * b.toNat < 2 ^ 64 then .ok (a * b) else .error .wrap

def toUInt64Checked (x : UInt128) : Except Error UInt64 :=
  if x.toNat < 2 ^ 64 then .ok (toUInt64 x) else .error .wrap

def _root_.BitVec.subChecked {w : Nat} (a b : BitVec w) : Except Error (BitVec w) :=
  if b.toNat ≤ a.toNat then .ok (a - b) else .error .wrap

def _root_.BitVec.addChecked {w : Nat} (a b : BitVec w) : Except Error (BitVec w) :=
  if a.toNat + b.toNat < 2 ^ w then .ok (a + b) else .error .wrap

def _root_.BitVec.mulChecked {w : Nat} (a b : BitVec w) : Except Error (BitVec w) :=
  if a.toNat * b.toNat < 2 ^ w then .ok (a * b) else .error .wrap

end XRPL.Model.Protocol
