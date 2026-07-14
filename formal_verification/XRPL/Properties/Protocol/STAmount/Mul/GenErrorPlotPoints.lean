import XRPL.Model.Protocol.STAmount

open XRPL.Model.Protocol

/-- εMulIOUToNearest, exactly as in RoundsWithin.lean. -/
def epsTN : Rat :=
  5 / (2 ^ 63 + 7 : Rat) + (1 / 2) * (1 / (10 : Rat) ^ 15)
    + 5 / (2 ^ 63 + 7 : Rat) * ((1 / 2) * (1 / (10 : Rat) ^ 15))

def iouAsset : Asset := .issue noIssue

/-- Evaluate v1 = v2 = ⟨m, e, neg⟩ through the real model; emit
    `bracket,v1num,v1den,errnum,errden,envnum,envden` (exact rationals).
    Skips overflow (`.error`) and underflow (`result = 0`): both are outside the
    ≤1-ULP theorem, whose hypothesis is `result.mValue ≠ 0`. -/
def emit (bracket : Nat) (m : UInt64) (e : Int) : IO Unit := do
  let v1 : STAmount := ⟨.issue noIssue, m, e, false⟩
  match STAmount.multiply v1 v1 iouAsset .to_nearest with
  | .error _ => pure ()
  | .ok result =>
    if result.mValue == 0 then pure ()          -- underflowed to zero: skip
    else
      let v1r   : Rat := v1.toRat
      let truth : Rat := v1r * v1r
      let err   : Rat := |result.toRat - truth|
      let env   : Rat := truth * epsTN
      IO.println s!"{bracket},{truth.num},{truth.den},{err.num},{err.den},{env.num},{env.den}"

/-- Exponent-field sweep: `eLo .. eHi` (inclusive), `perExp` mantissa samples across the
    16-digit band `[10^15, 10^16)`. Log-scale in value (each exponent = one decade).
    `signed` also emits negative operands (v1=v2 ⇒ same err/env; shows both sides).

    Mantissas are `10^15 + (i·P mod 9·10^15)` with `P` coprime to `9·10^15` — this spreads
    *full-precision* 16-digit mantissas across the band. (A plain arithmetic step from 10^15
    lands on multiples of a power of ten, whose squares have few significant digits and are
    representable exactly, giving a spurious zero rounding error.) -/
def sweepExp (bracket : Nat) (eLo eHi : Int) (perExp : Nat) : IO Unit := do
  let base : Nat := 1000000000000000        -- 10^15
  let span : Nat := 9000000000000000        -- 9·10^15  (band width)
  let p    : Nat := 7477777777777783        -- coprime to 9·10^15 (not div. by 2, 3, 5)
  let mut e : Int := eLo
  while e ≤ eHi do
    for i in [0:perExp] do
      let m : UInt64 := (base + i * p % span).toUInt64
      emit bracket m e
    e := e + 1

def main : IO Unit := do
  -- Bracket 0: two-sided log sweep of |v1| from ~10^-40 (square-underflow floor, e=-56)
  -- up to ~10^-6 (e=-22). Log, not linear: only log spacing can approach 0 to 10^-40.
  sweepExp 0 (-56) (-22) 200
  sweepExp 1 1     3     300      -- exponent_field ∈ [1, 3]
  sweepExp 2 6     10    300      -- exponent_field ∈ [6, 10]
  sweepExp 3 22    32    300      -- exponent_field ∈ [22, 32]
