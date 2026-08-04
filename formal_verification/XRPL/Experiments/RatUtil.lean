import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount

/-!
Exact-rational helpers for the deposit precision experiment: rendering, and
conversion from `ℚ` into the model's `Number` / `STAmount` representations.
-/

namespace XRPL.Experiments

open XRPL.Model.Protocol

def ratAbs (q : ℚ) : ℚ := if q < 0 then -q else q

/-- Safe `Number.toRat`.

`Number.toRat` builds `10 ^ (-exponent)` when the exponent is negative, and
`Number.zero` carries `exponent_ = -2147483648`. The unguarded version therefore tries
to construct a power of ten with about 2.1 billion digits, which never finishes. Always
convert `Number`s through this. -/
def numRat (n : Number) : ℚ := if n.mantissa_ = 0 then 0 else n.toRat

/-- Same guard for `STAmount`, whose zero also carries a non-zero offset. -/
def staRat (s : STAmount) : ℚ := if s.mValue = 0 then 0 else s.toRat

def padLeft (s : String) (n : Nat) (c : Char := '0') : String :=
  if s.length ≥ n then s else String.ofList (List.replicate (n - s.length) c) ++ s

def padRight (s : String) (n : Nat) (c : Char := ' ') : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) c)

/-- Fixed-point decimal rendering with `d` fractional digits (truncated). -/
def ratToDec (q : ℚ) (d : Nat := 12) : String :=
  let neg := q < 0
  let a := if neg then -q else q
  let scaled : Nat := (a * (10 : ℚ) ^ d).floor.toNat
  let p : Nat := 10 ^ d
  (if neg then "-" else "") ++ toString (scaled / p) ++ "." ++ padLeft (toString (scaled % p)) d

private partial def sciNorm (q : ℚ) (k : Int) : ℚ × Int :=
  if q < 1 then sciNorm (q * 10) (k - 1)
  else if q ≥ 10 then sciNorm (q / 10) (k + 1)
  else (q, k)

/-- Scientific rendering, e.g. `1.2345e-17`. Readable for tiny error magnitudes. -/
def ratToSci (q : ℚ) (digits : Nat := 4) : String :=
  if q = 0 then "0"
  else
    let neg := q < 0
    let a := if neg then -q else q
    let (m, e) := sciNorm a 0
    (if neg then "-" else "") ++ ratToDec m digits ++ "e" ++ toString e

/-- `10 ^ e` as a rational, for signed `e`. -/
def pow10 (e : Int) : ℚ :=
  if e ≥ 0 then (10 : ℚ) ^ e.toNat else 1 / (10 : ℚ) ^ (-e).toNat

/-- Nearest `Number` (19-digit mantissa) to an exact rational.

The target exponent comes from decimal digit counts rather than a scaling loop: a loop
that repeatedly multiplies a rational by 10 renormalizes (gcd) on every step, which
dominates the whole experiment's runtime. -/
def ratToNumber (q : ℚ) : Except Error Number :=
  if q = 0 then .ok Number.zero
  else
    let neg := q < 0
    let n : Nat := q.num.natAbs
    let d : Nat := q.den
    -- floor(log10 |q|) - 18, accurate to +/-1
    let e0 : Int := (Nat.log 10 n : Int) - (Nat.log 10 d : Int) - 18
    let (num, den) :=
      if e0 ≥ 0 then (n, d * 10 ^ e0.toNat)
      else (n * 10 ^ (-e0).toNat, d)
    let m0 : Nat := (2 * num + den) / (2 * den)          -- round half up
    let (m, e) :=
      if m0 ≥ 10 ^ 19 then (m0 / 10, e0 + 1)
      else if m0 < 10 ^ 18 then (m0 * 10, e0 - 1)
      else (m0, e0)
    Number.normalized neg m.toUInt64 e largeRange.min largeRange.max .to_nearest

/-- Nearest IOU `STAmount` (16-digit mantissa) to an exact rational. -/
def ratToSTAmount (q : ℚ) : Except Error STAmount := do
  let n ← ratToNumber q
  STAmount.ofNumber .fractional n .to_nearest

/-- An IOU `STAmount` built directly from mantissa/exponent, no rounding intended. -/
def iou (mantissa : Nat) (exponent : Int) : Except Error STAmount :=
  STAmount.checked .fractional mantissa.toUInt64 exponent false .to_nearest

end XRPL.Experiments
