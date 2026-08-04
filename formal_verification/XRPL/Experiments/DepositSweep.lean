import XRPL.Experiments.DepositPrecision

/-!
# Sweep / fuzz harness

Runs the instrumented deposit under each configuration and reports

* per-site rounding statistics (how often each site loses anything, and how much)
* conservation error: what the books say versus the exact sum of what actually moved
* divergence from a fully exact rational reference run
-/

namespace XRPL.Experiments

open XRPL.Model.Protocol

/-! ## Exact reference vault -/

structure IVault where
  assetsTotal : ℚ
  sharesTotal : ℚ
  deriving Repr

/-- The same algebra with no rounding anywhere. Share truncation is kept (semantic). -/
def idealStep (p : Nat) (v : IVault) (amountReq : ℚ) : IVault × ℚ × ℚ :=
  let u := pow10 (-(p : Int))
  let amt := (amountReq / u).floor * u
  let shares := (v.sharesTotal * amt / v.assetsTotal).floor
  let charged := v.assetsTotal * shares / v.sharesTotal
  ({ assetsTotal := v.assetsTotal + charged
    , sharesTotal := v.sharesTotal + (shares : ℚ) }, charged, (shares : ℚ))

/-! ## Run result -/

structure RunResult where
  cfg : Config
  final : EVault
  trueTotal : ℚ          -- exact Σ of what actually moved on the trust line
  idealTotal : ℚ         -- fully exact independent run
  steps : Nat
  events : Array RoundEvent
  bufMin : ℚ             -- buffer range seen during the run: must stay in [0, ulp)
  bufMax : ℚ
  zeroShares : Nat       -- deposits that minted nothing; if = steps the run is vacuous
  precisionLost : Nat    -- deposits after which assetsTotal no longer held 10^-precision

/-- Books minus what was actually received. Positive = vault overstates its holdings. -/
def RunResult.conservationErr (r : RunResult) : ℚ := r.final.booked - r.trueTotal
/-- Same, ignoring the buffer: what NAV sees when it reads `assetsTotal` alone. -/
def RunResult.primaryErr (r : RunResult) : ℚ := staRat r.final.assetsTotal - r.trueTotal
def RunResult.conservationUlp (r : RunResult) : ℚ := ratAbs r.conservationErr / r.final.ulp
def RunResult.primaryUlp (r : RunResult) : ℚ := ratAbs r.primaryErr / r.final.ulp
/-- Total mispricing charged to depositors: how far each `charged` landed from the exact
    `nav * shares / sharesTotal`. Independent of the conservation question. -/
def RunResult.pricingErr (r : RunResult) : ℚ :=
  (r.events.filter (fun e => e.site == Site.chargeStore)).foldl (fun a e => a + e.err) 0
/-- `true` iff the buffer stayed within `[0, ulp)` for the whole run. -/
def RunResult.bufOk (r : RunResult) : Bool := r.bufMin ≥ 0 && r.bufMax < r.final.ulp

def runSeq (cfg : Config) (v0 : EVault) (i0 : IVault) (amounts : Array STAmount)
    : Except Error RunResult := do
  let mut v := v0
  let mut iv := i0
  let mut trueTotal : ℚ := staRat v0.assetsTotal + numRat v0.buffer
  let mut evs : Array RoundEvent := #[]
  let mut bufMin : ℚ := 0
  let mut bufMax : ℚ := 0
  let mut zeroShares : Nat := 0
  let mut precisionLost : Nat := 0
  for a in amounts do
    let (out, evs') ← depositStep cfg v a evs
    if out.zeroShares then zeroShares := zeroShares + 1
    if out.precisionLost then precisionLost := precisionLost + 1
    v := out.v
    let b := numRat v.buffer
    bufMin := min bufMin b
    bufMax := max bufMax b
    trueTotal := trueTotal + staRat out.charged
    let (iv', _, _) := idealStep v0.precision iv (staRat a)
    iv := iv'
    evs := evs'
  return { cfg, final := v, trueTotal, idealTotal := iv.assetsTotal
         , steps := amounts.size, events := evs, bufMin, bufMax, zeroShares, precisionLost }

/-! ## Aggregation -/

structure SiteStat where
  site : Site
  n : Nat
  nRounded : Nat
  total : ℚ
  worst : ℚ
  deriving Inhabited

def aggregate (evs : Array RoundEvent) : List SiteStat :=
  allSites.filterMap fun s =>
    let es := evs.filter (fun e => e.site == s)
    if es.size == 0 then none
    else some
      { site := s
      , n := es.size
      , nRounded := (es.filter (fun e => e.rounded)).size
      , total := es.foldl (fun a e => a + e.err) 0
      , worst := es.foldl (fun a e => max a e.err) 0 }

def fmtSiteStat (s : SiteStat) : String :=
  padRight (s.site.name ++ (if s.site.intentional then "*" else "")) 18
    ++ padRight (toString s.nRounded ++ "/" ++ toString s.n) 12
    ++ padRight (ratToSci s.worst) 14
    ++ ratToSci s.total

def fmtRun (r : RunResult) : String :=
  padRight r.cfg.name 20
    ++ padRight (ratToSci (ratAbs r.conservationErr)) 13
    ++ padRight (ratToDec r.conservationUlp 3) 11
    ++ padRight (ratToSci (ratAbs r.primaryErr)) 13
    ++ padRight (ratToDec r.primaryUlp 3) 9
    ++ padRight (ratToSci r.pricingErr) 13
    ++ (if r.precisionLost > 0 then s!"OVER CAPACITY({r.precisionLost}/{r.steps}) " else "")
    ++ (if r.zeroShares == r.steps && r.steps > 0 then "VACUOUS(0 shares) "
        else if r.zeroShares > 0 then s!"{r.zeroShares}/{r.steps} zero-share "
        else "")
    ++ (if r.bufOk then "ok" else s!"OUT [{ratToSci r.bufMin},{ratToSci r.bufMax}] ulp={ratToSci r.final.ulp}")

def runHeader : String :=
  padRight "config" 20 ++ padRight "|books-true|" 13 ++ padRight "ulps" 11
    ++ padRight "|prim-true|" 13 ++ padRight "ulps" 9
    ++ padRight "pricingErr" 13 ++ "buffer"

def siteHeader : String :=
  padRight "site" 18 ++ padRight "rounded/n" 12 ++ padRight "worst" 14 ++ "sum|err|"

/-! ## Value generators -/

def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudorandom IOU amounts with `digits` significant digits near `10^expo`. -/
def fuzzAmounts (seed : UInt64) (n : Nat) (digits : Nat) (expo : Int) : Array STAmount :=
  let span : UInt64 := (10 ^ digits : Nat).toUInt64
  let lo : UInt64 := span / 10
  Id.run do
    let mut s := seed
    let mut out : Array STAmount := #[]
    for _ in [0:n] do
      s := lcgNext s
      let m := lo + (s % (span - lo))
      match iou m.toNat expo with
      | .ok a => out := out.push a
      | .error _ => pure ()
    return out

/-- Amounts alternating between two magnitudes.

The buffer's lowest significant digit is inherited from `charged`'s lowest digit. With a
single magnitude the span `top(charged) .. bottom(buffer)` is ~16 digits and always fits
the 19-digit `Number`, so `kahanY` never rounds. Mixing magnitudes lets the buffer keep
fine digits from a small deposit while a large one raises the top, widening the span past
19 — at which point the Kahan recovery is no longer exact. -/
def mixedAmounts (seed : UInt64) (n : Nat) (expoA expoB : Int) : Array STAmount :=
  Id.run do
    let mut sd := seed
    let mut out : Array STAmount := #[]
    for i in [0:n] do
      sd := lcgNext sd
      let m : UInt64 := 1000000000000000 + (sd % 9000000000000000)
      match iou m.toNat (if i % 2 == 0 then expoA else expoB) with
      | .ok a => out := out.push a
      | .error _ => pure ()
    return out

/-- The same amount repeated: the shape that accumulates drift fastest. -/
def constAmounts (n : Nat) (mantissa : Nat) (expo : Int) : Array STAmount :=
  match iou mantissa expo with
  | .ok a => Array.replicate n a
  | .error _ => #[]

/-! ## Reporting entry points -/

/-- Per-site breakdown for one configuration. -/
def siteReport (v0 : EVault) (i0 : IVault) (cfg : Config) (amounts : Array STAmount)
    : Except Error (List String) := do
  let r ← runSeq cfg v0 i0 amounts
  return [cfg.name ++ "  (" ++ toString r.steps ++ " deposits)", siteHeader]
         ++ (aggregate r.events).map fmtSiteStat
         ++ ["", runHeader, fmtRun r]

/-- Each amount run as its own fresh single deposit, then merged. Isolates per-site
    behaviour with no accumulation, so "site X never rounds" can be tested. -/
def fuzzSites (v0 : EVault) (i0 : IVault) (cfg : Config) (amounts : Array STAmount)
    : Except Error (List String) := do
  let mut evs : Array RoundEvent := #[]
  for a in amounts do
    let r ← runSeq cfg v0 i0 #[a]
    evs := evs ++ r.events
  return [siteHeader] ++ (aggregate evs).map fmtSiteStat

/-- Per-site stats over a single accumulating sequence (buffer carries across steps). -/
def fuzzSitesSeq (v0 : EVault) (i0 : IVault) (cfg : Config) (amounts : Array STAmount)
    : Except Error (List String) := do
  let r ← runSeq cfg v0 i0 amounts
  return [siteHeader] ++ (aggregate r.events).map fmtSiteStat
         ++ ["", runHeader, fmtRun r]

/-- Conservation error for every configuration over the same input. -/
def compareAll (v0 : EVault) (i0 : IVault) (amounts : Array STAmount)
    : Except Error (List String) := do
  let mut out := [runHeader]
  for cfg in configs do
    let r ← runSeq cfg v0 i0 amounts
    out := out ++ [fmtRun r]
  return out

/-- A seed with an arbitrary 16-digit `assetsTotal` and integer `sharesTotal`, so that
neither division reduces to a power of ten. `seedVault` below accidentally makes
`sharesDiv` exact, because its `assetsTotal` is exactly `10^k`. -/
def seedVaultAt (p : Nat) (aMant : Nat) (shares : Nat) : Except Error (EVault × IVault) := do
  let aT ← iou aMant (-(p : Int))
  let sT ← ratToNumber (shares : ℚ)
  return ({ precision := p, assetsTotal := aT, buffer := Number.zero, sharesTotal := sT }
         , { assetsTotal := staRat aT, sharesTotal := (shares : ℚ) })

/-- Seed a vault whose NAV is the non-terminating fraction 2/3.

`spare = 0` puts `assetsTotal` exactly at the 16-digit limit for the given precision:
`10^(15-p)` has `16-p` integer digits, which with `p` decimals uses all 16. Raising
`spare` gives the mantissa that many digits of headroom. -/
def seedVault (p : Nat) (spare : Nat := 0) : Except Error (EVault × IVault) := do
  let aT ← iou (10 ^ 15) (-(p : Int) - (spare : Int))
  let sT ← ratToNumber (staRat aT * 3 / 2)
  return ({ precision := p, assetsTotal := aT, buffer := Number.zero, sharesTotal := sT }
         , { assetsTotal := staRat aT, sharesTotal := staRat aT * 3 / 2 })

/-! ## Single-execution deep dive

One fresh deposit per sample, so nothing accumulates: this isolates the error of a
*single* `VaultDeposit`. Errors are reported both in ulps and in absolute asset units,
because a 100B vault forces a small `precision` and then one ulp is real money. -/

structure Scenario where
  label : String
  precision : Nat
  aMant : Nat            -- assetsTotal = aMant * 10^-precision
  shares : Nat           -- sharesTotal (integral)
  amtExpo : Int          -- deposit amounts are 16-digit mantissas at this exponent
  deriving Inhabited

def Scenario.seed (sc : Scenario) : Except Error (EVault × IVault) :=
  seedVaultAt sc.precision sc.aMant sc.shares

structure SingleStats where
  cfg : Config
  n : Nat
  nNonzeroCons : Nat
  maxCons : ℚ
  sumCons : ℚ
  maxPrim : ℚ
  sumPrim : ℚ
  maxPrice : ℚ
  sumPrice : ℚ
  nZeroShares : Nat
  nOverCap : Nat
  nBufBad : Nat
  ulp : ℚ
  deriving Inhabited

/-- `n` independent single deposits with 16-significant-digit random amounts. -/
def singleSweep (sc : Scenario) (cfg : Config) (n : Nat) (seed : UInt64)
    : Except Error SingleStats := do
  let (v0, i0) ← sc.seed
  let mut st : SingleStats :=
    { cfg, n, nNonzeroCons := 0, maxCons := 0, sumCons := 0, maxPrim := 0, sumPrim := 0
    , maxPrice := 0, sumPrice := 0, nZeroShares := 0, nOverCap := 0, nBufBad := 0
    , ulp := v0.ulp }
  let mut sd := seed
  for _ in [0:n] do
    sd := lcgNext sd
    let m : UInt64 := 1000000000000000 + (sd % 9000000000000000)
    let a ← iou m.toNat sc.amtExpo
    let r ← runSeq cfg v0 i0 #[a]
    let c := ratAbs r.conservationErr
    let pr := ratAbs r.primaryErr
    let pc := r.pricingErr
    st := { st with
      nNonzeroCons := st.nNonzeroCons + (if c ≠ 0 then 1 else 0)
      maxCons := max st.maxCons c, sumCons := st.sumCons + c
      maxPrim := max st.maxPrim pr, sumPrim := st.sumPrim + pr
      maxPrice := max st.maxPrice pc, sumPrice := st.sumPrice + pc
      nZeroShares := st.nZeroShares + r.zeroShares
      nOverCap := st.nOverCap + r.precisionLost
      nBufBad := st.nBufBad + (if r.bufOk then 0 else 1) }
  return st

def singleHeader : String :=
  padRight "config" 20 ++ padRight "nz/n" 15
    ++ padRight "maxCons" 12 ++ padRight "ulp" 8
    ++ padRight "meanCons" 12
    ++ padRight "maxPrim" 12 ++ padRight "ulp" 8
    ++ padRight "maxPrice" 12 ++ "flags"

def fmtSingle (s : SingleStats) : String :=
  let mean := if s.n == 0 then 0 else s.sumCons / (s.n : ℚ)
  padRight s.cfg.name 20
    ++ padRight (toString s.nNonzeroCons ++ "/" ++ toString s.n) 15
    ++ padRight (ratToSci s.maxCons) 12 ++ padRight (ratToDec (s.maxCons / s.ulp) 3) 8
    ++ padRight (ratToSci mean) 12
    ++ padRight (ratToSci s.maxPrim) 12 ++ padRight (ratToDec (s.maxPrim / s.ulp) 3) 8
    ++ padRight (ratToSci s.maxPrice) 12
    ++ (if s.nZeroShares > 0 then s!"zeroShares={s.nZeroShares} " else "")
    ++ (if s.nOverCap > 0 then s!"OVERCAP={s.nOverCap} " else "")
    ++ (if s.nBufBad > 0 then s!"BUFBAD={s.nBufBad}" else "")

def singleReport (sc : Scenario) (n : Nat) (seed : UInt64) : Except Error (List String) := do
  let (v0, _) ← sc.seed
  let mut out :=
    [ s!"assetsTotal={ratToDec (staRat v0.assetsTotal) (sc.precision)}  precision={sc.precision}"
      ++ s!"  ulp={ratToSci v0.ulp}  sharesTotal={sc.shares}  n={n}"
    , singleHeader ]
  for cfg in configs do
    let st ← singleSweep sc cfg n seed
    out := out ++ [fmtSingle st]
  return out

end XRPL.Experiments
