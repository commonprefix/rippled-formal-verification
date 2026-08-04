import XRPL.Experiments.WithdrawPrecision

/-!
Driver for the deposit precision experiment. Native-compiled because the model's
`BitVec 128` arithmetic is far too slow under the `#eval` interpreter.

    lake exe depositprecision                     -- everything
    lake exe depositprecision sites               -- per-site attribution
    lake exe depositprecision fuzz                -- which sites actually round
    lake exe depositprecision odd                 -- seeds where both divisions repeat
    lake exe depositprecision seq                 -- cumulative drift per config
    lake exe depositprecision headroom            -- effect of mantissa headroom
    lake exe depositprecision single N            -- deposit single-execution error
    lake exe depositprecision wseq wsites wsingle -- withdraw by shares
    lake exe depositprecision waseq wasites wasingle -- withdraw by assets
    lake exe depositprecision span                -- mixed deposit magnitudes vs buffer width
    lake exe depositprecision micro bench         -- timing diagnostics
-/

open XRPL.Experiments
open XRPL.Model.Protocol

def emit (title : String) (r : Except Error (List String)) : IO Unit := do
  IO.println s!"=== {title} ==="
  match r with
  | .error e => IO.println s!"ERROR: {repr e}"
  | .ok ls => for l in ls do IO.println l
  IO.println ""

/-- A deposit amount that is exact at the vault's precision. -/
def amtExact : Except Error STAmount := iou 5000000000000000 (-15)          -- 5
/-- A deposit amount with digits below any precision <= 8, forcing `inputRound`. -/
def amtLongTail : Except Error STAmount := iou 1234567890123456 (-15)       -- 1.234567890123456

def partSites : IO Unit := do
  for p in [0, 2, 4, 6, 8] do
    for (label, mk) in [("exact amount 5", amtExact), ("long tail 1.234567890123456", amtLongTail)] do
      emit s!"sites: precision={p}, {label}" do
        let (v0, i0) ← seedVault p 0
        let a ← mk
        siteReport v0 i0 configs[0]! #[a]

def partFuzz : IO Unit := do
  -- 16-significant-digit random amounts: the hardest case for every site
  for p in [2, 8] do
    emit s!"fuzz 200 random 16-digit amounts, precision={p}, baseline" do
      let (v0, i0) ← seedVault p 0
      fuzzSites v0 i0 configs[0]! (fuzzAmounts 12345 200 16 (-15))
    emit s!"fuzz 200 random 16-digit amounts, precision={p}, all compensation on" do
      let (v0, i0) ← seedVault p 0
      fuzzSites v0 i0 configs[4]! (fuzzAmounts 12345 200 16 (-15))

def partSeq : IO Unit := do
  for n in [10, 100, 1000] do
    emit s!"drift: {n} x deposit 5, precision=8, assetsTotal at 16-digit limit" do
      let (v0, i0) ← seedVault 8 0
      compareAll v0 i0 (constAmounts n 5000000000000000 (-15))
  for n in [10, 100, 1000] do
    emit s!"drift: {n} x random 16-digit amount, precision=8" do
      let (v0, i0) ← seedVault 8 0
      compareAll v0 i0 (fuzzAmounts 999 n 16 (-15))

def partHeadroom : IO Unit := do
  for spare in [0, 1, 2, 3, 4] do
    emit s!"headroom: 100 deposits, precision=8, mantissa spare digits={spare}" do
      let (v0, i0) ← seedVault 8 spare
      compareAll v0 i0 (constAmounts 100 5000000000000000 (-15))

/-- Seeds where BOTH divisions have non-terminating quotients. -/
def partOdd : IO Unit := do
  for (aMant, shares, tag) in
      [ (1234567890123456, 18518518,  "assetsTotal=12345678.90123456 shares=18518518")
      , (9999999999999999, 149999993, "assetsTotal=99999999.99999999 shares=149999993")
      , (3333333333333333, 49999991,  "assetsTotal=33333333.33333333 shares=49999991")
      , (1000000000000007, 15000000,  "assetsTotal=10000000.00000007 shares=15000000") ] do
    emit s!"odd seed, 200 random amounts, p=8: {tag}" do
      let (v0, i0) ← seedVaultAt 8 aMant shares
      compareAll v0 i0 (fuzzAmounts 777 200 16 (-15))
    emit s!"odd seed sites (baseline): {tag}" do
      let (v0, i0) ← seedVaultAt 8 aMant shares
      fuzzSites v0 i0 configs[0]! (fuzzAmounts 777 200 16 (-15))
    emit s!"odd seed sites (all compensation): {tag}" do
      let (v0, i0) ← seedVaultAt 8 aMant shares
      fuzzSites v0 i0 configs[4]! (fuzzAmounts 777 200 16 (-15))

/-- Scenarios spanning the magnitudes that matter. A 100B vault has 12 integer digits,
so with a 16-digit mantissa `precision` can be at most 4 — and at `precision = 0` one
ulp is a whole unit of the asset. -/
def scenarios : List Scenario :=
  [ { label := "100B  p=0  (ulp = 1)",        precision := 0, aMant := 100000000000,
      shares := 150000000000, amtExpo := -10 }
  , { label := "100B  p=2  (ulp = 0.01)",     precision := 2, aMant := 10000000000000,
      shares := 150000000000, amtExpo := -10 }
  , { label := "100B  p=4  (ulp = 0.0001, at digit limit)", precision := 4,
      aMant := 1000000000000000, shares := 150000000000, amtExpo := -10 }
  , { label := "123B  p=4  odd shares (at digit limit)", precision := 4,
      aMant := 1234567890123456, shares := 185185183518, amtExpo := -10 }
  , { label := "100B  p=4  tiny deposits (1..10)", precision := 4,
      aMant := 1000000000000000, shares := 150000000000, amtExpo := -15 }
  , { label := "100B  p=4  huge deposits (1e7..1e8)", precision := 4,
      aMant := 1000000000000000, shares := 150000000000, amtExpo := -8 }
  , { label := "10M   p=8  (at digit limit)",  precision := 8, aMant := 1000000000000000,
      shares := 15000000, amtExpo := -15 }
  , { label := "12M   p=8  odd (at digit limit)", precision := 8, aMant := 1234567890123456,
      shares := 18518518, amtExpo := -15 }
    -- NAV probes: if the by-assets over-payout is 1/2 * NAV, these should show
    -- maxOverpay ~= 5 and ~= 0.05 respectively, independent of precision.
  , { label := "100B  p=4  NAV=10  (few valuable shares)", precision := 4,
      aMant := 1000000000000000, shares := 10000000000, amtExpo := -10 }
  , { label := "100B  p=4  NAV=0.1 (many cheap shares)", precision := 4,
      aMant := 1000000000000000, shares := 1000000000000, amtExpo := -10 } ]

def partSingle (n : Nat) : IO Unit := do
  for sc in scenarios do
    emit s!"SINGLE deposit: {sc.label}" (singleReport sc n 20250730)

/-! withdraw -/

def partWSeq : IO Unit := do
  for sc in [scenarios[2]!, scenarios[3]!, scenarios[6]!] do
    for n in [10, 100, 1000] do
      emit s!"WITHDRAW drift: {n} x burn, {sc.label}" do
        let (v0, _) ← sc.seed
        wCompareAll v0 (← constShares n (sc.shares / 100000))
    emit s!"WITHDRAW drift: 1000 x random burn, {sc.label}" do
      let (v0, _) ← sc.seed
      wCompareAll v0 (← fuzzShares 31337 1000 (sc.shares / 100000))

def partWSites : IO Unit := do
  for sc in [scenarios[2]!, scenarios[3]!, scenarios[6]!] do
    for cfg in [configs[0]!, configs[4]!] do
      emit s!"WITHDRAW sites [{cfg.name}]: {sc.label}" do
        let (v0, _) ← sc.seed
        wSiteReport v0 cfg (← fuzzShares 777 200 (sc.shares / 100000))

def partWSingle (n : Nat) : IO Unit := do
  for sc in scenarios do
    emit s!"SINGLE withdraw: {sc.label}" (wSingleReport sc n 20250730)

/-! withdraw by assets (`computeWithdrawByAssets`) -/

def partWaSeq : IO Unit := do
  for sc in [scenarios[2]!, scenarios[3]!, scenarios[6]!] do
    for n in [10, 100, 1000] do
      emit s!"WITHDRAW-BY-ASSETS drift: {n} requests, {sc.label}" do
        let (v0, _) ← sc.seed
        waCompareAll v0 (fuzzAmounts 4242 n 16 sc.amtExpo)

def partWaSites : IO Unit := do
  for sc in [scenarios[2]!, scenarios[3]!, scenarios[6]!] do
    for cfg in [configs[0]!, configs[4]!] do
      emit s!"WITHDRAW-BY-ASSETS sites [{cfg.name}]: {sc.label}" do
        let (v0, _) ← sc.seed
        waSiteReport v0 cfg (fuzzAmounts 777 200 16 sc.amtExpo)

def partWaSingle (n : Nat) : IO Unit := do
  for sc in scenarios do
    emit s!"SINGLE withdraw-by-assets: {sc.label}" (waSingleReport sc n 20250730)

/-- Does the buffer lose digits past its own precision? Mixed deposit magnitudes widen
the span the Kahan recovery must represent. -/
def partSpan : IO Unit := do
  for (p, aM, sh) in [(0, 100000000000, 150000000000), (4, 1000000000000000, 150000000000)] do
    for (ea, eb, tag) in
        [ (-10, -10, "single magnitude (control)")
        , (-8,  -15, "1e7..1e8  mixed with 1..10")
        , (-5,  -15, "1e10..1e11 mixed with 1..10")
        , (-5,  -20, "1e10..1e11 mixed with 1e-5..1e-4") ] do
      emit s!"SPAN p={p}: {tag}" do
        let (v0, i0) ← seedVaultAt p aM sh
        compareAll v0 i0 (mixedAmounts 5150 400 ea eb)
      emit s!"SPAN p={p} sites [kahan add]: {tag}" do
        let (v0, i0) ← seedVaultAt p aM sh
        fuzzSitesSeq v0 i0 configs[1]! (mixedAmounts 5150 400 ea eb)

/-- Directed worst-case search. The single-op conservation error is bounded by 1 ulp, but
the achievable maximum depends on NAV: `charged = nav * shares / sharesTotal` with integral
`shares`, so the sub-ulp residue is quantised by `sharesTotal`'s factorisation. A NAV with a
small denominator (2/3) caps the residue at 2/3 ulp; a large prime denominator should let it
approach 1 ulp. -/
def partWorst (n : Nat) : IO Unit := do
  -- assetsTotal = 1e11 at the p=4 digit limit; IOU worth $1 so 1 ulp = $0.0001
  for (sh, tag) in
      [ (150000000000, "1.5e11 = 2^11*3*5^11 (NAV = 2/3)")
      , (150000000001, "1.5e11 + 1")
      , (149999999989, "149999999989 (prime)")
      , (100000000003, "100000000003 (prime, NAV ~ 1)")
      , (99999999977,  "99999999977 (prime, NAV ~ 1)")
      , (140000000041, "140000000041 (prime)") ] do
    emit s!"WORST p=4, assetsTotal=1e11 (AT digit limit), sharesTotal={tag}" do
      singleReport { label := tag, precision := 4, aMant := 1000000000000000
                   , shares := sh, amtExpo := -10 } n 20250730
  -- same but with spare mantissa digits, so the explicit grid-down step is live
  for (aM, sh, tag) in
      [ (10000000000,  1499999, "assetsTotal=1e6, 5 spare digits, shares=1499999")
      , (100000000000, 14999999, "assetsTotal=1e7, 4 spare digits, shares=14999999")
      , (10000000000,  1000003, "assetsTotal=1e6, 5 spare, shares=1000003 (prime)") ] do
    emit s!"WORST p=4, BELOW digit limit: {tag}" do
      singleReport { label := tag, precision := 4, aMant := aM
                   , shares := sh, amtExpo := -15 } n 20250730

def timeIt (label : String) (n : Nat) (f : Nat → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut acc := true
  for i in [0:n] do
    acc := acc && f i
  let t1 ← IO.monoMsNow
  IO.println s!"{padRight label 26} {n} iters  {t1 - t0} ms   (acc={acc})"

def orElseN (d : Number) : Except Error Number → Number
  | .ok a => a | .error _ => d
def orElseS (d : STAmount) : Except Error STAmount → STAmount
  | .ok a => a | .error _ => d

instance : Inhabited Number := ⟨Number.zero⟩
instance : Inhabited STAmount := ⟨STAmount.zero .fractional⟩

/-- Every closure below must depend on `i`, or the compiler hoists the work out of the
    loop and the timing is meaningless. -/
def partMicro : IO Unit := do
  let N := 2000
  let ns : Array Number := (Array.range N).map fun (i : Nat) =>
    orElseN Number.zero (ratToNumber (((i : ℚ) + 1) * 14 / 3))
  let ss : Array STAmount := (Array.range N).map fun (i : Nat) =>
    orElseS (STAmount.zero .fractional) (ratToSTAmount (((i : ℚ) + 1) * 14 / 3))
  let qs : Array ℚ := (Array.range N).map fun (i : Nat) =>
    ((i : ℚ) + 1) * 14 / 3 / 10 ^ 18
  timeIt "Rat mul" N (fun i => qs[i]! * qs[(i + 1) % N]! ≠ 0)
  timeIt "Rat div" N (fun i => qs[i]! / qs[(i + 1) % N]! ≠ 0)
  timeIt "ratToNumber" N (fun i => (ratToNumber qs[i]!).isOk)
  timeIt "Number.toRat" N (fun i => ns[i]!.toRat ≠ 0)
  timeIt "Number.operator_mul" N (fun i => (ns[i]!.operator_mul ns[(i+1)%N]! .to_nearest).isOk)
  timeIt "Number.operator_div" N (fun i => (ns[i]!.operator_div ns[(i+1)%N]! .to_nearest).isOk)
  timeIt "Number.operator_add" N (fun i => (ns[i]!.operator_add ns[(i+1)%N]! .to_nearest).isOk)
  timeIt "STAmount.roundToExponent" N (fun i => (STAmount.roundToExponent ss[i]! (-8) .downward).isOk)
  timeIt "STAmount.ofNumber" N (fun i => (STAmount.ofNumber .fractional ns[i]! .to_nearest).isOk)
  timeIt "STAmount.toNumber" N (fun i => (ss[i]!.toNumber .to_nearest).isOk)
  timeIt "pow10" N (fun i => pow10 (-((i % 9 : Nat) : Int)) ≠ 0)
  timeIt "ratToSci" N (fun i => (ratToSci qs[i]!).length > 0)
  -- suspects: well-founded recursion
  let shareLike : Array Number := (Array.range N).map fun (i : Nat) =>
    orElseN Number.zero (ratToNumber (((i : ℚ) + 1) * 15 / 2))
  timeIt "Number.truncate" 200 (fun i => (shareLike[i]!.truncate).isOk)
  let trunc : Array Number := (Array.range 200).map fun (i : Nat) =>
    orElseN Number.zero (shareLike[i]!.truncate)
  timeIt "ofNumber int64 (to_rep)" 200 (fun i => (STAmount.ofNumber .int64 trunc[i]! .to_nearest).isOk)
  timeIt "roundToVaultPrecision" N (fun i => (roundToVaultPrecision 8 ss[i]!).isOk)
  -- the real thing: one deposit each, distinct amounts
  match seedVault 8 0 with
  | .error _ => IO.println "seed failed"
  | .ok (v0, i0) =>
    let amts := fuzzAmounts 4242 200 16 (-15)
    timeIt "depositStep (1 deposit)" 200 (fun i => (runSeq configs[0]! v0 i0 #[amts[i]!]).isOk)

def partBench : IO Unit := do
  for n in [1, 5, 25] do
    let t0 ← IO.monoMsNow
    let r := do
      let (v0, i0) ← seedVault 8 0
      compareAll v0 i0 (constAmounts n 5000000000000000 (-15))
    let ok := match r with | .ok _ => "ok" | .error _ => "err"
    let t1 ← IO.monoMsNow
    IO.println s!"bench: {n} deposits x {configs.length} configs = {t1 - t0} ms ({ok})"

def main (args : List String) : IO Unit := do
  let want (s : String) : Bool := args.isEmpty || args.contains s
  let n : Nat := (args.filterMap (fun a => a.toNat?)).head?.getD 2000
  if want "worst" then partWorst n
  if want "span" then partSpan
  if want "single" then partSingle n
  if want "wseq" then partWSeq
  if want "wsites" then partWSites
  if want "wsingle" then partWSingle n
  if want "waseq" then partWaSeq
  if want "wasites" then partWaSites
  if want "wasingle" then partWaSingle n
  if want "odd" then partOdd
  if want "micro" then partMicro
  if want "bench" then partBench
  if want "sites" then partSites
  if want "fuzz" then partFuzz
  if want "seq" then partSeq
  if want "headroom" then partHeadroom
