import XRPL.Experiments.DepositSweep

/-!
# Withdraw precision experiment

Instrumented duplicate of `Vault.withdraw` on the by-shares path (IOU only), sharing the
`Site` / `RoundEvent` / `Config` machinery with the deposit experiment.

Faithful to the model: the payout rounds `.downward`, and a payout too small to move the
stored `assetsTotal` is rejected with `tecPRECISION_LOSS`. `assetsAvailable` is taken to
equal `assetsTotal` (fully liquid vault), and `lossUnrealized` is zero.
-/

namespace XRPL.Experiments

open XRPL.Model.Protocol

structure WStepOut where
  v : EVault
  payout : STAmount           -- what actually moved on the trust line
  rejected : Bool             -- tecPRECISION_LOSS: payout could not move assetsTotal
  finalWithdrawal : Bool      -- burned every share; the clamp path
  precisionLost : Bool
  deriving Repr

/-- `nav` as the withdraw path sees it: `assetsTotal - lossUnrealized` (zero here),
optionally compensated with the buffer. -/
def withdrawNav (cfg : Config) (v : EVault) : M (Number × Number) := do
  let totalN ← liftE (v.assetsTotal.toNumber .to_nearest)
  let nav ←
    if cfg.navWithBuffer then
      obs .wNavSub (numRat totalN + numRat v.buffer) (totalN.operator_add v.buffer .to_nearest)
    else
      pure totalN
  return (totalN, nav)

/-- One withdraw of `shares` shares (`computeWithdrawByShares`). `lossUnrealized = 0`. -/
def withdrawStep (cfg : Config) (v : EVault) (shares : Number) : M WStepOut := do
  let (totalN, nav) ← withdrawNav cfg v

  -- payout = roundDown(nav * shares / sharesTotal)
  let p1 ← cmul cfg.kahanMulDiv .wMul .wCorr (CVal.of nav) shares
  let p2 ← cdiv cfg.kahanMulDiv .wDiv .wCorr p1 v.sharesTotal
  let payout ← obsS .wStore p2.toRat
    (do let n ← ratToNumber p2.toRat; STAmount.ofNumber .fractional n .downward)
  let payoutN ← liftE (payout.toNumber .to_nearest)

  let isFinal := v.sharesTotal.operator_eq shares
  if isFinal then
    -- the clamp: pay out everything, zero the vault. The buffer is forfeited.
    return { v := { v with assetsTotal := STAmount.zero .fractional
                         , buffer := Number.zero, sharesTotal := Number.zero }
           , payout := v.assetsTotal, rejected := false, finalWithdrawal := true
           , precisionLost := false }

  -- debit assetsTotal
  let (total', buffer') ←
    if !cfg.kahanAdd then
      let diff ← obs .wTotalSub (numRat totalN - numRat payoutN)
        (totalN.operator_add payoutN.operator_neg .to_nearest)
      let st ← obsS .wTotalStore (numRat diff)
        (do let a ← STAmount.ofNumber .fractional diff .to_nearest
            roundToVaultPrecision v.precision a)
      pure (st, Number.zero)
    else
      -- y = payout - buffer ; t = grid(assetsTotal - y) ; buffer' = (assetsTotal - t) - y
      let y ← obs .wKahanY (numRat payoutN - numRat v.buffer)
        (payoutN.operator_add v.buffer.operator_neg .to_nearest)
      -- must round toward -inf so t <= assetsTotal - y and the buffer stays >= 0
      let diff ← obs .wKahanSub (numRat totalN - numRat y)
        (totalN.operator_add y.operator_neg .downward)
      let t ← obsS .wKahanGrid (numRat diff)
        (do let a ← STAmount.ofNumber .fractional diff .downward
            roundToVaultPrecision v.precision a)
      let tN ← liftE (t.toNumber .to_nearest)
      let back ← obs .wKahanBack (numRat totalN - numRat tN)
        (totalN.operator_add tN.operator_neg .to_nearest)
      let buf ← obs .wKahanBuffer (numRat back - numRat y)
        (back.operator_add y.operator_neg .to_nearest)
      pure (t, buf)

  -- model's guard: reject a payout too small to reduce the stored assetsTotal
  let movedNothing := !payoutN.operator_eq Number.zero && total'.operator_eq v.assetsTotal
  if movedNothing then
    return { v := v, payout := STAmount.zero .fractional, rejected := true
           , finalWithdrawal := false, precisionLost := false }

  let sharesTotal' ← obs .wSharesSub (numRat v.sharesTotal - numRat shares)
    (v.sharesTotal.operator_add shares.operator_neg .to_nearest)

  return { v := { v with assetsTotal := total', buffer := buffer', sharesTotal := sharesTotal' }
         , payout := payout, rejected := false, finalWithdrawal := false
         , precisionLost := total'.exponent > -(v.precision : Int) && total'.mantissa != 0 }

/-! ## By-assets entry point (`computeWithdrawByAssets`)

The caller names an amount of assets. Shares are derived and stored with `.to_nearest`
into an integer — **not** truncated (`truncateShares = false` in the model). Unlike
`computeDeposit`, which rejects with `tecINTERNAL` when the recomputed amount exceeds what
was offered, there is no `assetsOut <= assets` guard here in either the Lean model or the
C++. So the payout can exceed the request. -/

structure WAStepOut where
  step : WStepOut
  requested : ℚ
  shares : ℚ                  -- share count actually burned
  zeroShares : Bool           -- tecPRECISION_LOSS: request too small to buy a share
  deriving Repr

def withdrawByAssetsStep (cfg : Config) (v : EVault) (assetsReq : STAmount) : M WAStepOut := do
  let (_, nav) ← withdrawNav cfg v
  let reqN ← liftE (assetsReq.toNumber .to_nearest)

  -- shares = ofNumber int64 (sharesTotal * assetsReq / nav) to_nearest   [no truncate]
  let a1 ← cmul cfg.kahanMulDiv .waMul .waCorr (CVal.of v.sharesTotal) reqN
  let a2 ← cdiv cfg.kahanMulDiv .waDiv .waCorr a1 nav
  let shN ← liftE (ratToNumber a2.toRat)
  let shA ← obsS .waSharesStore a2.toRat (STAmount.ofNumber .int64 shN .to_nearest)
  let shares ← liftE (shA.toNumber .to_nearest)

  if shares.mantissa_ == 0 then
    return { step := { v := v, payout := STAmount.zero .fractional, rejected := true
                     , finalWithdrawal := false, precisionLost := false }
           , requested := staRat assetsReq, shares := 0, zeroShares := true }

  let st ← withdrawStep cfg v shares
  return { step := st, requested := staRat assetsReq, shares := numRat shares
         , zeroShares := false }

/-! ## Runs -/

structure WRunResult where
  cfg : Config
  final : EVault
  trueTotal : ℚ          -- initial minus the exact sum of what actually moved out
  steps : Nat
  events : Array RoundEvent
  bufMin : ℚ
  bufMax : ℚ
  nRejected : Nat
  nFinal : Nat
  nOverCap : Nat

def WRunResult.conservationErr (r : WRunResult) : ℚ := r.final.booked - r.trueTotal
def WRunResult.primaryErr (r : WRunResult) : ℚ := staRat r.final.assetsTotal - r.trueTotal
def WRunResult.payoutErr (r : WRunResult) : ℚ :=
  (r.events.filter (fun e => e.site == Site.wStore)).foldl (fun a e => a + e.err) 0
def WRunResult.bufOk (r : WRunResult) : Bool := r.bufMin ≥ 0 && r.bufMax < r.final.ulp

def wRunSeq (cfg : Config) (v0 : EVault) (shareSeq : Array Number)
    : Except Error WRunResult := do
  let mut v := v0
  let mut trueTotal : ℚ := staRat v0.assetsTotal + numRat v0.buffer
  let mut evs : Array RoundEvent := #[]
  let mut bufMin : ℚ := 0
  let mut bufMax : ℚ := 0
  let mut nRejected := 0
  let mut nFinal := 0
  let mut nOverCap := 0
  for sh in shareSeq do
    let (out, evs') ← withdrawStep cfg v sh evs
    v := out.v
    if out.rejected then nRejected := nRejected + 1
    if out.finalWithdrawal then nFinal := nFinal + 1
    if out.precisionLost then nOverCap := nOverCap + 1
    let b := numRat v.buffer
    bufMin := min bufMin b
    bufMax := max bufMax b
    trueTotal := trueTotal - staRat out.payout
    evs := evs'
  return { cfg, final := v, trueTotal, steps := shareSeq.size, events := evs
         , bufMin, bufMax, nRejected, nFinal, nOverCap }

def wFmtRun (r : WRunResult) : String :=
  padRight r.cfg.name 20
    ++ padRight (ratToSci (ratAbs r.conservationErr)) 13
    ++ padRight (ratToDec (ratAbs r.conservationErr / r.final.ulp) 3) 11
    ++ padRight (ratToSci (ratAbs r.primaryErr)) 13
    ++ padRight (ratToDec (ratAbs r.primaryErr / r.final.ulp) 3) 9
    ++ padRight (ratToSci r.payoutErr) 13
    ++ (if r.nRejected > 0 then s!"rej={r.nRejected} " else "")
    ++ (if r.nFinal > 0 then s!"final={r.nFinal} " else "")
    ++ (if r.nOverCap > 0 then s!"OVERCAP={r.nOverCap} " else "")
    ++ (if r.bufOk then "ok" else s!"BUF OUT [{ratToSci r.bufMin},{ratToSci r.bufMax}]")

def wRunHeader : String :=
  padRight "config" 20 ++ padRight "|books-true|" 13 ++ padRight "ulps" 11
    ++ padRight "|prim-true|" 13 ++ padRight "ulps" 9
    ++ padRight "payoutErr" 13 ++ "flags"

def wCompareAll (v0 : EVault) (shareSeq : Array Number) : Except Error (List String) := do
  let mut out := [wRunHeader]
  for cfg in configs do
    let r ← wRunSeq cfg v0 shareSeq
    out := out ++ [wFmtRun r]
  return out

def wSiteReport (v0 : EVault) (cfg : Config) (shareSeq : Array Number)
    : Except Error (List String) := do
  let r ← wRunSeq cfg v0 shareSeq
  return [cfg.name ++ "  (" ++ toString r.steps ++ " withdraws)", siteHeader]
         ++ (aggregate r.events).map fmtSiteStat
         ++ ["", wRunHeader, wFmtRun r]

/-! ## Single-execution deep dive -/

structure WSingleStats where
  cfg : Config
  n : Nat
  nNonzeroCons : Nat
  maxCons : ℚ
  sumCons : ℚ
  maxPrim : ℚ
  maxPayout : ℚ
  sumPayout : ℚ
  nRejected : Nat
  nOverCap : Nat
  nBufBad : Nat
  ulp : ℚ
  deriving Inhabited

/-- `n` independent single withdraws, random share counts in `[1, sharesTotal/2]`. -/
def wSingleSweep (sc : Scenario) (cfg : Config) (n : Nat) (seed : UInt64)
    : Except Error WSingleStats := do
  let (v0, _) ← sc.seed
  let cap : UInt64 := (sc.shares / 2).toUInt64
  let mut st : WSingleStats :=
    { cfg, n, nNonzeroCons := 0, maxCons := 0, sumCons := 0, maxPrim := 0
    , maxPayout := 0, sumPayout := 0, nRejected := 0, nOverCap := 0, nBufBad := 0
    , ulp := v0.ulp }
  let mut sd := seed
  for _ in [0:n] do
    sd := lcgNext sd
    let sh := 1 + (sd % cap)
    let shN ← ratToNumber ((sh.toNat : ℚ))
    let r ← wRunSeq cfg v0 #[shN]
    let c := ratAbs r.conservationErr
    st := { st with
      nNonzeroCons := st.nNonzeroCons + (if c ≠ 0 then 1 else 0)
      maxCons := max st.maxCons c, sumCons := st.sumCons + c
      maxPrim := max st.maxPrim (ratAbs r.primaryErr)
      maxPayout := max st.maxPayout r.payoutErr, sumPayout := st.sumPayout + r.payoutErr
      nRejected := st.nRejected + r.nRejected
      nOverCap := st.nOverCap + r.nOverCap
      nBufBad := st.nBufBad + (if r.bufOk then 0 else 1) }
  return st

def wFmtSingle (s : WSingleStats) : String :=
  let mean := if s.n == 0 then 0 else s.sumCons / (s.n : ℚ)
  padRight s.cfg.name 20
    ++ padRight (toString s.nNonzeroCons ++ "/" ++ toString s.n) 15
    ++ padRight (ratToSci s.maxCons) 12 ++ padRight (ratToDec (s.maxCons / s.ulp) 3) 8
    ++ padRight (ratToSci mean) 12
    ++ padRight (ratToSci s.maxPrim) 12 ++ padRight (ratToDec (s.maxPrim / s.ulp) 3) 8
    ++ padRight (ratToSci s.maxPayout) 12
    ++ (if s.nRejected > 0 then s!"rej={s.nRejected} " else "")
    ++ (if s.nOverCap > 0 then s!"OVERCAP={s.nOverCap} " else "")
    ++ (if s.nBufBad > 0 then s!"BUFBAD={s.nBufBad}" else "")

def wSingleReport (sc : Scenario) (n : Nat) (seed : UInt64) : Except Error (List String) := do
  let (v0, _) ← sc.seed
  let mut out :=
    [ s!"assetsTotal={ratToDec (staRat v0.assetsTotal) sc.precision}  precision={sc.precision}"
      ++ s!"  ulp={ratToSci v0.ulp}  sharesTotal={sc.shares}  n={n}"
    , singleHeader ]
  for cfg in configs do
    let st ← wSingleSweep sc cfg n seed
    out := out ++ [wFmtSingle st]
  return out

/-! ## By-assets runs and reports -/

structure WARunResult where
  cfg : Config
  final : EVault
  trueTotal : ℚ
  steps : Nat
  events : Array RoundEvent
  bufMin : ℚ
  bufMax : ℚ
  nRejected : Nat
  nOverCap : Nat
  nOver : Nat            -- payouts that EXCEEDED the requested amount
  maxOver : ℚ            -- by how much, at worst
  nUnder : Nat
  maxUnder : ℚ

def WARunResult.conservationErr (r : WARunResult) : ℚ := r.final.booked - r.trueTotal
def WARunResult.primaryErr (r : WARunResult) : ℚ := staRat r.final.assetsTotal - r.trueTotal
def WARunResult.bufOk (r : WARunResult) : Bool := r.bufMin ≥ 0 && r.bufMax < r.final.ulp

def waRunSeq (cfg : Config) (v0 : EVault) (reqs : Array STAmount)
    : Except Error WARunResult := do
  let mut v := v0
  let mut trueTotal : ℚ := staRat v0.assetsTotal + numRat v0.buffer
  let mut evs : Array RoundEvent := #[]
  let mut bufMin : ℚ := 0
  let mut bufMax : ℚ := 0
  let mut nRejected := 0
  let mut nOverCap := 0
  let mut nOver := 0
  let mut maxOver : ℚ := 0
  let mut nUnder := 0
  let mut maxUnder : ℚ := 0
  for req in reqs do
    let (out, evs') ← withdrawByAssetsStep cfg v req evs
    v := out.step.v
    if out.step.rejected then nRejected := nRejected + 1
    if out.step.precisionLost then nOverCap := nOverCap + 1
    if !out.step.rejected then
      let gap := staRat out.step.payout - out.requested
      if gap > 0 then
        nOver := nOver + 1; maxOver := max maxOver gap
      else if gap < 0 then
        nUnder := nUnder + 1; maxUnder := max maxUnder (-gap)
    let b := numRat v.buffer
    bufMin := min bufMin b
    bufMax := max bufMax b
    trueTotal := trueTotal - staRat out.step.payout
    evs := evs'
  return { cfg, final := v, trueTotal, steps := reqs.size, events := evs
         , bufMin, bufMax, nRejected, nOverCap, nOver, maxOver, nUnder, maxUnder }

def waFmtRun (r : WARunResult) : String :=
  padRight r.cfg.name 20
    ++ padRight (ratToSci (ratAbs r.conservationErr)) 13
    ++ padRight (ratToDec (ratAbs r.conservationErr / r.final.ulp) 3) 9
    ++ padRight (toString r.nOver ++ "/" ++ toString r.steps) 12
    ++ padRight (ratToSci r.maxOver) 13
    ++ padRight (ratToDec (r.maxOver / r.final.ulp) 3) 9
    ++ padRight (ratToSci r.maxUnder) 13
    ++ (if r.nRejected > 0 then s!"rej={r.nRejected} " else "")
    ++ (if r.nOverCap > 0 then s!"OVERCAP={r.nOverCap} " else "")
    ++ (if r.bufOk then "ok" else "BUF OUT")

def waRunHeader : String :=
  padRight "config" 20 ++ padRight "|books-true|" 13 ++ padRight "ulps" 9
    ++ padRight "overpaid/n" 12 ++ padRight "maxOverpay" 13 ++ padRight "ulps" 9
    ++ padRight "maxUnderpay" 13 ++ "flags"

def waCompareAll (v0 : EVault) (reqs : Array STAmount) : Except Error (List String) := do
  let mut out := [waRunHeader]
  for cfg in configs do
    let r ← waRunSeq cfg v0 reqs
    out := out ++ [waFmtRun r]
  return out

def waSiteReport (v0 : EVault) (cfg : Config) (reqs : Array STAmount)
    : Except Error (List String) := do
  let r ← waRunSeq cfg v0 reqs
  return [cfg.name ++ "  (" ++ toString r.steps ++ " by-assets withdraws)", siteHeader]
         ++ (aggregate r.events).map fmtSiteStat
         ++ ["", waRunHeader, waFmtRun r]

/-! Single-execution sweep on the by-assets path. -/

structure WASingleStats where
  cfg : Config
  n : Nat
  nNonzeroCons : Nat
  maxCons : ℚ
  sumCons : ℚ
  nOver : Nat
  maxOver : ℚ
  nUnder : Nat
  maxUnder : ℚ
  nRejected : Nat
  nBufBad : Nat
  ulp : ℚ
  deriving Inhabited

def waSingleSweep (sc : Scenario) (cfg : Config) (n : Nat) (seed : UInt64)
    : Except Error WASingleStats := do
  let (v0, _) ← sc.seed
  let mut st : WASingleStats :=
    { cfg, n, nNonzeroCons := 0, maxCons := 0, sumCons := 0, nOver := 0, maxOver := 0
    , nUnder := 0, maxUnder := 0, nRejected := 0, nBufBad := 0, ulp := v0.ulp }
  let mut sd := seed
  for _ in [0:n] do
    sd := lcgNext sd
    let m : UInt64 := 1000000000000000 + (sd % 9000000000000000)
    let a ← iou m.toNat sc.amtExpo
    let r ← waRunSeq cfg v0 #[a]
    let c := ratAbs r.conservationErr
    st := { st with
      nNonzeroCons := st.nNonzeroCons + (if c ≠ 0 then 1 else 0)
      maxCons := max st.maxCons c
      sumCons := st.sumCons + c
      nOver := st.nOver + r.nOver
      maxOver := max st.maxOver r.maxOver
      nUnder := st.nUnder + r.nUnder
      maxUnder := max st.maxUnder r.maxUnder
      nRejected := st.nRejected + r.nRejected
      nBufBad := st.nBufBad + (if r.bufOk then 0 else 1) }
  return st

def waSingleHeader : String :=
  padRight "config" 20 ++ padRight "nzCons/n" 15 ++ padRight "maxCons" 12
    ++ padRight "ulp" 8 ++ padRight "overpaid/n" 14 ++ padRight "maxOverpay" 12
    ++ padRight "ulps" 12 ++ padRight "maxUnderpay" 12 ++ "flags"

def waFmtSingle (s : WASingleStats) : String :=
  padRight s.cfg.name 20
    ++ padRight (toString s.nNonzeroCons ++ "/" ++ toString s.n) 15
    ++ padRight (ratToSci s.maxCons) 12 ++ padRight (ratToDec (s.maxCons / s.ulp) 3) 8
    ++ padRight (toString s.nOver ++ "/" ++ toString s.n) 14
    ++ padRight (ratToSci s.maxOver) 12 ++ padRight (ratToDec (s.maxOver / s.ulp) 1) 12
    ++ padRight (ratToSci s.maxUnder) 12
    ++ (if s.nRejected > 0 then s!"rej={s.nRejected} " else "")
    ++ (if s.nBufBad > 0 then s!"BUFBAD={s.nBufBad}" else "")

def waSingleReport (sc : Scenario) (n : Nat) (seed : UInt64) : Except Error (List String) := do
  let (v0, _) ← sc.seed
  let mut out :=
    [ s!"assetsTotal={ratToDec (staRat v0.assetsTotal) sc.precision}  precision={sc.precision}"
      ++ s!"  ulp={ratToSci v0.ulp}  sharesTotal={sc.shares}  n={n}"
    , waSingleHeader ]
  for cfg in configs do
    let st ← waSingleSweep sc cfg n seed
    out := out ++ [waFmtSingle st]
  return out

/-- Share counts for a sequence run: a constant burn, small relative to the total. -/
def constShares (n : Nat) (sh : Nat) : Except Error (Array Number) := do
  let x ← ratToNumber (sh : ℚ)
  return Array.replicate n x

def fuzzShares (seed : UInt64) (n : Nat) (cap : Nat) : Except Error (Array Number) := do
  let mut sd := seed
  let mut out : Array Number := #[]
  for _ in [0:n] do
    sd := lcgNext sd
    let sh := 1 + (sd % cap.toUInt64)
    out := out.push (← ratToNumber (sh.toNat : ℚ))
  return out

end XRPL.Experiments
