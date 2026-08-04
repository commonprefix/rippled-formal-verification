import XRPL.Experiments.RatUtil
import XRPL.Model.Vault.VaultDeposit

/-!
# Deposit precision experiment

A duplicate of `Vault.deposit` (IOU / non-integral only) instrumented so that every
rounding site reports the exact rational it should have produced alongside the value it
actually stored. Four implementation choices are varied independently:

* compensated (Kahan) accumulation of `assetsTotal`
* residual-carrying through `mul` / `div`
* whether NAV reads `assetsTotal` or `assetsTotal + buffer`
* (baseline) none of the above

`assetsTotal` round-trips through `STAmount` (16-digit mantissa) after every deposit, so
the stored width matches what the ledger persists rather than the 19-digit `Number` the
model keeps internally.
-/

namespace XRPL.Experiments

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

/-! ## Rounding sites -/

inductive Site where
  | inputRound        -- roundToVaultPrecision on the requested amount (intentional)
  | navBufferAdd      -- assetsTotal + buffer, when NAV includes the buffer
  | sharesMul         -- sharesTotal * amount
  | sharesDiv         -- (that) / nav
  | sharesCorr        -- storing a mul/div residual as a Number
  | sharesTrunc       -- truncate to a whole share count (semantic)
  | sharesStore       -- shares -> int64 STAmount
  | chargeMul         -- assetsTotal * shares
  | chargeDiv         -- (that) / sharesTotal
  | chargeCorr        -- storing a mul/div residual as a Number
  | chargeStore       -- charged -> IOU STAmount, upward
  | kahanY            -- y = charged + buffer
  | kahanSum          -- assetsTotal + y
  | kahanGrid         -- roundToVaultPrecision of the sum
  | kahanBack         -- t - assetsTotal
  | kahanBuffer       -- y - (t - assetsTotal)
  | totalAdd          -- plain assetsTotal + charged (no-Kahan path)
  | totalStore        -- assetsTotal -> STAmount (16d), the ledger width
  | sharesTotalAdd    -- sharesTotal + shares
  -- withdraw
  | wNavSub           -- assetsTotal - lossUnrealized
  | wMul              -- nav * shares
  | wDiv              -- (that) / sharesTotal
  | wCorr             -- storing a mul/div residual
  | wStore            -- payout -> IOU STAmount, downward
  | wTotalSub         -- plain assetsTotal - payout (no-Kahan path)
  | wTotalStore       -- assetsTotal -> STAmount (16d) + grid
  | wKahanY           -- y = payout - buffer
  | wKahanSub         -- assetsTotal - y
  | wKahanGrid        -- roundToVaultPrecision of the difference
  | wKahanBack        -- assetsTotal - t
  | wKahanBuffer      -- (assetsTotal - t) - y
  | wSharesSub        -- sharesTotal - shares
  -- withdraw by assets: assets -> shares (round to NEAREST, not truncated)
  | waMul             -- sharesTotal * assetsRequested
  | waDiv             -- (that) / nav
  | waCorr            -- storing a mul/div residual
  | waSharesStore     -- shares -> int64 STAmount, to_nearest (can round UP)
  deriving DecidableEq, Repr, BEq, Hashable, Inhabited

def Site.name : Site → String
  | .inputRound => "inputRound"     | .navBufferAdd => "navBufferAdd"
  | .sharesMul => "sharesMul"       | .sharesDiv => "sharesDiv"
  | .sharesCorr => "sharesCorr"     | .sharesTrunc => "sharesTrunc"
  | .sharesStore => "sharesStore"   | .chargeMul => "chargeMul"
  | .chargeDiv => "chargeDiv"       | .chargeCorr => "chargeCorr"
  | .chargeStore => "chargeStore"   | .kahanY => "kahanY"
  | .kahanSum => "kahanSum"         | .kahanGrid => "kahanGrid"
  | .kahanBack => "kahanBack"       | .kahanBuffer => "kahanBuffer"
  | .totalAdd => "totalAdd"         | .totalStore => "totalStore"
  | .sharesTotalAdd => "sharesTotalAdd"
  | .wNavSub => "wNavSub"           | .wMul => "wMul"
  | .wDiv => "wDiv"                 | .wCorr => "wCorr"
  | .wStore => "wStore"             | .wTotalSub => "wTotalSub"
  | .wTotalStore => "wTotalStore"   | .wKahanY => "wKahanY"
  | .wKahanSub => "wKahanSub"       | .wKahanGrid => "wKahanGrid"
  | .wKahanBack => "wKahanBack"     | .wKahanBuffer => "wKahanBuffer"
  | .wSharesSub => "wSharesSub"
  | .waMul => "waMul"               | .waDiv => "waDiv"
  | .waCorr => "waCorr"             | .waSharesStore => "waSharesStore"

def allSites : List Site :=
  [.inputRound, .navBufferAdd, .sharesMul, .sharesDiv, .sharesCorr, .sharesTrunc,
   .sharesStore, .chargeMul, .chargeDiv, .chargeCorr, .chargeStore, .kahanY,
   .kahanSum, .kahanGrid, .kahanBack, .kahanBuffer, .totalAdd, .totalStore,
   .sharesTotalAdd,
   .wNavSub, .wMul, .wDiv, .wCorr, .wStore, .wTotalSub, .wTotalStore,
   .wKahanY, .wKahanSub, .wKahanGrid, .wKahanBack, .wKahanBuffer, .wSharesSub,
   .waMul, .waDiv, .waCorr, .waSharesStore]

/-- `sharesTrunc` and `inputRound` are deliberate reductions, not precision defects. -/
def Site.intentional : Site → Bool
  | .inputRound | .sharesTrunc => true
  | _ => false

structure RoundEvent where
  site : Site
  exact : ℚ
  got : ℚ
  deriving Repr, Inhabited

def RoundEvent.err (e : RoundEvent) : ℚ := ratAbs (e.exact - e.got)
def RoundEvent.rounded (e : RoundEvent) : Bool := e.exact ≠ e.got

/-! ## Instrumented monad -/

abbrev M := StateT (Array RoundEvent) (Except Error)

def liftE (e : Except Error α) : M α := fun s =>
  match e with
  | .ok a => .ok (a, s)
  | .error err => .error err

def note (site : Site) (exact got : ℚ) : M Unit :=
  modify (·.push { site, exact, got })

/-- Run an op, recording the gap between its exact result and its stored result. -/
def obs (site : Site) (exact : ℚ) (r : Except Error Number) : M Number := do
  let n ← liftE r
  note site exact (numRat n)
  return n

def obsS (site : Site) (exact : ℚ) (r : Except Error STAmount) : M STAmount := do
  let s ← liftE r
  note site exact (staRat s)
  return s

/-! ## Compensated values

`main + corr` approximates the true value. `corr` is `Number.zero` when residual
carrying is off. The residual is itself stored as a `Number`, so compensating is not
free — `sharesCorr` / `chargeCorr` record what the residual itself lost. -/

structure CVal where
  main : Number
  corr : Number
  deriving Repr

def CVal.of (n : Number) : CVal := { main := n, corr := Number.zero }
def CVal.toRat (c : CVal) : ℚ := numRat c.main + numRat c.corr

/-- Multiply, optionally keeping the exact residual. -/
def cmul (carry : Bool) (site siteC : Site) (x : CVal) (y : Number) : M CVal := do
  let exact := x.toRat * numRat y
  let m ← obs site exact (x.main.operator_mul y .to_nearest)
  if !carry then
    return CVal.of m
  else
    let rExact := exact - numRat m
    let c ← obs siteC rExact (ratToNumber rExact)
    return { main := m, corr := c }

/-- Divide, optionally keeping the exact residual. -/
def cdiv (carry : Bool) (site siteC : Site) (x : CVal) (y : Number) : M CVal := do
  let exact := x.toRat / numRat y
  let m ← obs site exact (x.main.operator_div y .to_nearest)
  if !carry then
    return CVal.of m
  else
    let rExact := exact - numRat m
    let c ← obs siteC rExact (ratToNumber rExact)
    return { main := m, corr := c }

/-! ## Vault under test -/

structure EVault where
  precision : Nat              -- 0..8; assetsTotal is a multiple of 10^-precision
  assetsTotal : STAmount       -- stored at ledger width (16 digits)
  buffer : Number              -- assetsTotalBuffer; Number.zero when Kahan is off
  sharesTotal : Number         -- integral
  deriving Repr

def EVault.ulp (v : EVault) : ℚ := pow10 (-(v.precision : Int))

/-- Books as the vault would report them: primary field plus whatever the buffer holds. -/
def EVault.booked (v : EVault) : ℚ := staRat v.assetsTotal + numRat v.buffer

structure Config where
  name : String
  kahanAdd : Bool
  kahanMulDiv : Bool
  navWithBuffer : Bool
  deriving Repr, Inhabited

def configs : List Config :=
  [ { name := "1 baseline",          kahanAdd := false, kahanMulDiv := false, navWithBuffer := false }
  , { name := "2 kahan add",         kahanAdd := true,  kahanMulDiv := false, navWithBuffer := false }
  , { name := "3 kahan add + nav",   kahanAdd := true,  kahanMulDiv := false, navWithBuffer := true  }
  , { name := "4 kahan add+muldiv",  kahanAdd := true,  kahanMulDiv := true,  navWithBuffer := false }
  , { name := "5 all",               kahanAdd := true,  kahanMulDiv := true,  navWithBuffer := true  } ]

/-! ## One deposit -/

/-- Round an IOU amount down onto the vault's precision grid. -/
def roundToVaultPrecision (p : Nat) (a : STAmount) : Except Error STAmount :=
  STAmount.roundToExponent a (-(p : Int)) .downward

structure StepOut where
  v : EVault
  charged : STAmount          -- what actually moved on the trust line
  shares : Number
  zeroShares : Bool           -- deposit minted no shares: a no-op, run is vacuous
  precisionLost : Bool        -- assetsTotal could no longer hold 10^-precision
  deriving Repr

def depositStep (cfg : Config) (v : EVault) (amountReq : STAmount) : M StepOut := do
  -- 1. align the requested amount to the vault's precision (intentional reduction)
  let amt ← obsS .inputRound (staRat amountReq) (roundToVaultPrecision v.precision amountReq)
  let amtN ← liftE (amt.toNumber .to_nearest)
  let totalN ← liftE (v.assetsTotal.toNumber .to_nearest)

  -- 2. NAV: primary field alone, or compensated with the buffer
  let nav ←
    if cfg.navWithBuffer then
      obs .navBufferAdd (numRat totalN + numRat v.buffer) (totalN.operator_add v.buffer .to_nearest)
    else
      pure totalN

  -- 3. shares = truncate(sharesTotal * amt / nav)
  let s1 ← cmul cfg.kahanMulDiv .sharesMul .sharesCorr (CVal.of v.sharesTotal) amtN
  let s2 ← cdiv cfg.kahanMulDiv .sharesDiv .sharesCorr s1 nav
  let sharesRat := s2.toRat
  let sharesN ← obs .sharesTrunc sharesRat.floor (← liftE (ratToNumber s2.toRat)).truncate
  let sharesA ← obsS .sharesStore (numRat sharesN) (STAmount.ofNumber .int64 sharesN .to_nearest)
  let sharesNum ← liftE (sharesA.toNumber .to_nearest)

  -- 4. charged = roundUp(nav * shares / sharesTotal)
  let c1 ← cmul cfg.kahanMulDiv .chargeMul .chargeCorr (CVal.of nav) sharesNum
  let c2 ← cdiv cfg.kahanMulDiv .chargeDiv .chargeCorr c1 v.sharesTotal
  let charged ← obsS .chargeStore c2.toRat
    (do let n ← ratToNumber c2.toRat; STAmount.ofNumber .fractional n .upward)
  let chargedN ← liftE (charged.toNumber .to_nearest)

  -- 5. credit assetsTotal
  let (total', buffer') ←
    if !cfg.kahanAdd then
      let sum ← obs .totalAdd (numRat totalN + numRat chargedN)
        (totalN.operator_add chargedN .to_nearest)
      let st ← obsS .totalStore (numRat sum)
        (do let a ← STAmount.ofNumber .fractional sum .to_nearest
            roundToVaultPrecision v.precision a)
      pure (st, Number.zero)
    else
      -- y = charged + buffer ; t = grid(assetsTotal + y) ; buffer' = y - (t - assetsTotal)
      let y ← obs .kahanY (numRat chargedN + numRat v.buffer)
        (chargedN.operator_add v.buffer .to_nearest)
      -- MUST round downward: with .to_nearest the sum can overshoot, `t` then exceeds
      -- the true assetsTotal + y, and the buffer goes negative (measured).
      let sum ← obs .kahanSum (numRat totalN + numRat y) (totalN.operator_add y .downward)
      let t ← obsS .kahanGrid (numRat sum)
        (do let a ← STAmount.ofNumber .fractional sum .downward
            roundToVaultPrecision v.precision a)
      let tN ← liftE (t.toNumber .to_nearest)
      let back ← obs .kahanBack (numRat tN - numRat totalN)
        (tN.operator_add totalN.operator_neg .to_nearest)
      let buf ← obs .kahanBuffer (numRat y - numRat back)
        (y.operator_add back.operator_neg .to_nearest)
      pure (t, buf)

  -- 6. sharesTotal += shares
  let sharesTotal' ← obs .sharesTotalAdd (numRat v.sharesTotal + numRat sharesNum)
    (v.sharesTotal.operator_add sharesNum .to_nearest)

  return { v := { v with assetsTotal := total', buffer := buffer', sharesTotal := sharesTotal' }
         , charged := charged
         , shares := sharesNum
         , zeroShares := sharesNum.mantissa_ == 0
           -- capacity: p decimals need 16-p integer digits. Past 10^(16-p) the mantissa
           -- runs out and the stored exponent rises above -p, silently coarsening the grid.
         , precisionLost := total'.exponent > -(v.precision : Int) && total'.mantissa != 0 }

end XRPL.Experiments
