import XRPL.Model.Model

-- Random search for loan payment histories that reach the rarely-hit LoanPay / LoanState arms.
-- Run in the instrumented copy: every arm prints "COV n" on stderr, each trial prints "TRIAL ...".

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault

def num (m : Int) (e : Int) : Number :=
  (Number.from_rep (Int64.ofInt m) e largeRange.min largeRange.max .to_nearest).toOption.getD Number.zero

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : Rng × Nat :=
  let s := r.s * 6364136223846793005 + 1442695040888963407
  (⟨s⟩, (s >>> 33).toNat)

def Rng.range (r : Rng) (lo hi : Nat) : Rng × Nat :=
  let (r, x) := r.next
  (r, lo + x % (hi - lo + 1))

def mkVault (assets : Number) (shares : Number) : Option Vault :=
  (RawVault.to_lawful {
    assetsAvailable := assets, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := .fractional, scale := 6, sharesTotal := shares,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero,
    schedule := some { subscriptionDate := 100, redemptionDate := 900_000_000 },
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }).toOption

def mkBroker (mgmt : UInt16) : Option LoanBroker :=
  (RawLoanBroker.to_lawful {
    numericType := .fractional, managementFeeRate := mgmt, coverRateMinimum := 0,
    coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero,
    coverAvailable := Number.zero, loanCount := 0 }).toOption

def fmt (n : Number) : String :=
  s!"{if n.negative_ then "-" else ""}{n.mantissa_}e{n.exponent_}"

-- One trial: create a loan, then pay it with a random mix of on-time regular payments and overpayments.
def trial (r : Rng) (i : Nat) : IO Rng := do
  let (r, pm) := r.range 1 9_999
  let (r, pe) := r.range 0 7          -- principal = pm * 10^(pe-6+...) spread over many magnitudes
  let principal := num pm (Int.ofNat pe - 6 + 2)
  let (r, rate) := r.range 0 100_000
  let (r, total) := r.range 2 400
  let (r, interval) := r.range 60 2_000_000
  let interval := min interval (800_000_000 / total)
  let (r, mgmt) := r.range 0 10_000
  let (r, ovRate) := r.range 0 100_000
  let (r, ovFee) := r.range 0 100_000
  let (r, style) := r.range 0 2      -- 0 regular, 1 overpay each time, 2 mixed
  let some vault := mkVault (num 1 9) (num 1 15) | return r
  let some broker := mkBroker mgmt.toUInt16 | return r
  let rates : LoanRates := { interestRate := rate.toUInt32, lateInterestRate := 0, closeInterestRate := 0,
                             overpaymentInterestRate := ovRate.toUInt32, overpaymentFee := ovFee.toUInt32 }
  let fees : LoanFees := { originationFee := Number.zero, serviceFee := Number.zero,
                           latePaymentFee := Number.zero, closePaymentFee := Number.zero }
  let start : UInt32 := 1_000_000
  let schedule := LoanSchedule.build (some interval.toUInt32) (some total.toUInt32) none start start false
  match Loan.canCreate broker vault principal fees schedule start false with
  | .ok .tesSUCCESS => pure ()
  | _ => return r
  let .ok (.ok created) := (Loan.create broker vault principal rates fees schedule true false).run | return r
  IO.eprintln s!"TRIAL {i} principal={fmt principal} rate={rate} total={total} interval={interval} mgmt={mgmt} ovRate={ovRate} ovFee={ovFee} style={style}"
  (← IO.getStderr).flush
  let mut loan := created.loan'
  let mut pool := created.pool'
  let mut r := r
  let mut step := 0
  while loan.paymentRemaining != 0 && step < 500 do
    step := step + 1
    let (r1, k) := r.range 1 3
    let (r2, extraM) := r1.range 0 9_999
    let (r3, extraE) := r2.range 0 6
    let (r4, pick) := r3.range 0 1
    r := r4
    let overpay := style == 1 || (style == 2 && pick == 1)
    -- amount: k instalments (rounded up) plus, for an overpayment, a random extra
    let .ok base := loan.periodicPayment.operator_mul (num (Int.ofNat k) 0) .upward | break
    let extra := num extraM (Int.ofNat extraE - 6)
    let .ok amount := (if overpay then base.operator_add extra .to_nearest else .ok base) | break
    let .ok amount := amount.operator_add (num 1 (-6)) .upward | break
    -- an IOU amount on the ledger carries 16 digits
    let .ok amountSt := STAmount.ofNumber .fractional amount .upward | break
    let .ok amount := amountSt.toNumber .to_nearest | break
    let now := loan.nextPaymentDueDate
    let res := (if overpay then loan.overpayment pool amount now else loan.regularPayment pool amount now).run
    match res with
    | .ok (.ok w) =>
      IO.eprintln s!"STEP {step} {if overpay then "over" else "reg"} amount={fmt amount} -> remaining={w.loan'.paymentRemaining}"
      (← IO.getStderr).flush
      loan := w.loan'
      pool := w.pool'
    | .ok (.error ter) =>
      IO.eprintln s!"STEP {step} rejected {ter.code}"
      break
    | .error e =>
      IO.eprintln s!"STEP {step} model error {repr e}"
      break
  return r

def main (args : List String) : IO Unit := do
  let n := (args.headD "200").toNat!
  let seed := (args.getD 1 "42").toNat!
  let mut r : Rng := ⟨seed.toUInt64⟩
  for i in [0:n] do
    r ← trial r i

