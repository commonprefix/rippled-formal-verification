import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness

/-! # `LoanBroker.roundedCoverClawback` and `LoanBroker.coverClawback`

A clawback takes the cover above the minimum cover, or less if asked, rounded to nearest.
That rounding can go up, so a clawback can end just below the minimum cover. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- When the amount is unset or 0 and roundedAmount ≠ 0 -> roundedAmount − (CoverAvailable -
minCover) ≤ ½ ULP. -/
theorem LoanBroker.roundedCoverClawback_all_upper_bound (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    claw.toRat - maxClaw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_all_upper_bound_proof lb pool amount e minimumCover maxClaw claw
    hexp hmin hsub hall hok hnz

/-- Witness: a run where the error reaches the bound. With a debt of `5` at a 10% minimum, the
minimum cover is `0.5`, and a cover of `1234567890123458` has `1234567890123457.5` above it. A
full clawback rounds that up to `1234567890123458`, the whole cover. -/
theorem LoanBroker.roundedCoverClawback_all_upper_bound_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      lb.roundedCoverClawback pool none = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      claw.toRat - maxClaw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_all_upper_bound_witness

/-- When the amount is unset or 0 and roundedAmount ≠ 0 -> (CoverAvailable - minCover) −
roundedAmount ≤ ½ ULP. -/
theorem LoanBroker.roundedCoverClawback_all_lower_bound (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    maxClaw.toRat - claw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_all_lower_bound_proof lb pool amount e minimumCover maxClaw claw
    hexp hmin hsub hall hok hnz

/-- Witness: a run where the error reaches the bound. A tie rounds to the even neighbor, so with
`1234567890123457` of cover and a minimum of `0.5`, a full clawback rounds `1234567890123456.5`
down to `1234567890123456`. -/
theorem LoanBroker.roundedCoverClawback_all_lower_bound_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      lb.roundedCoverClawback pool none = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      maxClaw.toRat - claw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_all_lower_bound_witness

/-- When roundedAmount ≠ 0 -> roundedAmount − min(amount, CoverAvailable - minCover) ≤ ½ ULP. -/
theorem LoanBroker.roundedCoverClawback_capped_upper_bound (pool : α) (a : STAmount)
    (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hza : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    claw.toRat - min a.toRat maxClaw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_capped_upper_bound_proof lb pool a e minimumCover maxClaw claw
    hexp hmin hsub hza hac ha0 hok hnz

/-- Witness: a run where the error reaches the bound. On the broker of
`roundedCoverClawback_all_upper_bound_attained`, a request of `2 * 10^15` is capped at
`1234567890123457.5` and rounded up to `1234567890123458`. -/
theorem LoanBroker.roundedCoverClawback_capped_upper_bound_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (e : Int) (minimumCover maxClaw : Number)
      (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      a.isZero = false ∧ a.ExactCanonical ∧ 0 ≤ a.toRat ∧
      lb.roundedCoverClawback pool (some a) = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      claw.toRat - min a.toRat maxClaw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_capped_upper_bound_witness

/-- When roundedAmount ≠ 0 -> min(amount, CoverAvailable - minCover) − roundedAmount ≤ ½ ULP. -/
theorem LoanBroker.roundedCoverClawback_capped_lower_bound (pool : α) (a : STAmount)
    (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hza : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    min a.toRat maxClaw.toRat - claw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_capped_lower_bound_proof lb pool a e minimumCover maxClaw claw
    hexp hmin hsub hza hac ha0 hok hnz

/-- Witness: a run where the error reaches the bound. On the broker of
`roundedCoverClawback_all_lower_bound_attained`, a request of `2 * 10^15` is capped at
`1234567890123456.5` and rounded down to `1234567890123456`. -/
theorem LoanBroker.roundedCoverClawback_capped_lower_bound_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (e : Int) (minimumCover maxClaw : Number)
      (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      a.isZero = false ∧ a.ExactCanonical ∧ 0 ≤ a.toRat ∧
      lb.roundedCoverClawback pool (some a) = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      min a.toRat maxClaw.toRat - claw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  LoanBroker.roundedCoverClawback_capped_lower_bound_witness

/-- For integral type, an amount ≠ 0 that fits above the minCover is clawed exactly. -/
theorem LoanBroker.roundedCoverClawback_integral (pool : α) (a claw : STAmount) (e : Int)
    (minimumCover : Number)
    (hint : a.IntegralCanonical) (hsz : a.mValue.toNat ≤ 2 ^ 63 - 1) (ha0 : 0 ≤ a.toRat)
    (hat : a.mNumericType = lb.numericType)
    (hza : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw)) :
    claw = a :=
  LoanBroker.roundedCoverClawback_integral_proof lb pool a claw e minimumCover hint hsz ha0 hat hza
    hexp hmin hfit hok

/-- When the new CoverAvailable fits a Number -> roundedAmount = CoverAvailable - CoverAvailable'. -/
theorem LoanBroker.coverClawback_debit (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat :=
  LoanBroker.coverClawback_debit_proof lb pool amount res hcan hok hreq hexact

/-- Integral strengthening of `coverClawback_debit`: on an XRP or MPT broker, a
whole `coverAvailable` below `2^63` is debited exactly. -/
theorem LoanBroker.coverClawback_debit_integral (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat :=
  LoanBroker.coverClawback_debit_integral_proof lb pool amount res hcan hok hreq hnt hcint hbound

/-- When the amount ≠ 0 and the new CoverAvailable fits a Number -> amount ≥ CoverAvailable -
CoverAvailable'. -/
theorem LoanBroker.coverClawback_debit_le_amount (pool : α) (a : STAmount)
    (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool (some a) = .ok (.ok res))
    (hac : a.ExactCanonical) (hat : a.mNumericType = lb.numericType) (ha0 : 0 ≤ a.toRat)
    (hza : a.isZero = false)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ a.toRat :=
  LoanBroker.coverClawback_debit_le_amount_proof lb pool a res hcan hok hac hat ha0 hza hexact

/-- Witness: a run where CoverAvailable drops by more than the amount. Clawing `1234.567890123456`
from `10^18` of cover lowers `coverAvailable` by `1235`. -/
theorem LoanBroker.coverClawback_debit_le_amount_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some a) = .ok (.ok res) ∧
      a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat ∧ a.isZero = false ∧
      res.amount' = a ∧
      a.toRat < lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_debit_le_amount_witness

/-- Witness: the clawed amount is never rounded to the cover scale, so STAmount(CoverAvailable −
CoverAvailable') ≠ roundedAmount even when CoverAvailable fits an STAmount exactly. Clawing
`1234.567890123456` from `10^18` moves `coverAvailable` by `1235`, while a deposit would round
the amount down to `1000`.
`amount''` - the clawed amount rounded down to the cover scale, as a deposit rounds it -/
theorem LoanBroker.coverClawback_applied_delta_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (amount'' : STAmount)
      (res : LoanBrokerCoverResult) (deltaCover : Number) (deltaAmount : STAmount),
      lb.canCoverClawback pool amount = .ok .tesSUCCESS ∧
      lb.coverClawback pool amount = .ok (.ok res) ∧
      (∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) ∧
      lb.roundedCoverAmount res.amount' = .ok (.rounded amount'') ∧
      amount''.operator_eq res.amount' = false ∧
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq res.amount' = false :=
  LoanBroker.coverClawback_applied_delta_witness

/-- Cover clawback only lowers CoverAvailable (monotone down). -/
theorem LoanBroker.coverClawback_decreases_cover (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_decreases_cover_proof lb pool amount res hcan hok hreq

/-- A bigger clawback amount never takes less. -/
theorem LoanBroker.coverClawback_monotone (pool : α) (a b : STAmount)
    (ra rb : LoanBrokerCoverResult)
    (hoka : lb.coverClawback pool (some a) = .ok (.ok ra))
    (hokb : lb.coverClawback pool (some b) = .ok (.ok rb))
    (hac : a.ExactCanonical) (hbc : b.ExactCanonical) (hat : a.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false)
    (hab : a.toRat ≤ b.toRat)
    (hcanb : lb.canCoverClawback pool (some b) = .ok .tesSUCCESS) :
    ra.amount'.toRat ≤ rb.amount'.toRat :=
  LoanBroker.coverClawback_monotone_proof lb pool a b ra rb hoka hokb hac hbc hat ha0 hza hzb hab
    hcanb

/-- When the checks pass and CoverAvailable - minCover fits an STAmount exactly -> CoverAvailable' ≥
minCover. -/
theorem LoanBroker.coverClawback_keeps_minimum (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    -- `coverAvailable` minus the minimum cover is on the STAmount grid of the vault asset
    (hfit : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable - minimumCover.toRat) :
    minimumCover.toRat ≤ res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_keeps_minimum_proof lb pool amount res e minimumCover hcan hok hexp hmin
    hreq hfit

/-- Witness: a run where CoverAvailable' < minCover when CoverAvailable - minCover doesn't fit an
STAmount exactly. With a debt of `5` at a 10% minimum, a cover of `10^16` has
`9999999999999999.5` above the minimum cover of `0.5`. A full clawback rounds the clawed amount
up to `10^16` and leaves no cover. -/
theorem LoanBroker.coverClawback_keeps_minimum_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .ok (.ok res) ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat :=
  LoanBroker.coverClawback_keeps_minimum_witness

/-- A clawback with no amount or 0 leaves exactly the minCover, when CoverAvailable - minCover fits
an STAmount exactly. -/
theorem LoanBroker.coverClawback_all_leaves_minimum (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    -- `coverAvailable` minus the minimum cover is on the STAmount grid of the vault asset
    (hfit : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable - minimumCover.toRat) :
    res.loanBroker'.toExact.coverAvailable = minimumCover.toRat :=
  LoanBroker.coverClawback_all_leaves_minimum_proof lb pool amount res e minimumCover hall hcan
    hok hexp hmin hfit

/-- When the checks pass -> never throws an error (other than notLawful). -/
theorem LoanBroker.coverClawback_total (pool : α) (amount : Option STAmount)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hcap : lb.toExact.coverAvailable < 10 ^ 96) : -- below `10^96`, above every IOU amount
    (∃ res, lb.coverClawback pool amount = .ok (.ok res)) ∨
      lb.coverClawback pool amount = .error .notLawful :=
  LoanBroker.coverClawback_total_proof lb pool amount hcan hreq hcap

/-- When the checks pass and CoverAvailable fits an STAmount exactly -> never notLawful. -/
theorem LoanBroker.coverClawback_lawful_total (pool : α)
    (amount : Option STAmount)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    -- `coverAvailable` is on the STAmount grid of the vault asset, so it converts without rounding
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    ∃ res, lb.coverClawback pool amount = .ok (.ok res) :=
  LoanBroker.coverClawback_lawful_total_proof lb pool amount hcan hreq hrep

/-- Witness: a run that passes the checks but is notLawful. With a 17-digit `coverAvailable` off the
IOU grid, a full clawback rounds the clawed amount up above the cover, so the new cover is
negative. -/
theorem LoanBroker.coverClawback_lawful_total_attained :
    ∃ (lb : LoanBroker) (pool : Vault),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .error .notLawful :=
  LoanBroker.coverClawback_lawful_total_witness

/-- With no debt, the whole cover (≠ 0) can be clawed back, when CoverAvailable fits an STAmount
exactly. -/
theorem LoanBroker.coverClawback_all (pool : α) (e : Int) (s : STAmount)
    (hdebt : lb.debtTotal = Number.zero)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0)
    (hrep : s.toRat = lb.toExact.coverAvailable)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      ∃ res, lb.coverClawback pool none = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable = 0 :=
  LoanBroker.coverClawback_all_proof lb pool e s hdebt hs hnz hrep hexp

end XRPL.Model.Lending
