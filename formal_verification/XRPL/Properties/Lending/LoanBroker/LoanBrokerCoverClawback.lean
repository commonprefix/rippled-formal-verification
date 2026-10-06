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

/-- With no amount or a zero amount, the clawback takes all cover above the minimum cover, rounded
down to a `Number` and then to nearest in the vault asset. A nonzero clawed amount is off from
that difference by at most half a unit in its last digit. -/
theorem LoanBroker.roundedCoverClawback_all (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hpos : 0 < maxClaw.signum)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hclaw : STAmount.ofNumber lb.numericType maxClaw .to_nearest = .ok claw) :
    lb.roundedCoverClawback pool amount = .ok (.rounded claw) ∧
      (claw.mValue ≠ 0 →
        |claw.toRat - maxClaw.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent) :=
  LoanBroker.roundedCoverClawback_all_proof lb pool amount e minimumCover maxClaw claw hexp hmin
    hsub hpos hall hclaw

/-- Otherwise the clawback takes the requested amount, capped at the cover above the minimum and
rounded to nearest in the vault asset. A nonzero clawed amount is off from the smaller of the two
by at most half a unit in its last digit. -/
theorem LoanBroker.roundedCoverClawback_capped (pool : α) (a : STAmount)
    (e : Int) (minimumCover maxClaw magnitude : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hpos : 0 < maxClaw.signum)
    (hnz : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hmag : a.toNumber .to_nearest = .ok magnitude)
    (hclaw : STAmount.ofNumber lb.numericType
      (if magnitude.operator_gt maxClaw = true then maxClaw else magnitude) .to_nearest =
        .ok claw) :
    lb.roundedCoverClawback pool (some a) = .ok (.rounded claw) ∧
      (claw.mValue ≠ 0 →
        |claw.toRat - min a.toRat maxClaw.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent) :=
  LoanBroker.roundedCoverClawback_capped_proof lb pool a e minimumCover maxClaw magnitude claw
    hexp hmin hsub hpos hnz hac ha0 hmag hclaw

/-- Integral strengthening of `roundedCoverClawback_capped`: a nonzero XRP or
MPT request that fits under the cover above the minimum is clawed exactly. -/
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

/-- When the new `coverAvailable` fits a `Number`, the clawback subtracts
exactly the clawed amount. -/
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

/-- Witness: the fit hypothesis of `coverClawback_debit` cannot be dropped, a run
whose checks passed claws `1234.567890123456` from `10^18` of cover and lowers
`coverAvailable` by `1235`. -/
theorem LoanBroker.coverClawback_debit_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverClawback pool amount = .ok .tesSUCCESS ∧
      lb.coverClawback pool amount = .ok (.ok res) ∧
      (∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) ∧
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≠ res.amount'.toRat :=
  LoanBroker.coverClawback_debit_witness

/-- A clawback only lowers `coverAvailable`. -/
theorem LoanBroker.coverClawback_decreases_cover (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_decreases_cover_proof lb pool amount res hcan hok hreq

/-- A larger request never claws less. A request below the cover above the
minimum is clawed whole, and every larger request claws the same capped
amount. -/
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

/-- A clawback can leave `coverAvailable` below the minimum cover, but only by half a unit in the
last digit of the clawed amount. Only the final rounding to nearest can take it below the minimum. -/
theorem LoanBroker.coverClawback_keeps_minimum_within_half (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    minimumCover.toRat - res.loanBroker'.toExact.coverAvailable ≤
      (1 / 2 : ℚ) * (10 : ℚ) ^ res.amount'.exponent :=
  LoanBroker.coverClawback_keeps_minimum_within_half_proof lb pool amount res e minimumCover hcan
    hok hexp hmin hreq hexact

/-- Witness: the half-unit term in `coverClawback_keeps_minimum_within_half` cannot be dropped. A full
clawback that passes its checks, with an exact difference, leaves `coverAvailable` below the minimum cover. -/
theorem LoanBroker.coverClawback_keeps_minimum_within_half_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .ok (.ok res) ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) ∧
      0 < minimumCover.toRat - res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_keeps_minimum_within_half_witness

/-- With no amount or a zero amount, a clawback whose checks passed leaves exactly
the minimum cover, when the asset holds the cover above the minimum exactly. -/
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

/-- A clawback whose checks passed runs to the end: it succeeds, or the new broker
fails the lawfulness re-check. -/
theorem LoanBroker.coverClawback_total (pool : α) (amount : Option STAmount)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hcap : lb.toExact.coverAvailable < 10 ^ 96) : -- below `10^96`, above every IOU amount
    (∃ res, lb.coverClawback pool amount = .ok (.ok res)) ∨
      lb.coverClawback pool amount = .error .notLawful :=
  LoanBroker.coverClawback_total_proof lb pool amount hcan hreq hcap

/-- A clawback whose checks passed returns a lawful broker when the asset holds
`coverAvailable` exactly: the clawed amount then never exceeds it. -/
theorem LoanBroker.coverClawback_lawful_total (pool : α)
    (amount : Option STAmount)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    -- `coverAvailable` is on the STAmount grid of the vault asset, so it converts without rounding
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    ∃ res, lb.coverClawback pool amount = .ok (.ok res) :=
  LoanBroker.coverClawback_lawful_total_proof lb pool amount hcan hreq hrep

/-- Witness: the STAmount grid hypothesis of `coverClawback_lawful_total` cannot be dropped.
With a 17-digit `coverAvailable` off the IOU grid, a full clawback passes its checks, rounds the
clawed amount up above the cover, and fails as `notLawful` because the new cover is negative. -/
theorem LoanBroker.coverClawback_lawful_total_attained :
    ∃ (lb : LoanBroker) (pool : Vault),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .error .notLawful :=
  LoanBroker.coverClawback_lawful_total_witness

/-- With no debt, a full clawback passes the checks and leaves zero cover, when the
asset holds `coverAvailable` exactly. -/
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
