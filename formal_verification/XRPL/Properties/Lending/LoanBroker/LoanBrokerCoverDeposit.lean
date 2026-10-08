import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness

/-! # `LoanBroker.roundedCoverAmount` and `LoanBroker.coverDeposit`

A deposit rounds the amount down to the cover scale and adds it with 19-digit `Number`
rounding. The credit is exact only when the sum fits a `Number`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable (lb : LoanBroker)

/-- 0 ≤ amount - roundedAmount < 1 ULP at CoverAvailable's scale (`10 ^ e`). -/
theorem LoanBroker.roundedCoverAmount_bounds (amount r : STAmount) (e : Int)
    (hcanon : amount.integral = false → amount.IOUCanonical)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    r.toRat ≤ amount.toRat ∧ amount.toRat - r.toRat < 10 ^ e :=
  LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hcanon hexp hok

/-- Witness: a run where the error reaches 1 − 10⁻¹⁵ ULP, just under the bound. On a cover of
`10^15` one unit is `1`, and a deposit of `1.999999999999999` is rounded down to `1`. -/
theorem LoanBroker.roundedCoverAmount_bounds_attained :
    ∃ (lb : LoanBroker) (amount r : STAmount) (e : Int),
      (amount.integral = false → amount.IOUCanonical) ∧
      numberExponent lb.coverAvailable lb.numericType = .ok e ∧
      lb.roundedCoverAmount amount = .ok (.rounded r) ∧
      (1 - 1 / 10 ^ 15) * 10 ^ e ≤ amount.toRat - r.toRat :=
  LoanBroker.roundedCoverAmount_bounds_witness

/-- When integral type, roundedAmount = amount (no rounding). -/
theorem LoanBroker.roundedCoverAmount_integral (amount r : STAmount)
    (hint : amount.integral = true)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) : r = amount :=
  LoanBroker.roundedCoverAmount_integral_proof lb amount r hint hok

/-- When the new CoverAvailable fits a Number -> roundedAmount = CoverAvailable' - CoverAvailable. -/
theorem LoanBroker.coverDeposit_credit (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat :=
  LoanBroker.coverDeposit_credit_proof lb amount res hok hc hexact

/-- Integral strengthening of `coverDeposit_credit`: a whole `coverAvailable`
plus a whole deposit, below `2^63`, is credited exactly. -/
theorem LoanBroker.coverDeposit_credit_integral (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = amount.toRat :=
  LoanBroker.coverDeposit_credit_integral_proof lb amount res hok hint hsz hcint hbound

/-- When the new CoverAvailable fits a Number -> amount ≥ CoverAvailable' - CoverAvailable. -/
theorem LoanBroker.coverDeposit_credit_le_amount (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat :=
  LoanBroker.coverDeposit_credit_le_amount_proof lb amount res hok hc hexact

/-- Witness: a run that credits more than was deposited. On a cover of `6.6 * 10^12`, a deposit of
`9999999999999999 * 10^15` raises `coverAvailable` by `3.4 * 10^12` more than the deposit. -/
theorem LoanBroker.coverDeposit_credit_le_amount_attained :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.IOUCanonical ∧ lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      amount.toRat < res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable :=
  LoanBroker.coverDeposit_credit_le_amount_witness

/-- When CoverAvailable fits an STAmount exactly -> STAmount(CoverAvailable' − CoverAvailable) =
roundedAmount, and roundedAmount is already at the cover scale.
`amount''` - the deposited amount rounded to the cover scale again -/
theorem LoanBroker.coverDeposit_applied_delta (amount amount'' : STAmount)
    (res : LoanBrokerCoverResult) (deltaCover : Number) (deltaAmount : STAmount)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hat : amount.mNumericType = lb.numericType)
    (hnn : 0 ≤ amount.toRat)
    -- `coverAvailable` is on the STAmount grid of the vault asset
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable)
    -- an XRP or MPT cover plus the deposit stays within the largest MPT amount, `2^63 - 1`
    (hbound : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hround : lb.roundedCoverAmount res.amount' = .ok (.rounded amount''))
    (hsub : res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest =
      .ok deltaCover)
    (hda : STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount) :
    amount''.operator_eq res.amount' = true ∧ deltaAmount.operator_eq res.amount' = true :=
  LoanBroker.coverDeposit_applied_delta_proof lb amount amount'' res deltaCover deltaAmount hok hc
    hat hnn hrep hbound hround hsub hda

/-- Cover deposit only raises CoverAvailable (monotone up). -/
theorem LoanBroker.coverDeposit_increases_cover (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_increases_cover_proof lb amount res hok hc hnn

/-- When CoverAvailable + roundedAmount < 10^96 -> the deposit succeeds with roundedAmount and never
throws, not even notLawful. -/
theorem LoanBroker.coverDeposit_total (amount r : STAmount)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    -- the sum is below `10^96`, above every IOU amount
    (hcap : lb.toExact.coverAvailable + r.toRat < 10 ^ 96) :
    ∃ res, lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = r :=
  LoanBroker.coverDeposit_total_proof lb amount r hrounded hc hnn hcap

/-- A deposit into an empty cover is credited whole: CoverAvailable' = amount. -/
theorem LoanBroker.coverDeposit_empty (amount : STAmount) (res : LoanBrokerCoverResult)
    (hzero : lb.coverAvailable = Number.zero)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hat : amount.mNumericType = lb.numericType) :
    res.amount' = amount ∧ res.loanBroker'.toExact.coverAvailable = amount.toRat :=
  LoanBroker.coverDeposit_empty_proof lb amount res hzero hok hc hat

/-- If CoverAvailable ≥ minCover before a deposit, it stays also after. -/
theorem LoanBroker.coverDeposit_keeps_minimum (amount : STAmount) (res : LoanBrokerCoverResult)
    (e : Int)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    (hmin : lb.HasMinimumCover e) :
    res.loanBroker'.HasMinimumCover e :=
  LoanBroker.coverDeposit_keeps_minimum_proof lb amount res e hok hc hnn hmin

end XRPL.Model.Lending
