import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness

/-! # `LoanBroker.roundedCoverAmount` and `LoanBroker.coverDeposit`

The deposit rounds the amount down to the scale of `coverAvailable` and adds it
with 19-digit `Number` rounding, so the credit is exact only when the true sum
fits a `Number`. `AssociateAsset.lean` covers the rounding C++ applies after. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable (lb : LoanBroker)

/-- The rounded amount never exceeds the requested amount, and stays within one
step `10 ^ e` of the cover scale below it. -/
theorem LoanBroker.roundedCoverAmount_bounds (amount r : STAmount) (e : Int)
    (hcanon : amount.integral = false → amount.IOUCanonical)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    r.toRat ≤ amount.toRat ∧ amount.toRat - r.toRat < 10 ^ e :=
  LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hcanon hexp hok

/-- An integral amount passes through `roundedCoverAmount` unchanged. -/
theorem LoanBroker.roundedCoverAmount_integral (amount r : STAmount)
    (hint : amount.integral = true)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) : r = amount :=
  LoanBroker.roundedCoverAmount_integral_proof lb amount r hint hok

/-- When the new `coverAvailable` fits a `Number`, the deposit adds exactly the
rounded amount. -/
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

/-- When the new `coverAvailable` fits a `Number`, it rises by no more than the
requested amount. -/
theorem LoanBroker.coverDeposit_credit_le_amount (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat :=
  LoanBroker.coverDeposit_credit_le_amount_proof lb amount res hok hc hexact

/-- Witness: the fit hypothesis of `coverDeposit_credit_le_amount` cannot be
dropped, a run exists whose `coverAvailable` rises by more than the deposit. -/
theorem LoanBroker.coverDeposit_credit_le_amount_attained :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.IOUCanonical ∧ lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      amount.toRat < res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable :=
  LoanBroker.coverDeposit_credit_le_amount_witness

/-- A deposit only raises `coverAvailable`. -/
theorem LoanBroker.coverDeposit_increases_cover (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_increases_cover_proof lb amount res hok hc hnn

/-- An amount that passed `roundedCoverAmount` deposits without a throw: the
result is a lawful broker holding the rounded amount, never `.notLawful`. -/
theorem LoanBroker.coverDeposit_total (amount r : STAmount)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    -- the sum is below `10^96`, above every IOU amount
    (hcap : lb.toExact.coverAvailable + r.toRat < 10 ^ 96) :
    ∃ res, lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = r :=
  LoanBroker.coverDeposit_total_proof lb amount r hrounded hc hnn hcap

/-- A deposit onto an empty cover is taken whole, never rounded, and becomes the
new `coverAvailable`. An empty cover has no scale to round to. -/
theorem LoanBroker.coverDeposit_empty (amount : STAmount) (res : LoanBrokerCoverResult)
    (hzero : lb.coverAvailable = Number.zero)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hat : amount.mNumericType = lb.numericType) :
    res.amount' = amount ∧ res.loanBroker'.toExact.coverAvailable = amount.toRat :=
  LoanBroker.coverDeposit_empty_proof lb amount res hzero hok hc hat

/-- A deposit never breaks the minimum cover: if `coverAvailable` was at least the
minimum cover, it still is, because the debt is unchanged and `coverAvailable` only rises. -/
theorem LoanBroker.coverDeposit_keeps_minimum (amount : STAmount) (res : LoanBrokerCoverResult)
    (e : Int)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat)
    (hmin : lb.HasMinimumCover e) :
    res.loanBroker'.HasMinimumCover e :=
  LoanBroker.coverDeposit_keeps_minimum_proof lb amount res e hok hc hnn hmin

end XRPL.Model.Lending
