import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness

/-! # `LoanBroker.coverWithdraw`

A withdrawal subtracts the amount as is, with 19-digit `Number` rounding. Once its checks
pass it always succeeds and keeps the minimum cover. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- A withdraw pays out exactly the requested amount. -/
theorem LoanBroker.coverWithdraw_amount (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res)) :
    res.amount' = amount :=
  LoanBroker.coverWithdraw_amount_proof lb amount res hok

/-- When the new CoverAvailable fits a Number -> amount' = CoverAvailable − CoverAvailable', where
`amount'` is the paid-out amount. -/
theorem LoanBroker.coverWithdraw_debit (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat :=
  LoanBroker.coverWithdraw_debit_proof lb amount res hok hc hexact

/-- Integral strengthening of `coverWithdraw_debit`: a whole `coverAvailable`
below `2^63` minus a nonnegative whole withdrawal is debited exactly. -/
theorem LoanBroker.coverWithdraw_debit_integral (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat :=
  LoanBroker.coverWithdraw_debit_integral_proof lb amount res hok hint hsz hnn hcint hbound

/-- When the new CoverAvailable fits a Number -> amount ≥ CoverAvailable − CoverAvailable'. -/
theorem LoanBroker.coverWithdraw_debit_le_amount (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ amount.toRat :=
  LoanBroker.coverWithdraw_debit_le_amount_proof lb amount res hok hc hexact

/-- Witness: a run where CoverAvailable drops by more than the amount. Withdrawing
`1234.567890123456` from `10^18` lowers `coverAvailable` by `1235`. -/
theorem LoanBroker.coverWithdraw_debit_le_amount_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧ res.amount' = amount ∧
      amount.toRat < lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_debit_le_amount_witness

/-- Witness: the withdrawal amount is never rounded to the CoverAvailable scale, so
STAmount(CoverAvailable − CoverAvailable') ≠ amount even when CoverAvailable fits an STAmount
exactly. Withdrawing `1234.567890123456` from `10^18` moves `coverAvailable` by `1235`, while a
deposit would round the amount down to `1000`.
`amount''` - the withdrawn amount rounded down to the cover scale, as a deposit rounds it -/
theorem LoanBroker.coverWithdraw_applied_delta_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount amount'' : STAmount) (res : LoanBrokerCoverResult)
      (deltaCover : Number) (deltaAmount : STAmount),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧
      lb.roundedCoverAmount res.amount' = .ok (.rounded amount'') ∧
      amount''.operator_eq res.amount' = false ∧
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq res.amount' = false :=
  LoanBroker.coverWithdraw_applied_delta_witness

/-- Cover withdraw only lowers CoverAvailable (monotone down). -/
theorem LoanBroker.coverWithdraw_decreases_cover (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_decreases_cover_proof lb amount res hok hc hnn

/-- When the checks pass -> CoverAvailable' ≥ minCover. -/
theorem LoanBroker.coverWithdraw_keeps_minimum (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    res.loanBroker'.HasMinimumCover e :=
  LoanBroker.coverWithdraw_keeps_minimum_proof lb pool amount res e hcan hok hexp

/-- When the checks pass -> the withdrawal succeeds with the amount and never throws, not even
notLawful. -/
theorem LoanBroker.coverWithdraw_total (pool : α) (amount : STAmount)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hc : amount.ExactCanonical) :
    ∃ res, lb.coverWithdraw amount = .ok (.ok res) ∧ res.amount' = amount :=
  LoanBroker.coverWithdraw_total_proof lb pool amount hcan hc

/-- With no debt, the whole cover (≠ 0) can be withdrawn, when CoverAvailable fits an STAmount
exactly. -/
theorem LoanBroker.coverWithdraw_all (pool : α) (e : Int) (s : STAmount)
    (hdebt : lb.debtTotal = Number.zero)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0)
    (hrep : s.toRat = lb.toExact.coverAvailable)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    lb.canCoverWithdraw pool s = .ok .tesSUCCESS ∧
      ∃ res, lb.coverWithdraw s = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0 :=
  LoanBroker.coverWithdraw_all_proof lb pool e s hdebt hs hnz hrep hexp

end XRPL.Model.Lending
