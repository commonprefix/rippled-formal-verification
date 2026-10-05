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

/-- A successful withdrawal pays out exactly the requested amount. -/
theorem LoanBroker.coverWithdraw_amount (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res)) :
    res.amount' = amount :=
  LoanBroker.coverWithdraw_amount_proof lb amount res hok

/-- When the new `coverAvailable` fits a `Number`, the withdrawal subtracts
exactly the requested amount. -/
theorem LoanBroker.coverWithdraw_debit (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat :=
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

/-- Witness: the fit hypothesis of `coverWithdraw_debit` cannot be dropped, a run
whose checks passed withdraws `1234.567890123456` from `10^18` and lowers
`coverAvailable` by `1235`. -/
theorem LoanBroker.coverWithdraw_debit_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ amount.IOUCanonical ∧
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≠ amount.toRat :=
  LoanBroker.coverWithdraw_debit_witness

/-- A withdrawal only lowers `coverAvailable`. -/
theorem LoanBroker.coverWithdraw_decreases_cover (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_decreases_cover_proof lb amount res hok hc hnn

/-- A withdrawal whose checks passed leaves at least the minimum cover. -/
theorem LoanBroker.coverWithdraw_keeps_minimum (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    res.loanBroker'.HasMinimumCover e :=
  LoanBroker.coverWithdraw_keeps_minimum_proof lb pool amount res e hcan hok hexp

/-- A withdrawal whose checks passed never throws: it returns a lawful broker
and the requested amount, never `.notLawful`. -/
theorem LoanBroker.coverWithdraw_total (pool : α) (amount : STAmount)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hc : amount.ExactCanonical) :
    ∃ res, lb.coverWithdraw amount = .ok (.ok res) ∧ res.amount' = amount :=
  LoanBroker.coverWithdraw_total_proof lb pool amount hcan hc

/-- With no debt, withdrawing the whole cover passes the checks and leaves zero
cover, when the asset holds `coverAvailable` exactly. -/
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
