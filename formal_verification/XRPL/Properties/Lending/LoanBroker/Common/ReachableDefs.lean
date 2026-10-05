import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Properties.Lending.LoanBroker.Defs
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber

/-! # Loan broker reachability

`LoanBroker.ReachableFrom start lb` holds when `lb` is `start` after a sequence
of successful `update`, `coverDeposit`, `coverWithdraw` and `coverClawback`
calls. `LoanBroker.Reachable lb` adds that `start` came from
`LoanBroker.create`. Loans are not part of this model, so no operation here
changes `debtTotal` or `loanCount`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Brokers reachable from `start` by successful LoanBroker operations. -/
inductive LoanBroker.ReachableFrom (start : LoanBroker) : LoanBroker → Prop where
  | refl : LoanBroker.ReachableFrom start start
  | update (lb lb' : LoanBroker) (debtMaximum : Option Number) :
      LoanBroker.ReachableFrom start lb → lb.update debtMaximum = .ok lb' →
      LoanBroker.ReachableFrom start lb'
  | coverDeposit (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom start lb → lb.coverDeposit amount = .ok (.ok res) →
      LoanBroker.ReachableFrom start res.loanBroker'
  | coverWithdraw (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom start lb → lb.coverWithdraw amount = .ok (.ok res) →
      LoanBroker.ReachableFrom start res.loanBroker'
  | coverClawback (lb : LoanBroker) (α : Type) [AssetPool α] (pool : α)
      (amount : Option STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom start lb → lb.coverClawback pool amount = .ok (.ok res) →
      LoanBroker.ReachableFrom start res.loanBroker'

/-- Brokers reachable from a successful `LoanBroker.create`. -/
def LoanBroker.Reachable (lb : LoanBroker) : Prop :=
  ∃ (tx : LoanBrokerSetCreate) (nt : NumericType) (start : LoanBroker),
    LoanBroker.create tx nt = .ok start ∧ LoanBroker.ReachableFrom start lb

/-- Brokers reachable from `start` by successful operations whose cover amounts
are nonnegative canonical XRP or MPT amounts, with every new `coverAvailable`
below `2^63`. -/
inductive LoanBroker.WholeCoverFrom (start : LoanBroker) : LoanBroker → Prop where
  | refl : LoanBroker.WholeCoverFrom start start
  | update (lb lb' : LoanBroker) (debtMaximum : Option Number) :
      LoanBroker.WholeCoverFrom start lb → lb.update debtMaximum = .ok lb' →
      LoanBroker.WholeCoverFrom start lb'
  | coverDeposit (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.WholeCoverFrom start lb → lb.coverDeposit amount = .ok (.ok res) →
      amount.IntegralCanonical → amount.mValue.toNat ≤ 2 ^ 63 - 1 → 0 ≤ amount.toRat →
      lb.toExact.coverAvailable + amount.toRat < 2 ^ 63 → -- the new cover stays below `2^63`
      LoanBroker.WholeCoverFrom start res.loanBroker'
  | coverWithdraw (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.WholeCoverFrom start lb → lb.coverWithdraw amount = .ok (.ok res) →
      amount.IntegralCanonical → amount.mValue.toNat ≤ 2 ^ 63 - 1 → 0 ≤ amount.toRat →
      LoanBroker.WholeCoverFrom start res.loanBroker'
  | coverClawback (lb : LoanBroker) (α : Type) [AssetPool α] (pool : α)
      (amount : Option STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.WholeCoverFrom start lb → lb.coverClawback pool amount = .ok (.ok res) →
      res.amount'.IntegralCanonical → res.amount'.mValue.toNat ≤ 2 ^ 63 - 1 →
      0 ≤ res.amount'.toRat →
      LoanBroker.WholeCoverFrom start res.loanBroker'

/-- Brokers reachable from `start` in `n` cover operations. `applied` is the net
amount moved and `requested` the net amount asked for. Every new
`coverAvailable` fits a `Number`, and every step rounds by at most `unit`. -/
inductive LoanBroker.ReachableFromIn (start : LoanBroker) (unit : ℚ) :
    LoanBroker → ℕ → ℚ → ℚ → Prop where
  | refl : LoanBroker.ReachableFromIn start unit start 0 0 0
  | update (lb lb' : LoanBroker) (n : ℕ) (applied requested : ℚ) (debtMaximum : Option Number) :
      LoanBroker.ReachableFromIn start unit lb n applied requested →
      lb.update debtMaximum = .ok lb' →
      LoanBroker.ReachableFromIn start unit lb' n applied requested
  | coverDeposit (lb : LoanBroker) (n : ℕ) (applied requested : ℚ) (amount : STAmount)
      (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFromIn start unit lb n applied requested →
      lb.coverDeposit amount = .ok (.ok res) →
      amount.ExactCanonical → -- the amount is stored canonically
      -- the true sum is a normalized `Number`
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) →
      -- one step of the cover scale is at most `unit`
      (∀ e, numberExponent lb.coverAvailable lb.numericType = .ok e → (10 : ℚ) ^ e ≤ unit) →
      LoanBroker.ReachableFromIn start unit res.loanBroker' (n + 1)
        (applied + res.amount'.toRat) (requested + amount.toRat)
  | coverWithdraw (lb : LoanBroker) (n : ℕ) (applied requested : ℚ) (amount : STAmount)
      (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFromIn start unit lb n applied requested →
      lb.coverWithdraw amount = .ok (.ok res) →
      amount.ExactCanonical → -- the amount is stored canonically
      -- the true difference is a normalized `Number`
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - amount.toRat) →
      LoanBroker.ReachableFromIn start unit res.loanBroker' (n + 1)
        (applied - amount.toRat) (requested - amount.toRat)
  | coverClawback (lb : LoanBroker) (n : ℕ) (applied requested : ℚ) (α : Type) [AssetPool α]
      (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult) (e : Int)
      (minimumCover : Number) :
      LoanBroker.ReachableFromIn start unit lb n applied requested →
      lb.coverClawback pool (some amount) = .ok (.ok res) →
      amount.ExactCanonical → 0 ≤ amount.toRat → -- a canonical nonnegative request
      amount.isZero = false → -- a zero request claws all cover above the minimum
      AssetPool.exponent pool lb.numericType = .ok e → -- the vault scale
      -- the minimum cover the debt requires
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover →
      -- the request fits under the cover above the minimum, so the clawback does not cap it
      amount.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat →
      lb.canCoverClawback pool (some amount) = .ok .tesSUCCESS → -- the checks passed
      -- the true difference is a normalized `Number`
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) →
      -- half a unit of the clawed amount's exponent is at most `unit`
      (1 / 2 : ℚ) * (10 : ℚ) ^ res.amount'.exponent ≤ unit →
      LoanBroker.ReachableFromIn start unit res.loanBroker' (n + 1)
        (applied - res.amount'.toRat) (requested - amount.toRat)

end XRPL.Model.Lending
