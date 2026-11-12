import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.LoanBroker.Defs
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Lending.Loan.Common.Grid

/-! # Loan broker reachability

A reachable broker is built by `create` and successful broker transactions, so `debtTotal` and `loanCount` never
change. Each step runs on any vault with the broker's asset and base exponent, which C++ never changes. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Brokers reachable from `start` by successful broker transactions on a vault with base exponent
`base`. -/
inductive LoanBroker.ReachableFrom (base : Int) (start : LoanBroker) : LoanBroker → Prop where
  | refl : LoanBroker.ReachableFrom base start start
  | update (lb lb' : LoanBroker) (v : Vault) (debtMaximum : Option Number) :
      LoanBroker.ReachableFrom base start lb →
      v.baseExponent = base → v.numericType = lb.numericType →
      lb.canUpdate v debtMaximum = .ok .tesSUCCESS →
      lb.update debtMaximum = .ok lb' →
      LoanBroker.ReachableFrom base start lb'
  | coverDeposit (lb : LoanBroker) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom base start lb →
      v.baseExponent = base → v.numericType = lb.numericType →
      amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      -- an XRP or MPT holding never exceeds the asset's maximum amount
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS →
      (lb.coverDeposit v amount).run = .ok (.ok res) →
      LoanBroker.ReachableFrom base start res.loanBroker'
  | coverWithdraw (lb : LoanBroker) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom base start lb →
      v.baseExponent = base → v.numericType = lb.numericType →
      amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS →
      (lb.coverWithdraw v amount).run = .ok (.ok res) →
      LoanBroker.ReachableFrom base start res.loanBroker'
  | coverClawback (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
      (res : LoanBrokerCoverResult) :
      LoanBroker.ReachableFrom base start lb →
      v.baseExponent = base → v.numericType = lb.numericType →
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) →
      lb.canCoverClawback v amount = .ok .tesSUCCESS →
      (lb.coverClawback v amount).run = .ok (.ok res) →
      LoanBroker.ReachableFrom base start res.loanBroker'

/-- The state a broker-only history keeps: CoverAvailable is a whole number of base units within the
Open limit and stored exactly, and DebtMaximum is on the base grid. -/
structure LoanBroker.OpenZone (lb : LoanBroker) (base : Int) : Prop where
  cover : Number.OnGrid base lb.coverAvailable
  coverLimit : lb.toExact.coverAvailable ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ base
  coverExact : STAmount.isRounded lb.numericType lb.coverAvailable = false
  debtMaximum : lb.debtMaximum.isOnExponentGrid base lb.numericType = .ok true

/-- CoverAvailable is a whole number of base units below `10^16` base units, as in the Open zone and on a cover
that is not coarsened. -/
structure LoanBroker.CoverFits (lb : LoanBroker) (base : Int) : Prop where
  cover : Number.OnGrid base lb.coverAvailable
  coverLt : lb.toExact.coverAvailable < 10 ^ 16 * (10 : ℚ) ^ base

/-- Brokers reachable from a successful `LoanBroker.create` in the asset of a vault with base
exponent `base`, after `canCreate` passed on that vault. -/
def LoanBroker.Reachable (lb : LoanBroker) (base : Int) : Prop :=
  ∃ (v : Vault) (tx : LoanBrokerSetCreate) (start : LoanBroker),
    v.baseExponent = base ∧
    LoanBroker.canCreate v tx.debtMaximum v.numericType = .ok .tesSUCCESS ∧
    LoanBroker.create tx v.numericType = .ok start ∧ LoanBroker.ReachableFrom base start lb

end XRPL.Model.Lending
