import XRPL.Properties.Lending.Ledger.Defs
import XRPL.Properties.Lending.Loan.Common.CreditTotal

/-! # Which loan and broker a transaction acts on

The isolation theorems compare a transaction on one loan or broker with a transaction on another loan. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The stored loan a transaction names: LoanAccept, LoanDelete, LoanManage or LoanPay. -/
def LendingTx.loanIndex? : LendingTx → Option Nat
  | .loanAccept i | .loanDelete i | .loanManage i _ | .loanPay i _ _ => some i
  | _ => none

/-- The broker a loan transaction acts on: the broker a LoanSet names, or the broker of the stored loan a
LoanAccept, LoanDelete, LoanManage or LoanPay names. -/
def LendingLedger.loanTxBroker? (l : LendingLedger) : LendingTx → Option Nat
  | .loanSet k .. => some k
  | tx => tx.loanIndex?.bind fun i => (l.loan? i).map (·.brokerIndex)

/-- The broker a broker or loan transaction acts on. LoanBrokerCreate acts on the new broker at the end of the
list. -/
def LendingLedger.txBroker? (l : LendingLedger) : LendingTx → Option Nat
  | .loanBrokerCreate _ => some l.brokers.length
  | .loanBrokerUpdate k _ | .loanBrokerCoverDeposit k _ | .loanBrokerCoverWithdraw k _
  | .loanBrokerCoverClawback k _ | .loanBrokerDelete k => some k
  | tx => l.loanTxBroker? tx

/-- On an XRP or MPT vault, AssetsAvailable plus the principal and interest a payment of loan `j` pays stays a unit
below the asset's maximum. -/
def LendingLedger.CreditFits (l : LendingLedger) (j : Nat) (pt : LoanPaymentType) (amount : Number) : Prop :=
  ∀ loan p, l.LoanAt j loan → (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
    l.vault.numericType.isIntegral = true → l.vault.assetsAvailable.toRat + p.amounts.principalPaid.toRat +
      p.amounts.interestPaid.toRat + 1 ≤ l.vault.numericType.maxValue.toNat

/-- The fee a payment of loan `j` pays fits: with the broker's cover below `10^89` for an IOU, and alone a unit
below the maximum of XRP or an MPT. -/
def LendingLedger.FeeFits (l : LendingLedger) (j : Nat) (pt : LoanPaymentType) (amount : Number) : Prop :=
  ∀ loan p, l.LoanAt j loan → (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
    l.vault.numericType.CreditFits loan.broker.coverAvailable.toRat p.amounts.feePaid.toRat

end XRPL.Model.Lending
