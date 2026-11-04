import XRPL.Properties.Lending.Loan.Common.AcceptDeleteLedger
import XRPL.Properties.Lending.Loan.Common.AcceptDeleteWitness

/-! # `LoanDelete` properties

What deleting a loan moves between the vault and the broker. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

/-- Deleting a closed loan -> vault unchanged, and for the broker's last loan DebtTotal is already 0. -/
theorem Lending.deleteActive_settled (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan) (e : LoanEntry)
    (he : l.loan? i = some e) (broker' : LoanBroker) (hb' : l'.broker? e.brokerIndex = some broker')
    (hp : loan.isPending = false) :
    l'.vault = l.vault ∧
    (loan.broker.loanCount = 1 → loan.broker.debtTotal = Number.zero ∧ broker'.debtTotal = loan.broker.debtTotal) :=
  ⟨LendingLedger.deleteActive_keeps_vault_proof h hat hp, LendingLedger.deleteActive_last_proof hr h hat he hb' hp⟩

/-- Create pending then delete -> AssetsAvailable, AssetsReserved, DebtTotal and LoanCount are restored. -/
theorem Lending.createPending_deletePending_restores (l : LendingLedger) (hr : l.Reachable) (l₁ l₂ : LendingLedger)
    (j : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
    (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32) (allowsOverpayment : Bool)
    (hset : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate true
      allowsOverpayment)).run = .ok (.ok l₁))
    (hdelete : (l₁.apply (.loanDelete l.loans.length)).run = .ok (.ok l₂)) (broker broker' : LoanBroker)
    (hb : l.broker? j = some broker) (hb' : l₂.broker? j = some broker') :
    l₂.vault.assetsAvailable = l.vault.assetsAvailable ∧ l₂.vault.assetsReserved = l.vault.assetsReserved ∧
      broker'.debtTotal = broker.debtTotal ∧ broker'.loanCount = broker.loanCount :=
  LendingLedger.createPending_deletePending_restores_proof hr hset hdelete hb hb'

/-- Pending delete -> AssetsAvailable' − AssetsAvailable = AssetsReserved − AssetsReserved' = AssetsDeployed −
AssetsDeployed' = DebtTotal − DebtTotal' = PrincipalOutstanding. `haa` - AssetsAvailable + PrincipalOutstanding fits -/
theorem Lending.deletePending_principal (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan) (e : LoanEntry)
    (he : l.loan? i = some e) (broker' : LoanBroker) (hb' : l'.broker? e.brokerIndex = some broker')
    (hp : loan.isPending = true)
    (haa : STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + loan.principalOutstanding.toRat)) :
    l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat = loan.principalOutstanding.toRat ∧
      l.vault.assetsReserved.toRat - l'.vault.assetsReserved.toRat = loan.principalOutstanding.toRat ∧
      l.vault.assetsDeployed.toRat - l'.vault.assetsDeployed.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.toRat - broker'.debtTotal.toRat = loan.principalOutstanding.toRat :=
  LendingLedger.deletePending_principal_proof hr h hat he hb' hp haa

/-- Witness: a run where AssetsAvailable' − AssetsAvailable ≠ PrincipalOutstanding. Late interest takes a scale 1
vault to AssetsAvailable 1874246907153724 on the grid of 1, and deleting a pending loan of 0.6 credits 1. -/
theorem Lending.deletePending_principal_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan),
      l.Reachable ∧ (l.apply (.loanDelete i)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧ loan.isPending = true ∧
      l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat ≠ loan.principalOutstanding.toRat :=
  LendingLedger.deletePending_principal_witness

end XRPL.Model
