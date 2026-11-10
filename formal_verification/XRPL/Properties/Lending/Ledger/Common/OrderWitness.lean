import XRPL.Properties.Lending.Ledger.Defs

/-! # Witnesses for the order of loan transactions

Concrete ledgers with one closed-ended IOU vault in its investment phase, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A closed-ended IOU vault holding 1000 shares, in its investment phase from close time 101 on. -/
def owVault (scale : UInt8) (assetsAvailable assetsDeployed assetsReserved : Number) : RawVault :=
  { assetsAvailable := assetsAvailable, assetsDeployed := assetsDeployed, assetsReserved := assetsReserved
  , assetsMaximum := none, numericType := .fractional, scale := scale
  , sharesTotal := ⟨false, 1000000000000000000, -15⟩, lossUnrealized := Number.zero
  , yieldUnrealized := Number.zero, schedule := some ⟨100, 10000000⟩, earlyExitFeeRate := none
  , ownerCanBlockDeposit := false, depositBlocked := false }

/-- An IOU broker with the given cover rates, debt, cover and loan count. -/
def owBroker (coverRateMinimum coverRateLiquidation : UInt32) (debtTotal coverAvailable : Number)
    (loanCount : UInt32) : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := coverRateMinimum
  , coverRateLiquidation := coverRateLiquidation, debtTotal := debtTotal, debtMaximum := Number.zero
  , coverAvailable := coverAvailable, loanCount := loanCount }

/-- A loan of one payment of TotalValueOutstanding: active and due at 60 seconds, or pending and starting at
5000. -/
private def owLoan (broker : LoanBroker) (principal total : Number) (loanScale : Int) (pending : Bool) : RawLoan :=
  { broker := broker
    rates := { interestRate := 0, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
               overpaymentFee := 0 }
    fees := { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
              closePaymentFee := Number.zero }
    schedule := { paymentInterval := 60, paymentTotal := 1, gracePeriod := 60
                  startDate := if pending then 5000 else 0 }
    paymentRemaining := 1, periodicPayment := total, principalOutstanding := principal
    totalValueOutstanding := total, managementFeeOutstanding := Number.zero, loanScale := loanScale
    previousPaymentDueDate := 0, nextPaymentDueDate := if pending then 5060 else 60
    isPending := pending, isImpaired := false, isDefault := false, allowsOverpayment := false }

/-! ### Two defaults on one broker, at scale `10^0` -/

private def owDefaultVault : Vault :=
  ⟨owVault 0 ⟨false, 1000000000000000000, -14⟩ ⟨false, 9500000000000000000, -16⟩ Number.zero,
    by native_decide, by native_decide⟩

/-- DebtTotal 950, the sum of its two loans, cover 2000, CoverRateMinimum 100% and CoverRateLiquidation 90%. -/
private def owDefaultBroker : LoanBroker :=
  ⟨owBroker 100000 90000 ⟨false, 9500000000000000000, -16⟩ ⟨false, 2000000000000000000, -15⟩ 2,
    by native_decide, by native_decide⟩

/-- A loan of 800. -/
private def owDefaultLoanA : Loan :=
  ⟨owLoan owDefaultBroker ⟨false, 8000000000000000000, -16⟩ ⟨false, 8000000000000000000, -16⟩ 0 false,
    by native_decide, by native_decide⟩

/-- A loan of 150. -/
private def owDefaultLoanB : Loan :=
  ⟨owLoan owDefaultBroker ⟨false, 1500000000000000000, -16⟩ ⟨false, 1500000000000000000, -16⟩ 0 false,
    by native_decide, by native_decide⟩

/-- Both loans on broker 0, past their grace period at close time 1000. -/
private def owDefaultLedger : LendingLedger :=
  { vault := owDefaultVault, shares := [⟨false, 1000000000000000000, -15⟩], brokers := [some owDefaultBroker]
    loans := [some ⟨0, owDefaultLoanA⟩, some ⟨0, owDefaultLoanB⟩], now := 1000 }

/-- An IOU vault at scale `10^-10` with AssetsTotal 800000, 100000 of it reserved for two pending loans. Its Open
limit is 900000. -/
private def owPendingVault : Vault :=
  ⟨owVault 10 ⟨false, 7000000000000000000, -13⟩ ⟨false, 1000000000000000000, -13⟩
    ⟨false, 1000000000000000000, -13⟩, by native_decide, by native_decide⟩

/-- A broker without cover requirements holding both pending loans. -/
private def owSharedBroker : LoanBroker :=
  ⟨owBroker 0 0 ⟨false, 1000000000000000000, -13⟩ Number.zero 2, by native_decide, by native_decide⟩

/-- A broker without cover requirements holding one pending loan. -/
private def owSingleBroker : LoanBroker :=
  ⟨owBroker 0 0 ⟨false, 5000000000000000000, -14⟩ Number.zero 1, by native_decide, by native_decide⟩

/-- A pending loan of 50000 that owes 60000 of interest, on the shared broker. -/
private def owSharedLoan : Loan :=
  ⟨owLoan owSharedBroker ⟨false, 5000000000000000000, -14⟩ ⟨false, 1100000000000000000, -13⟩ (-10) true,
    by native_decide, by native_decide⟩

/-- A pending loan of 50000 that owes 60000 of interest, alone on its broker. -/
private def owSingleLoan : Loan :=
  ⟨owLoan owSingleBroker ⟨false, 5000000000000000000, -14⟩ ⟨false, 1100000000000000000, -13⟩ (-10) true,
    by native_decide, by native_decide⟩

/-- Both pending loans on broker 0. -/
private def owSharedLedger : LendingLedger :=
  { vault := owPendingVault, shares := [⟨false, 1000000000000000000, -15⟩], brokers := [some owSharedBroker]
    loans := [some ⟨0, owSharedLoan⟩, some ⟨0, owSharedLoan⟩], now := 1000 }

/-- One pending loan on each of brokers 0 and 1. -/
private def owSplitLedger : LendingLedger :=
  { vault := owPendingVault, shares := [⟨false, 1000000000000000000, -15⟩]
    brokers := [some owSingleBroker, some owSingleBroker]
    loans := [some ⟨0, owSingleLoan⟩, some ⟨1, owSingleLoan⟩], now := 1000 }

/-- The two defaults in both orders: the first order covers 935, the second only 870. -/
private def defaultsCheck : Bool :=
  match (owDefaultLedger.apply (.loanManage 0 .default)).run, (owDefaultLedger.apply (.loanManage 1 .default)).run with
  | .ok (.ok la), .ok (.ok lb) =>
    match (la.apply (.loanManage 1 .default)).run, (lb.apply (.loanManage 0 .default)).run with
    | .ok (.ok lab), .ok (.ok lba) => decide (lab.vault.toExact.assetsTotal ≠ lba.vault.toExact.assetsTotal)
    | _, _ => false
  | _, _ => false

private lemma defaultsCheck_true : defaultsCheck = true := by native_decide

/-- Two defaults of loans 800 and 150 on one broker with DebtTotal 950, 2000 of cover and a 90% liquidation
rate. Defaulting the larger loan first covers 800 + 135 = 935, the other order 150 + 720 = 870. -/
lemma LendingLedger.defaults_comm_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat),
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      lab.vault.toExact.assetsTotal ≠ lba.vault.toExact.assetsTotal := by
  have h := defaultsCheck_true
  unfold defaultsCheck at h
  split at h
  · rename_i la lb ha hb
    split at h
    · rename_i lab lba hab hba
      exact ⟨_, la, lb, lab, lba, 0, 1, ha, hab, hb, hba, of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Accepting the second pending loan alone succeeds, after the first one it exceeds the Open limit. -/
private def acceptsCheck (l : LendingLedger) : Bool :=
  match (l.apply (.loanAccept 1)).run, (l.apply (.loanAccept 0)).run with
  | .ok (.ok _), .ok (.ok la) =>
    match (la.apply (.loanAccept 1)).run with
    | .ok (.error .tecLIMIT_EXCEEDED) => true
    | _ => false
  | _, _ => false

private lemma acceptsCheck_shared : acceptsCheck owSharedLedger = true := by native_decide

private lemma acceptsCheck_split : acceptsCheck owSplitLedger = true := by native_decide

/-- The accepts on a ledger that passes `acceptsCheck`. -/
private lemma accepts_of_check (l : LendingLedger) (h : acceptsCheck l = true) :
    ∃ lb la : LendingLedger, (l.apply (.loanAccept 1)).run = .ok (.ok lb) ∧
      (l.apply (.loanAccept 0)).run = .ok (.ok la) ∧
      (la.apply (.loanAccept 1)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  unfold acceptsCheck at h
  split at h
  · rename_i lb la hb ha
    split at h
    · exact ⟨lb, la, hb, ha, ‹_›⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Two pending loans on one broker that each fit the Open zone: accepting the first books its interest, and
the second can no longer be accepted. -/
lemma LendingLedger.payment_isolation_witness :
    ∃ (l lb la : LendingLedger) (i j : Nat) (e e' : LoanEntry), i ≠ j ∧
      l.loan? i = some e ∧ l.loan? j = some e' ∧ e.brokerIndex = e'.brokerIndex ∧
      (l.apply (.loanAccept j)).run = .ok (.ok lb) ∧ (l.apply (.loanAccept i)).run = .ok (.ok la) ∧
      (la.apply (.loanAccept j)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨lb, la, hb, ha, hab⟩ := accepts_of_check owSharedLedger acceptsCheck_shared
  exact ⟨_, lb, la, 0, 1, _, _, by decide, rfl, rfl, rfl, hb, ha, hab⟩

/-- Two pending loans on two brokers that each fit the Open zone: accepting the first books its interest, and
the second can no longer be accepted. -/
lemma LendingLedger.broker_isolation_witness :
    ∃ (l lb la : LendingLedger) (i j : Nat) (e e' : LoanEntry), i ≠ j ∧
      l.loan? i = some e ∧ l.loan? j = some e' ∧ e.brokerIndex ≠ e'.brokerIndex ∧
      (l.apply (.loanAccept j)).run = .ok (.ok lb) ∧ (l.apply (.loanAccept i)).run = .ok (.ok la) ∧
      (la.apply (.loanAccept j)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨lb, la, hb, ha, hab⟩ := accepts_of_check owSplitLedger acceptsCheck_split
  exact ⟨_, lb, la, 0, 1, _, _, by decide, rfl, rfl, by decide, hb, ha, hab⟩

end XRPL.Model.Lending
