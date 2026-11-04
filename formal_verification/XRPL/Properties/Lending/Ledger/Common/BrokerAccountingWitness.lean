import XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
import XRPL.Properties.Lending.Loan.Common.ManageLedgerWitness

/-! # A sequence where the CoverAvailable line fails

The default of the cover precision run takes `1.0000000001` off a cover of `1000000000001` at the scale `10^-10`.
The cover holds 23 digits of base units and the `Number` difference keeps 19, so CoverAvailable' is `10^12`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private LendingLedger.LoanAt.read from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting

/-- A sequence of one successful transaction sums its own amount. -/
private lemma LendingLedger.runSum_single {l l' : LendingLedger} {tx : LendingTx}
    (hok : (l.apply tx).run = .ok (.ok l')) (f : LendingLedger → LendingTx → ℚ) : l.runSum f [tx] = f l tx := by
  have h := LendingLedger.runSum_snoc (f := f) (txs := []) LendingLedger.Reaches.refl hok
  simp only [List.nil_append, LendingLedger.runSum, zero_add] at h
  exact h

/-- A reachable sequence where CoverAvailable' ≠ CoverAvailable + Σ coverDeposits − Σ coverWithdrawals −
Σ coverClawbacks + Σ feesToCover − Σ defaultCovered: one default on a coarsened cover. -/
lemma LendingLedger.accounting_coverAvailable_witness :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧ ∃ (j : Nat) (b b' : LoanBroker), start.broker? j = some b ∧
        l.broker? j = some b' ∧
        b'.coverAvailable.toRat ≠ b.coverAvailable.toRat + start.coverDeposits j txs -
          start.coverWithdrawals j txs - start.coverClawbacks j txs + start.feesToCover j txs -
          start.brokerDefaultCovered j txs := by
  obtain ⟨l, l', i, loan, loan', r, hr, hok, hat, hat', hdef, hne⟩ := LendingLedger.manageDefault_coverAvailable_witness
  obtain ⟨e, loan₂, r₂, he, hat₂, -, hdef₂, -, -, hat₂', -, hbr⟩ := LendingLedger.loanDefault_ok hok
  obtain rfl := hat.eq hat₂
  obtain rfl : r₂ = r := Except.ok.inj (Except.ok.inj (hdef₂.symm.trans hdef))
  obtain rfl := hat'.eq hat₂'
  obtain ⟨e₀, he₀, hbk, -⟩ := hat.stored
  obtain rfl := Option.some.inj (he₀.symm.trans he)
  refine ⟨l, [.loanManage i .default], l', hr, .step _ .refl hok, e₀.brokerIndex, loan.broker, r₂.loan'.broker, hbk,
    by rw [hbr, if_pos rfl], ?_⟩
  have hdc : l.brokerDefaultCoveredOf e₀.brokerIndex (.loanManage i .default) = r₂.amountToPool.toRat := by
    simp [LendingLedger.brokerDefaultCoveredOf, LendingLedger.onBroker, LendingLedger.defaultCoveredOf, he₀,
      LendingLedger.LoanAt.read hat, hdef]
  unfold LendingLedger.coverDeposits LendingLedger.coverWithdrawals LendingLedger.coverClawbacks
    LendingLedger.feesToCover LendingLedger.brokerDefaultCovered
  simp only [LendingLedger.runSum_single hok, hdc]
  simp only [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf,
    LendingLedger.feesToCoverOf, ite_self, add_zero, sub_zero]
  exact hne

end XRPL.Model.Lending
