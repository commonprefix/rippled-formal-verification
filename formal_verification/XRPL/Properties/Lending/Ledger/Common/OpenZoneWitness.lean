import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.ReachableFromIn

/-! # A run that leaves the Open zone by rounding

A deposit fills the Open zone, late interest coarsens the vault, and deleting a pending loan of 0.6 credits 1. The
sum ends 0.4 above the Open limit plus the interest collected beyond the schedule. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Apply the transactions in order and add up what the payments collect beyond the schedule, or `none` when one
of them does not succeed. -/
private def LendingLedger.runIn (l : LendingLedger) : List LendingTx → Option (LendingLedger × ℚ)
  | [] => some (l, 0)
  | tx :: txs =>
    match (l.apply tx).run with
    | .ok (.ok l') => (l'.runIn txs).map fun p => (p.1, l.extraInterest tx l' + p.2)
    | _ => none

/-- A run that succeeds at every step is a `ReachableFromIn` run. -/
private lemma LendingLedger.runIn_reachableFromIn {l l' : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : l.runIn txs = some (l', x)) : l.ReachableFromIn txs l' x := by
  induction txs generalizing l l' x with
  | nil =>
    simp only [LendingLedger.runIn, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl
  | cons tx txs ih =>
    unfold LendingLedger.runIn at h
    split at h
    · rename_i l₁ hl₁
      obtain ⟨⟨l₂, x₂⟩, h₂, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact LendingLedger.ReachableFromIn.cons hl₁ (ih h₂)
    · cases h

/-- The coarsened run with a deposit of exactly the Open limit and a pending loan E of 0.6, created before the vault
coarsens, then loan A paid 800 days late and loan E deleted. -/
private def ozTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 9000000000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanBrokerCreate ⟨none, none, some 9999, some 100000⟩,
   .loanBrokerCoverDeposit 1 (cwAmount 1000000000000000 (-16)),
   .loanSet 0 ⟨false, 7000000000000000000, -4⟩ (cwRates 100000) cwFees (some 86400) (some 5) (some 60) 0 false false,
   .loanSet 1 ⟨false, 1000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 2000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 20) (some 60) 0 false false,
   .loanSet 0 ⟨false, 6000000000000000000, -19⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 70000000 true
     false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩,
   .loanDelete 3]

/-- Every step succeeds and the run ends above the Open limit plus what it collected. -/
private def ozCheck : Bool :=
  match cwGenesis.runIn ozTxs with
  | some (l, x) => decide (l.openLimit + x < l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat)
  | none => false

private lemma ozCheck_true : ozCheck = true := by native_decide

/-- A run from a new vault can leave the Open zone by rounding. The pending delete on the coarsened vault
credits 0.6 as 1. -/
lemma LendingLedger.within_open_zone_witness :
    ∃ (genesis l : LendingLedger) (txs : List LendingTx) (x : ℚ), genesis.Genesis ∧
      genesis.ReachableFromIn txs l x ∧
      ¬ l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat ≤ l.openLimit + x := by
  have h := ozCheck_true
  unfold ozCheck at h
  split at h
  · rename_i l x hrun
    exact ⟨cwGenesis, l, ozTxs, x, cwGenesis_genesis, LendingLedger.runIn_reachableFromIn hrun,
      not_le.mpr (of_decide_eq_true h)⟩
  · cases h

end XRPL.Model.Lending
