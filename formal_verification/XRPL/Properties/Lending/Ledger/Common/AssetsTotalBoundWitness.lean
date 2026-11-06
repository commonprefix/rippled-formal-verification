import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.AssetFlowDefs

/-! # Runs whose AssetsTotal strays from the flows by more than one ULP per transaction

A late payment that moves AssetsTotal to a coarser scale credits it 1.99 ULP less than its flows. A pending delete
on a coarsened vault followed by a withdrawal ends four ULP above them. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- Apply the transactions in order and add up what the payments collect beyond the schedule, or `none` when one
of them does not succeed. -/
private def LendingLedger.runIn'' (l : LendingLedger) : List LendingTx → Option (LendingLedger × ℚ)
  | [] => some (l, 0)
  | tx :: txs =>
    match (l.apply tx).run with
    | .ok (.ok l') => (l'.runIn'' txs).map fun p => (p.1, l.extraInterest tx l' + p.2)
    | _ => none

/-- A run that succeeds at every step is a `ReachableFromIn` run. -/
private lemma LendingLedger.runIn''_reachableFromIn {l l' : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : l.runIn'' txs = some (l', x)) : l.ReachableFromIn txs l' x := by
  induction txs generalizing l l' x with
  | nil =>
    simp only [LendingLedger.runIn'', Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl
  | cons tx txs ih =>
    unfold LendingLedger.runIn'' at h
    split at h
    · rename_i l₁ hl₁
      obtain ⟨⟨l₂, x₂⟩, h₂, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact LendingLedger.ReachableFromIn.cons hl₁ (ih h₂)
    · cases h

/-- An interest rate of 0.964% and a late rate of 100%. -/
private def lbRates : LoanRates :=
  { interestRate := 964, lateInterestRate := 100000, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of `603953705712463.7`, a broker with no fee and no cover, the loan of `603946999675283.3` over 7
monthly payments, and a close about 32 years after the first due date. -/
private def lbSetup : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 6039537057124637 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 6039469996752833000, -4⟩ lbRates cwFees (some 2592000) (some 7) (some 60) 0 false false,
   .close (1001 + 2592000 + 1014453797)]

/-- The late payment of the first instalment, rounded up to 16 digits. -/
private def lbTxs : List LendingTx := [.loanPay 0 .late ⟨false, 1951439068477936000, -2⟩]

/-- The payment credits the vault `1.99` ULP less than the flows, at a scale above the scale it started at. -/
private def lbCheck : Bool :=
  match cwGenesis.run lbSetup with
  | .ok s =>
    match s.runIn'' lbTxs with
    | some (l, _) =>
      match s.vault.assetsTotal, l.vault.assetsTotal with
      | .ok t₀, .ok t =>
        match numberExponent t₀ s.vault.baseExponent s.vault.numericType,
            numberExponent t l.vault.baseExponent l.vault.numericType with
        | .ok e₀, .ok e =>
          decide (e₀ < e ∧ s.vault.toRawVault.toExact.assetsTotal + (s.flows lbTxs).deposits -
            (s.flows lbTxs).withdrawals - (s.flows lbTxs).clawbacks + (s.flows lbTxs).interestPaid -
            (s.flows lbTxs).defaultLosses - l.vault.toRawVault.toExact.assetsTotal = (199 / 100 : ℚ) * 10 ^ e)
        | _, _ => false
      | _, _ => false
    | none => false
  | .error _ => false

private lemma lbCheck_true : lbCheck = true := by native_decide

/-- A one-transaction run can credit AssetsTotal 1.99 ULP less than its flows at the vault scale. The scale of
AssetsTotal rises from `10^-1` to `10^1` in the run. -/
lemma LendingLedger.assetsTotal_lower_bound_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (x : ℚ) (total₀ total : Number) (e₀ e : Int),
      start.Reachable ∧ start.ReachableFromIn txs l x ∧ txs.length = 1 ∧
      start.vault.assetsTotal = .ok total₀ ∧ l.vault.assetsTotal = .ok total ∧
      numberExponent total₀ start.vault.baseExponent start.vault.numericType = .ok e₀ ∧
      numberExponent total l.vault.baseExponent l.vault.numericType = .ok e ∧ e₀ < e ∧
      start.vault.toRawVault.toExact.assetsTotal + (start.flows txs).deposits - (start.flows txs).withdrawals -
        (start.flows txs).clawbacks + (start.flows txs).interestPaid - (start.flows txs).defaultLosses -
        l.vault.toRawVault.toExact.assetsTotal = (199 / 100 : ℚ) * 10 ^ e := by
  have h := lbCheck_true
  unfold lbCheck at h
  split at h
  case h_2 => cases h
  rename_i s hs
  split at h
  case h_2 => cases h
  rename_i l x hl
  split at h
  case h_2 => cases h
  rename_i t₀ t ht₀ ht
  split at h
  case h_2 => cases h
  rename_i e₀ e he₀ he
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  exact ⟨s, l, lbTxs, x, t₀, t, e₀, e, LendingLedger.Reachable.of_run cwGenesis_genesis hs,
    LendingLedger.runIn''_reachableFromIn hl, rfl, ht₀, ht, he₀, he, h1, h2⟩

/-- The coarsened run with a pending loan E of 0.6, created before the vault coarsens. -/
private def ubSetup : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 ⟨false, 6000000000000000000, -19⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 70000000 true
     false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- Delete loan E, wait for the redemption phase and withdraw `1474246907153727`. -/
private def ubTxs : List LendingTx :=
  [.loanDelete 3, .close (1000 + 900 * 86400 + 1), .vaultWithdraw 0 (.vaultAssets (cwAmount 1474246907153727 0))]

/-- AssetsTotal ends four ULP of its final scale above the flows. -/
private def ubCheck : Bool :=
  match cwGenesis.run ubSetup with
  | .ok s =>
    match s.runIn'' ubTxs with
    | some (l, _) =>
      match l.vault.assetsTotal with
      | .ok t =>
        match numberExponent t l.vault.baseExponent l.vault.numericType with
        | .ok e =>
          decide (l.vault.toRawVault.toExact.assetsTotal - (s.vault.toRawVault.toExact.assetsTotal +
            (s.flows ubTxs).deposits - (s.flows ubTxs).withdrawals - (s.flows ubTxs).clawbacks +
            (s.flows ubTxs).interestPaid - (s.flows ubTxs).defaultLosses) = 4 * 10 ^ e)
        | .error _ => false
      | .error _ => false
    | none => false
  | .error _ => false

private lemma ubCheck_true : ubCheck = true := by native_decide

/-- A three-transaction run can end with AssetsTotal four ULP above its flows at the final vault scale. The
pending delete credits 0.4 too much at the scale `10^0`, and the withdrawal brings the scale down to `10^-1`. -/
lemma LendingLedger.assetsTotal_upper_bound_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (x : ℚ) (total : Number) (e : Int),
      start.Reachable ∧ start.ReachableFromIn txs l x ∧ txs.length = 3 ∧ l.vault.assetsTotal = .ok total ∧
      numberExponent total l.vault.baseExponent l.vault.numericType = .ok e ∧
      l.vault.toRawVault.toExact.assetsTotal - (start.vault.toRawVault.toExact.assetsTotal +
        (start.flows txs).deposits - (start.flows txs).withdrawals - (start.flows txs).clawbacks +
        (start.flows txs).interestPaid - (start.flows txs).defaultLosses) = 4 * 10 ^ e := by
  have h := ubCheck_true
  unfold ubCheck at h
  split at h
  case h_2 => cases h
  rename_i s hs
  split at h
  case h_2 => cases h
  rename_i l x hl
  split at h
  case h_2 => cases h
  rename_i t ht
  split at h
  case h_2 => cases h
  rename_i e he
  exact ⟨s, l, ubTxs, x, t, e, LendingLedger.Reachable.of_run cwGenesis_genesis hs,
    LendingLedger.runIn''_reachableFromIn hl, rfl, ht, he, of_decide_eq_true h⟩

end XRPL.Model.Lending
