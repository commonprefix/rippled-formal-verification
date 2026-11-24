import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witnesses for isolation

Two clawbacks in the investment phase, one worth a fraction of a base unit and one worth whole base units, after
which a withdrawal that paid 1 under the early-exit fee pays nothing (FV_M2_3). -/

set_option linter.style.native false

namespace XRPL.Model.SingleAssetVault.IsoWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

/-- Subscriptions until time 100, redemptions from time 400. -/
def sched : VaultSchedule := { subscriptionDate := 100, redemptionDate := 400 }

def vI : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 (some sched) (some 75000) 0
    [(iouAmount 7500000000000060 (-1), false), (iouAmount 2500000000000020 (-1), true)]

def jM : UInt64 := 60515300031

def vM : Vault :=
  createHistory.vault Vault.placeholder .int64 0 (some sched) (some 99989) 0
    [(int64Amount (18178 * jM), false), (int64Amount (3 * jM), true)]

lemma vI_reach : Vault.Reachable vI 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vM_reach : Vault.Reachable vM 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

/-- The withdrawn shares and the clawed-back holdings. -/
def sI : STAmount := int64Amount 3
def sM : STAmount := int64Amount 9089
def holdI : STAmount := int64Amount 750000000000002
def holdM : STAmount := int64Amount (18178 * (jM - 1))

lemma sI_pos : 0 < (WithdrawAmount.vaultShares sI).amount.toRat := by native_decide
lemma sM_pos : 0 < (WithdrawAmount.vaultShares sM).amount.toRat := by native_decide

/-- A zero clawback amount claws back the whole holding. -/
def zeroI : STAmount := STAmount.zero .fractional
def zeroM : STAmount := STAmount.zero .int64

lemma zeroI_nn : 0 ≤ zeroI.toRat := by native_decide
lemma zeroM_nn : 0 ≤ zeroM.toRat := by native_decide

lemma holdI_balance : holdI.ShareBalance := ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩
lemma holdM_balance : holdM.ShareBalance := ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩

/-- A withdrawal's and a clawback's result at time 200, computed by the model. -/
def wdRun (v : Vault) (a : WithdrawAmount) (h : 0 < a.amount.toRat) : VaultWithAmounts :=
  ((v.withdraw a false 200 h).run.toOption.bind Except.toOption).getD ⟨⟨a.amount, a.amount⟩, v⟩
def clRun (v : Vault) (a hold : STAmount) (h : 0 ≤ a.toRat) : VaultWithAmounts :=
  ((v.clawback a hold false h).run.toOption.bind Except.toOption).getD ⟨⟨a, a⟩, v⟩

end XRPL.Model.SingleAssetVault.IsoWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol IsoWit

/-- Clawback worth a fraction of a base unit, lowering the per-share value: a withdrawal of shares worth whole base
units that succeeded fails after it. -/
lemma Vault.Reachable.isolation_clawback_witness :
    ∃ (v : Vault) (t0 t : UInt32) (shares : STAmount) (waive : Bool)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (rW : VaultWithAmounts)
      (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ shares.Canonical ∧ shares.mNumericType = .int64 ∧
      (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW) ∧
      assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧ holderShares.ShareBalance ∧
      (waiveX = true ↔ v.IsSoleShareholder holderShares) ∧
      (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r) ∧ r.shares.toRat ≤ holderShares.toRat ∧
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal ∧
      v.earlyExitFeeRateAt t ≠ 0 ∧ v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
      (∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) ∧
      (r.vault'.withdraw (.vaultShares shares) waive t hpos).run = .ok (.error .tecPRECISION_LOSS) :=
  ⟨vI, 0, 200, sI, false, sI_pos, wdRun vI (.vaultShares sI) sI_pos, zeroI, holdI, false, zeroI_nn,
    clRun vI zeroI holdI zeroI_nn, vI_reach, by decide, STAmount.canonical_of_canonicalB _ (by native_decide), rfl,
    by native_decide, Or.inr (by native_decide), by native_decide, holdI_balance,
    ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by native_decide)⟩, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, ⟨4, by native_decide⟩, by native_decide⟩

/-- Clawback worth whole base units, keeping the per-share value: a withdrawal of shares worth a fraction of a base
unit that succeeded fails after it. -/
lemma Vault.Reachable.isolation_clawback_tie_witness :
    ∃ (v : Vault) (t0 t : UInt32) (shares : STAmount) (waive : Bool)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (rW : VaultWithAmounts)
      (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ shares.Canonical ∧ shares.mNumericType = .int64 ∧
      (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW) ∧
      assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧ holderShares.ShareBalance ∧
      (waiveX = true ↔ v.IsSoleShareholder holderShares) ∧
      (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r) ∧ r.shares.toRat ≤ holderShares.toRat ∧
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal ∧
      v.earlyExitFeeRateAt t ≠ 0 ∧ v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
      (∃ k : ℤ, v.idealAssetsWithdraw waiveX r.shares.toRat = k * 10 ^ v.baseExponent) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) = v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) ∧
      (r.vault'.withdraw (.vaultShares shares) waive t hpos).run = .ok (.error .tecPRECISION_LOSS) :=
  ⟨vM, 0, 200, sM, false, sM_pos, wdRun vM (.vaultShares sM) sM_pos, zeroM, holdM, false, zeroM_nn,
    clRun vM zeroM holdM zeroM_nn, vM_reach, by decide, STAmount.canonical_of_canonicalB _ (by native_decide), rfl,
    by native_decide, Or.inr (by native_decide), by native_decide, holdM_balance,
    ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by native_decide)⟩, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, ⟨18181 * 60515300030, by native_decide⟩, by native_decide,
    by native_decide⟩

end XRPL.Model.SingleAssetVault
