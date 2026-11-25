import XRPL.Properties.Lending.Ledger.Common.CoverGridInv
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.YieldGridInv

/-! # Every balance on the base grid

On a reachable ledger the vault's balances and every broker's DebtTotal are whole numbers of base units, and on
an IOU vault every broker's CoverAvailable as well. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- AssetsAvailable is a whole number of base units: on an IOU vault by the grid invariant, on an integral one
because the asset stores it exactly at base exponent 0. -/
lemma LendingLedger.Reachable.assetsAvailable_onGrid {l : LendingLedger} (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat) :
    Number.OnGrid l.vault.baseExponent l.vault.assetsAvailable := by
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  cases hnt : l.vault.numericType with
  | fractional => exact (hr.gridInv.grid hnt).1
  | integral mv mo ms msh =>
    have hint : l.vault.numericType.isIntegral = true := by rw [hnt]; rfl
    have hrep := (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm hAA0).mp
      (hr.storesAvailable hmax)
    rw [Vault.baseExponent_integral l.vault hint]
    rcases hrep with h0 | hrep
    · exact Number.OnGrid.of_nat l.vault.wf.assetsAvailable_norm 0 (by rw [h0]; simp)
    · rw [hnt] at hrep
      obtain ⟨-, k, -, -, hk⟩ := hrep
      exact Number.OnGrid.of_nat l.vault.wf.assetsAvailable_norm k (by rw [hk]; simp)

/-- On a reachable ledger of XRP, an MPT or an IOU, AssetsAvailable is a whole number of base units. -/
lemma LendingLedger.Reachable.assetsAvailable_units {l : LendingLedger} (hr : l.Reachable)
    (hasset : Vault.HoldsAsset l.vault) :
    ∃ n : ℕ, l.vault.assetsAvailable.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent :=
  (hr.assetsAvailable_onGrid hasset.maxValue_le).nat l.vault.exact.assetsAvailable_nonneg

/-- Every vault balance and every broker's DebtTotal are on the base grid, and on an IOU vault every broker's
CoverAvailable. -/
lemma LendingLedger.base_grid_proof (l : LendingLedger) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat) :
    Number.OnGrid l.vault.baseExponent l.vault.assetsAvailable ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsDeployed ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsReserved ∧
      Number.OnGrid l.vault.baseExponent l.vault.lossUnrealized ∧
      Number.OnGrid l.vault.baseExponent l.vault.yieldUnrealized ∧
      ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        Number.OnGrid l.vault.baseExponent b.debtTotal ∧
          (l.vault.numericType = .fractional → Number.OnGrid l.vault.baseExponent b.coverAvailable) := by
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨nl, hnl⟩ := hr.lossInv.grid
  refine ⟨hr.assetsAvailable_onGrid hmax,
    Number.OnGrid.of_nat l.vault.wf.assetsDeployed_norm nd (by rw [hr.debtInv.deployed, hnd]),
    Number.OnGrid.of_nat l.vault.wf.assetsReserved_norm nr hnr,
    Number.OnGrid.of_nat l.vault.wf.lossUnrealized_norm nl hnl, hr.yieldGridInv.grid,
    fun j b hb => ⟨?_, fun hfr => hr.coverGridInv.cover hfr j b hb⟩⟩
  obtain ⟨n, hn⟩ := hr.scaleInv.brokerPrincipal_grid j
  exact Number.OnGrid.of_nat b.wf.debtTotal_norm n (by rw [hr.debtInv.debt j b hb, hn])

end XRPL.Model.Lending
