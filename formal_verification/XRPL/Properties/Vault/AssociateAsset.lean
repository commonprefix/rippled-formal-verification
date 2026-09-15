import XRPL.Properties.Vault.Common.ReachableProofs
import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.WithdrawWitness
import XRPL.Properties.Vault.Common.ClawbackWitness

/-! # The `associateAsset` no-op invariant

Every vault transactor calls `associateAsset` on the vault SLE after updating it, which
rounds each `kSmdNeedsAsset` field (`assetsTotal`, `assetsAvailable`, `assetsReserved`,
`lossUnrealized`, `assetsMaximum`) to the asset's precision. A correct transactor keeps
those fields on the grid, so `associateAsset` should be a no-op: `Vault.assetsRounded`
should never hold on a stored vault. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000

/-- `Number.zero` is exact for any asset: converting it to an STAmount is the identity, so
it is never rounded. -/
private lemma STAmount.isRounded_zero (nt : NumericType) : STAmount.isRounded nt Number.zero = false := by
  cases nt <;> rfl

/-- NOT PROVABLE: **`associateAsset` is a no-op on every reachable vault** -/
theorem Vault.Reachable.associateAsset_noop (v : Vault)
    (hr : Vault.Reachable v) : ¬ v.assetsRounded := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    -- Only assetsMaximum can be off-grid, which `Reachable.create` does not constrain to the asset grid
    unfold Vault.assetsRounded
    simp only [Vault.create_lawful_toRawVault, STAmount.isRounded_zero, Bool.false_eq_true,
      false_or]
    sorry
  | deposit lw amount isDonation r hrv hdep _ _ _ ih =>
    -- `assetsTotal += assetDeposited` uses a raw `operator_add` whose result is not
    -- re-rounded to the asset grid, so this case cannot be discharged
    sorry
  | withdraw lw amount waive r hrv hwd _ _ _ _ _ ih =>
    -- `assetsTotal -= payout` uses a raw `operator_sub` whose result is not re-rounded
    -- to the asset grid, so this case cannot be discharged
    sorry
  | clawback lw assets holderShares r hrv hcb _ _ _ _ _ _ ih =>
    -- `assetsTotal -= assetsRecovered` uses a raw `operator_sub` whose result is not
    -- re-rounded to the asset grid, so this case cannot be discharged
    sorry
  | burnShares lw sharesDestroyed sharesTotalAmount lw' hrv hcan hcanon hnn hle hfit hburn ih =>
    -- `burnShares` writes only `sharesTotal`, which `assetsRounded` ignores
    unfold Vault.burnShares at hburn
    simp only [] at hburn
    obtain ⟨sdn, _, hburn⟩ := bind_ok_peel _ _ _ hburn
    obtain ⟨st', _, hburn⟩ := bind_ok_peel _ _ _ hburn
    have hrec : lw'.toRawVault = { lw.toRawVault with sharesTotal := st' } :=
      (RawVault.to_lawful_ok hburn).1
    have heq : lw'.assetsRounded = lw.assetsRounded := by
      simp only [Vault.assetsRounded, hrec]
    rw [heq]; exact ih

/-- **`associateAsset` is not a no-op.** A deposit into the lawful int64 vault of
`DilutionWitness` (holding `2^63 - 1`) pushes `assetsTotal` past the int64 STAmount
range, so the post-deposit vault satisfies `assetsRounded`.

A fractional vault no longer works here: `clampToSumExponent` aligns the charge to
the post-sum grid, so the stored total lands exactly on the STAmount grid. -/
theorem Vault.deposit_associateAsset_rounds :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.deposit amountDeposit false = .ok r ∧ r.vault'.assetsRounded :=
  ⟨baseLV, depAmt, depR, by native_decide, by unfold Vault.assetsRounded; native_decide⟩

/-- The off-grid witness vault: `assetsTotal = assetsAvailable = 3.000000000000000123`
carries 19 significant digits, two past the 16-digit IOU grid. -/
def offGridV : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000123, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000123, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The off-grid witness vault as a `Vault`. -/
def offGridVL : Vault := ⟨offGridV, by native_decide, by native_decide⟩

/-- Witness withdrawal share count for the off-grid vault. -/
def offGridShares : STAmount := STAmount.unchecked .int64 3 0 false

/-- Witness clawback amount for the off-grid vault, `1` of the IOU. -/
def offGridClawAmt : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- **`associateAsset` is not a no-op after a withdrawal.** The clamp only aligns the
payout, not `assetsTotal`'s own sub-grid digits, so a withdrawal out of `offGridV`
leaves `assetsTotal` off the STAmount grid. -/
theorem Vault.withdraw_associateAsset_rounds :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.vault'.assetsRounded :=
  ⟨offGridVL, .vaultShares offGridShares, false,
    (offGridVL.withdraw (.vaultShares offGridShares) false).toOption.getD
      (WithdrawResult.rejected offGridVL .tecINTERNAL),
    by native_decide, by unfold Vault.assetsRounded; native_decide⟩

/-- **`associateAsset` is not a no-op after a clawback.** Same mechanism as the
withdrawal witness. -/
theorem Vault.clawback_associateAsset_rounds :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.vault'.assetsRounded :=
  ⟨offGridVL, offGridClawAmt, cwHolderShares,
    (offGridVL.clawback offGridClawAmt cwHolderShares).toOption.getD
      (ClawbackResult.rejected offGridVL .tecINTERNAL),
    by native_decide, by unfold Vault.assetsRounded; native_decide⟩

end XRPL.Model.SingleAssetVault
