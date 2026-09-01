import XRPL.Properties.Vault.Common.ReachableProofs
import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.WithdrawWitness
import XRPL.Properties.Vault.Common.ClawbackWitness

/-! # The `associateAsset` no-op invariant

Every vault transactor calls `associateAsset` on the vault SLE after updating it, which
rounds each `kSmdNeedsAsset` field (`assetsTotal`, `assetsAvailable`, `assetsReserved`,
`lossUnrealized`, `assetsMaximum`) to the asset's precision. A correct transactor keeps
those fields on the grid, so `associateAsset` should be a no-op: `LawfulVault.assetsRounded`
should never hold on a stored vault. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000

/-- `Number.zero` is exact for any asset: converting it to an STAmount is the identity, so
it is never rounded. -/
theorem STAmount.isRounded_zero (nt : NumericType) : STAmount.isRounded nt Number.zero = false := by
  cases nt <;> rfl

/-- NOT PROVABLE: **`associateAsset` is a no-op on every reachable vault** -/
theorem LawfulVault.Reachable.associateAsset_noop (lv : LawfulVault)
    (hr : LawfulVault.Reachable lv) : ¬ lv.assetsRounded := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    -- Only assetsMaximum can be off-grid, which `Reachable.create` does not constrain to the asset grid
    unfold LawfulVault.assetsRounded
    simp only [LawfulVault.create_lawful_toRawVault, STAmount.isRounded_zero, Bool.false_eq_true,
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
    unfold LawfulVault.burnShares at hburn
    simp only [] at hburn
    obtain ⟨sdn, _, hburn⟩ := bind_ok_peel _ _ _ hburn
    obtain ⟨st', _, hburn⟩ := bind_ok_peel _ _ _ hburn
    have hrec : lw'.toRawVault = { lw.toRawVault with sharesTotal := st' } :=
      (RawVault.to_lawful_ok hburn).1
    have heq : lw'.assetsRounded = lw.assetsRounded := by
      simp only [LawfulVault.assetsRounded, hrec]
    rw [heq]; exact ih

/-- **`associateAsset` is not a no-op.** A deposit into a lawful IOU vault leaves `assetsTotal`
off the STAmount grid (`3.9999999999999999`, 17 significant digits), so the post-deposit vault
satisfies `assetsRounded`. -/
theorem LawfulVault.deposit_associateAsset_rounds :
    ∃ (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult),
      lv.deposit amountDeposit false = .ok r ∧ r.vault'.assetsRounded :=
  ⟨wvFL, waF, wrF, by native_decide, by unfold LawfulVault.assetsRounded; native_decide⟩

/-- **`associateAsset` is not a no-op after a withdrawal.** A share withdrawal leaves
`assetsTotal` off the STAmount grid (`2.999000000000000143`, 19 significant digits), so the
post-withdraw vault satisfies `assetsRounded`. -/
theorem LawfulVault.withdraw_associateAsset_rounds :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.vault'.assetsRounded :=
  ⟨wvWL, .vaultShares wsh4W, false, wr4W, by native_decide,
    by unfold LawfulVault.assetsRounded; native_decide⟩

/-- **`associateAsset` is not a no-op after a clawback.** A clawback leaves `assetsTotal`
off the STAmount grid (`2.999900000000000143`, 19 significant digits), so the post-clawback
vault satisfies `assetsRounded`. -/
theorem LawfulVault.clawback_associateAsset_rounds :
    ∃ (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult),
      lv.clawback assets holderShares = .ok r ∧ r.vault'.assetsRounded :=
  ⟨cwvBL, cwa1, cwHolderShares, cwr2, by native_decide,
    by unfold LawfulVault.assetsRounded; native_decide⟩

end XRPL.Model.SingleAssetVault
