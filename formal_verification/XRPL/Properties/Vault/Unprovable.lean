import XRPL.Properties.Vault.Proofs.UnprovableWitness

/-! # Statements kept but false

Each `…_claim` is a statement we would like to hold but which the model refutes;
`…_false` proves its negation from a concrete counterexample. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `associateAsset` is a no-op on every reachable vault. False: the model has no
`associateAsset` step, and a deposit's clamped charge can leave a total the asset grid
cannot hold (create at scale 15, deposit `1.234567890123456`, deposit `100` stores
`101.234567890123396`, 18 digits). -/
def Vault.Reachable.associateAsset_noop_claim : Prop :=
  ∀ v : Vault, Vault.Reachable v → ¬ v.assetsRounded

theorem Vault.Reachable.associateAsset_noop_false :
    ¬ Vault.Reachable.associateAsset_noop_claim := fun h =>
  let ⟨v, hr, hrd⟩ := Vault.reachable_offgrid_witness
  h v hr hrd

/-- Every lawful vault with nothing lent out can be emptied by redeeming all its shares.
False: the funds guard runs on the priced payout before the final-withdrawal branch, and
the interior to-nearest `mul`/`div` can price a full redemption above `assetsAvailable`
(int64 vault with `9223372036854775806` assets and `3` shares prices one unit over and is
rejected with `tecINSUFFICIENT_FUNDS`). -/
def Vault.withdraw_can_empty_claim : Prop :=
  ∀ (v : Vault) (sharesTotalAmount : STAmount),
    v.toExact.assetsTotal = v.toExact.assetsAvailable →
    STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
    ∀ hpos : 0 < sharesTotalAmount.toRat,
    ∃ allAvailable : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable ∧
      ∃ v' : Vault,
        v.withdraw (.vaultShares sharesTotalAmount) false hpos =
          .ok ⟨none, v', allAvailable, sharesTotalAmount⟩ ∧
        v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero }

theorem Vault.withdraw_can_empty_false : ¬ Vault.withdraw_can_empty_claim := fun h =>
  let ⟨v, s, hpos, r, hlent, hst, hok, herr⟩ := Vault.full_exit_rejected_witness
  let ⟨_, _, _, hw, _⟩ := h v s hlent hst hpos
  by rw [hw] at hok; cases hok; cases herr

end XRPL.Model.SingleAssetVault
