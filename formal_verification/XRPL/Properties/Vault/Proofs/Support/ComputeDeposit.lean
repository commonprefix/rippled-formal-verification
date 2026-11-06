import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Vault.Proofs.Walk

/-! # `computeDeposit`

The successful paths of `computeDeposit`, and the codes it can reject with. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful deposit computation. The shares were priced (nonzero), re-priced to at most
the offered amount, and that charge was clamped to the vault total's exponent. -/
lemma computeDeposit_success_reduces (v : Vault) (amount : STAmount) (amounts : VaultAmounts)
    (hok : (computeDeposit v amount false).run = .ok (.ok amounts)) :
    ∃ (assets : STAmount) (assetsTotal : Number),
      assetsToSharesDeposit v amount = .ok amounts.shares ∧ amounts.shares.isZero = false ∧
      sharesToAssetsDeposit v amounts.shares = .ok assets ∧ assets.operator_gt amount = .ok false ∧
      v.assetsTotal = .ok assetsTotal ∧
      clampToSumExponent assetsTotal assets v.baseExponent = .ok amounts.assets ∧
      amounts.assets.isFractionalNonPositive = .ok false := by
  simp only [computeDeposit] at hok
  unfold_ter at hok
  walk_ok
  simp only [Bool.not_eq_true] at *
  subst_vars
  exact ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- A successful donation computation. It mints no shares and clamps the offered amount to the
vault total's exponent. -/
lemma computeDeposit_donation_reduces (v : Vault) (amount : STAmount) (amounts : VaultAmounts)
    (hok : (computeDeposit v amount true).run = .ok (.ok amounts)) :
    ∃ assetsTotal : Number, amounts.shares = STAmount.zero .int64 ∧ v.assetsTotal = .ok assetsTotal ∧
      clampToSumExponent assetsTotal amount v.baseExponent = .ok amounts.assets ∧
      amounts.assets.isFractionalNonPositive = .ok false := by
  simp only [computeDeposit] at hok
  unfold_ter at hok
  walk_ok
  simp only [Bool.not_eq_true] at *
  subst_vars
  exact ⟨_, by first | rfl | trivial, ‹_›, ‹_›, ‹_›⟩

/-- Every rejection `computeDeposit` returns: `tecPRECISION_LOSS`, `tecINTERNAL`, or `tecPATH_DRY`
for an overflow. -/
lemma computeDeposit_codes (v : Vault) (amount : STAmount) (isDonation : Bool) (ter : TER)
    (hok : (computeDeposit v amount isDonation).run = .ok (.error ter)) :
    ter = .tecPRECISION_LOSS ∨ ter = .tecINTERNAL ∨ ter = .tecPATH_DRY := by
  simp only [computeDeposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals simp

end XRPL.Model.SingleAssetVault
