import XRPL.Properties.Vault.Proofs.DilutionWitness

/-! # Witness for the history dilution bound

Two redemptions from a reachable vault lower the per-share value from `7/4` to `1` with no deposit in the run. -/

set_option linter.style.native false

namespace XRPL.Model.SingleAssetVault.DilWit

open XRPL.Model.Protocol

def vH : Vault := intVault 4 3

lemma vH_reach : Vault.Reachable vH 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

lemma burn2_pos : 0 < (burn 2).amount.toRat := by native_decide

def r1 : VaultWithAmounts := wdRun vH (burn 2) burn2_pos
def r2 : VaultWithAmounts := wdRun r1.vault' (burn 1) burn1_pos

lemma shareBalance (n : UInt64) (h : (int64Amount n).canonicalB = true) : (int64Amount n).ShareBalance :=
  ⟨rfl, STAmount.canonical_of_canonicalB _ h, rfl⟩

end XRPL.Model.SingleAssetVault.DilWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DilWit

/-- Two withdrawals that each overpay by half a unit lower per-share value. -/
lemma Vault.ReachableFromIn.dilution_witness :
    ∃ (v : Vault) (t0 t : UInt32) (n : ℕ) (w : Vault),
      Vault.Reachable v t0 ∧ Vault.ReachableFromIn false v t w n ∧ 1 < n ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) < v.withdrawNav / (v.toExact.sharesTotal : ℚ) := by
  have s1 := Vault.ReachableFromIn.withdraw (whole := false) vH vH 0 0 0 (burn 2) (int64Amount 2) false r1
    (Vault.ReachableFromIn.refl (whole := false) vH 0) (by decide)
    (STAmount.canonical_of_canonicalB _ (by native_decide)) rfl
    (shareBalance 2 (by native_decide)) (by unfold Vault.IsSoleShareholder; native_decide) burn2_pos
    (by native_decide) (by native_decide) (by native_decide) (fun h => absurd h (by decide))
  have s2 := Vault.ReachableFromIn.withdraw (whole := false) vH r1.vault' 0 0 _ (burn 1) (int64Amount 1) false r2 s1
    (by decide)
    (STAmount.canonical_of_canonicalB _ (by native_decide)) rfl
    (shareBalance 1 (by native_decide)) (by unfold Vault.IsSoleShareholder; native_decide) burn1_pos
    (by native_decide) (by native_decide) (by native_decide) (fun h => absurd h (by decide))
  exact ⟨vH, 0, 0, _, _, vH_reach, s2, by decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
