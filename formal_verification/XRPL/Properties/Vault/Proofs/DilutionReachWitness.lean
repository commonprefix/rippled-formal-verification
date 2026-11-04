import XRPL.Properties.Vault.Proofs.DilutionWitness

/-! # Witness for the history dilution bound

A reachable `int64` vault of 7 assets and 4 shares (a deposit of 4, then a donation of 3) redeems 2
shares, worth `3.5`, for `4`, then 1 of the remaining 2, worth `1.5`, for `2`. Per-share value falls
`7/4 → 3/2 → 1` although the run has no deposit, so its budget is zero. -/

set_option linter.style.nativeDecide false

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

/-- History budget: two withdrawals that each overpay by half a unit lower per-share value with a zero budget. -/
lemma Vault.ReachableFromIn.dilution_witness :
    ∃ (v : Vault) (t0 t : UInt32) (n : ℕ) (D : ℚ) (w : Vault),
      Vault.Reachable v t0 ∧ Vault.ReachableFromIn false v t w n D ∧ 1 < n ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) < v.withdrawNav / (v.toExact.sharesTotal : ℚ) - D := by
  have s1 := Vault.ReachableFromIn.withdraw (whole := false) vH vH 0 0 0 0 (burn 2) (int64Amount 2) false r1
    (Vault.ReachableFromIn.refl (whole := false) vH 0) (by decide)
    (STAmount.canonical_of_canonicalB _ (by native_decide)) rfl
    (shareBalance 2 (by native_decide)) (by unfold Vault.IsSoleShareholder; native_decide) burn2_pos
    (by native_decide) (by native_decide) (by native_decide) (fun h => absurd h (by decide))
  have s2 := Vault.ReachableFromIn.withdraw (whole := false) vH r1.vault' 0 0 _ _ (burn 1) (int64Amount 1) false r2 s1
    (by decide)
    (STAmount.canonical_of_canonicalB _ (by native_decide)) rfl
    (shareBalance 1 (by native_decide)) (by unfold Vault.IsSoleShareholder; native_decide) burn1_pos
    (by native_decide) (by native_decide) (by native_decide) (fun h => absurd h (by decide))
  exact ⟨vH, 0, 0, _, _, _, vH_reach, s2, by decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
