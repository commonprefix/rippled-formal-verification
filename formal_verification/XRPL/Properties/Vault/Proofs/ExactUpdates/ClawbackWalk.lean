import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk

/-! # The successful paths of `computeClawback` and `Vault.clawback` -/

namespace XRPL.Model.SingleAssetVault.Exact

open XRPL.Model.Protocol

/-- A successful `computeClawback` on a nonzero amount prices shares computed from
the request or from the available assets, the priced amount passes the availability
check, and the clamped recovery passes the fractional sign check. -/
lemma computeClawback_facts (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hznz : assets.isZero = false)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ X priced prn,
      (X = assets ∨ STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) ∧
      assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      priced.toNumber .to_nearest = .ok prn ∧
      prn.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.isFractionalNonPositive = .ok false := by
  simp only [computeClawback, assetsToSharesClawback, hznz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd ‹false = true› (by decide)
    | (dsimp only; exact ⟨_, _, _, Or.inl rfl, ‹_›, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all⟩)
    | (dsimp only; exact ⟨_, _, _, Or.inr ‹_›, ‹_›, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all⟩)

/-- The stored-field updates of a successful `Vault.clawback`. -/
lemma clawback_ok_cases (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error = none) :
    ∃ cr sdn arn at' atr av' st', computeClawback v assets holderShares = .ok cr ∧
      cr.error = none ∧
      r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
      cr.sharesDestroyed.toNumber .to_nearest = .ok sdn ∧
      cr.assetsRecovered.toNumber .to_nearest = .ok arn ∧
      v.assetsTotal.operator_sub arn .to_nearest = .ok at' ∧
      STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr ∧
      v.assetsAvailable.operator_sub arn .to_nearest = .ok av' ∧
      v.sharesTotal.operator_sub sdn .to_nearest = .ok st' ∧
      r.vault'.assetsTotal = at' ∧ r.vault'.assetsAvailable = av' ∧
      r.vault'.sharesTotal = st' := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp [ClawbackResult.rejected] at herr; done)
    | (simp only at herr; simp [herr] at *; done)
    | skip
  have hl := (RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1
  refine ⟨_, _, _, _, _, _, _, ‹computeClawback _ _ _ = _›, ?_, rfl, rfl, ‹_›, ‹_›, ‹_›, ‹_›,
    ‹_›, ‹_›, ?_, ?_, ?_⟩
  · simpa using ‹¬ (Option.isSome _) = true›
  · dsimp only; rw [hl]
  · dsimp only; rw [hl]
  · dsimp only; rw [hl]

end XRPL.Model.SingleAssetVault.Exact
