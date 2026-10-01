import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Proofs.Walk

/-! # Paths of a successful `Vault.clawback` -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

/-- The final pricing chain of a successful nonzero-amount `computeClawback`, and which
branch produced it. -/
lemma computeClawback_cases (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hznz : assets.isZero = false)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ X priced arn, assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      priced.toNumber .to_nearest = .ok arn ∧ arn.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.isFractionalNonPositive = .ok false ∧
      (X = assets ∨
        ∃ sd0 p0 n0, assetsToSharesWithdraw v assets true false = .ok sd0 ∧
          v.sharesToAssetsWithdraw sd0 false = .ok p0 ∧ p0.toNumber .to_nearest = .ok n0 ∧
          n0.operator_gt v.assetsAvailable = true ∧
          STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) := by
  simp only [computeClawback, assetsToSharesClawback, hznz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd ‹false = true› (by decide)
    | skip
  all_goals
    rename_i hfnp hb
    simp only [Bool.not_eq_true] at hb
    subst hb
    refine ⟨_, _, _, ‹_›, ‹_›, ‹_›, ?_, ‹_›, hfnp, ?_⟩
  · simpa using ‹¬ _ = true›
  · exact Or.inr ⟨_, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  · simpa using ‹¬ _ = true›
  · exact Or.inl rfl

/-- A successful `Vault.clawback` reports its `computeClawback` amounts, with a nonzero
share count. -/
lemma clawback_cr (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error = none) :
    ∃ cr, computeClawback v assets holderShares = .ok cr ∧ cr.error = none ∧
      cr.sharesDestroyed.isZero = false ∧ r.assetsRecovered = cr.assetsRecovered ∧
      r.sharesDestroyed = cr.sharesDestroyed := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp [ClawbackResult.rejected] at herr; done)
    | (simp only at herr; simp [herr] at *; done)
    | skip
  refine ⟨_, ‹computeClawback _ _ _ = _›, ?_, ?_, rfl, rfl⟩
  · simpa using ‹¬ (Option.isSome _) = true›
  · simpa using ‹¬ (STAmount.isZero _) = true›

/-- The zero-amount (claw all) branch of a successful `computeClawback`. -/
lemma computeClawback_zero (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hz : assets.isZero = true)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ priced arn, v.sharesToAssetsWithdraw holderShares false = .ok priced ∧
      priced.toNumber .to_nearest = .ok arn ∧
      (arn.operator_gt v.assetsAvailable = true ∨
        (cr.sharesDestroyed = holderShares ∧
          clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered)) := by
  simp only [computeClawback, assetsToSharesClawback, hz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd trivial ‹¬ True›
    | skip
  · exact ⟨_, _, ‹_›, ‹_›, Or.inl ‹_›⟩
  · exact ⟨_, _, ‹_›, ‹_›, Or.inr ⟨rfl, ‹_›⟩⟩

end XRPL.Model.SingleAssetVault.ClwTight
