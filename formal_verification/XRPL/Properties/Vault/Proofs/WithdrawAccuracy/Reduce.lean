import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk

/-! # The successful paths of `Vault.withdraw` -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

/-- Every successful `Vault.withdraw` is either the final branch or the
non-final branch, with each step's result. -/
lemma withdraw_ok_cases (v : Vault) (amount : WithdrawAmount) (w : Bool) (r : WithdrawResult)
    (hpos : 0 < amount.amount.toRat) (hok : v.withdraw amount w hpos = .ok r) (herr : r.error = none) :
    ∃ cw an sta,
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw ∧
      cw.error = none ∧ cw.assets'.toNumber .to_nearest = .ok an ∧
      v.assetsAvailable.operator_lt an = false ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta ∧
      r.sharesBurned = cw.sharesRedeemed ∧ r.error = none ∧
      ((cw.sharesRedeemed.operator_eq sta = true ∧
        v.lossUnrealized.operator_ne Number.zero = false ∧
        STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok r.assets' ∧
        r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero }) ∨
       (cw.sharesRedeemed.operator_eq sta = false ∧
        ∃ an' sbn at' atr atr' av' st',
          clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok r.assets' ∧
          r.assets'.isFractionalNonPositive = .ok false ∧
          r.assets'.toNumber .to_nearest = .ok an' ∧
          cw.sharesRedeemed.toNumber .to_nearest = .ok sbn ∧
          v.assetsTotal.operator_sub an' .to_nearest = .ok at' ∧
          STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr ∧
          STAmount.ofNumber v.numericType at' .to_nearest = .ok atr' ∧
          (an'.mantissa_ != 0 && atr.operator_eq atr') = false ∧
          v.assetsAvailable.operator_sub an' .to_nearest = .ok av' ∧
          v.sharesTotal.operator_sub sbn .to_nearest = .ok st' ∧
          r.vault'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' })) := by
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals try (simp [WithdrawResult.rejected] at herr; done)
  all_goals try (have h := ‹Option.isSome _ = true›; simp at herr; simp [herr] at h)
  all_goals refine ⟨_, _, _, ‹_›, by simp_all, ‹_›, by simp_all, ‹_›, rfl, rfl, ?_⟩
  all_goals first
    | exact Or.inl ⟨by simp_all, by simp_all, ‹_›, by rw_lawful⟩
    | exact Or.inr ⟨by simp_all, _, _, _, _, _, _, _, ‹_›, by simp_all, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›,
        by simp_all, ‹_›, ‹_›, by rw_lawful⟩

end XRPL.Model.SingleAssetVault.WdAcc
