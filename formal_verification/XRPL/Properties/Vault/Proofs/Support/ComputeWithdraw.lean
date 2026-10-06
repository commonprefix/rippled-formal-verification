import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.Walk

/-! # Withdraw computation

The successful `computeWithdrawByAssets` / `computeWithdrawByShares` step prices the redeemed
shares with `sharesToAssetsWithdraw`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful computation prices the redeemed shares. -/
lemma computeWithdraw_ok_priced (v : Vault) (amount : WithdrawAmount) (w : Bool) (cw : ComputeWithdrawResult)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw)
    (herr : cw.error = none) :
    v.sharesToAssetsWithdraw cw.sharesRedeemed w = .ok cw.assets' := by
  cases amount <;>
    simp only [computeWithdrawByAssets, computeWithdrawByShares, bind, Except.bind, pure,
      Except.pure, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hcomp <;>
    walk_ok <;> first | assumption | simp at herr

lemma computeWithdrawByShares_ok_of_price (v : Vault) (shares assets : STAmount)
    (hok : v.sharesToAssetsWithdraw shares false = .ok assets) :
    computeWithdrawByShares v shares false = .ok ⟨none, assets, shares⟩ := by
  simp [computeWithdrawByShares, hok, tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
    Except.tryCatch, bind, Except.bind, pure, Except.pure]

end XRPL.Model.SingleAssetVault
