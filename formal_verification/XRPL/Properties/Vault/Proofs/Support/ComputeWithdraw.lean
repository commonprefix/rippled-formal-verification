import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.Walk

/-! # Withdraw computation

A successful `computeWithdraw` prices the redeemed shares with `sharesToAssetsWithdraw`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful computation prices the redeemed shares. -/
lemma computeWithdraw_ok_priced (v : Vault) (amount : WithdrawAmount) (w : Bool) (amounts : VaultAmounts)
    (hcomp : (computeWithdraw v amount w).run = .ok (.ok amounts)) :
    v.sharesToAssetsWithdraw amounts.shares w = .ok amounts.assets := by
  simp only [computeWithdraw] at hcomp
  unfold_ter at hcomp
  walk_ok
  all_goals assumption

/-- Redeeming a nonzero share amount whose price succeeds computes that price. -/
lemma computeWithdraw_shares_ok_of_price (v : Vault) (shares assets : STAmount) (w : Bool)
    (hz : shares.isZero = false) (hok : v.sharesToAssetsWithdraw shares w = .ok assets) :
    (computeWithdraw v (.vaultShares shares) w).run = .ok (.ok { assets := assets, shares := shares }) := by
  simp [computeWithdraw, hz, hok, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure,
    ExceptT.bindCont, bind, pure, Except.bind, Except.pure, Except.map, Except.tryCatch, Functor.map,
    tryCatchThe, MonadExceptOf.tryCatch, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift]

end XRPL.Model.SingleAssetVault
