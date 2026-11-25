import XRPL.Properties.Vault.Common.Flows
import XRPL.Properties.Vault.Reachable
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.CreateUpdate
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts

/-! # Vault accounting over a sequence of transactions

On a vault with no lending every cash update is exact, so over any sequence of transactions the cash and the share
total end at their start values plus what the transactions moved in, less what they moved out. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A reachable vault never passes the burn check: a burn needs an insolvent vault, which has shares but no cash,
while on a reachable vault every share is worth at least one base unit of cash. -/
private lemma Vault.Reachable.canBurnShares_not_ok (u : Vault) (t : UInt32) (hr : Vault.Reachable u t)
    (amount holderShares sharesTotalAmount : STAmount)
    (hcan : (u.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) : False := by
  sorry

/-- The cash and the share total along a sequence from a reachable vault. -/
private lemma Vault.Flows.balances {w : Vault} {t : UInt32} (hr : Vault.Reachable w t) {u : Vault} {t' : UInt32}
    {D W C SC SR SD : ℚ} (h : Vault.Flows w t u t' D W C SC SR SD) :
    u.assetsAvailable.toRat = w.assetsAvailable.toRat + D - W - C ∧
      (u.toExact.sharesTotal : ℚ) = w.toExact.sharesTotal + SC - SR - SD := by
  sorry

/-- Over any sequence of transactions from a reachable vault -> AssetsTotal and AssetsAvailable each move by Σ deposits
− Σ withdrawals − Σ clawbacks, and SharesTotal by Σ sharesCreated − Σ sharesRedeemed − Σ sharesDestroyed. -/
theorem Vault.Reachable.accounting :
    (∀ (w : Vault) (t : UInt32), Vault.Reachable w t →
      ∀ (u : Vault) (t' : UInt32) (deposited withdrawn recovered created redeemed destroyed : ℚ),
      Vault.Flows w t u t' deposited withdrawn recovered created redeemed destroyed →
      u.toExact.assetsTotal = w.toExact.assetsTotal + deposited - withdrawn - recovered ∧
      u.assetsAvailable.toRat = w.assetsAvailable.toRat + deposited - withdrawn - recovered ∧
      (u.toExact.sharesTotal : ℚ) = w.toExact.sharesTotal + created - redeemed - destroyed) ∧
    -- from a new vault
    ∀ (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType) (t : UInt32)
      (w : Vault),
      Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok w →
      ∀ (u : Vault) (t' : UInt32) (deposited withdrawn recovered created redeemed destroyed : ℚ),
      Vault.Flows w t u t' deposited withdrawn recovered created redeemed destroyed →
      u.toExact.assetsTotal = deposited - withdrawn - recovered ∧
      u.assetsAvailable.toRat = deposited - withdrawn - recovered ∧
      (u.toExact.sharesTotal : ℚ) = created - redeemed - destroyed := by
  sorry

end XRPL.Model.SingleAssetVault
