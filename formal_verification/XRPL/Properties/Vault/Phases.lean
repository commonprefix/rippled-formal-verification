import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultSet
import XRPL.Properties.Vault.Proofs.Phases

/-! # The share total across the phases of a closed-ended vault

In the investment phase the share total moves only through a withdrawal from a vault that has an
early-exit fee rate (even a zero one), a clawback, or burning the shares of an insolvent vault. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- In the investment phase a deposit, donation or update leaves the share total as it is, a withdrawal
succeeds only on a vault with an early-exit fee rate, and a burn only on an insolvent vault. -/
theorem Vault.investment_shares_fixed (v : Vault) (t : UInt32) (hphase : v.phase t = .investment) :
    (∀ (amount : STAmount) (isDonation : Bool) (hpos : 0 < amount.toRat) (r : VaultWithAmounts),
      (v.deposit amount isDonation t hpos).run = .ok (.ok r) → r.vault'.sharesTotal = v.sharesTotal) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      (v.withdraw amount waive t hpos).run = .ok (.ok r) → v.earlyExitFeeRate.isSome = true) ∧
    (∀ (amount holderShares sharesTotalAmount : STAmount) (v' : Vault),
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (v.burnShares holderShares).run = .ok (.ok v') → v.isInsolvent = true) ∧
    (∀ (assetsMaximum : Option Number) (blockDeposit : Option Bool) (v' : Vault),
      v.canVaultUpdate assetsMaximum blockDeposit = .ok .tesSUCCESS →
      v.update assetsMaximum blockDeposit = .ok v' → v'.sharesTotal = v.sharesTotal) :=
  Vault.investment_shares_fixed_proof v t hphase

end XRPL.Model.SingleAssetVault
