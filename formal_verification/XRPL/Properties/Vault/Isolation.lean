import XRPL.Properties.Vault.Proofs.Isolation
import XRPL.Properties.Vault.Proofs.IsolationWitness

/-! # Isolation of a holder's withdrawal

A transaction by another holder, or by the owner, never makes a withdrawal by shares that would have succeeded fail,
as long as it leaves the withdrawn shares in place. Without a partial early-exit fee a reachable vault pays every
withdrawal by shares it covers. Under a partial fee the withdrawal needs the price of its shares not to fall: a deposit,
a donation and an update keep it, another withdrawal keeps it on an XRP or MPT vault, and otherwise the amounts priced
must be worth whole base units. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Vault transaction by another holder or the owner, at the same time -> a withdrawal by shares that would have
succeeded still succeeds, with 0 < feeRate < 100% when the shares priced are worth whole base units. -/
theorem Vault.Reachable.isolation (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) -- close times only move forward
    (shares : STAmount) (waive : Bool) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hc : shares.Canonical) -- a transaction amount is a canonical amount
    (hty : shares.mNumericType = .int64) -- of the vault's shares
    (rW : VaultWithAmounts) (hW : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW)) :
    -- a deposit or a donation
    (∀ (amount : STAmount) (isDonation : Bool) (hposX : 0 < amount.toRat) (r : VaultWithAmounts),
      amount.Canonical → amount.mNumericType = v.numericType →
      (v.deposit amount isDonation t hposX).run = .ok (.ok r) →
      ∀ waive' : Bool, ∃ r' : VaultWithAmounts,
        (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r')) ∧
    -- a withdrawal by another holder, of at most its own shares and none of the withdrawn ones
    (∀ (amount : WithdrawAmount) (holderShares : STAmount) (waiveX : Bool) (hposX : 0 < amount.amount.toRat)
        (r : VaultWithAmounts),
      amount.amount.Canonical → amount.InAsset v.numericType → holderShares.ShareBalance →
      (waiveX = true ↔ v.IsSoleShareholder holderShares) →
      (v.withdraw amount waiveX t hposX).run = .ok (.ok r) → r.shares.toRat ≤ holderShares.toRat →
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal →
      -- on an IOU vault under a partial fee, the withdrawn shares are worth whole base units
      (v.earlyExitFeeRateAt t ≠ 0 → v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate →
        v.numericType.isIntegral = false →
        ∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) →
      ∀ waive' : Bool, ∃ r' : VaultWithAmounts,
        (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r')) ∧
    -- a clawback of another holder's shares, none of the withdrawn ones
    (∀ (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      assets.CanonicalOrZero → assets.mNumericType = v.numericType → holderShares.ShareBalance →
      (waiveX = true ↔ v.IsSoleShareholder holderShares) →
      (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r) → r.shares.toRat ≤ holderShares.toRat →
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal →
      -- under a partial fee, the clawed-back shares and the withdrawn shares are worth whole base units
      (v.earlyExitFeeRateAt t ≠ 0 → v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate →
        (∃ k : ℤ, v.idealAssetsWithdraw waiveX r.shares.toRat = k * 10 ^ v.baseExponent) ∧
        ∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) →
      ∀ waive' : Bool, ∃ r' : VaultWithAmounts,
        (r.vault'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r')) ∧
    -- an update by the owner
    (∀ (assetsMaximum : Option Number) (blockDeposit : Option Bool) (v' : Vault),
      v.canVaultUpdate assetsMaximum blockDeposit = .ok .tesSUCCESS →
      v.update assetsMaximum blockDeposit = .ok v' →
      ∀ waive' : Bool, ∃ r' : VaultWithAmounts,
        (v'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r')) ∧
    -- a burn by the owner, which needs an insolvent vault and so never succeeds here
    ∀ (amount holderShares sharesTotalAmount : STAmount) (v' : Vault),
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (v.burnShares holderShares).run = .ok (.ok v') →
      ∀ waive' : Bool, ∃ r' : VaultWithAmounts,
        (v'.withdraw (.vaultShares shares) waive' t hpos).run = .ok (.ok r') :=
  ⟨fun amount isDonation hposX r hcX htyX hok waive' =>
    Vault.Reachable.isolation_deposit_proof v t0 t hr ht shares waive hpos hc hty rW hW amount isDonation hposX hcX
      htyX r hok waive',
    fun amount holderShares waiveX hposX r hcX htyX hhs hsole hok hheld hother hwhole waive' =>
    Vault.Reachable.isolation_withdraw_proof v t0 t hr ht shares waive hpos hc hty rW hW amount holderShares waiveX
      hposX hcX htyX hhs hsole r hok hheld hother hwhole waive',
    fun assets holderShares waiveX hnn r hcX htyX hhs hsole hok hheld hother hwhole waive' =>
    Vault.Reachable.isolation_clawback_proof v t0 t hr ht shares waive hpos hc hty rW hW assets holderShares waiveX
      hnn hcX htyX hhs hsole r hok hheld hother hwhole waive',
    fun assetsMaximum blockDeposit v' hcan hok waive' =>
    Vault.Reachable.isolation_update_proof v t0 t hr ht shares waive hpos hc hty rW hW assetsMaximum blockDeposit
      v' hcan hok waive',
    fun amount holderShares sharesTotalAmount _ hcan _ _ =>
    (Vault.Reachable.isolation_burn_proof v t0 t hr shares waive hpos hc hty rW hW amount holderShares
      sharesTotalAmount hcan).elim⟩

/-- Witness for `Reachable.isolation` on a clawback: under a 75% fee, clawing back IOU shares worth a fraction of a
base unit lowers the per-share value, and a withdrawal of shares worth exactly 4 then pays nothing. -/
theorem Vault.Reachable.isolation_clawback_attained :
    ∃ (v : Vault) (t0 t : UInt32) (shares : STAmount) (waive : Bool)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (rW : VaultWithAmounts)
      (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ shares.Canonical ∧ shares.mNumericType = .int64 ∧
      (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW) ∧
      assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧ holderShares.ShareBalance ∧
      (waiveX = true ↔ v.IsSoleShareholder holderShares) ∧
      (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r) ∧ r.shares.toRat ≤ holderShares.toRat ∧
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal ∧
      v.earlyExitFeeRateAt t ≠ 0 ∧ v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
      (∃ k : ℤ, v.idealAssetsWithdraw waive shares.toRat = k * 10 ^ v.baseExponent) ∧
      (r.vault'.withdraw (.vaultShares shares) waive t hpos).run = .ok (.error .tecPRECISION_LOSS) :=
  Vault.Reachable.isolation_clawback_witness

/-- Witness for `Reachable.isolation` on a clawback worth whole base units: the per-share value stays, but 9089 MPT
shares worth `9090.5` price at 9091 before and at 9090 after, which a 99.989% fee leaves at nothing. -/
theorem Vault.Reachable.isolation_clawback_tie_attained :
    ∃ (v : Vault) (t0 t : UInt32) (shares : STAmount) (waive : Bool)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (rW : VaultWithAmounts)
      (assets holderShares : STAmount) (waiveX : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ shares.Canonical ∧ shares.mNumericType = .int64 ∧
      (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok rW) ∧
      assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧ holderShares.ShareBalance ∧
      (waiveX = true ↔ v.IsSoleShareholder holderShares) ∧
      (v.clawback assets holderShares waiveX hnn).run = .ok (.ok r) ∧ r.shares.toRat ≤ holderShares.toRat ∧
      r.shares.toRat + shares.toRat ≤ v.toExact.sharesTotal ∧
      v.earlyExitFeeRateAt t ≠ 0 ∧ v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
      (∃ k : ℤ, v.idealAssetsWithdraw waiveX r.shares.toRat = k * 10 ^ v.baseExponent) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) = v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) ∧
      (r.vault'.withdraw (.vaultShares shares) waive t hpos).run = .ok (.error .tecPRECISION_LOSS) :=
  Vault.Reachable.isolation_clawback_tie_witness

end XRPL.Model.SingleAssetVault
