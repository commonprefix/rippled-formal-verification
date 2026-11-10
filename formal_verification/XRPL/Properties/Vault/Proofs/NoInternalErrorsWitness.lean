import XRPL.Properties.Vault.Proofs.Support.ReachableHistory

/-! # Witnesses for internal errors on a reachable vault

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, then deposits.

* Deposit `tecINTERNAL`: an MPT vault of 2 assets and 2 shares, deposit `5000000000000000003`. The 19-digit product
  `2 · 5000000000000000003` rounds up to `10000000000000000010`, so the deposit prices `5000000000000000005` shares,
  worth `5000000000000000005`, two units above the amount.
* `tecPATH_DRY`: a scale-10 IOU vault of 10 assets and `10^11` shares, after two deposits of 5. An amount of `10^9`,
  past the Open limit of `9·10^5`, prices `10^19` shares, past the `int64` maximum, in a deposit, a withdrawal and a
  clawback from a holder of half the shares. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.NoInternalWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

/-- An MPT vault of 2 assets and 2 shares. -/
def vMpt : Vault := createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 2, false)]

/-- A scale-10 IOU vault of 10 assets and `10^11` shares. -/
def vIou : Vault :=
  createHistory.vault Vault.placeholder .fractional 10 none none 0
    [(iouAmount 5000000000000000 (-15), false), (iouAmount 5000000000000000 (-15), false)]

lemma vMpt_reach : Vault.Reachable vMpt 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vIou_reach : Vault.Reachable vIou 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

/-- The MPT deposit that prices one share above the amount. -/
def aMpt : STAmount := int64Amount 5000000000000000003

/-- `10^9` of the IOU, worth `10^19` shares of `vIou`. -/
def aBig : STAmount := iouAmount 1000000000000000 (-6)

/-- A holder of half the shares of `vIou`. -/
def holder : STAmount := int64Amount 50000000000

lemma aMpt_pos : 0 < aMpt.toRat := by native_decide
lemma aBig_pos : 0 < aBig.toRat := by native_decide
lemma aBig_pos' : 0 < (WithdrawAmount.vaultAssets aBig).amount.toRat := aBig_pos

lemma holder_balance : holder.ShareBalance :=
  ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩

lemma holder_not_sole : (false = true ↔ vIou.IsSoleShareholder holder) :=
  ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by native_decide)⟩

end XRPL.Model.SingleAssetVault.NoInternalWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol NoInternalWit

/-- Deposit on a reachable MPT vault of a canonical amount above `10^18` units -> the 19-digit share price can round
up past the amount, and the deposit returns `tecINTERNAL`. -/
lemma Vault.deposit_internal_witness :
    ∃ (v : Vault) (t0 t : UInt32) (amount shares assets : STAmount) (hpos : 0 < amount.toRat),
      Vault.Reachable v t0 ∧ amount.Canonical ∧ amount.mNumericType = v.numericType ∧
      v.numericType.isIntegral = true ∧ amount.toRat = 5000000000000000003 ∧
      assetsToSharesDeposit v amount = .ok shares ∧ sharesToAssetsDeposit v shares = .ok assets ∧
      shares.toRat = 5000000000000000005 ∧ assets.toRat = 5000000000000000005 ∧
      (v.deposit amount false t hpos).run = .ok (.error .tecINTERNAL) :=
  ⟨vMpt, 0, 0, aMpt, int64Amount 5000000000000000005, int64Amount 5000000000000000005, aMpt_pos, vMpt_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Deposit on a reachable IOU vault of an amount past the Open limit, worth more shares than an `int64` holds ->
`tecPATH_DRY`. -/
lemma Vault.deposit_path_dry_witness :
    ∃ (v : Vault) (t0 t : UInt32) (amount : STAmount) (hpos : 0 < amount.toRat),
      Vault.Reachable v t0 ∧ amount.Canonical ∧ amount.mNumericType = v.numericType ∧
      9 * 10 ^ (15 + v.baseExponent) < amount.toRat ∧
      (v.deposit amount false t hpos).run = .ok (.error .tecPATH_DRY) :=
  ⟨vIou, 0, 0, aBig, aBig_pos, vIou_reach, STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide,
    by native_decide, by native_decide⟩

/-- Withdrawal on a reachable IOU vault of an asset amount past the Open limit, worth more shares than an `int64`
holds -> `tecPATH_DRY`. -/
lemma Vault.withdraw_path_dry_witness :
    ∃ (v : Vault) (t0 t : UInt32) (amount : WithdrawAmount) (holderShares : STAmount) (waive : Bool)
      (hpos : 0 < amount.amount.toRat),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧ holderShares.ShareBalance ∧
      (waive = true ↔ v.IsSoleShareholder holderShares) ∧ holderShares.toRat ≤ v.toExact.sharesTotal ∧
      (∃ assets, amount = .vaultAssets assets ∧ 9 * 10 ^ (15 + v.baseExponent) < assets.toRat) ∧
      (v.withdraw amount waive t hpos).run = .ok (.error .tecPATH_DRY) :=
  ⟨vIou, 0, 0, .vaultAssets aBig, holder, false, aBig_pos', vIou_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), show aBig.mNumericType = vIou.numericType by native_decide,
    holder_balance, holder_not_sole, by native_decide, ⟨aBig, rfl, by native_decide⟩, by native_decide⟩

/-- Clawback on a reachable IOU vault of an amount past the Open limit, worth more shares than an `int64` holds ->
`tecPATH_DRY`. -/
lemma Vault.clawback_path_dry_witness :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧
      holderShares.ShareBalance ∧ (waive = true ↔ v.IsSoleShareholder holderShares) ∧
      holderShares.toRat ≤ v.toExact.sharesTotal ∧ 9 * 10 ^ (15 + v.baseExponent) < assets.toRat ∧
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPATH_DRY) :=
  ⟨vIou, 0, aBig, holder, false, aBig_pos.le, vIou_reach,
    Or.inl (STAmount.canonical_of_canonicalB _ (by native_decide)), by native_decide, holder_balance,
    holder_not_sole, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
