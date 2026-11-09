import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witness for the withdrawal payout with no fee

Each vault comes from a reachable history the model computes: a create, a deposit, then a donation.

* `vI`: an integral vault of 3 assets / 2 shares, one share is worth `1.5` and a withdrawal of it pays `2`
  (ties to even), a full half unit above the worth. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WdPriceWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

/-- An integral vault: deposit `d`, then donate `g`. -/
def intVault (d g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount d, false), (int64Amount g, true)]

def vI : Vault := intVault 2 1

lemma vI_reach : Vault.Reachable vI 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
/-- One share. -/
def one : STAmount := int64Amount 1

lemma one_canonical : one.Canonical := STAmount.canonical_of_canonicalB _ (by native_decide)

lemma oneShare_pos : 0 < one.toRat := by native_decide

/-- The withdrawal of one share from `vI`, as the model computes it. -/
def wdOne : VaultWithAmounts :=
  ((vI.withdraw (.vaultShares one) false 0 oneShare_pos).run.toOption.bind Except.toOption).getD ⟨⟨one, one⟩, vI⟩

/-- The net asset value a vault's withdrawal prices at, as the model computes it. -/
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

end XRPL.Model.SingleAssetVault.WdPriceWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdPriceWit

/-- Integral overshoot: a withdrawal with no fee of one share worth `1.5` pays `2`. -/
lemma Vault.withdraw_payout_worth_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧ v.earlyExitFeeRateAt t = 0 ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat < r.assets.toRat :=
  ⟨vI, 0, 0, .vaultShares one, false, oneShare_pos, wdOne, nav vI, vI_reach, one_canonical, rfl, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
