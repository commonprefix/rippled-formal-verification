import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witnesses for `withdraw_sharesRedeemed` and `withdraw_payout`

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Truncation: `4577096644444257` assets and shares, withdraw `5005`: ideal `5005` shares, burned
  `5004`, a whole share short.
* Sharp share overshoot: a scale-1 vault of `100000000500000` assets and `100001000500005` shares,
  withdraw `10000000098999.01`: the ideal sits just below a whole share and both `.to_nearest` stages
  round up onto it, so the withdrawal burns more shares than the ideal. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WdTightWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

/-- The closed-ended schedule of the fee witnesses: withdrawals at time 500 are in the investment
phase. -/
def schedule : VaultSchedule := ⟨100, 1000⟩

def vT : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 4577096644444257, false)]
def vS : Vault :=
  createHistory.vault Vault.placeholder .fractional 1 none none 0
    [(iouAmount 1000010005000050 (-2), false), (iouAmount 8999990044999950 (-2), true)]
lemma vT_reach : Vault.Reachable vT 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vS_reach : Vault.Reachable vS 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
def aT : STAmount := int64Amount 5005
def aS : STAmount := iouAmount 1000000009899901 (-2)
lemma aT_pos : 0 < aT.toRat := by native_decide
lemma aS_pos : 0 < aS.toRat := by native_decide

def rT : VaultWithAmounts :=
  ((vT.withdraw (.vaultAssets aT) false 0 aT_pos).run.toOption.bind Except.toOption).getD ⟨⟨aT, aT⟩, vT⟩
def rS : VaultWithAmounts :=
  ((vS.withdraw (.vaultAssets aS) false 0 aS_pos).run.toOption.bind Except.toOption).getD ⟨⟨aS, aS⟩, vS⟩
/-- The net asset value a vault's withdrawal prices at, as the model computes it. -/
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

end XRPL.Model.SingleAssetVault.WdTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdTightWit

/-- Truncation: a withdrawal by assets redeems fewer shares than the ideal rounded down. -/
lemma Vault.withdraw_sharesRedeemed_witness :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  ⟨vT, 0, 0, aT, false, nav vT, aT_pos, rT, vT_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide⟩

/-- Sharp share overshoot: the redeemed shares exceed the ideal rounded down. -/
lemma Vault.withdraw_sharesRedeemed_sharp_witness :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ < r.shares.toRat :=
  ⟨vS, 0, 0, aS, false, nav vS, aS_pos, rS, vS_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
