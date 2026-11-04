import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witnesses for the tight `withdraw_sharesBurned` and `withdraw_payout` bounds

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Truncation: `4577096644444257` assets and shares, withdraw `5005`: ideal `5005` shares, burned
  `5004`, a whole share short.
* Sharp share overshoot: a scale-1 vault of `100000000500000` assets and `100001000500005` shares,
  withdraw `10000000098999.01`: the ideal sits just below a whole share and both `.to_nearest` stages
  round up onto it, so the withdrawal burns more shares than the ideal.
* Payout at the bound: 3 assets and 2 shares, burn 1: priced `2`, paid `2`.
* Integral payout shortfall: `200002` assets and shares at a `0.001%` fee, burn `100001`: worth
  `99999.99999` after the fee, paid `99999`. -/

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
def vP : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 2, false), (int64Amount 1, true)]
def vN : Vault :=
  createHistory.vault Vault.placeholder .int64 0 (some schedule) (some 1) 0 [(int64Amount 200002, false)]

lemma vT_reach : Vault.Reachable vT 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vS_reach : Vault.Reachable vS 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vN_reach : Vault.Reachable vN 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def aT : STAmount := int64Amount 5005
def aS : STAmount := iouAmount 1000000009899901 (-2)
lemma aT_pos : 0 < aT.toRat := by native_decide
lemma aS_pos : 0 < aS.toRat := by native_decide

/-- Burning `n` shares. -/
def burn (n : UInt64) : WithdrawAmount := .vaultShares (int64Amount n)

lemma burn1_pos : 0 < (burn 1).amount.toRat := by native_decide
lemma burnN_pos : 0 < (burn 100001).amount.toRat := by native_decide

def rT : VaultWithAmounts :=
  ((vT.withdraw (.vaultAssets aT) false 0 aT_pos).run.toOption.bind Except.toOption).getD ⟨⟨aT, aT⟩, vT⟩
def rS : VaultWithAmounts :=
  ((vS.withdraw (.vaultAssets aS) false 0 aS_pos).run.toOption.bind Except.toOption).getD ⟨⟨aS, aS⟩, vS⟩
def rP : VaultWithAmounts :=
  ((vP.withdraw (burn 1) false 0 (burn1_pos)).run.toOption.bind Except.toOption).getD
    ⟨⟨aT, aT⟩, vP⟩
def rN : VaultWithAmounts :=
  ((vN.withdraw (burn 100001) false 500 (burnN_pos)).run.toOption.bind
    Except.toOption).getD ⟨⟨aT, aT⟩, vN⟩

/-- The net asset value a vault's withdrawal prices at, as the model computes it. -/
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

/-- The priced amount of `n` shares. -/
def priced (v : Vault) (n : UInt64) : STAmount :=
  (v.sharesToAssetsWithdraw (int64Amount n) false).toOption.getD (int64Amount 0)

end XRPL.Model.SingleAssetVault.WdTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdTightWit

/-- Truncation: a withdrawal by assets burns a whole share less than the ideal. -/
lemma Vault.withdraw_sharesBurned_witness :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - 1 :=
  ⟨vT, 0, 0, aT, false, aT_pos, rT, vT_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide⟩

/-- Sharp share overshoot: the burned shares exceed the ideal. -/
lemma Vault.withdraw_sharesBurned_sharp_witness :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat < r.shares.toRat :=
  ⟨vS, 0, 0, aS, false, aS_pos, rS, vS_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide⟩

/-- `_total` truncation: a whole share short of the ideal at the computed net asset value. -/
lemma Vault.withdraw_sharesBurned_total_witness :
    ∃ (v : Vault) (t : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - 1 :=
  ⟨vT, 0, aT, false, nav vT, aT_pos, rT, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide⟩

/-- `_total` sharp overshoot: above the ideal at the computed net asset value. -/
lemma Vault.withdraw_sharesBurned_total_sharp_witness :
    ∃ (v : Vault) (t : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat < r.shares.toRat :=
  ⟨vS, 0, aS, false, nav vS, aS_pos, rS, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide⟩

/-- `_total` payout at the bound: with no fee the payout is the whole priced amount. -/
lemma Vault.withdraw_payout_total_witness :
    ∃ (v : Vault) (t : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        r.assets.toRat = priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) :=
  ⟨vP, 0, burn 1, false, burn1_pos, rP,
    STAmount.canonical_of_canonicalB _ (by native_decide), rfl, fun _ => by native_decide, by native_decide,
    by native_decide, priced vP 1, by native_decide, by native_decide⟩

/-- Integral payout shortfall: `1 - 10⁻⁵` of a unit. -/
lemma Vault.withdraw_payout_integral_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      v.numericType.isIntegral = true ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) - r.assets.toRat = 1 - 1 / 10 ^ 5 :=
  ⟨vN, 500, 0, burn 100001, false, burnN_pos, rN, vN_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), rfl, by native_decide,
    by native_decide, by native_decide, priced vN 100001, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
