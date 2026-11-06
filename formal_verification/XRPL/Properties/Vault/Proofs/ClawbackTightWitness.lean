import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.ClawbackDefs

/-! # Witnesses for the clawback share count and recovery

Each run's result is computed by the model and checked by `native_decide`. Every vault but the one capped
above the ideal comes from a reachable history: a create, a deposit, then a donation.

* Truncation: `4577096644444257` assets and shares, claw back `5005`: ideal `5005` shares, destroyed
  `5004`.
* Sharp share overshoot: a scale-1 vault of `100000000500000` assets and `100001000500005` shares,
  claw back `10000000098999.01`: the clawback destroys more shares than the ideal.
* Capped: `6564360495` assets and shares, claw back `4168` more than the cash: the recovery is capped
  at the cash, whose share price `6564360495` is truncated to `6564360494`.
* Capped above the ideal: a lawful vault of cash 1, 2 deployed and `3000000000000000002` shares, claw back 2: the
  ideal for the cash is `1000000000000000000.67`, and the 19-digit price rounds it up to a whole share.
* Recovery overshoot: 3 assets and 2 shares, claw back `2`: one share, worth `1.5`, recovered `2`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.ClawTightWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

def intVault (d g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0
    (if g = 0 then [(int64Amount d, false)] else [(int64Amount d, false), (int64Amount g, true)])

def vT : Vault := intVault 4577096644444257 0
def vS : Vault :=
  createHistory.vault Vault.placeholder .fractional 1 none none 0
    [(iouAmount 1000010005000050 (-2), false), (iouAmount 8999990044999950 (-2), true)]
def vC : Vault := intVault 6564360495 0
def vO : Vault := intVault 2 1
lemma vT_reach : Vault.Reachable vT 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vS_reach : Vault.Reachable vS 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vC_reach : Vault.Reachable vC 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vO_reach : Vault.Reachable vO 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
/-- A valid `int64` vault of cash 1, 2 deployed and `3000000000000000002` shares. -/
def rawBig : RawVault :=
  { assetsAvailable := ⟨false, 1000000000000000000, -18⟩, assetsDeployed := ⟨false, 2000000000000000000, -18⟩
    assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0
    sharesTotal := ⟨false, 3000000000000000002, 0⟩, lossUnrealized := Number.zero
    yieldUnrealized := Number.zero, schedule := none, earlyExitFeeRate := none
    ownerCanBlockDeposit := false, depositBlocked := false }

def vBig : Vault := ⟨rawBig, by native_decide, by native_decide⟩

def aT : STAmount := int64Amount 5005
def aS : STAmount := iouAmount 1000000009899901 (-2)
def aC : STAmount := int64Amount 6564364663
def aO : STAmount := int64Amount 2
def aBig : STAmount := int64Amount 2

/-- The holder's balance: one share is enough, a positive clawback amount sets the shares. -/
def hold : STAmount := int64Amount 1

/-- A clawback's result, computed by the model. -/
def run (v : Vault) (a : STAmount) (h : 0 ≤ a.toRat) : VaultWithAmounts :=
  ((v.clawback a hold false h).run.toOption.bind Except.toOption).getD ⟨⟨a, a⟩, v⟩

/-- The shares an amount prices to, then the worth of those shares, as the model computes them. -/
def shares (v : Vault) (a : STAmount) : STAmount :=
  (assetsToSharesWithdraw v a true false).toOption.getD a
def worth (v : Vault) (s : STAmount) : STAmount := (v.sharesToAssetsWithdraw s false).toOption.getD s
def number (a : STAmount) : Number := (a.toNumber .to_nearest).toOption.getD Number.zero
def cashAmount (v : Vault) : STAmount :=
  (STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest).toOption.getD (int64Amount 0)

/-- The net asset value a vault's clawback prices at, as the model computes it. -/
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

lemma aT_nn : 0 ≤ aT.toRat := by native_decide
lemma aS_nn : 0 ≤ aS.toRat := by native_decide
lemma aC_nn : 0 ≤ aC.toRat := by native_decide
lemma aO_nn : 0 ≤ aO.toRat := by native_decide
lemma aBig_nn : 0 ≤ aBig.toRat := by native_decide

end XRPL.Model.SingleAssetVault.ClawTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol ClawTightWit

/-- Truncation: a clawback destroys fewer shares than the ideal rounded down. -/
lemma Vault.clawback_sharesDestroyed_witness :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat < ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  ⟨vT, 0, aT, hold, shares vT aT, worth vT (shares vT aT), false, number (worth vT (shares vT aT)), nav vT,
    aT_nn, run vT aT aT_nn, vT_reach, by native_decide, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Sharp share overshoot: above the ideal rounded down. -/
lemma Vault.clawback_sharesDestroyed_upper_witness :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ < r.shares.toRat :=
  ⟨vS, 0, aS, hold, shares vS aS, worth vS (shares vS aS), false, number (worth vS (shares vS aS)), nav vS,
    aS_nn, run vS aS aS_nn, vS_reach, by native_decide, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Capped: a recovery capped at the cash destroys fewer shares than the ideal for the cash rounded down. -/
lemma Vault.clawback_sharesDestroyed_clamped_witness :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat < ⌊v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat⌋ :=
  ⟨vC, 0, aC, hold, shares vC aC, worth vC (shares vC aC), cashAmount vC, false,
    number (worth vC (shares vC aC)), nav vC, aC_nn, run vC aC aC_nn, vC_reach, by native_decide,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Capped above the ideal: on a lawful vault the capped recovery destroys more shares than the ideal for
the cash at the computed net asset value. -/
lemma Vault.clawback_sharesDestroyed_clamped_total_upper_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      ⌊v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat⌋ < r.shares.toRat :=
  ⟨vBig, aBig, hold, shares vBig aBig, worth vBig (shares vBig aBig), cashAmount vBig, false,
    number (worth vBig (shares vBig aBig)), nav vBig, aBig_nn, run vBig aBig aBig_nn, by native_decide,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Recovery overshoot: half a unit above the destroyed shares' worth. -/
lemma Vault.clawback_assetsRecovered_upper_witness :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧ assets.isZero = false ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat < r.assets.toRat :=
  ⟨vO, 0, aO, hold, false, aO_nn, run vO aO aO_nn, vO_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, fun _ => by native_decide,
    by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
