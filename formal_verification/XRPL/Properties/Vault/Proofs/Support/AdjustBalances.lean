import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.TotalStores

/-! # Vault balance updates by the lending operations

The exits of `Vault.adjustBalances`, the update a lending operation makes to the vault's balances. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Lending (PoolBalanceChange)

/-- The new balances of a vault update, each the old balance plus its change. The new
AssetsAvailable is rounded to the vault's asset. -/
structure Vault.AdjustSums (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number) : Prop where
  cash : ∃ aa, v.assetsAvailable.operator_add c.cash .to_nearest = .ok aa ∧
    STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa'
  deployed : v.assetsDeployed.operator_add c.deployed .to_nearest = .ok ad'
  loss : v.lossUnrealized.operator_add c.loss .to_nearest = .ok lu'
  reserved : v.assetsReserved.operator_add c.reserved .to_nearest = .ok ar'
  yield : v.yieldUnrealized.operator_add c.yield .to_nearest = .ok yu'

/-- An update that leaves a balance negative -> tefBAD_LEDGER. -/
lemma Vault.adjustBalances_bad_ledger (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hneg : aa'.signum < 0 ∨ ad'.signum < 0 ∨ lu'.signum < 0 ∨ yu'.signum < 0 ∨ ar'.signum < 0) :
    (v.adjustBalances c).run = .ok (.error .tefBAD_LEDGER) := by
  obtain ⟨aa, h1, h2⟩ := hs.cash
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances]
  unfold_ter
  have hb : (decide (aa'.signum < 0) || decide (ad'.signum < 0) || decide (lu'.signum < 0) ||
      decide (yu'.signum < 0) || decide (ar'.signum < 0)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto
  simp [h1, h2, hs.deployed, hs.loss, hs.reserved, hs.yield, hb]

/-- An update that leaves LossUnrealized above AssetsDeployed -> tecLIMIT_EXCEEDED. -/
lemma Vault.adjustBalances_limit_exceeded (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hgt : lu'.operator_gt ad' = true) :
    (v.adjustBalances c).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨aa, h1, h2⟩ := hs.cash
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances]
  unfold_ter
  have hb : (decide (aa'.signum < 0) || decide (ad'.signum < 0) || decide (lu'.signum < 0) ||
      decide (yu'.signum < 0) || decide (ar'.signum < 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]; tauto
  simp [h1, h2, hs.deployed, hs.loss, hs.reserved, hs.yield, hb, hgt]

/-- Otherwise the update writes the five new balances, when the new total is an amount of the asset
(C++ `syncAssetsTotal`). -/
lemma Vault.adjustBalances_ok (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hle : lu'.operator_gt ad' = false) (hst : TotalStores v.numericType aa' ad') :
    (v.adjustBalances c).run = .ok (.ok { v.toRawVault with
      assetsAvailable := aa'
      assetsDeployed := ad'
      assetsReserved := ar'
      lossUnrealized := lu'
      yieldUnrealized := yu' }) := by
  obtain ⟨aa, h1, h2⟩ := hs.cash
  obtain ⟨total, amount, htotal, hamount⟩ := hst
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances]
  unfold_ter
  have hb : (decide (aa'.signum < 0) || decide (ad'.signum < 0) || decide (lu'.signum < 0) ||
      decide (yu'.signum < 0) || decide (ar'.signum < 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]; tauto
  simp [h1, h2, hs.deployed, hs.loss, hs.reserved, hs.yield, hb, hle, RawVault.assetsTotal, htotal, hamount]

/-- A successful vault update left a total that is an amount of the asset. -/
lemma Vault.adjustBalances_ok_totalStores (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    TotalStores v.numericType raw.assetsAvailable raw.assetsDeployed := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  exact ⟨_, _, ‹_›, ‹_›⟩

/-- A successful vault update wrote the five new balances, each the old balance plus its change. -/
lemma Vault.adjustBalances_ok_parts (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    ∃ aa' ad' lu' ar' yu', Vault.AdjustSums v c aa' ad' lu' ar' yu' ∧
      (0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum) ∧
      lu'.operator_gt ad' = false ∧
      raw = { v.toRawVault with
        assetsAvailable := aa'
        assetsDeployed := ad'
        assetsReserved := ar'
        lossUnrealized := lu'
        yieldUnrealized := yu' } := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  refine ⟨_, _, _, _, _, ⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, ?_, by simpa using ‹¬ _ = true›, rfl⟩
  have hc := ‹¬ (_ || _) = true›
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hc
  tauto

/-- A vault update that passes wrote the five sums. -/
lemma Vault.adjustBalances_ok_inv (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    Vault.AdjustSums v c raw.assetsAvailable raw.assetsDeployed raw.lossUnrealized raw.assetsReserved
      raw.yieldUnrealized ∧
    raw = { v.toRawVault with
      assetsAvailable := raw.assetsAvailable, assetsDeployed := raw.assetsDeployed,
      assetsReserved := raw.assetsReserved, lossUnrealized := raw.lossUnrealized,
      yieldUnrealized := raw.yieldUnrealized } := by
  simp only [ExceptT.run, XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  exact ⟨⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, rfl⟩

end XRPL.Model.SingleAssetVault
