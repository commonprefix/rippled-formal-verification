import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.VaultValid

/-! # The vault as the lending pool

What the lending operations read from a vault, and the exits of the balance update they make. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The vault holds an IOU, XRP or an MPT. -/
def Vault.HoldsAsset (v : Vault) : Prop :=
  v.numericType = .fractional ∨ v.numericType = .native ∨ v.numericType = .int64

/-- On a vault holding XRP or an MPT, the asset's maximum fits an int64. -/
lemma Vault.HoldsAsset.maxValue_le {v : Vault} (h : Vault.HoldsAsset v) :
    v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
  intro hi
  rcases h with h | h | h <;> rw [h] at hi ⊢
  · cases hi
  all_goals decide

lemma Vault.pool_amounts (v : Vault) : AssetPool.amounts v = {
    assetsAvailable := v.assetsAvailable
    assetsDeployed := v.assetsDeployed
    assetsReserved := v.assetsReserved
    lossUnrealized := v.lossUnrealized
    yieldUnrealized := v.yieldUnrealized } := rfl

lemma Vault.pool_assetsTotal (v : Vault) : AssetPool.assetsTotal v = v.assetsTotal := rfl

lemma Vault.pool_baseExponent (v : Vault) : AssetPool.baseExponent v = v.baseExponent := rfl

lemma Vault.pool_phase (v : Vault) (t : UInt32) : AssetPool.phase v t = v.phase t := rfl

lemma Vault.pool_redemptionDate (v : Vault) :
    AssetPool.redemptionDate v = v.schedule.map (·.redemptionDate) := rfl

lemma Vault.pool_exceedsOpenLimit (v : Vault) (x : Number) :
    AssetPool.exceedsOpenLimit v x = v.exceedsOpenLimit x := rfl

lemma Vault.pool_adjustBalances (v : Vault) (c : PoolBalanceChange) :
    AssetPool.adjustBalances v c = (do let raw ← v.adjustBalances c; raw.to_lawful) := rfl

/-- The vault takes a balance change when the update succeeds and the new vault is lawful. -/
lemma Vault.poolAdjust_ok (v : Vault) (c : PoolBalanceChange) (raw : RawVault) (v' : Vault)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw)) (hv' : raw.to_lawful = .ok v') :
    AssetPool.adjustBalances v c = .ok (.ok v') := by
  rw [Vault.pool_adjustBalances]
  simp only [ExceptT.run] at hadj
  unfold_ter
  simp [hadj, hv']

/-- A balance change the vault takes came from a successful update and a lawful new vault. -/
lemma Vault.poolAdjust_ok_inv (v : Vault) (c : PoolBalanceChange) (v' : Vault)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    ∃ raw, (v.adjustBalances c).run = .ok (.ok raw) ∧ raw.to_lawful = .ok v' := by
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  simp only [ExceptT.run]
  walk_ok
  exact ⟨_, ‹_›, ‹_›⟩

/-- A rejected update rejects the balance change with the same code. -/
lemma Vault.poolAdjust_rejected (v : Vault) (c : PoolBalanceChange) (ter : TER)
    (hadj : (v.adjustBalances c).run = .ok (.error ter)) :
    AssetPool.adjustBalances v c = .ok (.error ter) := by
  rw [Vault.pool_adjustBalances]
  simp only [ExceptT.run] at hadj
  unfold_ter
  simp [hadj]

/-- A balance change the vault rejects was rejected by the update with the same code. -/
lemma Vault.poolAdjust_rejected_parts (v : Vault) (c : PoolBalanceChange) (ter : TER)
    (h : AssetPool.adjustBalances v c = .ok (.error ter)) :
    (v.adjustBalances c).run = .ok (.error ter) := by
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  simp only [ExceptT.run]
  walk_ok
  exact ‹_›

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

/-- Otherwise the update writes the five new balances. -/
lemma Vault.adjustBalances_ok (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hle : lu'.operator_gt ad' = false) :
    (v.adjustBalances c).run = .ok (.ok { v.toRawVault with
      assetsAvailable := aa'
      assetsDeployed := ad'
      assetsReserved := ar'
      lossUnrealized := lu'
      yieldUnrealized := yu' }) := by
  obtain ⟨aa, h1, h2⟩ := hs.cash
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances]
  unfold_ter
  have hb : (decide (aa'.signum < 0) || decide (ad'.signum < 0) || decide (lu'.signum < 0) ||
      decide (yu'.signum < 0) || decide (ar'.signum < 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]; tauto
  simp [h1, h2, hs.deployed, hs.loss, hs.reserved, hs.yield, hb, hle]

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

/-- A balance change the vault takes wrote the five new balances, each the old balance plus its change. -/
lemma Vault.poolAdjust_adjustSums (v : Vault) (c : PoolBalanceChange) (v' : Vault)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    Vault.AdjustSums v c v'.assetsAvailable v'.assetsDeployed v'.lossUnrealized v'.assetsReserved
      v'.yieldUnrealized := by
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok ‹_›).1
  rw [hraw]
  exact ⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- Two lawful vaults with the same record are the same vault. -/
lemma vault_eq_of_raw {a b : Vault} (h : a.toRawVault = b.toRawVault) : a = b := by
  obtain ⟨ra, _, _⟩ := a
  obtain ⟨rb, _, _⟩ := b
  simp only at h
  subst h
  rfl

end XRPL.Model.Lending
