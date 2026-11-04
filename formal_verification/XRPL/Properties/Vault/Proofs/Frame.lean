import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultSet
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Protocol.Number.Totality

/-! # What each operation writes

A successful `deposit`, `withdraw` or `clawback` writes only `assetsAvailable` and
`sharesTotal`: the cash-only balance change adds zero to every other balance, which keeps
it as it is. `burnShares` writes only `sharesTotal`, and `update` only `assetsMaximum` and
`depositBlocked`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A cash-only balance change writes only `assetsAvailable`. -/
private lemma Vault.adjustBalances_cash_frame (v : Vault) (rv' : RawVault) (cash : Number)
    (h : (v.adjustBalances { cash := cash }).run = .ok (.ok rv')) :
    ∃ assetsAvailable', rv' = { v.toRawVault with assetsAvailable := assetsAvailable' } := by
  simp only [Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  simp only [Number.operator_add_zero_right, Except.ok.injEq] at *
  subst_vars
  exact ⟨_, rfl⟩

/-- Adjusting the cash and the shares writes only `assetsAvailable` and `sharesTotal`. -/
lemma Vault.adjustAssetsAndShares_frame (v : Vault) (assets shares : STAmount) (rv' : RawVault)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok rv')) :
    ∃ assetsAvailable' sharesTotal',
      rv' = { v.toRawVault with assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  simp only [Vault.adjustAssetsAndShares] at h
  unfold_ter at h
  walk_ok
  obtain ⟨assetsAvailable', rfl⟩ := Vault.adjustBalances_cash_frame _ _ _ ‹_›
  exact ⟨assetsAvailable', _, rfl⟩

/-- A successful deposit writes only `assetsAvailable` and `sharesTotal`. -/
lemma Vault.deposit_frame (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    ∃ assetsAvailable' sharesTotal', r.vault'.toRawVault =
      { v.toRawVault with assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨assetsAvailable', sharesTotal', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    dsimp only
    rw_lawful
    exact ⟨assetsAvailable', sharesTotal', hrv⟩

/-- A deposit keeps the vault's asset. -/
lemma Vault.deposit_numericType (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.numericType = v.numericType := by
  obtain ⟨_, _, hv⟩ := Vault.deposit_frame v _ _ _ _ r hok
  exact (congrArg RawVault.numericType hv).trans rfl

/-- A deposit keeps the vault's base grid. -/
lemma Vault.deposit_baseExponent (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.baseExponent = v.baseExponent := by
  obtain ⟨_, _, hv⟩ := Vault.deposit_frame v _ _ _ _ r hok
  unfold Vault.baseExponent
  rw [show r.vault'.numericType = v.numericType from (congrArg RawVault.numericType hv).trans rfl,
    show r.vault'.scale = v.scale from (congrArg RawVault.scale hv).trans rfl]

/-- A successful withdrawal writes only `assetsAvailable` and `sharesTotal`. -/
lemma Vault.withdraw_frame (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    ∃ assetsAvailable' sharesTotal', r.vault'.toRawVault =
      { v.toRawVault with assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨assetsAvailable', sharesTotal', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    dsimp only
    rw_lawful
    exact ⟨assetsAvailable', sharesTotal', hrv⟩

/-- A successful clawback writes only `assetsAvailable` and `sharesTotal`. -/
lemma Vault.clawback_frame (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ assetsAvailable' sharesTotal', r.vault'.toRawVault =
      { v.toRawVault with assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨assetsAvailable', sharesTotal', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    dsimp only
    rw_lawful
    exact ⟨assetsAvailable', sharesTotal', hrv⟩

/-- A successful burn writes only `sharesTotal`. -/
lemma Vault.burnShares_frame (v : Vault) (sharesDestroyed : STAmount) (v' : Vault)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v')) :
    ∃ sharesTotal', v'.toRawVault = { v.toRawVault with sharesTotal := sharesTotal' } := by
  simp only [Vault.burnShares] at hok
  unfold_ter at hok
  walk_ok
  rw_lawful
  exact ⟨_, rfl⟩

/-- A successful update writes only `assetsMaximum` and `depositBlocked`. -/
lemma Vault.update_frame (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    (v' : Vault) (hok : v.update assetsMaximum blockDeposit unblockDeposit = .ok v') :
    ∃ assetsMaximum' depositBlocked', v'.toRawVault =
      { v.toRawVault with assetsMaximum := assetsMaximum', depositBlocked := depositBlocked' } := by
  unfold Vault.update at hok
  exact ⟨_, _, (RawVault.to_lawful_ok hok).1⟩

end XRPL.Model.SingleAssetVault
