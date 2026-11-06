import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.OpenZone
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Reachability induction proofs

Induction on `Vault.Reachable`: the base case reads the created record, and each step case uses
the frame facts of `Frame.lean` and the Open-zone steps of `OpenZone.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- No vault transaction lends: a reachable vault has nothing deployed, no unrealized loss and no
unrealized yield. -/
lemma Vault.Reachable.noLending_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.assetsDeployed = Number.zero ∧ v.lossUnrealized = Number.zero ∧ v.yieldUnrealized = Number.zero := by
  induction hr with
  | create _ _ _ _ _ _ _ _ _ hcr =>
    have hv := Vault.create_ok_toRawVault hcr
    exact ⟨(congrArg RawVault.assetsDeployed hv).trans rfl, (congrArg RawVault.lossUnrealized hv).trans rfl,
      (congrArg RawVault.yieldUnrealized hv).trans rfl⟩
  | deposit u _ _ _ _ r _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    exact ⟨((congrArg RawVault.assetsDeployed hv).trans rfl).trans ih.1,
      ((congrArg RawVault.lossUnrealized hv).trans rfl).trans ih.2.1,
      ((congrArg RawVault.yieldUnrealized hv).trans rfl).trans ih.2.2⟩
  | withdraw u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    exact ⟨((congrArg RawVault.assetsDeployed hv).trans rfl).trans ih.1,
      ((congrArg RawVault.lossUnrealized hv).trans rfl).trans ih.2.1,
      ((congrArg RawVault.yieldUnrealized hv).trans rfl).trans ih.2.2⟩
  | clawback u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    exact ⟨((congrArg RawVault.assetsDeployed hv).trans rfl).trans ih.1,
      ((congrArg RawVault.lossUnrealized hv).trans rfl).trans ih.2.1,
      ((congrArg RawVault.yieldUnrealized hv).trans rfl).trans ih.2.2⟩
  | burnShares u _ _ _ _ _ u' _ _ _ _ hok ih =>
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    exact ⟨((congrArg RawVault.assetsDeployed hv).trans rfl).trans ih.1,
      ((congrArg RawVault.lossUnrealized hv).trans rfl).trans ih.2.1,
      ((congrArg RawVault.yieldUnrealized hv).trans rfl).trans ih.2.2⟩
  | update u _ _ _ _ _ u' _ _ _ hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    exact ⟨((congrArg RawVault.assetsDeployed hv).trans rfl).trans ih.1,
      ((congrArg RawVault.lossUnrealized hv).trans rfl).trans ih.2.1,
      ((congrArg RawVault.yieldUnrealized hv).trans rfl).trans ih.2.2⟩

/-- Every reachable vault is in the Open zone, for an asset whose integral maximum fits an
`int64`. The asset never changes along a history, so the condition holds at every step. -/
lemma Vault.Reachable.openZone_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) : v.OpenZone := by
  induction hr with
  | create _ _ _ _ _ _ _ _ _ hcr => exact Vault.create_openZone hcr
  | deposit u _ _ _ _ r _ _ hc hty _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    exact (Vault.deposit_openZone u _ _ _ _ hc hty (ih (hnt ▸ hmax)) r hok).2
  | withdraw u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    exact (Vault.withdraw_openZone u _ _ _ _ (ih (hnt ▸ hmax)) (hnt ▸ hmax) r hok).2
  | clawback u _ _ _ _ _ r _ _ hc _ hhs _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    exact (Vault.clawback_openZone u _ _ _ _ hc hhs (hnt ▸ hmax) (ih (hnt ▸ hmax)) r hok).2
  | burnShares u _ _ _ _ _ u' _ _ _ _ hok ih =>
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    exact Vault.burnShares_openZone u _ u' (ih (hnt ▸ hmax)) hok
  | update u _ _ _ _ _ u' _ _ _ hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    exact Vault.update_openZone u _ _ _ u' (ih (hnt ▸ hmax)) hok

lemma Vault.Reachable.lossUnrealized_zero_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.toExact.lossUnrealized = 0 := by
  show v.lossUnrealized.toRat = 0
  rw [(Vault.Reachable.noLending_proof v t hr).2.1, Number.toRat_zero]

lemma Vault.Reachable.asset_parity_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.assetsTotal = .ok v.assetsAvailable :=
  Vault.assetsTotal_of_noLending v (Vault.Reachable.noLending_proof v t hr).1

lemma Vault.Reachable.withdrawNavExact_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) (w : Bool) :
    v.WithdrawNavExact w :=
  Vault.withdrawNavExact_of_noLending v (Vault.Reachable.noLending_proof v t hr).1 w

/-- A reachable vault prices at its cash: nothing is lent, so there is no loss to subtract. -/
lemma Vault.Reachable.nav_eq_cash (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (nav : Number) (hsub : v.assetsTotalForWithdrawal waive = .ok nav) :
    nav.toRat = v.assetsAvailable.toRat :=
  congrArg Number.toRat (Except.ok.inj (hsub.symm.trans
    (Vault.assetsTotalForWithdrawal_of_noLending v (Vault.Reachable.noLending_proof v t0 hr).1 waive)))

/-- The cash of an Open-zone vault stays within the Open-zone limit. -/
lemma Vault.OpenZone.assetsAvailable_le_openLimit {v : Vault} (hz : v.OpenZone) :
    v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) := by
  obtain ⟨k, hk, hkv⟩ := hz.cash
  have hk' : (k : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hk
  rw [hkv, zpow_add₀ (by norm_num)]
  have hpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  push_cast
  nlinarith

lemma Vault.deposit_vault_updates_exact_proof (v : Vault) (amount : STAmount) (isDonation : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.toRat) (hr : Vault.Reachable v t0) (hc : amount.Canonical)
    (hty : amount.mNumericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.assets.toRat ∧
      (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal + r.shares.toRat :=
  ⟨(Vault.deposit_openZone v amount isDonation t hpos hc hty (Vault.Reachable.openZone_proof v t0 hr hmax) r hok).1,
    Vault.deposit_exact_sharesTotal v amount isDonation t hpos hc hty r hok hSsz⟩

lemma Vault.withdraw_vault_updates_exact_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
      (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat :=
  ⟨(Vault.withdraw_openZone v amount waive t hpos (Vault.Reachable.openZone_proof v t0 hr hmax) hmax r hok).1,
    Vault.withdraw_exact_sharesTotal v amount waive t hpos hc hty r hok⟩

lemma Vault.clawback_vault_updates_exact_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (t0 : UInt32) (hnn : 0 ≤ assets.toRat) (hr : Vault.Reachable v t0) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
      (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat :=
  ⟨(Vault.clawback_openZone v assets holderShares waive hnn hc hhs hmax (Vault.Reachable.openZone_proof v t0 hr hmax)
      r hok).1,
    Vault.clawback_exact_sharesTotal v assets holderShares waive hnn hc hhs hmax r hok⟩

/-- No vault transaction reserves assets. -/
lemma Vault.Reachable.assetsReserved_zero_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.assetsReserved = Number.zero := by
  induction hr with
  | create _ _ _ _ _ _ _ _ _ hcr => exact (congrArg RawVault.assetsReserved (Vault.create_ok_toRawVault hcr)).trans rfl
  | deposit u _ _ _ _ r _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    exact ((congrArg RawVault.assetsReserved hv).trans rfl).trans ih
  | withdraw u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    exact ((congrArg RawVault.assetsReserved hv).trans rfl).trans ih
  | clawback u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    exact ((congrArg RawVault.assetsReserved hv).trans rfl).trans ih
  | burnShares u _ _ _ _ _ u' _ _ _ _ hok ih =>
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    exact ((congrArg RawVault.assetsReserved hv).trans rfl).trans ih
  | update u _ _ _ _ _ u' _ _ _ hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    exact ((congrArg RawVault.assetsReserved hv).trans rfl).trans ih

/-- The asset stores a reachable vault's maximum exactly: creation and updates only accept a
maximum on the base grid. -/
lemma Vault.Reachable.assetsMaximum_exact_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    ∀ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m = false := by
  induction hr with
  | create _ amax _ _ _ nt _ w hcan hcr =>
    intro m hm
    have hv := Vault.create_ok_toRawVault hcr
    have hmax : w.assetsMaximum = _ := (congrArg RawVault.assetsMaximum hv).trans rfl
    have hnt : w.numericType = nt := (congrArg RawVault.numericType hv).trans rfl
    rw [hmax] at hm
    -- a kept maximum is one the creation named
    have hm' : m ∈ amax := by
      clear hcan hcr hv
      cases amax with
      | none => simp at hm
      | some b =>
        simp only [Option.filter, Option.mem_def] at hm ⊢
        split at hm <;> simp_all
    rw [hnt]
    exact Number.isRounded_eq_false_of_isOnExponentGrid _ _ _ (Vault.canCreate_assetsMaximum _ _ _ _ _ hcan m hm')
  | deposit u _ _ _ _ r _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    rw [(congrArg RawVault.assetsMaximum hv).trans rfl, (congrArg RawVault.numericType hv).trans rfl]; exact ih
  | withdraw u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    rw [(congrArg RawVault.assetsMaximum hv).trans rfl, (congrArg RawVault.numericType hv).trans rfl]; exact ih
  | clawback u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    rw [(congrArg RawVault.assetsMaximum hv).trans rfl, (congrArg RawVault.numericType hv).trans rfl]; exact ih
  | burnShares u _ _ _ _ _ u' _ _ _ _ hok ih =>
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    rw [(congrArg RawVault.assetsMaximum hv).trans rfl, (congrArg RawVault.numericType hv).trans rfl]; exact ih
  | update u _ _ assetsMaximum _ _ u' _ _ hcan hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    rw [(congrArg RawVault.numericType hv).trans rfl]
    intro m hm
    rcases Vault.update_assetsMaximum_mem u _ _ _ u' hok m hm with h | h
    · exact ih m h
    · subst h
      exact Number.isRounded_eq_false_of_isOnExponentGrid _ _ _ (Vault.canVaultUpdate_assetsMaximum u m _ _ hcan)

/-- `associateAsset` is a no-op on a reachable vault whose cash is stored exactly: every other amount
it rounds is zero or a maximum on the base grid. -/
lemma Vault.Reachable.associateAsset_noop_of_cashExact (v : Vault) (t : UInt32) (hr : Vault.Reachable v t)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false) : ¬ v.assetsRounded := by
  obtain ⟨hAD, hLU, hYU⟩ := Vault.Reachable.noLending_proof v t hr
  have hAR := Vault.Reachable.assetsReserved_zero_proof v t hr
  have hM := Vault.Reachable.assetsMaximum_exact_proof v t hr
  unfold Vault.assetsRounded
  rw [hAD, hLU, hYU, hAR, hAA, STAmount.isRounded_zero]
  rintro (h | h | h | h | h | ⟨m, hm, h⟩)
  all_goals simp_all

end XRPL.Model.SingleAssetVault
