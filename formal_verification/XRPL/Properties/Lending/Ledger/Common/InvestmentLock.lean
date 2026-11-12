import XRPL.Properties.Lending.Ledger.Common.RedemptionRecovery
import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # What can take AssetsAvailable down in the investment phase

A deposit that is not a donation is refused, a donation adds a nonnegative charge, and a withdrawal needs an
early-exit fee rate. The other vault and broker transactions leave AssetsAvailable as it is. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault WithdrawAmount VaultWithAmounts)

/-- A deposit that is not a donation is refused in the investment phase. -/
private lemma Vault.deposit_not_investment (v : Vault) (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat)
    (hinv : v.phase t = .investment) (r : VaultWithAmounts) (h : (v.deposit amount false t hpos).run = .ok (.ok r)) :
    False := by
  simp only [XRPL.Model.SingleAssetVault.Vault.deposit, hinv] at h
  unfold_ter at h
  simp at h

/-- A withdrawal in the investment phase needs an early-exit fee rate. -/
private lemma Vault.withdraw_investment_fee (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hs : Option Number) (hinv : v.phase t = .investment) (r : VaultWithAmounts)
    (h : (v.withdraw amount waive t hpos hs).run = .ok (.ok r)) : v.earlyExitFeeRate.isSome = true := by
  cases hf : v.earlyExitFeeRate with
  | some _ => rfl
  | none =>
    exfalso
    simp only [XRPL.Model.SingleAssetVault.Vault.withdraw, hf, hinv] at h
    unfold_ter at h
    simp at h

/-- A vault transaction writes its vault. -/
private lemma LendingLedger.commitVault_vault' (l : LendingLedger) (u : VaultEffect) :
    (l.commitVault u).vault = u.vault := by
  unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]

/-- A donation adds a nonnegative amount. -/
private lemma LendingLedger.depositedAssets_nonneg (l : LendingLedger) (amount : STAmount) (isDonation : Bool)
    (hc : amount.Canonical) (hty : amount.mNumericType = l.vault.numericType) :
    0 ≤ l.depositedAssets amount isDonation := by
  unfold LendingLedger.depositedAssets
  split
  · rename_i hpos
    split
    · rename_i r hok
      exact (XRPL.Model.SingleAssetVault.Vault.deposit_charge_form _ _ _ _ hpos hc hty r hok).2.2
    · exact le_refl 0
  · exact le_refl 0

open XRPL.Model.SingleAssetVault in
/-- A donation that succeeds passed the Open-limit check, so the vault it went into was not coarsened. -/
private lemma Vault.donation_notCoarsened (v : Vault) (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat)
    (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType) (hasset : Vault.HoldsAsset v)
    (hv : Vault.OnBaseGrid v) (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (r : VaultWithAmounts) (h : (v.deposit amount true t hpos).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨ra, amounts, -, hra, hcomp, hin, -, -, -, -⟩ := Vault.deposit_ok_reduces v amount true t hpos r h
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra true amounts hrac hraty hasset.maxValue_le hcomp
  obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
  obtain ⟨k, hk⟩ := Vault.clamp_grid v _ _ _ hrac hcl
  obtain ⟨x, hnum, hex⟩ := Vault.checkOpenLimit_ok_inv v _ hin
  obtain ⟨hxv, hxn⟩ := hcf.toNumber_exact x hnum
  have hb := Vault.exceedsOpenLimit_false_sum v x hv hYg ⟨hxn, k, by rw [hxv, hk]⟩ (by rw [hxv]; exact hc0) hex
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hx0 : 0 ≤ x.toRat := by rw [hxv]; exact hc0
  linarith

/-- A donation that succeeds on a reachable ledger was made to a vault that is not coarsened. -/
private lemma LendingLedger.donation_notCoarsened (l l' : LendingLedger) (hr : l.Reachable) (holder : Nat)
    (amount : STAmount) (h : (l.apply (.vaultDeposit holder amount true)).run = .ok (.ok l')) : l.NotCoarsened := by
  obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l holder amount true hr.holdsAsset
    (LendingLedger.apply_checked h).1
  obtain ⟨hAAg, hADg, -, -, hYg, -⟩ := LendingLedger.base_grid_proof l hr hr.holdsAsset.maxValue_le
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_vault rfl h
  simp only [LendingLedger.applyVault] at hu
  split at hu
  · unfold_ter at hu
    walk_ok
    exact Vault.donation_notCoarsened _ _ _ _ hc hty hr.holdsAsset ⟨hAAg, hADg⟩ hYg _ ‹_›
  · cases hu

/-- Proof body of `Lending.investment_lock`. -/
lemma LendingLedger.investment_lock_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hinv : l.vault.phase l.now = .investment) (h : (l.apply tx).run = .ok (.ok l'))
    (hdec : l'.vault.assetsAvailable.toRat < l.vault.assetsAvailable.toRat) :
    tx.isLoan = true ∨
      (∃ holder amount, tx = .vaultWithdraw holder amount ∧ l.vault.earlyExitFeeRate.isSome = true) ∨
      ∃ holder assets, tx = .vaultClawback holder assets := by
  cases tx with
  | vaultDeposit holder amount isDonation =>
    exfalso
    cases isDonation
    · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · unfold_ter at hu
        walk_ok
        exact Vault.deposit_not_investment _ _ _ _ hinv _ ‹_›
      · cases hu
    · -- a donation adds its charge to AssetsAvailable + AssetsDeployed and keeps AssetsDeployed
      have hnc := LendingLedger.donation_notCoarsened l l' hr holder amount h
      have hflow : l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat =
          l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat +
            (l.depositedAssets amount true - 0 - 0 + 0 - 0) :=
        LendingLedger.flow_step l l' _ hr h hnc (by rintro ⟨_, _, _, ⟨⟩⟩)
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l holder amount true hr.holdsAsset
        (LendingLedger.apply_checked h).1
      have hdep := LendingLedger.depositedAssets_nonneg l amount true hc hty
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
      have hAD := (LendingLedger.applyVault_keepsLending l _ u hu).assetsDeployed
      rw [LendingLedger.commitVault_vault'] at hflow hdec
      rw [hAD] at hflow
      linarith
  | vaultWithdraw holder amount =>
    refine Or.inr (Or.inl ⟨holder, amount, rfl, ?_⟩)
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      exact Vault.withdraw_investment_fee _ _ _ _ _ _ hinv _ ‹_›
    · cases hu
  | vaultClawback holder assets => exact Or.inr (Or.inr ⟨holder, assets, rfl⟩)
  | vaultBurnShares holder amount =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
    rw [LendingLedger.commitVault_vault'] at hdec
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    rw [show RawVault.assetsAvailable _ = _ from (congrArg RawVault.assetsAvailable hf :)] at hdec
    exact lt_irrefl _ hdec
  | vaultSet m b ub =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
    rw [LendingLedger.commitVault_vault'] at hdec
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
    rw [show RawVault.assetsAvailable _ = _ from (congrArg RawVault.assetsAvailable hf :)] at hdec
    exact lt_irrefl _ hdec
  | vaultDelete =>
    exfalso
    have hc := (LendingLedger.apply_checked h).2
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact lt_irrefl _ hdec
  | loanBrokerCreate _ | loanBrokerUpdate _ _ | loanBrokerCoverDeposit _ _ | loanBrokerCoverWithdraw _ _
  | loanBrokerCoverClawback _ _ | loanBrokerDelete _ =>
    exfalso
    rw [(LendingLedger.broker_ops_scope_proof l l' _ rfl h).2.2.1] at hdec
    exact lt_irrefl _ hdec
  | loanSet _ _ _ _ _ _ _ _ _ _ | loanAccept _ | loanDelete _ | loanManage _ _ | loanPay _ _ _ => exact Or.inl rfl
  | close t =>
    exfalso
    have hc := (LendingLedger.apply_checked h).2
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact lt_irrefl _ hdec

end XRPL.Model.Lending
