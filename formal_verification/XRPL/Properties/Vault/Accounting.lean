import XRPL.Properties.Vault.Common.Flows
import XRPL.Properties.Vault.Reachable
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.CreateUpdate
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts

/-! # Vault accounting over a sequence of transactions

On a vault with no lending every cash update is exact, so over any sequence of transactions the cash and the share
total end at their start values plus what the transactions moved in, less what they moved out. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A reachable vault never passes the burn check: a burn needs an insolvent vault, which has shares but no cash,
while on a reachable vault every share is worth at least one base unit of cash. -/
private lemma Vault.Reachable.canBurnShares_not_ok (u : Vault) (t : UInt32) (hr : Vault.Reachable u t)
    (amount holderShares sharesTotalAmount : STAmount)
    (hcan : (u.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) : False := by
  have hcash := (Vault.Reachable.vault_fields u t hr).2.2.2
  have hSpos := Vault.canBurnShares_sharesTotal_pos u amount holderShares sharesTotalAmount hcan
  obtain ⟨hins, -, -⟩ := Vault.canBurnShares_ok_reduces u amount holderShares sharesTotalAmount hcan
  have hAm : u.assetsAvailable.mantissa_ = 0 := by
    unfold Vault.isInsolvent at hins
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hins
    exact hins.1.1
  rw [Number.toRat_eq_zero_of_mantissa_zero _ hAm] at hcash
  have hbpos : (0 : ℚ) < 10 ^ u.baseExponent := zpow_pos (by norm_num) _
  nlinarith [mul_pos hSpos hbpos]

/-- The cash and the share total along a sequence from a reachable vault. -/
private lemma Vault.Flows.balances {w : Vault} {t : UInt32} (hr : Vault.Reachable w t) {u : Vault} {t' : UInt32}
    {D W C SC SR SD : ℚ} (h : Vault.Flows w t u t' D W C SC SR SD) :
    u.assetsAvailable.toRat = w.assetsAvailable.toRat + D - W - C ∧
      (u.toExact.sharesTotal : ℚ) = w.toExact.sharesTotal + SC - SR - SD := by
  induction h with
  | refl => constructor <;> ring
  | deposit u t₁ t' _ _ _ _ _ _ amount isDonation r hf _ hc hty hpos hok _ ih =>
    have hu := Vault.Flows.reachable hr hf
    obtain ⟨hA, hS, -⟩ := (Vault.vault_updates_exact u t₁ hu).1 amount isDonation t' hpos hc hty r hok
    constructor <;> linarith [ih.1, ih.2]
  | withdraw u t₁ t' _ _ _ _ _ _ amount _ waive r hf _ hc hty _ _ hpos hok _ ih =>
    have hu := Vault.Flows.reachable hr hf
    obtain ⟨hA, hS, -⟩ := (Vault.vault_updates_exact u t₁ hu).2.1 amount waive t' hpos hc hty r hok
    constructor <;> linarith [ih.1, ih.2]
  | clawback u t₁ t' _ _ _ _ _ _ assets holderShares waive r hf _ hc _ hhs _ hnn hok _ ih =>
    have hu := Vault.Flows.reachable hr hf
    obtain ⟨hA, hS, -⟩ := (Vault.vault_updates_exact u t₁ hu).2.2 assets holderShares waive hnn hc hhs r hok
    constructor <;> linarith [ih.1, ih.2]
  | burnShares u t₁ _ _ _ _ _ _ _ amount holderShares sharesTotalAmount _ hf _ _ hcan _ _ =>
    exact (Vault.Reachable.canBurnShares_not_ok u t₁ (Vault.Flows.reachable hr hf) amount holderShares
      sharesTotalAmount hcan).elim
  | update u _ _ _ _ _ _ _ _ assetsMaximum blockDeposit u' _ _ _ hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u assetsMaximum blockDeposit u' hok
    have hA : u'.assetsAvailable = u.assetsAvailable := (congrArg RawVault.assetsAvailable hv).trans rfl
    have hS : u'.toExact.sharesTotal = u.toExact.sharesTotal := by
      show u'.toRawVault.toExact.sharesTotal = u.toRawVault.toExact.sharesTotal
      rw [hv]
      rfl
    rw [hA, hS]
    exact ih

/-- Over any sequence of transactions from a reachable vault -> AssetsTotal and AssetsAvailable each move by Σ deposits
− Σ withdrawals − Σ clawbacks, and SharesTotal by Σ sharesCreated − Σ sharesRedeemed − Σ sharesDestroyed. -/
theorem Vault.Reachable.accounting :
    (∀ (w : Vault) (t : UInt32), Vault.Reachable w t →
      ∀ (u : Vault) (t' : UInt32) (deposited withdrawn recovered created redeemed destroyed : ℚ),
      Vault.Flows w t u t' deposited withdrawn recovered created redeemed destroyed →
      u.toExact.assetsTotal = w.toExact.assetsTotal + deposited - withdrawn - recovered ∧
      u.assetsAvailable.toRat = w.assetsAvailable.toRat + deposited - withdrawn - recovered ∧
      (u.toExact.sharesTotal : ℚ) = w.toExact.sharesTotal + created - redeemed - destroyed) ∧
    -- from a new vault
    ∀ (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType) (t : UInt32)
      (w : Vault),
      Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok w →
      ∀ (u : Vault) (t' : UInt32) (deposited withdrawn recovered created redeemed destroyed : ℚ),
      Vault.Flows w t u t' deposited withdrawn recovered created redeemed destroyed →
      u.toExact.assetsTotal = deposited - withdrawn - recovered ∧
      u.assetsAvailable.toRat = deposited - withdrawn - recovered ∧
      (u.toExact.sharesTotal : ℚ) = created - redeemed - destroyed := by
  -- on a reachable vault nothing is deployed, so the exact total is the cash
  have htot : ∀ (v : Vault) (t : UInt32), Vault.Reachable v t → v.toExact.assetsTotal = v.assetsAvailable.toRat :=
    fun v t hr => by
      have hD := (Vault.Reachable.lendingFields_zero_proof v t hr).1
      show v.assetsAvailable.toRat + v.toExact.assetsDeployed = _
      rw [hD, add_zero]
  refine ⟨fun w t hr u t' D W C SC SR SD h => ?_, fun scale assetsMaximum schedule earlyExitFeeRate
    ownerCanBlockDeposit nt t w hcan hok u t' D W C SC SR SD h => ?_⟩
  · obtain ⟨hA, hS⟩ := Vault.Flows.balances hr h
    rw [htot u t' (Vault.Flows.reachable hr h), htot w t hr]
    exact ⟨hA, hA, hS⟩
  · have hr : Vault.Reachable w t := .create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt t w
      hcan hok
    obtain ⟨hA, hS⟩ := Vault.Flows.balances hr h
    obtain ⟨hAA, -, -, hST, -, -⟩ :=
      Vault.create_empty_proof scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt w hok
    have hS0 : (w.toExact.sharesTotal : ℚ) = 0 := by
      rw [RawVault.WF.toExact_sharesTotal w.toRawVault w.wf]
      show w.sharesTotal.toRat = 0
      rw [hST, Number.toRat_zero]
    rw [hAA, Number.toRat_zero] at hA
    rw [hS0] at hS
    rw [htot u t' (Vault.Flows.reachable hr h)]
    refine ⟨?_, ?_, ?_⟩ <;> linarith

end XRPL.Model.SingleAssetVault
