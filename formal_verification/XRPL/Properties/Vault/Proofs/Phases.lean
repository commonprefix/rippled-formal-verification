import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.OpenZone

/-! # What can change the share total in the investment phase

Proof bodies behind `Phases.lean`. In the investment phase a deposit is refused and a donation
issues no shares, a withdrawal needs an early-exit fee rate, a burn needs an insolvent vault, and an
update never touches the share total. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful donation leaves the share total as it was: it issues no shares, and adding a zero
share amount is the identity. -/
private lemma Vault.donation_sharesTotal (v : Vault) (amount : STAmount) (t : UInt32)
    (hpos : 0 < amount.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amount true t hpos).run = .ok (.ok r)) :
    r.vault'.sharesTotal = v.sharesTotal := by
  obtain ⟨roundedAmount, amounts, raw, -, hcomp, -, hadj, hraw, -, -⟩ :=
    Vault.deposit_ok_reduces v amount true t hpos r hok
  obtain ⟨-, hshares, -, -, -⟩ := computeDeposit_donation_reduces v roundedAmount amounts hcomp
  obtain ⟨_, sharesNum, _, _, st', -, hsnum, hst, -, -, hrawEq⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  have hzero : sharesNum = Number.zero :=
    STAmount.toNumber_zero_eq _ _ _ (by rw [hshares]; exact STAmount.zero_mValue _) hsnum
  rw [hzero, Number.operator_add_zero_right, Except.ok.injEq] at hst
  show r.vault'.toRawVault.sharesTotal = _
  rw [hraw, hrawEq, ← hst]

/-- Proof of `Vault.investment_shares_fixed`. -/
lemma Vault.investment_shares_fixed_proof (v : Vault) (t : UInt32) (hphase : v.phase t = .investment) :
    (∀ (amount : STAmount) (isDonation : Bool) (hpos : 0 < amount.toRat) (r : VaultWithAmounts),
      (v.deposit amount isDonation t hpos).run = .ok (.ok r) → r.vault'.sharesTotal = v.sharesTotal) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      (v.withdraw amount waive t hpos).run = .ok (.ok r) → v.earlyExitFeeRate.isSome = true) ∧
    (∀ (amount holderShares sharesTotalAmount : STAmount) (v' : Vault),
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (v.burnShares holderShares).run = .ok (.ok v') → v.isInsolvent = true) ∧
    (∀ (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool) (v' : Vault),
      v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tesSUCCESS →
      v.update assetsMaximum blockDeposit unblockDeposit = .ok v' → v'.sharesTotal = v.sharesTotal) := by
  refine ⟨fun amount isDonation hpos r hok => ?_, fun amount waive hpos r hok => ?_,
    fun amount holderShares sharesTotalAmount _ hcan _ => ?_,
    fun assetsMaximum blockDeposit unblockDeposit v' _ hok => ?_⟩
  · cases isDonation with
    | false =>
      -- a deposit after the subscription period is refused
      rw [Vault.deposit_expired_proof v amount t hpos (by rw [hphase]; decide)] at hok
      exact absurd hok (by simp)
    | true => exact Vault.donation_sharesTotal v amount t hpos r hok
  · -- without a fee rate the withdrawal is too soon
    by_contra hnone
    have hfee : v.earlyExitFeeRate = none := by
      cases h : v.earlyExitFeeRate with
      | none => rfl
      | some _ => rw [h] at hnone; exact absurd rfl hnone
    have hsoon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = true := by
      rw [hphase, hfee]
      decide
    rw [Vault.withdraw_too_soon_proof v amount waive t hpos hsoon] at hok
    exact absurd hok (by simp)
  · exact (Vault.canBurnShares_ok_reduces v amount holderShares sharesTotalAmount hcan).1
  · obtain ⟨_, _, hv⟩ := Vault.update_frame v assetsMaximum blockDeposit unblockDeposit v' hok
    show v'.toRawVault.sharesTotal = _
    rw [hv]

end XRPL.Model.SingleAssetVault
