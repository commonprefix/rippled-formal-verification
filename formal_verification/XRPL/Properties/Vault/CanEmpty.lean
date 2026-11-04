import XRPL.Properties.Vault.Proofs.CanEmpty
import XRPL.Properties.Vault.Proofs.UnprovableWitness

/-! # Emptying a vault

A reachable vault can always be emptied. A lawful vault outside any history cannot always be:
the funds check runs on the priced payout before the final-withdrawal rule. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A reachable vault can be emptied by a finite withdrawal sequence. One withdrawal of every share
suffices, made once the vault is outside its investment phase. -/
theorem Vault.Reachable.canEmpty (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) : CanEmpty v t :=
  Vault.Reachable.canEmpty_proof v t hr

/-- When withdrawals are open, a withdrawal of every share from a reachable vault succeeds, pays out
all the cash, and leaves no cash and no shares. -/
theorem Vault.Reachable.withdraw_all (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (hopen : v.earlyExitFeeRate.isSome = true ∨ v.phase t ≠ .investment)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero :=
  Vault.Reachable.withdraw_all_proof v t0 t hr waive
    (by rcases hopen with h | h <;> cases hf : v.earlyExitFeeRate <;> simp_all) shares hc hty hall hpos

/-- Every lawful vault with nothing lent out can be emptied by redeeming all its shares once withdrawals are
open. False, see `withdraw_can_empty_false`. -/
def Vault.withdraw_can_empty_claim : Prop :=
  ∀ (v : Vault) (t : UInt32) (sharesTotalAmount : STAmount),
    v.assetsDeployed = Number.zero →
    (v.earlyExitFeeRate.isSome = true ∨ v.phase t ≠ .investment) →
    STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
    ∀ hpos : 0 < (WithdrawAmount.vaultShares sharesTotalAmount).amount.toRat,
    ∃ r : VaultWithAmounts,
      (v.withdraw (.vaultShares sharesTotalAmount) false t hpos).run = .ok (.ok r) ∧
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero

/-- `withdraw_can_empty_claim` is false: an int64 vault with `9223372036854775806` assets and `3` shares
prices the full exit one unit above the cash and rejects it with `tecINSUFFICIENT_FUNDS`. -/
theorem Vault.withdraw_can_empty_false : ¬ Vault.withdraw_can_empty_claim := fun h =>
  let ⟨v, t, s, hpos, hlent, hphase, hst, hrej⟩ := Vault.full_exit_rejected_witness
  let ⟨_, hok, _⟩ := h v t s hlent (Or.inr hphase) hst hpos
  by rw [hok] at hrej; cases hrej

end XRPL.Model.SingleAssetVault
