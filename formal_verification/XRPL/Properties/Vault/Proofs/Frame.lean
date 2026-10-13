import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk

/-! # What each operation writes

Every exit of `deposit`, `withdraw` and `clawback` either returns the starting
vault with zero amounts, or writes `assetsTotal` and `assetsAvailable` with the
same update and copies `lossUnrealized`. `burnShares` writes only
`sharesTotal`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Rejections -/

lemma Vault.deposit_error_frame (v : Vault) (amount : STAmount) (isDonation : Bool)
    (r : DepositResult) (hpos : 0 < amount.toRat)
    (hok : v.deposit amount isDonation hpos = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.amountDeposit' = STAmount.zero v.numericType ∧
    r.sharesIssued = STAmount.zero .int64 := by
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | simp at herr

lemma Vault.withdraw_error_frame (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (r : WithdrawResult) (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waive hpos = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assets' = STAmount.zero v.numericType ∧
    r.sharesBurned = STAmount.zero .int64 := by
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | simp at herr

lemma Vault.clawback_error_frame (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assetsRecovered = STAmount.zero v.numericType ∧
    r.sharesDestroyed = STAmount.zero .int64 := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | simp at herr

/-! ## `lossUnrealized` is copied -/

lemma Vault.deposit_lossUnrealized_frame (v : Vault) (amount : STAmount) (isDonation : Bool)
    (r : DepositResult) (hpos : 0 < amount.toRat)
    (hok : v.deposit amount isDonation hpos = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | rfl | rw_lawful

lemma Vault.withdraw_lossUnrealized_frame (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (r : WithdrawResult) (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waive hpos = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | rfl | rw_lawful

lemma Vault.clawback_lossUnrealized_frame (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | rfl | rw_lawful

lemma Vault.burnShares_lossUnrealized_frame (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.lossUnrealized = v.lossUnrealized := by
  simp only [Vault.burnShares, bind, Except.bind] at hok
  walk_ok
  all_goals rw_lawful

/-! ## Asset parity is kept -/

lemma Vault.deposit_parity_frame (v : Vault) (amount : STAmount) (isDonation : Bool)
    (r : DepositResult) (hpos : 0 < amount.toRat)
    (hok : v.deposit amount isDonation hpos = .ok r)
    (hp : v.assetsAvailable = v.assetsTotal) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact hp | rw_lawful
  all_goals (dsimp only; rw [hp] at *; simp_all)

lemma Vault.withdraw_parity_frame (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (r : WithdrawResult) (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waive hpos = .ok r)
    (hp : v.assetsAvailable = v.assetsTotal) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact hp | rw_lawful
  all_goals (dsimp only; rw [hp] at *; simp_all)

lemma Vault.clawback_parity_frame (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r)
    (hp : v.assetsAvailable = v.assetsTotal) :
    r.vault'.assetsAvailable = r.vault'.assetsTotal := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | exact hp | rw_lawful
  all_goals (dsimp only; rw [hp] at *; simp_all)

lemma Vault.burnShares_parity_frame (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hok : v.burnShares sharesDestroyed = .ok v')
    (hp : v.assetsAvailable = v.assetsTotal) :
    v'.assetsAvailable = v'.assetsTotal := by
  simp only [Vault.burnShares, bind, Except.bind] at hok
  walk_ok
  all_goals rw_lawful; exact hp

end XRPL.Model.SingleAssetVault
