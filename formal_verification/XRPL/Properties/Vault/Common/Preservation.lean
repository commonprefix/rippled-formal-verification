import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Model.Vault.VaultBurn

/-! # No operation writes `interestUnrealized` or `lossUnrealized`

Each operation's do-block updates only `assetsTotal`, `assetsAvailable`, and
`sharesTotal` on success, and returns the starting vault on rejection. So the two
unrealized fields are the same in `r.vault'` as in `v` on every exit. Walked with
the same reduction toolkit as `Unchanged.lean`; every leaf closes by `rfl` because
both a bare `v` and a `{v with assetsTotal, assetsAvailable, sharesTotal := …}`
record carry `v`'s unrealized fields unchanged. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit keeps both unrealized fields at their starting values. -/
theorem Vault.deposit_preserves_unrealized (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized ∧
    r.vault'.interestUnrealized = v.interestUnrealized := by
  unfold Vault.deposit at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_pos hd] at hok
          obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : v.assetsMaximum.any (fun m => at'.operator_gt m) = true
          · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
          · rw [if_neg hm] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
        · rw [if_neg hd] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          cases cres with
          | error e => injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
          | success a s =>
            simp only [] at hok
            obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hm : v.assetsMaximum.any (fun m => at'.operator_gt m) = true
            · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
            · rw [if_neg hm] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩

/-- A withdrawal keeps both unrealized fields at their starting values. -/
theorem Vault.withdraw_preserves_unrealized (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized ∧
    r.vault'.interestUnrealized = v.interestUnrealized := by
  unfold Vault.withdraw at hok
  cases amount
  all_goals {
    simp only [] at hok
    obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h2 : v.assetsAvailable.operator_lt assetsNumber' = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : result.sharesRedeemed.operator_eq sta = true
        · rw [if_pos h3] at hok
          by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h5 : (assetsNumber'.mantissa_ != 0 && atr.operator_eq atr') = true
          · rw [if_pos h5] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
          · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
  }

/-- A clawback keeps both unrealized fields at their starting values. -/
theorem Vault.clawback_preserves_unrealized (v : Vault) (assets : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized ∧
    r.vault'.interestUnrealized = v.interestUnrealized := by
  unfold Vault.clawback at hok
  obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
    by_cases h2 : result.sharesDestroyed.isZero = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
    · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
      obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩
      · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
        obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
        injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩

/-- `burnShares` writes only `sharesTotal`, so both unrealized fields carry
over unchanged. -/
theorem Vault.burnShares_preserves_unrealized (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.lossUnrealized = v.lossUnrealized ∧
    v'.interestUnrealized = v.interestUnrealized := by
  unfold Vault.burnShares at hok
  obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
  injection hok with h; rw [← h]; exact ⟨rfl, rfl⟩

end XRPL.Model.SingleAssetVault
