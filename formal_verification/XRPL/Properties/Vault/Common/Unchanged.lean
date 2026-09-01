import XRPL.Properties.Vault.Common.DepositExits
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback

/-! # Rejected operations leave the vault unchanged (proofs)

Each proof walks the operation's do-block and shows every exit either returns
the full rejection record (`vault' = v`, both amount fields zero) or returns
`error = none`. The `error`-carrying disjunct is then discharged by the
`isSome` hypothesis. The `*_error_unchanged_proof` corollaries keep the
vault-only conclusion. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem LawfulVault.deposit_error_rejected_proof (lv : LawfulVault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : lv.deposit amountDeposit isDonation = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.amountDeposit' = STAmount.zero lv.numericType ∧
    r.sharesIssued = STAmount.zero .int64 := by
  have key : (r.vault' = lv ∧ r.amountDeposit' = STAmount.zero lv.numericType ∧
      r.sharesIssued = STAmount.zero .int64) ∨ r.error = none := by
    unfold LawfulVault.deposit at hok
    simp only [] at hok
    obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : amount.isZero = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg h1] at hok
      by_cases h2 : (isDonation && lv.sharesTotal.mantissa_ == 0) = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h2] at hok
        by_cases h3 : (lv.isInsolvent && !isDonation) = true
        · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
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
            by_cases hm : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true
            · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg hm] at hok
              obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]; exact .inr rfl
          · rw [if_neg hd] at hok
            obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
            cases cres with
            | error e =>
              injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            | success a s =>
              simp only [] at hok
              obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hm : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true
              · rw [if_pos hm] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
              · rw [if_neg hm] at hok
                obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h]; exact .inr rfl
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A deposit returning a `TER` leaves the vault unchanged. -/
theorem LawfulVault.deposit_error_unchanged_proof (lv : LawfulVault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult) (hok : lv.deposit amountDeposit isDonation = .ok r)
    (herr : r.error.isSome = true) : r.vault' = lv :=
  (LawfulVault.deposit_error_rejected_proof lv amountDeposit isDonation r hok herr).1

/-- A withdrawal returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem LawfulVault.withdraw_error_rejected_proof (lv : LawfulVault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.assets' = STAmount.zero lv.numericType ∧
    r.sharesBurned = STAmount.zero .int64 := by
  have key : (r.vault' = lv ∧ r.assets' = STAmount.zero lv.numericType ∧
      r.sharesBurned = STAmount.zero .int64) ∨ r.error = none := by
    unfold LawfulVault.withdraw at hok
    simp only [] at hok
    cases amount
    all_goals {
      simp only [] at hok
      obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h1 : result.error.isSome = true
      · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
        obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h2 : lv.assetsAvailable.operator_lt assetsNumber' = true
        · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
        · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
          obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h3 : result.sharesRedeemed.operator_eq sta = true
          · rw [if_pos h3] at hok
            by_cases h4 : lv.lossUnrealized.operator_ne Number.zero = true
            · rw [if_pos h4] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
              obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]; exact .inr rfl
          · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
            obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases h5 : (assetsNumber'.mantissa_ != 0 && atr.operator_eq atr') = true
            · rw [if_pos h5] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
            · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
              obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]; exact .inr rfl
    }
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A withdrawal returning a `TER` leaves the vault unchanged. -/
theorem LawfulVault.withdraw_error_unchanged_proof (lv : LawfulVault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) : r.vault' = lv :=
  (LawfulVault.withdraw_error_rejected_proof lv amount waiveUnrealizedLoss r hok herr).1

/-- A clawback returning a `TER` leaves the vault unchanged and reports zero
amounts. -/
theorem LawfulVault.clawback_error_rejected_proof (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : lv.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = lv ∧ r.assetsRecovered = STAmount.zero lv.numericType ∧
    r.sharesDestroyed = STAmount.zero .int64 := by
  have key : (r.vault' = lv ∧ r.assetsRecovered = STAmount.zero lv.numericType ∧
      r.sharesDestroyed = STAmount.zero .int64) ∨ r.error = none := by
    unfold LawfulVault.clawback at hok
    simp only [] at hok
    obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      by_cases h2 : result.sharesDestroyed.isZero = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
        · rw [if_pos h3] at hok; injection hok with h; rw [← h]; exact .inl ⟨rfl, rfl, rfl⟩
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
          injection hok with h; rw [← h]
          cases hre : result.error with
          | none => exact .inr rfl
          | some x => rw [hre] at h1; simp at h1
  rcases key with h | h
  · exact h
  · rw [h] at herr; simp at herr

/-- A clawback returning a `TER` leaves the vault unchanged. -/
theorem LawfulVault.clawback_error_unchanged_proof (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : lv.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) : r.vault' = lv :=
  (LawfulVault.clawback_error_rejected_proof lv assets holderShares r hok herr).1

end XRPL.Model.SingleAssetVault
