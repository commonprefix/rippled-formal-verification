import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Model.Vault.VaultWithdraw

/-! # Withdraw exit reductions

Code inventories for the two exchange computations (`computeWithdrawByAssets`,
`computeWithdrawByShares`) and the full `Vault.withdraw` walk behind
`withdraw_error_codes`. The walks use `bind_ok_peel`, `if`-elimination, and the
`tryCatch` step lemmas only, keeping the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeWithdrawByAssets` that runs without a throw. -/
theorem computeWithdrawByAssets_codes (v : Vault) (assets : STAmount) (waive : Bool)
    (cw : ComputeWithdrawResult) (hok : computeWithdrawByAssets v assets waive = .ok cw) :
    cw.error = none ∨ cw.error = some .tecPRECISION_LOSS ∨ cw.error = some .tecPATH_DRY := by
  unfold computeWithdrawByAssets at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  cases hats : assetsToSharesWithdraw v assets false waive with
  | error e =>
    rw [hats, err_bind, tryCatch_error] at htc
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr (.inr rfl)
    · rw [if_neg hov, ethrow, err_bind] at htc
      exact absurd htc (by simp)
  | ok shares =>
    simp only [hats, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPRECISION_LOSS, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr (.inl rfl)
    · rw [if_neg hz] at htc
      cases hsa : Vault.sharesToAssetsWithdraw v shares waive with
      | error e2 =>
        rw [hsa, err_bind, tryCatch_error] at htc
        by_cases hov : isOverflow e2 = true
        · rw [if_pos hov] at htc
          rw [← Except.ok.inj htc] at hK
          have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
              STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
          rw [← Except.ok.inj hK2]
          exact .inr (.inr rfl)
        · rw [if_neg hov, ethrow, err_bind] at htc
          exact absurd htc (by simp)
      | ok assets' =>
        simp only [hsa, ok_bind] at htc
        rw [tryCatch_ok] at htc
        rw [← Except.ok.inj htc] at hK
        have hK2 : Except.ok (⟨none, assets', shares⟩ : ComputeWithdrawResult)
            = Except.ok cw := hK
        rw [← Except.ok.inj hK2]
        exact .inl rfl

/-- Every outcome of a `computeWithdrawByShares` that runs without a throw. -/
theorem computeWithdrawByShares_codes (v : Vault) (shares : STAmount) (waive : Bool)
    (cw : ComputeWithdrawResult) (hok : computeWithdrawByShares v shares waive = .ok cw) :
    cw.error = none ∨ cw.error = some .tecPATH_DRY := by
  unfold computeWithdrawByShares at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  cases hsa : Vault.sharesToAssetsWithdraw v shares waive with
  | error e =>
    rw [hsa, err_bind, tryCatch_error] at htc
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
          STAmount.zero .int64⟩ : ComputeWithdrawResult) = Except.ok cw := hK
      rw [← Except.ok.inj hK2]
      exact .inr rfl
    · rw [if_neg hov, ethrow, err_bind] at htc
      exact absurd htc (by simp)
  | ok assets =>
    simp only [hsa, ok_bind, epure] at htc
    rw [tryCatch_ok] at htc
    rw [← Except.ok.inj htc] at hK
    have hK2 : Except.ok (⟨none, assets, shares⟩ : ComputeWithdrawResult)
        = Except.ok cw := hK
    rw [← Except.ok.inj hK2]
    exact .inl rfl

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem Vault.withdraw_error_codes_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL := by
  unfold Vault.withdraw at hok
  cases amount
  case' vaultAssets a =>
    simp only [] at hok
    obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
    have hcodes : result.error = none ∨ result.error = some .tecPRECISION_LOSS ∨
        result.error = some .tecPATH_DRY :=
      computeWithdrawByAssets_codes v a waiveUnrealizedLoss result hres
    clear hres
  case' vaultShares s =>
    simp only [] at hok
    obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
    have hcodes : result.error = none ∨ result.error = some .tecPRECISION_LOSS ∨
        result.error = some .tecPATH_DRY :=
      (computeWithdrawByShares_codes v s waiveUnrealizedLoss result hres).elim Or.inl
        (fun hc => Or.inr (Or.inr hc))
    clear hres
  all_goals {
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]
      rcases hcodes with hc | hc | hc
      · exact .inl hc
      · exact .inr (.inl hc)
      · exact .inr (.inr (.inl hc))
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h2 : v.assetsAvailable.operator_lt assetsNumber' = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]
        exact .inr (.inr (.inr (.inl rfl)))
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : result.sharesRedeemed.operator_eq sta = true
        · rw [if_pos h3] at hok
          by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr rfl)))
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]; exact .inl rfl
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h5 : (assetsNumber'.mantissa_ != 0 && atr.operator_eq atr') = true
          · rw [if_pos h5] at hok; injection hok with h; rw [← h]
            exact .inr (.inl rfl)
          · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]; exact .inl rfl
  }

end XRPL.Model.SingleAssetVault
