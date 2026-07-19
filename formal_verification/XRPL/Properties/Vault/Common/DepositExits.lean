import XRPL.Properties.Vault.Common.DepositReduction

/-! # Deposit exit reductions

`computeDeposit_codes` inventories every outcome of a `computeDeposit` that
runs without a throw, and `Vault.deposit_error_codes_proof` walks every exit of
`Vault.deposit` to inventory the codes a deposit can return. Both walks use
`bind_ok_peel`, `if`-elimination, and the `tryCatch` step lemmas only, keeping
the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeDeposit` that runs without a throw: one of the
three error codes, or a success carrying the priced amounts. -/
theorem computeDeposit_codes (v : Vault) (amount : STAmount) (cres : ComputeDepositResult)
    (hok : computeDeposit v amount = .ok cres) :
    cres = .error .tecPRECISION_LOSS ∨
    cres = .error .tecINTERNAL ∨
    cres = .error .tecPATH_DRY ∨
    ∃ a s, cres = .success a s := by
  unfold computeDeposit at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  have handler_path_dry : ∀ (e : String),
      tryCatch (Except.error e : Except String (DoResultPR ComputeDepositResult ComputeDepositResult PUnit))
        (fun e => if isOverflow e = true then
            pure (DoResultPR.return (ComputeDepositResult.error TER.tecPATH_DRY) PUnit.unit)
          else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr →
      cres = ComputeDepositResult.error .tecPATH_DRY := by
    intro e htc'
    rw [tryCatch_error] at htc'
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc'
      rw [← Except.ok.inj htc'] at hK
      have hK2 : Except.ok (ComputeDepositResult.error TER.tecPATH_DRY) = Except.ok cres := hK
      exact (Except.ok.inj hK2).symm
    · rw [if_neg hov, ethrow, err_bind] at htc'
      exact absurd htc' (by simp)
  cases hatsd : assetsToSharesDeposit v amount with
  | error e =>
    rw [hatsd, err_bind] at htc
    exact .inr (.inr (.inl (handler_path_dry e htc)))
  | ok shares =>
    simp only [hatsd, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (ComputeDepositResult.error TER.tecPRECISION_LOSS) = Except.ok cres := hK
      exact .inl (Except.ok.inj hK2).symm
    · rw [if_neg hz] at htc
      cases hsad : sharesToAssetsDeposit v shares with
      | error e2 =>
        rw [hsad, err_bind] at htc
        exact .inr (.inr (.inl (handler_path_dry e2 htc)))
      | ok amountDeposit' =>
        simp only [hsad, ok_bind] at htc
        cases hgt : amountDeposit'.operator_gt amount with
        | error e3 =>
          rw [hgt, err_bind] at htc
          exact .inr (.inr (.inl (handler_path_dry e3 htc)))
        | ok gtb =>
          simp only [hgt, ok_bind] at htc
          by_cases hgtb : gtb = true
          · rw [if_pos hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.error TER.tecINTERNAL) = Except.ok cres := hK
            exact .inr (.inl (Except.ok.inj hK2).symm)
          · rw [if_neg hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.success amountDeposit' shares) = Except.ok cres := hK
            exact .inr (.inr (.inr ⟨amountDeposit', shares, (Except.ok.inj hK2).symm⟩))

/-- Every outcome of a deposit that runs without a throw. -/
theorem Vault.deposit_error_codes_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED := by
  unfold Vault.deposit at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok
    injection hok with h; rw [← h]
    exact .inr (.inl rfl)
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok
      injection hok with h; rw [← h]
      exact .inr (.inr (.inl rfl))
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok
        injection hok with h; rw [← h]
        exact .inr (.inr (.inr (.inl rfl)))
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
          · rw [if_pos hm] at hok
            injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
          · rw [if_neg hm] at hok
            injection hok with h; rw [← h]
            exact .inl rfl
        · rw [if_neg hd] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          rcases computeDeposit_codes v amount cres hcd with h5 | h5 | h5 | ⟨a, s, h5⟩
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inl rfl))))
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inl rfl)
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
          · subst h5
            simp only [] at hok
            obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hm : v.assetsMaximum.any (fun m => at'.operator_gt m) = true
            · rw [if_pos hm] at hok
              injection hok with h; rw [← h]
              exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
            · rw [if_neg hm] at hok
              injection hok with h; rw [← h]
              exact .inl rfl

end XRPL.Model.SingleAssetVault
