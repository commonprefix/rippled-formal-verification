import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Model.Vault.VaultClawback

/-! # Clawback exit reductions

`computeClawback_codes` inventories every outcome of a `computeClawback` that
runs without a throw, and `Vault.clawback_error_codes_proof` walks every exit
of `Vault.clawback`. The walks use `bind_ok_peel`, `if`-elimination, and the
`tryCatch` step lemmas only, keeping the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeClawback` that runs without a throw. -/
theorem computeClawback_codes (v : Vault) (assets : STAmount) (cc : ComputeClawbackResult)
    (hok : computeClawback v assets = .ok cc) :
    cc.error = none ∨ cc.error = some .tecINTERNAL ∨ cc.error = some .tecPATH_DRY := by
  unfold computeClawback at hok
  simp only [] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    injection hok with h
    rw [← h]
    exact .inr (.inl rfl)
  · rw [if_neg hneg] at hok
    simp only [pure_bind] at hok
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    have handler_path_dry : ∀ (e : String),
        tryCatch (Except.error e : Except String (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
          (fun e => if isOverflow e = true then
              pure (DoResultPR.return (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
                STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) PUnit.unit)
            else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr →
        cc.error = some .tecPATH_DRY := by
      intro e htc'
      rw [tryCatch_error] at htc'
      by_cases hov : isOverflow e = true
      · rw [if_pos hov, epure] at htc'
        rw [← Except.ok.inj htc'] at hK
        have hK2 : Except.ok (⟨some TER.tecPATH_DRY, STAmount.zero v.numericType,
            STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) = Except.ok cc := hK
        rw [← Except.ok.inj hK2]
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    cases hats : assetsToSharesWithdraw v assets false false with
    | error e =>
      rw [hats, err_bind] at htc
      exact .inr (.inr (handler_path_dry e htc))
    | ok sd =>
      simp only [hats, ok_bind, epure] at htc
      cases hsa : Vault.sharesToAssetsWithdraw v sd false with
      | error e2 =>
        rw [hsa, err_bind] at htc
        exact .inr (.inr (handler_path_dry e2 htc))
      | ok ar =>
        simp only [hsa, ok_bind] at htc
        cases han : ar.toNumber .to_nearest with
        | error e3 =>
          rw [han, err_bind] at htc
          exact .inr (.inr (handler_path_dry e3 htc))
        | ok arn =>
          simp only [han, ok_bind] at htc
          by_cases hgt : arn.operator_gt v.assetsAvailable = true
          · rw [if_pos hgt] at htc
            cases hof : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest with
            | error e4 =>
              rw [hof, err_bind] at htc
              exact .inr (.inr (handler_path_dry e4 htc))
            | ok ar2 =>
              simp only [hof, ok_bind] at htc
              cases hats2 : assetsToSharesWithdraw v ar2 true false with
              | error e5 =>
                rw [hats2, err_bind] at htc
                exact .inr (.inr (handler_path_dry e5 htc))
              | ok sd2 =>
                simp only [hats2, ok_bind] at htc
                cases hsa2 : Vault.sharesToAssetsWithdraw v sd2 false with
                | error e6 =>
                  rw [hsa2, err_bind] at htc
                  exact .inr (.inr (handler_path_dry e6 htc))
                | ok ar3 =>
                  simp only [hsa2, ok_bind] at htc
                  cases han2 : ar3.toNumber .to_nearest with
                  | error e7 =>
                    rw [han2, err_bind] at htc
                    exact .inr (.inr (handler_path_dry e7 htc))
                  | ok arn3 =>
                    simp only [han2, ok_bind] at htc
                    by_cases hgt2 : arn3.operator_gt v.assetsAvailable = true
                    · rw [if_pos hgt2, tryCatch_ok] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hK2 : Except.ok (⟨some TER.tecINTERNAL, STAmount.zero v.numericType,
                          STAmount.zero NumericType.int64⟩ : ComputeClawbackResult) = Except.ok cc := hK
                      rw [← Except.ok.inj hK2]
                      exact .inr (.inl rfl)
                    · rw [if_neg hgt2, tryCatch_ok] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hK2 : Except.ok (⟨none, ar3, sd2⟩ : ComputeClawbackResult)
                          = Except.ok cc := hK
                      rw [← Except.ok.inj hK2]
                      exact .inl rfl
          · rw [if_neg hgt, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (⟨none, ar, sd⟩ : ComputeClawbackResult) = Except.ok cc := hK
            rw [← Except.ok.inj hK2]
            exact .inl rfl

/-- Every outcome of a clawback that runs without a throw. -/
theorem Vault.clawback_error_codes_proof (v : Vault) (assets : STAmount) (r : ClawbackResult)
    (hok : v.clawback assets = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS := by
  unfold Vault.clawback at hok
  obtain ⟨result, hres, hok⟩ := bind_ok_peel _ _ _ hok
  have hcodes := computeClawback_codes v assets result hres
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]
    rcases hcodes with hc | hc | hc
    · exact .inl hc
    · exact .inr (.inl hc)
    · exact .inr (.inr (.inl hc))
  · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
    by_cases h2 : result.sharesDestroyed.isZero = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]
      exact .inr (.inr (.inr rfl))
    · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
      obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]
        exact .inr (.inr (.inr rfl))
      · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
        obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
        injection hok with h; rw [← h]
        exact .inl rfl

end XRPL.Model.SingleAssetVault
