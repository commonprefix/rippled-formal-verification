import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.WithdrawReduction

/-! # Guard-extraction reductions for `LawfulVault.clawback`

The clawback accuracy proofs recover, from a successful run
(`v.clawback … = .ok r` with `r.error = none`), every intermediate of the
`computeClawback` exchange (including the recompute-from-`assetsAvailable`
branch) and of the stored-field updates. Same discipline as
`WithdrawReduction`: `bind_ok_peel` plus `if`-elimination only. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- With a nonzero amount the clawback share computation is the withdraw one. -/
theorem assetsToSharesClawback_nonzero (lv : LawfulVault) (assets holderShares : STAmount)
    (hz : assets.isZero = false) :
    assetsToSharesClawback lv assets holderShares =
      assetsToSharesWithdraw lv assets false false := by
  unfold assetsToSharesClawback
  rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  simp only [pure_bind]

/-- With a zero amount the clawback share computation returns the holder's
entire share balance unchanged. -/
theorem assetsToSharesClawback_zero (lv : LawfulVault) (assets holderShares : STAmount)
    (hz : assets.isZero = true) :
    assetsToSharesClawback lv assets holderShares = .ok holderShares := by
  unfold assetsToSharesClawback
  rw [if_pos hz]
  rfl

/-- **`computeClawback` no-error reduction.** A `cr.error = none` outcome for a
nonzero amount forces the happy path of the body: the two-way exchange, and
either the computed recovery fit under `assetsAvailable`, or the clamped
recompute did. -/
theorem computeClawback_none_reduces (lv : LawfulVault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult)
    (hz : assets.isZero = false)
    (hok : computeClawback lv assets holderShares = .ok cr) (herr : cr.error = none) :
    assets.negative = false ∧
    ∃ (sharesDestroyed assetsRecovered : STAmount) (assetsRecoveredNumber : Number),
      assetsToSharesWithdraw lv assets false false = .ok sharesDestroyed ∧
      lv.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      ((assetsRecoveredNumber.operator_gt lv.assetsAvailable = false ∧
        cr.assetsRecovered = assetsRecovered ∧ cr.sharesDestroyed = sharesDestroyed) ∨
       (assetsRecoveredNumber.operator_gt lv.assetsAvailable = true ∧
        ∃ (clamped sharesDestroyed' assetsRecovered' : STAmount)
          (assetsRecoveredNumber' : Number),
          STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok clamped ∧
          assetsToSharesWithdraw lv clamped true false = .ok sharesDestroyed' ∧
          lv.sharesToAssetsWithdraw sharesDestroyed' false = .ok assetsRecovered' ∧
          assetsRecovered'.toNumber .to_nearest = .ok assetsRecoveredNumber' ∧
          assetsRecoveredNumber'.operator_gt lv.assetsAvailable = false ∧
          cr.assetsRecovered = assetsRecovered' ∧
          cr.sharesDestroyed = sharesDestroyed')) := by
  unfold computeClawback at hok
  simp only [pure_bind] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    have hcr := (Except.ok.inj hok).symm
    rw [hcr] at herr
    exact absurd herr (by simp)
  · rw [if_neg hneg] at hok
    refine ⟨by simpa using hneg, ?_⟩
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    rw [assetsToSharesClawback_nonzero lv assets holderShares hz] at htc
    have handler_err : ∀ e : Error,
        tryCatch (Except.error e :
            Except Error (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
          (fun e => if isOverflow e = true then
              pure (DoResultPR.return
                ⟨some .tecPATH_DRY, STAmount.zero lv.numericType, STAmount.zero .int64⟩
                PUnit.unit)
            else do
              let y ← throw e
              pure (DoResultPR.pure y PUnit.unit)) = .ok rr → False := by
      intro e htc'
      rw [tryCatch_error] at htc'
      by_cases hov : isOverflow e = true
      · rw [if_pos hov, epure] at htc'
        rw [← Except.ok.inj htc'] at hK
        have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
        rw [← hcr] at herr
        exact absurd herr (by simp)
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    cases h1 : assetsToSharesWithdraw lv assets false false with
    | error e => rw [h1, err_bind] at htc; exact absurd htc (handler_err e)
    | ok sharesDestroyed =>
      rw [h1] at htc
      simp only [ok_bind] at htc
      cases h2 : lv.sharesToAssetsWithdraw sharesDestroyed false with
      | error e => rw [h2, err_bind] at htc; exact absurd htc (handler_err e)
      | ok assetsRecovered =>
        rw [h2] at htc
        simp only [ok_bind] at htc
        cases h3 : assetsRecovered.toNumber .to_nearest with
        | error e => rw [h3, err_bind] at htc; exact absurd htc (handler_err e)
        | ok arn =>
          rw [h3] at htc
          simp only [ok_bind] at htc
          by_cases hgt : arn.operator_gt lv.assetsAvailable = true
          · rw [if_pos hgt] at htc
            cases h4 : STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest with
            | error e => rw [h4, err_bind] at htc; exact absurd htc (handler_err e)
            | ok clamped =>
              rw [h4] at htc
              simp only [ok_bind] at htc
              cases h5 : assetsToSharesWithdraw lv clamped true false with
              | error e => rw [h5, err_bind] at htc; exact absurd htc (handler_err e)
              | ok sharesDestroyed' =>
                rw [h5] at htc
                simp only [ok_bind] at htc
                cases h6 : lv.sharesToAssetsWithdraw sharesDestroyed' false with
                | error e => rw [h6, err_bind] at htc; exact absurd htc (handler_err e)
                | ok assetsRecovered' =>
                  rw [h6] at htc
                  simp only [ok_bind] at htc
                  cases h7 : assetsRecovered'.toNumber .to_nearest with
                  | error e => rw [h7, err_bind] at htc; exact absurd htc (handler_err e)
                  | ok arn' =>
                    rw [h7] at htc
                    simp only [ok_bind] at htc
                    by_cases hgt' : arn'.operator_gt lv.assetsAvailable = true
                    · rw [if_pos hgt', epure, tryCatch_ok] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                      rw [← hcr] at herr
                      exact absurd herr (by simp)
                    · rw [if_neg hgt', epure, tryCatch_ok] at htc
                      rw [← Except.ok.inj htc] at hK
                      have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                      rw [← hcr]
                      exact ⟨sharesDestroyed, assetsRecovered, arn, rfl, h2, h3,
                        Or.inr ⟨hgt, clamped, sharesDestroyed', assetsRecovered', arn',
                          rfl, h5, h6, h7, by simpa using hgt', rfl, rfl⟩⟩
          · rw [if_neg hgt, epure, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
            rw [← hcr]
            exact ⟨sharesDestroyed, assetsRecovered, arn, rfl, h2, h3,
              Or.inl ⟨by simpa using hgt, rfl, rfl⟩⟩

/-- **`computeClawback` no-error reduction, zero amount.** A `cr.error = none`
outcome for a zero amount destroys the holder's shares directly: the withdraw
prices `holderShares` through the withdraw pipeline, and either it fit under
`assetsAvailable` and the destroyed shares are exactly `holderShares`, or the
clamped recompute did. -/
theorem computeClawback_none_reduces_zero (lv : LawfulVault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult)
    (hz : assets.isZero = true)
    (hok : computeClawback lv assets holderShares = .ok cr) (herr : cr.error = none) :
    assets.negative = false ∧
    ∃ (assetsRecovered : STAmount) (assetsRecoveredNumber : Number),
      lv.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      ((assetsRecoveredNumber.operator_gt lv.assetsAvailable = false ∧
        cr.assetsRecovered = assetsRecovered ∧ cr.sharesDestroyed = holderShares) ∨
       (assetsRecoveredNumber.operator_gt lv.assetsAvailable = true ∧
        ∃ (clamped sharesDestroyed' assetsRecovered' : STAmount)
          (assetsRecoveredNumber' : Number),
          STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok clamped ∧
          assetsToSharesWithdraw lv clamped true false = .ok sharesDestroyed' ∧
          lv.sharesToAssetsWithdraw sharesDestroyed' false = .ok assetsRecovered' ∧
          assetsRecovered'.toNumber .to_nearest = .ok assetsRecoveredNumber' ∧
          assetsRecoveredNumber'.operator_gt lv.assetsAvailable = false ∧
          cr.assetsRecovered = assetsRecovered' ∧
          cr.sharesDestroyed = sharesDestroyed')) := by
  unfold computeClawback at hok
  simp only [pure_bind] at hok
  by_cases hneg : assets.negative = true
  · rw [if_pos hneg] at hok
    have hcr := (Except.ok.inj hok).symm
    rw [hcr] at herr
    exact absurd herr (by simp)
  · rw [if_neg hneg] at hok
    refine ⟨by simpa using hneg, ?_⟩
    obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
    rw [assetsToSharesClawback_zero lv assets holderShares hz] at htc
    have handler_err : ∀ e : Error,
        tryCatch (Except.error e :
            Except Error (DoResultPR ComputeClawbackResult ComputeClawbackResult PUnit))
          (fun e => if isOverflow e = true then
              pure (DoResultPR.return
                ⟨some .tecPATH_DRY, STAmount.zero lv.numericType, STAmount.zero .int64⟩
                PUnit.unit)
            else do
              let y ← throw e
              pure (DoResultPR.pure y PUnit.unit)) = .ok rr → False := by
      intro e htc'
      rw [tryCatch_error] at htc'
      by_cases hov : isOverflow e = true
      · rw [if_pos hov, epure] at htc'
        rw [← Except.ok.inj htc'] at hK
        have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
        rw [← hcr] at herr
        exact absurd herr (by simp)
      · rw [if_neg hov, ethrow, err_bind] at htc'
        exact absurd htc' (by simp)
    simp only [ok_bind] at htc
    cases h2 : lv.sharesToAssetsWithdraw holderShares false with
    | error e => rw [h2, err_bind] at htc; exact absurd htc (handler_err e)
    | ok assetsRecovered =>
      rw [h2] at htc
      simp only [ok_bind] at htc
      cases h3 : assetsRecovered.toNumber .to_nearest with
      | error e => rw [h3, err_bind] at htc; exact absurd htc (handler_err e)
      | ok arn =>
        rw [h3] at htc
        simp only [ok_bind] at htc
        by_cases hgt : arn.operator_gt lv.assetsAvailable = true
        · rw [if_pos hgt] at htc
          cases h4 : STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest with
          | error e => rw [h4, err_bind] at htc; exact absurd htc (handler_err e)
          | ok clamped =>
            rw [h4] at htc
            simp only [ok_bind] at htc
            cases h5 : assetsToSharesWithdraw lv clamped true false with
            | error e => rw [h5, err_bind] at htc; exact absurd htc (handler_err e)
            | ok sharesDestroyed' =>
              rw [h5] at htc
              simp only [ok_bind] at htc
              cases h6 : lv.sharesToAssetsWithdraw sharesDestroyed' false with
              | error e => rw [h6, err_bind] at htc; exact absurd htc (handler_err e)
              | ok assetsRecovered' =>
                rw [h6] at htc
                simp only [ok_bind] at htc
                cases h7 : assetsRecovered'.toNumber .to_nearest with
                | error e => rw [h7, err_bind] at htc; exact absurd htc (handler_err e)
                | ok arn' =>
                  rw [h7] at htc
                  simp only [ok_bind] at htc
                  by_cases hgt' : arn'.operator_gt lv.assetsAvailable = true
                  · rw [if_pos hgt', epure, tryCatch_ok] at htc
                    rw [← Except.ok.inj htc] at hK
                    have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                    rw [← hcr] at herr
                    exact absurd herr (by simp)
                  · rw [if_neg hgt', epure, tryCatch_ok] at htc
                    rw [← Except.ok.inj htc] at hK
                    have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
                    rw [← hcr]
                    exact ⟨assetsRecovered, arn, rfl, h3,
                      Or.inr ⟨hgt, clamped, sharesDestroyed', assetsRecovered', arn',
                        rfl, h5, h6, h7, by simpa using hgt', rfl, rfl⟩⟩
        · rw [if_neg hgt, epure, tryCatch_ok] at htc
          rw [← Except.ok.inj htc] at hK
          have hcr := Except.ok.inj (show Except.ok _ = Except.ok cr from hK)
          rw [← hcr]
          exact ⟨assetsRecovered, arn, rfl, h3, Or.inl ⟨by simpa using hgt, rfl, rfl⟩⟩

/-- **`LawfulVault.clawback` success reduction.** A run that returns no error code
exposes the `computeClawback` result (nonzero destroyed shares), the passed
too-small guard, and the three stored-field updates in the success record. -/
theorem LawfulVault.clawback_success_reduces (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    ∃ cr : ComputeClawbackResult,
      computeClawback lv assets holderShares = .ok cr ∧ cr.error = none ∧
      cr.sharesDestroyed.isZero = false ∧
      r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
      ∃ (sharesDestroyedNumber assetsRecoveredNumber
          assetsTotal' sharesTotal' assetsAvailable' : Number)
        (assetsTotalRounded assetsTotalRounded' : STAmount),
        cr.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber ∧
        cr.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
        lv.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsTotal' ∧
        STAmount.ofNumber lv.numericType lv.assetsTotal .to_nearest = .ok assetsTotalRounded ∧
        STAmount.ofNumber lv.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded' ∧
        (assetsRecoveredNumber.mantissa_ != 0 &&
          assetsTotalRounded.operator_eq assetsTotalRounded') = false ∧
        lv.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok sharesTotal' ∧
        lv.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok assetsAvailable' ∧
        r.vault'.toRawVault = { lv.toRawVault with sharesTotal := sharesTotal', assetsAvailable := assetsAvailable', assetsTotal := assetsTotal' } := by
  unfold LawfulVault.clawback at hok
  simp only [] at hok
  obtain ⟨cr, hcomp, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_bind] at hok
  by_cases he : cr.error.isSome = true
  · rw [if_pos he] at hok
    have hr := (Except.ok.inj hok).symm
    rw [hr] at herr
    have herr' : cr.error = none := herr
    rw [herr'] at he
    exact absurd he (by simp)
  · rw [if_neg he] at hok
    have herr2 : cr.error = none := by
      cases hce : cr.error with
      | none => rfl
      | some t => exact absurd (by rw [hce]; rfl) he
    by_cases hz : cr.sharesDestroyed.isZero = true
    · rw [if_pos hz] at hok
      have hr := (Except.ok.inj hok).symm
      rw [hr] at herr
      exact absurd herr (by simp [ClawbackResult.rejected])
    · rw [if_neg hz] at hok
      obtain ⟨sbn, hsbn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, harn, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, hatr, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', hatr', hok⟩ := bind_ok_peel _ _ _ hok
      by_cases hg : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos hg] at hok
        have hr := (Except.ok.inj hok).symm
        rw [hr] at herr
        exact absurd herr (by simp [ClawbackResult.rejected])
      · rw [if_neg hg] at hok
        obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨lv', htl, hok⟩ := bind_ok_peel _ _ _ hok
        obtain rfl := Except.ok.inj hok
        exact ⟨cr, hcomp, herr2, by simpa using hz, rfl, rfl,
          sbn, arn, at', st', av', atr, atr', hsbn, harn, hat, hatr, hatr',
          by simpa using hg, hst, hav, (RawVault.to_lawful_ok htl).1⟩

/-- **Proof body of `clawback_zero_all_shares`.** -/
theorem LawfulVault.clawback_zero_all_shares_proof (lv : LawfulVault)
    (assets holderShares assetsRecovered : STAmount) (assetsRecoveredNumber : Number)
    (r : ClawbackResult)
    (hz : assets.isZero = true)
    (hassets : lv.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt lv.assetsAvailable = false)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = assetsRecovered ∧
    holderShares.isZero = false := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra, hsd, -⟩ :=
    LawfulVault.clawback_success_reduces lv assets holderShares r hok herr
  obtain ⟨-, ar, arn, har, harn, hdisj⟩ :=
    computeClawback_none_reduces_zero lv assets holderShares cr hz hcomp herr2
  -- the run is deterministic, pin the intermediates against the hypotheses
  obtain rfl := Except.ok.inj (har.symm.trans hassets)
  obtain rfl := Except.ok.inj (harn.symm.trans hnum)
  rcases hdisj with ⟨-, hra', hsd'⟩ | ⟨hgt, -⟩
  · rw [hsd'] at hsd hcrnz
    exact ⟨hsd, hra.trans hra', hcrnz⟩
  · rw [hle] at hgt
    exact absurd hgt Bool.false_ne_true

end XRPL.Model.SingleAssetVault
