import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # `computeDeposit`

The successful path of `computeDeposit`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **`computeDeposit` success reduction.** A `.success` outcome forces the body's
happy path: the shares priced (nonzero), the assets re-priced, and the internal
`operator_gt` guard reads `false` (`amountDeposit' ≤ amountDeposit`). The
`try`/`catch` handler can only produce `.error` codes, so it is ruled out. -/
lemma computeDeposit_success_reduces (v : Vault) (amount c s : STAmount)
    (hok : computeDeposit v amount = .ok (.success c s)) :
    ∃ shares : STAmount,
      assetsToSharesDeposit v amount = .ok shares ∧
      shares.isZero = false ∧
      sharesToAssetsDeposit v shares = .ok c ∧
      c.operator_gt amount = .ok false ∧
      s = shares := by
  unfold computeDeposit at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  -- The handler can only yield `.error` codes, so a `.success` forces the body path.
  have handler_absurd : ∀ (e : Error),
      tryCatch (Except.error e : Except Error (DoResultPR ComputeDepositResult ComputeDepositResult PUnit))
        (fun e => if isOverflow e = true then
            pure (DoResultPR.return (ComputeDepositResult.error TER.tecPATH_DRY) PUnit.unit)
          else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr → False := by
    intro e htc'
    rw [tryCatch_error] at htc'
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc'
      rw [← Except.ok.inj htc'] at hK; exact absurd hK (by simp [epure])
    · rw [if_neg hov, ethrow, err_bind] at htc'
      exact absurd htc' (by simp)
  cases hatsd : assetsToSharesDeposit v amount with
  | error e => rw [hatsd, err_bind] at htc; exact (handler_absurd e htc).elim
  | ok shares =>
    simp only [hatsd, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK; exact absurd hK (by simp [epure])
    · rw [if_neg hz] at htc
      cases hsad : sharesToAssetsDeposit v shares with
      | error e2 => rw [hsad, err_bind] at htc; exact (handler_absurd e2 htc).elim
      | ok amountDeposit' =>
        simp only [hsad, ok_bind] at htc
        cases hgt : amountDeposit'.operator_gt amount with
        | error e3 => rw [hgt, err_bind] at htc; exact (handler_absurd e3 htc).elim
        | ok gtb =>
          simp only [hgt, ok_bind] at htc
          by_cases hgtb : gtb = true
          · rw [if_pos hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK; exact absurd hK (by simp [epure])
          · rw [if_neg hgtb, tryCatch_ok] at htc
            have hgtf : gtb = false := by simpa using hgtb
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.success amountDeposit' shares)
                = Except.ok (ComputeDepositResult.success c s) := hK
            obtain ⟨hc, hs⟩ := ComputeDepositResult.success.inj (Except.ok.inj hK2)
            subst hc
            refine ⟨shares, ?_, ?_, ?_, ?_, ?_⟩
            · rfl
            · simpa using hz
            · exact hsad
            · rw [← hgtf]; exact hgt
            · exact hs.symm

/-- Every outcome of a `computeDeposit` that runs without a throw: one of the
three error codes, or a success carrying the priced amounts. -/
lemma computeDeposit_codes (v : Vault) (amount : STAmount) (cres : ComputeDepositResult)
    (hok : computeDeposit v amount = .ok cres) :
    cres = .error .tecPRECISION_LOSS ∨
    cres = .error .tecINTERNAL ∨
    cres = .error .tecPATH_DRY ∨
    ∃ a s, cres = .success a s := by
  unfold computeDeposit at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  have handler_path_dry : ∀ (e : Error),
      tryCatch (Except.error e : Except Error (DoResultPR ComputeDepositResult ComputeDepositResult PUnit))
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

/-- **`computeDeposit` charge bound.** On comparable operands the internal
`operator_gt` guard means the charge never exceeds the rounded deposit:
`amountDeposit'.toRat ≤ amountDeposit.toRat`. -/
lemma computeDeposit_success_charge_le (v : Vault) (amount c s : STAmount)
    (hcmp : STAmount.CmpFaithful c amount)
    (hok : computeDeposit v amount = .ok (.success c s)) :
    c.toRat ≤ amount.toRat := by
  obtain ⟨_, _, _, _, hgt, _⟩ := computeDeposit_success_reduces v amount c s hok
  exact STAmount.operator_gt_false_le c amount hcmp hgt

end XRPL.Model.SingleAssetVault
