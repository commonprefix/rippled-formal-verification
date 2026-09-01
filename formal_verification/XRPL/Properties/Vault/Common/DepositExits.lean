import XRPL.Properties.Vault.Common.DepositReduction

/-! # Deposit exit reductions

`computeDeposit_codes` inventories every outcome of a `computeDeposit` that
runs without a throw, and `LawfulVault.deposit_error_codes_proof` walks every exit of
`LawfulVault.deposit` to inventory the codes a deposit can return. Both walks use
`bind_ok_peel`, `if`-elimination, and the `tryCatch` step lemmas only, keeping
the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeDeposit` that runs without a throw: one of the
three error codes, or a success carrying the priced amounts. -/
theorem computeDeposit_codes (lv : LawfulVault) (amount : STAmount) (cres : ComputeDepositResult)
    (hok : computeDeposit lv amount = .ok cres) :
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
  cases hatsd : assetsToSharesDeposit lv amount with
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
      cases hsad : sharesToAssetsDeposit lv shares with
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
theorem LawfulVault.deposit_error_codes_proof (lv : LawfulVault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : lv.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED := by
  unfold LawfulVault.deposit at hok
  simp only [] at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok
    injection hok with h; rw [← h]
    exact .inr (.inl rfl)
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && lv.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok
      injection hok with h; rw [← h]
      exact .inr (.inr (.inl rfl))
    · rw [if_neg h2] at hok
      by_cases h3 : (lv.isInsolvent && !isDonation) = true
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
          by_cases hm : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok
            injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
          · rw [if_neg hm] at hok
            obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]
            exact .inl rfl
        · rw [if_neg hd] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          rcases computeDeposit_codes lv amount cres hcd with h5 | h5 | h5 | ⟨a, s, h5⟩
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
            by_cases hm : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true
            · rw [if_pos hm] at hok
              injection hok with h; rw [← h]
              exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
            · rw [if_neg hm] at hok
              obtain ⟨lv', _, hok⟩ := bind_ok_peel _ _ _ hok
              injection hok with h; rw [← h]
              exact .inl rfl

/-- **Proof body of `roundedDepositAmount_rejected_code`.** -/
theorem LawfulVault.roundedDepositAmount_rejected_code_proof (lv : LawfulVault) (amountDeposit : STAmount)
    (ter : TER) (hok : lv.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS := by
  obtain ⟨ra, _, _, h⟩ := roundedDepositAmount_rejected lv amountDeposit ter hok
  exact h

/-- **Proof body of `deposit_rejected_request`.** -/
theorem LawfulVault.deposit_rejected_request_proof (lv : LawfulVault) (amountDeposit : STAmount)
    (isDonation : Bool) (ter : TER)
    (hrej : lv.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    lv.deposit amountDeposit isDonation = .ok (.rejected lv .tecINTERNAL) := by
  obtain ⟨ra, hround, hz, _⟩ := roundedDepositAmount_rejected lv amountDeposit ter hrej
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- **Proof body of `deposit_rounded_zero`.** -/
theorem LawfulVault.deposit_rounded_zero_proof (lv : LawfulVault) (amountDeposit roundedAmount : STAmount)
    (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit lv.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    lv.deposit amountDeposit isDonation = .ok (.rejected lv .tecINTERNAL) := by
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- **Proof body of `deposit_donation_no_shares`.** -/
theorem LawfulVault.deposit_donation_no_shares_proof (lv : LawfulVault) (amountDeposit roundedAmount : STAmount)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : lv.sharesTotal.mantissa_ = 0) :
    lv.deposit amountDeposit true = .ok (.rejected lv .tecNO_PERMISSION) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [Bool.true_and]; exact beq_iff_eq.mpr hsh)]
  rfl

/-- **Proof body of `deposit_insolvent`.** -/
theorem LawfulVault.deposit_insolvent_proof (lv : LawfulVault) (amountDeposit roundedAmount : STAmount)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : lv.isInsolvent = true) :
    lv.deposit amountDeposit false = .ok (.rejected lv .tecLOCKED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [hins]; rfl)]
  rfl

/-- **Proof body of `deposit_maximum_exceeded`.** -/
theorem LawfulVault.deposit_maximum_exceeded_proof (lv : LawfulVault) (amountDeposit roundedAmount c s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : lv.isInsolvent = false)
    (hcomp : computeDeposit lv roundedAmount = .ok (.success c s))
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : lv.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true) :
    lv.deposit amountDeposit false = .ok (.rejected lv .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg Bool.false_ne_true]
  rw [hcomp, ok_bind]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

/-- **Proof body of `deposit_donation_maximum`.** -/
theorem LawfulVault.deposit_donation_maximum_proof (lv : LawfulVault) (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : lv.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : lv.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true) :
    lv.deposit amountDeposit true = .ok (.rejected lv .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos trivial]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

end XRPL.Model.SingleAssetVault
