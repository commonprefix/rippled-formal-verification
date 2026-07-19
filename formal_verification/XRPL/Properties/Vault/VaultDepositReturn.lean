import XRPL.Properties.Vault.Common.DepositExits

/-! # `Vault.deposit` exits

One theorem per exit, each giving the exact result record. Conclusions are
about the public API, `Vault.roundedDepositAmount` and `Vault.deposit`.
Hypotheses may name internal functions and intermediate values where an exit's
trigger is internal to the exchange computation. Every rejection returns
`DepositResult.rejected`: the vault unchanged and both amount fields zero.
The accuracy bounds are in `VaultDeposit.lean`. Lawfulness preservation is
`deposit_lawful` in `Lawful.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.roundedDepositAmount` -/

/-- `tecPRECISION_LOSS` is the only rejection `roundedDepositAmount` can
return. -/
theorem Vault.roundedDepositAmount_rejected_code (amountDeposit : STAmount) (ter : TER)
    (hok : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS := by
  obtain ⟨ra, _, _, h⟩ := roundedDepositAmount_rejected v amountDeposit ter hok
  exact h

/-! ## `Vault.deposit` -/

/-- An `amountDeposit` that `roundedDepositAmount` rejects makes `deposit`
fail with `tecINTERNAL`: the depositing transaction never runs on such
an amount. -/
theorem Vault.deposit_rejected_request (amountDeposit : STAmount) (isDonation : Bool)
    (ter : TER)
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) := by
  obtain ⟨ra, hround, hz, _⟩ := roundedDepositAmount_rejected v amountDeposit ter hrej
  unfold Vault.deposit
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- `amountDeposit` rounds to zero at the vault exponent: `tecINTERNAL`. -/
theorem Vault.deposit_rounded_zero (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) := by
  unfold Vault.deposit
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- A donation into a vault with no outstanding shares: `tecNO_PERMISSION`. -/
theorem Vault.deposit_donation_no_shares (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0) :
    v.deposit amountDeposit true = .ok (.rejected v .tecNO_PERMISSION) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [Bool.true_and]; exact beq_iff_eq.mpr hsh)]
  rfl

/-- A non-donation deposit into an insolvent vault: `tecLOCKED`. -/
theorem Vault.deposit_insolvent (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLOCKED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [hins]; rfl)]
  rfl

/-- The updated total exceeds `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_maximum_exceeded (amountDeposit roundedAmount c s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success c s))
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : v.assetsMaximum.any (fun m => at'.operator_gt m) = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg Bool.false_ne_true]
  rw [hcomp, ok_bind]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

/-- A donation pushes the total above `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_donation_maximum (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : v.assetsMaximum.any (fun m => at'.operator_gt m) = true) :
    v.deposit amountDeposit true = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos trivial]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

/-- Every guard passes: the deposit returns the exact updated vault, the taken
`amountDeposit'`, and the issued shares. -/
theorem Vault.deposit_success (amountDeposit roundedAmount c s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success c s))
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : v.assetsMaximum.any (fun m => at'.operator_gt m) = false) :
    v.deposit amountDeposit false =
      .ok ⟨none, { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' },
        c, s⟩ := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg Bool.false_ne_true]
  rw [hcomp, ok_bind]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true)]
  rfl

/-- A donation with every guard passing: `roundedAmount` is taken, no shares
are issued, both asset totals grow. -/
theorem Vault.deposit_donation_success (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : v.assetsMaximum.any (fun m => at'.operator_gt m) = false) :
    v.deposit amountDeposit true =
      .ok ⟨none, { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' },
        roundedAmount, STAmount.zero .int64⟩ := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos trivial]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true)]
  rfl

/-- Every outcome of a deposit that runs without a throw. -/
theorem Vault.deposit_error_codes (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED :=
  Vault.deposit_error_codes_proof v amountDeposit isDonation r hok

end XRPL.Model.SingleAssetVault
