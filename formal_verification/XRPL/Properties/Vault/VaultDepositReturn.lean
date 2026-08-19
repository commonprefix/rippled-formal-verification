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
    ter = .tecPRECISION_LOSS :=
  Vault.roundedDepositAmount_rejected_code_proof v amountDeposit ter hok

/-! ## `Vault.deposit` -/

/-- An `amountDeposit` that `roundedDepositAmount` rejects makes `deposit`
fail with `tecINTERNAL`: the depositing transaction never runs on such
an amount. -/
theorem Vault.deposit_rejected_request (amountDeposit : STAmount) (isDonation : Bool)
    (ter : TER)
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rejected_request_proof v amountDeposit isDonation ter hrej

/-- `amountDeposit` rounds to zero at the vault exponent: `tecINTERNAL`. -/
theorem Vault.deposit_rounded_zero (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rounded_zero_proof v amountDeposit roundedAmount isDonation hround hz

/-- A donation into a vault with no outstanding shares: `tecNO_PERMISSION`. -/
theorem Vault.deposit_donation_no_shares (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0) :
    v.deposit amountDeposit true = .ok (.rejected v .tecNO_PERMISSION) :=
  Vault.deposit_donation_no_shares_proof v amountDeposit roundedAmount hrounded hsh

/-- A non-donation deposit into an insolvent vault: `tecLOCKED`. -/
theorem Vault.deposit_insolvent (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLOCKED) :=
  Vault.deposit_insolvent_proof v amountDeposit roundedAmount hrounded hins

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
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_maximum_exceeded_proof v amountDeposit roundedAmount c s cN sN at' av' st'
    hrounded hins hcomp hcN hsN hat hav hst hmax

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
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit true = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_donation_maximum_proof v amountDeposit roundedAmount aN zN at' av' st'
    hrounded hsh haN hzN hat hav hst hmax

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
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false) :
    v.deposit amountDeposit false =
      .ok ⟨none, { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' },
        c, s⟩ :=
  Vault.deposit_success_proof v amountDeposit roundedAmount c s cN sN at' av' st'
    hrounded hins hcomp hcN hsN hat hav hst hmax

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
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false) :
    v.deposit amountDeposit true =
      .ok ⟨none, { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' },
        roundedAmount, STAmount.zero .int64⟩ :=
  Vault.deposit_donation_success_proof v amountDeposit roundedAmount aN zN at' av' st'
    hrounded hsh haN hzN hat hav hst hmax

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
