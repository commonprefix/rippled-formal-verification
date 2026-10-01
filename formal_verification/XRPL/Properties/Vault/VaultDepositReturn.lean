import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.DepositExitsB
import XRPL.Properties.Vault.Proofs.DepositExitsC

/-! # `Vault.deposit` exits

One theorem per exit, each giving the exact result record. Conclusions are
about the public API, `Vault.roundedDepositAmount` and `Vault.deposit`.
Every rejection returns `DepositResult.rejected`: the vault unchanged and both
amount fields zero. The success cases return the post-state as a `Vault`
(`v'`), proving the `to_lawful` re-check succeeds via `deposit_poststate_lawful`,
so the `.notLawful` throw is unreachable. -/

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
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter))
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit isDonation hpos = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rejected_request_proof v amountDeposit isDonation ter hrej hpos

/-- `amountDeposit` rounds to zero at the vault exponent: `tecINTERNAL`. -/
theorem Vault.deposit_rounded_zero (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit isDonation hpos = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rounded_zero_proof v amountDeposit roundedAmount isDonation hround hz hpos

/-- A donation into a vault with no outstanding shares: `tecNO_PERMISSION`. -/
theorem Vault.deposit_donation_no_shares (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit true hpos = .ok (.rejected v .tecNO_PERMISSION) :=
  Vault.deposit_donation_no_shares_proof v amountDeposit roundedAmount hrounded hsh hpos

/-- A non-donation deposit into an insolvent vault: `tecLOCKED`. -/
theorem Vault.deposit_insolvent (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecLOCKED) :=
  Vault.deposit_insolvent_proof v amountDeposit roundedAmount hrounded hins hpos

/-- The updated total exceeds `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_maximum_exceeded (amountDeposit roundedAmount c cl s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success c s))
    (hclamp : clampToSumExponent v.assetsTotal c = .ok cl)
    (hcN : cl.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_maximum_exceeded_proof v amountDeposit roundedAmount c cl s cN sN at' av' st'
    hrounded hins hcomp hclamp hcN hsN hat hav hst hmax hpos

/-- A donation pushes the total above `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_donation_maximum (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit true hpos = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_donation_maximum_proof v amountDeposit roundedAmount aN zN at' av' st'
    hpos hrounded hsh haN hzN hat hav hst hmax

/-- Every guard passes: the deposit returns the exact updated vault (still a
`Vault`), the taken `amountDeposit'`, and the issued shares. The
`to_lawful` re-check is proven to succeed. -/
theorem Vault.deposit_success (amountDeposit roundedAmount priced c s : STAmount)
    (cN sN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success priced s))
    (hclamp : clampToSumExponent v.assetsTotal priced = .ok c)
    (hcpos : c.integral = true ∨ 0 < c.toRat)
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + s.toRat ≤ 2 ^ 63 - 1)
    (hpos : 0 < amountDeposit.toRat) :
    ∃ v' : Vault, v.deposit amountDeposit false hpos = .ok ⟨none, v', c, s⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } :=
  Vault.deposit_success_proof v amountDeposit roundedAmount priced c s cN sN at' av' st'
    hL hAV hcanonA hrounded hins hcomp hclamp hcpos hcN hsN hat hav hst hmax hSsz hpos

/-- The grid clamp can snap a priced charge below one grid step to zero (or
below), and the deposit then fails with `tecPRECISION_LOSS`. With
`deposit_success` this covers both outcomes of the clamp. -/
theorem Vault.deposit_clamp_precision_loss (amountDeposit roundedAmount priced c s : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success priced s))
    (hclamp : clampToSumExponent v.assetsTotal priced = .ok c)
    (hvanish : c.integral = false ∧ c.toRat ≤ 0)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.deposit_clamp_precision_loss_proof v amountDeposit roundedAmount priced c s
    hrounded hins hcomp hclamp hvanish hpos

/-- A donation with every guard passing: `roundedAmount` is taken, no shares
are issued, both asset totals grow, and the post-state is a `Vault`. -/
theorem Vault.deposit_donation_success (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + (STAmount.zero .int64).toRat ≤ 2 ^ 63 - 1)
    (hpos : 0 < amountDeposit.toRat) :
    ∃ v' : Vault, v.deposit amountDeposit true hpos = .ok ⟨none, v', roundedAmount, STAmount.zero .int64⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } :=
  Vault.deposit_donation_success_proof v amountDeposit roundedAmount aN zN at' av' st'
    hL hAV hcanonA hnnA hrounded hsh haN hzN hat hav hst hmax hSsz hpos

/-- Every outcome of a deposit that runs without a throw. -/
theorem Vault.deposit_error_codes (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hpos : 0 < amountDeposit.toRat) (hok : v.deposit amountDeposit isDonation hpos = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED :=
  Vault.deposit_error_codes_proof v amountDeposit isDonation r hpos hok

end XRPL.Model.SingleAssetVault
