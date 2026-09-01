import XRPL.Properties.Vault.Common.DepositExits
import XRPL.Properties.Vault.Common.Preservation

/-! # `LawfulVault.deposit` exits

One theorem per exit, each giving the exact result record. Conclusions are
about the public API, `LawfulVault.roundedDepositAmount` and `LawfulVault.deposit`.
Every rejection returns `DepositResult.rejected`: the vault unchanged and both
amount fields zero. The success cases return the post-state as a `LawfulVault`
(`lv'`), proving the `to_lawful` re-check succeeds via `deposit_poststate_lawful`,
so the `.notLawful` throw is unreachable. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)

/-! ## `LawfulVault.roundedDepositAmount` -/

/-- `tecPRECISION_LOSS` is the only rejection `roundedDepositAmount` can
return. -/
theorem LawfulVault.roundedDepositAmount_rejected_code (amountDeposit : STAmount) (ter : TER)
    (hok : lv.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS :=
  LawfulVault.roundedDepositAmount_rejected_code_proof lv amountDeposit ter hok

/-! ## `LawfulVault.deposit` -/

/-- An `amountDeposit` that `roundedDepositAmount` rejects makes `deposit`
fail with `tecINTERNAL`: the depositing transaction never runs on such
an amount. -/
theorem LawfulVault.deposit_rejected_request (amountDeposit : STAmount) (isDonation : Bool)
    (ter : TER)
    (hrej : lv.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    lv.deposit amountDeposit isDonation = .ok (.rejected lv .tecINTERNAL) :=
  LawfulVault.deposit_rejected_request_proof lv amountDeposit isDonation ter hrej

/-- `amountDeposit` rounds to zero at the vault exponent: `tecINTERNAL`. -/
theorem LawfulVault.deposit_rounded_zero (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit lv.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    lv.deposit amountDeposit isDonation = .ok (.rejected lv .tecINTERNAL) :=
  LawfulVault.deposit_rounded_zero_proof lv amountDeposit roundedAmount isDonation hround hz

/-- A donation into a vault with no outstanding shares: `tecNO_PERMISSION`. -/
theorem LawfulVault.deposit_donation_no_shares (amountDeposit roundedAmount : STAmount)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : lv.sharesTotal.mantissa_ = 0) :
    lv.deposit amountDeposit true = .ok (.rejected lv .tecNO_PERMISSION) :=
  LawfulVault.deposit_donation_no_shares_proof lv amountDeposit roundedAmount hrounded hsh

/-- A non-donation deposit into an insolvent vault: `tecLOCKED`. -/
theorem LawfulVault.deposit_insolvent (amountDeposit roundedAmount : STAmount)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : lv.isInsolvent = true) :
    lv.deposit amountDeposit false = .ok (.rejected lv .tecLOCKED) :=
  LawfulVault.deposit_insolvent_proof lv amountDeposit roundedAmount hrounded hins

/-- The updated total exceeds `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem LawfulVault.deposit_maximum_exceeded (amountDeposit roundedAmount c s : STAmount)
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
    lv.deposit amountDeposit false = .ok (.rejected lv .tecLIMIT_EXCEEDED) :=
  LawfulVault.deposit_maximum_exceeded_proof lv amountDeposit roundedAmount c s cN sN at' av' st'
    hrounded hins hcomp hcN hsN hat hav hst hmax

/-- A donation pushes the total above `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem LawfulVault.deposit_donation_maximum (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : lv.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : lv.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = true) :
    lv.deposit amountDeposit true = .ok (.rejected lv .tecLIMIT_EXCEEDED) :=
  LawfulVault.deposit_donation_maximum_proof lv amountDeposit roundedAmount aN zN at' av' st'
    hrounded hsh haN hzN hat hav hst hmax

/-- Every guard passes: the deposit returns the exact updated vault (still a
`LawfulVault`), the taken `amountDeposit'`, and the issued shares. The
`to_lawful` re-check is proven to succeed via `deposit_poststate_lawful`. -/
theorem LawfulVault.deposit_success (amountDeposit roundedAmount c s : STAmount)
    (cN sN at' av' st' : Number)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : lv.isInsolvent = false)
    (hcomp : computeDeposit lv roundedAmount = .ok (.success c s))
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : lv.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (lv.toExact.sharesTotal : ℚ) + s.toRat ≤ 2 ^ 63 - 1) :
    ∃ lv' : LawfulVault, lv.deposit amountDeposit false = .ok ⟨none, lv', c, s⟩ ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  obtain ⟨lv', htl, hlv'eq⟩ := LawfulVault.deposit_poststate_lawful lv amountDeposit false hL hAV hcanonA hnnA
    roundedAmount c s cN sN at' av' st' hround hnz
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => hcomp) hcN hsN hat hav hst hmax hSsz
  refine ⟨lv', ?_, hlv'eq⟩
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hnz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg Bool.false_ne_true]
  rw [hcomp, ok_bind]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true), htl]
  rfl

/-- A donation with every guard passing: `roundedAmount` is taken, no shares
are issued, both asset totals grow, and the post-state is a `LawfulVault`. -/
theorem LawfulVault.deposit_donation_success (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : lv.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : lv.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (lv.toExact.sharesTotal : ℚ) + (STAmount.zero .int64).toRat ≤ 2 ^ 63 - 1) :
    ∃ lv' : LawfulVault, lv.deposit amountDeposit true = .ok ⟨none, lv', roundedAmount, STAmount.zero .int64⟩ ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded lv amountDeposit roundedAmount hrounded
  obtain ⟨lv', htl, hlv'eq⟩ := LawfulVault.deposit_poststate_lawful lv amountDeposit true hL hAV hcanonA hnnA
    roundedAmount roundedAmount (STAmount.zero .int64) aN zN at' av' st' hround hnz
    (fun _ => hsh) (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (by decide)) haN hzN hat hav hst hmax hSsz
  refine ⟨lv', ?_, hlv'eq⟩
  unfold LawfulVault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hnz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos trivial]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true), htl]
  rfl

/-- Every outcome of a deposit that runs without a throw. -/
theorem LawfulVault.deposit_error_codes (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hok : lv.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED :=
  LawfulVault.deposit_error_codes_proof lv amountDeposit isDonation r hok

end XRPL.Model.SingleAssetVault
