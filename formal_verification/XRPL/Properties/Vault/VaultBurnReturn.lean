import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.BurnExits
import XRPL.Properties.Vault.Common.Preservation

/-! # `LawfulVault.burnShares` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)

/-! ## `LawfulVault.canBurnShares` -/

/-- `tecNO_PERMISSION` is the only rejection `canBurnShares` can return. -/
theorem LawfulVault.canBurnShares_rejected_code (ter : TER)
    (hok : lv.canBurnShares = .ok (.error ter)) :
    ter = .tecNO_PERMISSION :=
  LawfulVault.canBurnShares_rejected_code_proof lv ter hok

/-- Force-burning shares is allowed only when shares are outstanding while both
asset totals are zero. When `sharesTotal` is zero, or `assetsTotal` or
`assetsAvailable` is nonzero: `.error .tecNO_PERMISSION`. -/
theorem LawfulVault.canBurnShares_no_permission
    (hperm : lv.sharesTotal.mantissa_ = 0 ∨
      lv.assetsTotal.mantissa_ ≠ 0 ∨ lv.assetsAvailable.mantissa_ ≠ 0) :
    lv.canBurnShares = .ok (.error .tecNO_PERMISSION) :=
  LawfulVault.canBurnShares_no_permission_proof lv hperm

/-- The vault has outstanding shares and both `assetsTotal` and
`assetsAvailable` are zero: the result is the whole `sharesTotal` converted
to an `int64` amount. -/
theorem LawfulVault.canBurnShares_ok (sharesTotalAmount : STAmount)
    (hsh : lv.sharesTotal.mantissa_ ≠ 0)
    (hat : lv.assetsTotal.mantissa_ = 0)
    (hav : lv.assetsAvailable.mantissa_ = 0)
    (hshares : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    lv.canBurnShares = .ok (.assets sharesTotalAmount) :=
  LawfulVault.canBurnShares_ok_proof lv sharesTotalAmount hsh hat hav hshares

/-! ## `LawfulVault.burnShares` -/

/-- `burnShares` stores the rounded difference `sharesTotal - sharesDestroyed`
and changes no other field. The post-state is a `LawfulVault` (`lv'`): the in-op
`to_lawful` re-check succeeds via `burnShares_poststate_lawful`. -/
theorem LawfulVault.burnShares_ok (sharesDestroyed sharesTotalAmount : STAmount)
    (sharesDestroyedNumber st' : Number)
    (hcan : lv.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (hst : lv.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st') :
    ∃ lv' : LawfulVault, lv.burnShares sharesDestroyed = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with sharesTotal := st' } := by
  obtain ⟨lv', htl, hlv'eq⟩ := LawfulVault.burnShares_poststate_lawful lv sharesDestroyed sharesTotalAmount
    sharesDestroyedNumber st' hcan hcanon hnn hle hfit hnum hst
  refine ⟨lv', ?_, hlv'eq⟩
  unfold LawfulVault.burnShares
  simp only []
  rw [hnum, ok_bind, hst, ok_bind, htl]

end XRPL.Model.SingleAssetVault
