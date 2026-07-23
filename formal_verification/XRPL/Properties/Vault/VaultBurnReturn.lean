import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.BurnExits

/-! # `Vault.burnShares` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.canBurnShares` -/

/-- `tecNO_PERMISSION` is the only rejection `canBurnShares` can
return. -/
theorem Vault.canBurnShares_rejected_code (ter : TER)
    (hok : v.canBurnShares = .ok (.error ter)) :
    ter = .tecNO_PERMISSION :=
  Vault.canBurnShares_rejected_code_proof v ter hok

/-- Force-burning shares is allowed only when shares are outstanding while
both asset totals are zero. When `sharesTotal` is zero, or `assetsTotal` or
`assetsAvailable` is nonzero: `.error .tecNO_PERMISSION`. -/
theorem Vault.canBurnShares_no_permission
    (hperm : v.sharesTotal.mantissa_ = 0 ∨
      v.assetsTotal.mantissa_ ≠ 0 ∨ v.assetsAvailable.mantissa_ ≠ 0) :
    v.canBurnShares = .ok (.error .tecNO_PERMISSION) :=
  Vault.canBurnShares_no_permission_proof v hperm

/-- The vault has outstanding shares and both `assetsTotal` and
`assetsAvailable` are zero: the result is the whole `sharesTotal` converted
to an `int64` amount. -/
theorem Vault.canBurnShares_ok (sharesTotalAmount : STAmount)
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (hat : v.assetsTotal.mantissa_ = 0)
    (hav : v.assetsAvailable.mantissa_ = 0)
    (hshares : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    v.canBurnShares = .ok (.assets sharesTotalAmount) :=
  Vault.canBurnShares_ok_proof v sharesTotalAmount hsh hat hav hshares

/-! ## `Vault.burnShares` -/

/-- `burnShares` stores the rounded difference `sharesTotal - sharesDestroyed`
and changes no other field. -/
theorem Vault.burnShares_ok (sharesDestroyed : STAmount)
    (sharesDestroyedNumber st' : Number)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st') :
    v.burnShares sharesDestroyed = .ok { v with sharesTotal := st' } :=
  Vault.burnShares_ok_proof v sharesDestroyed sharesDestroyedNumber st' hnum hst

end XRPL.Model.SingleAssetVault
