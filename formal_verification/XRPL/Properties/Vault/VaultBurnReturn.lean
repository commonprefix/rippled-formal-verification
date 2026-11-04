import XRPL.Properties.Vault.Proofs.Burn

/-! # `Vault.burnShares` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- `tecNO_PERMISSION` and `tecLIMIT_EXCEEDED` are the only rejections `canBurnShares` can
return. -/
theorem Vault.canBurnShares_rejected_code (amount holderShares : STAmount) (ter : TER)
    (hok : (v.canBurnShares amount holderShares).run = .ok (.error ter)) :
    ter = .tecNO_PERMISSION ∨ ter = .tecLIMIT_EXCEEDED :=
  Vault.canBurnShares_rejected_code_proof v amount holderShares ter hok

/-- The exits of `canBurnShares`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.canBurnShares_exits (amount holderShares : STAmount) :
    (v.isInsolvent = false → (v.canBurnShares amount holderShares).run = .ok (.error .tecNO_PERMISSION)) ∧
    (v.isInsolvent = true → (!amount.isZero && !(amount.operator_eq holderShares)) = true →
      (v.canBurnShares amount holderShares).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    ∀ sharesTotalAmount : STAmount, v.isInsolvent = true →
      (!amount.isZero && !(amount.operator_eq holderShares)) = false →
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) :=
  ⟨Vault.canBurnShares_no_permission_proof v amount holderShares,
    Vault.canBurnShares_limit_exceeded_proof v amount holderShares, Vault.canBurnShares_ok_proof v amount holderShares⟩

/-- The exits of `burnShares`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.burnShares_exits (sharesDestroyed : STAmount) :
    (sharesDestroyed.isZero = true → (v.burnShares sharesDestroyed).run = .ok (.error .tecPRECISION_LOSS)) ∧
    -- the destroyed shares are a holder's balance: a canonical, nonnegative MPT amount within the share total
    ∀ (amount holderShares sharesTotalAmount : STAmount) (sharesDestroyedNumber st' : Number),
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      sharesDestroyed.IntegralCanonical → sharesDestroyed.negative = false → sharesDestroyed.isZero = false →
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat →
      sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber →
      v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st' →
      ∃ v' : Vault, (v.burnShares sharesDestroyed).run = .ok (.ok v') ∧
        v'.toRawVault = { v.toRawVault with sharesTotal := st' } :=
  ⟨Vault.burnShares_zero_shares_proof v sharesDestroyed,
    fun amount holderShares sharesTotalAmount =>
      Vault.burnShares_ok_proof v amount holderShares sharesDestroyed sharesTotalAmount⟩

end XRPL.Model.SingleAssetVault
