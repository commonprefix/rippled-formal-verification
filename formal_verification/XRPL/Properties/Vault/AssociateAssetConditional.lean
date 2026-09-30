import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve

/-! # Withdraw and clawback keep a fractional vault on the asset grid

Temporary: to be replaced when `associateAsset` is modeled. Absent that step, a
withdrawal or clawback from an on-grid fractional vault leaves every asset field on the
`STAmount` grid, as long as the new stored totals do not underflow the IOU floor `10⁻⁸¹`
(they can: see `Vault.withdraw_associateAsset_rounds`). -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Withdraw keeps a fractional vault on the asset's `STAmount` grid**, as long as the
stored asset fields do not underflow the IOU floor `10⁻⁸¹`. -/
theorem Vault.withdraw_assetsRounded_preserved (v : Vault) (amount : WithdrawAmount)
    (waive : Bool) (r : WithdrawResult)
    (hfr : v.numericType = .fractional)
    (hpre : ¬ v.assetsRounded)
    (hsbc : r.sharesBurned.Canonical)
    (hsbnn : 0 ≤ r.sharesBurned.toRat)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waive hpos = .ok r) (herr : r.error = none)
    (hnf₁ : r.vault'.assetsTotal.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsTotal.toRat)
    (hnf₂ : r.vault'.assetsAvailable.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsAvailable.toRat) :
    ¬ r.vault'.assetsRounded :=
  Vault.withdraw_assetsRounded_preserved_proof v amount waive r hfr hpre hsbc hsbnn hpos hok herr
    hnf₁ hnf₂

/-- **Clawback keeps a fractional vault on the asset's `STAmount` grid**, under the same
no-underflow side condition as `Vault.withdraw_assetsRounded_preserved`. -/
theorem Vault.clawback_assetsRounded_preserved (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hfr : v.numericType = .fractional)
    (hpre : ¬ v.assetsRounded)
    (hac : assets.Canonical) (hSc : holderShares.Canonical) (hSnn : holderShares.negative = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none)
    (hnf₁ : r.vault'.assetsTotal.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsTotal.toRat)
    (hnf₂ : r.vault'.assetsAvailable.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsAvailable.toRat) :
    ¬ r.vault'.assetsRounded :=
  Vault.clawback_assetsRounded_preserved_proof v assets holderShares r hfr hpre hac hSc hSnn hnn
    hok herr hnf₁ hnf₂

end XRPL.Model.SingleAssetVault
