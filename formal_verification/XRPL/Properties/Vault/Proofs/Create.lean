import XRPL.Properties.Vault.Common.Create

/-! # The freshly created vault's exact projections -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.create_toExact_proof (nt : NumericType) (scale : UInt8) (am : Option Number)
    (hmax_norm : ∀ m ∈ am, m.isNormalized) (hmax_pos : ∀ m ∈ am, 0 < m.toRat)
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsTotal = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsAvailable = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.sharesTotal = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.lossUnrealized = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsMaximum
      = am.map Number.toRat ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).numericType = nt ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).scale = scale := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RawVault.toExact, Vault.create_lawful_toRawVault, Number.toRat_zero,
      Rat.num_zero, Int.toNat_zero]

end XRPL.Model.SingleAssetVault
