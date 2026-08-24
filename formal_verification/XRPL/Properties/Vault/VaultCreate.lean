import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Model.Vault.VaultCreate

/-! # `Vault.create` initial state -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `Vault.create` -/

/-- The exact state of a created vault: every quantity is zero and the maximum
keeps the configured value. -/
theorem Vault.create_exact_state (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number) :
    (Vault.create nt scale assetsMaximum).assetsTotal.toRat = 0 ∧
    (Vault.create nt scale assetsMaximum).assetsAvailable.toRat = 0 ∧
    (Vault.create nt scale assetsMaximum).sharesTotal.toRat = 0 ∧
    (Vault.create nt scale assetsMaximum).lossUnrealized.toRat = 0 ∧
    (Vault.create nt scale assetsMaximum).assetsMaximum = assetsMaximum := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> simp only [Vault.create, Number.toRat_zero]

end XRPL.Model.SingleAssetVault
