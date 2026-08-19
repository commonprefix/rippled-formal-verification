import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Model.Vault.VaultCreate

/-! # `Vault.create` initial state -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `Vault.create` -/

/-- The exact state of a created vault: every quantity is zero and the maximum
is the exact image of `assetsMaximum`. -/
theorem Vault.create_toExact (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number) :
    (Vault.create nt scale assetsMaximum).toExact =
      { assetsTotal := 0, assetsAvailable := 0,
        assetsMaximum := assetsMaximum.map Number.toRat,
        sharesTotal := 0, lossUnrealized := 0 } := by
  unfold Vault.toExact Vault.create
  simp only [Number.toRat_zero, Rat.num_zero, Int.toNat_zero]

end XRPL.Model.SingleAssetVault
