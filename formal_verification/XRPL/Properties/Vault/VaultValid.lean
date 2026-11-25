import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.DiffSignRepresents
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Equivalence of the operator and exact-rational vault invariants -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- For a nonnegative `Number`, the mantissa test of `RawVault.Valid.assetsAvailable_onGrid` reads a whole number
of `10^s` units. -/
lemma Number.mod_grid_iff (x : Number) (s : ℤ) (hneg : x.negative_ = false) :
    x.mantissa_.toNat % 10 ^ (s - x.exponent_).toNat = 0 ↔ ∃ k : ℤ, x.toRat = k * 10 ^ s := by
  sorry

/-- On a well-formed representation the operator invariant `RawVault.Valid` and the exact-rational
invariant coincide. `WF` is needed because the operators read only normalized `Number`s exactly. -/
theorem RawVault.valid_iff_exact (rv : RawVault) (hwf : rv.WF) :
    rv.Valid ↔ rv.toExact.Valid := by
  sorry

/-- The exact-rational invariant of a lawful vault, derived from its operator
proof and well-formedness. -/
theorem Vault.exact (v : Vault) : v.toExact.Valid := by
  sorry

/-- When `to_lawful` accepts a raw state, the returned vault is that state, and the state is
well-formed and valid. -/
theorem RawVault.to_lawful_ok {rv : RawVault} {v : Vault}
    (h : rv.to_lawful = .ok v) : v.toRawVault = rv ∧ rv.WF ∧ rv.Valid := by
  sorry

/-- A well-formed, valid raw state passes `to_lawful` unchanged. -/
theorem RawVault.to_lawful_ok_of {rv : RawVault} (hwf : rv.WF) (hvalid : rv.Valid) :
    ∃ v, rv.to_lawful = .ok v ∧ v.toRawVault = rv := by
  sorry

end XRPL.Model.SingleAssetVault
