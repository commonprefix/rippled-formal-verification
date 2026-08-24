import XRPL.Model.Vault.Vault

/-! # Single-asset vault state validity -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Representation well-formedness of the raw record: every `Number` field
normalized, shares a nonnegative integer, scale consistent with the asset kind.
The per-issuance shares bound (`OutstandingAmount ≤ MaximumAmount`) is not
stated here: the issuance's `MaximumAmount` is not part of this record. -/
structure Vault.WF (v : Vault) : Prop where
  assetsTotal_norm : v.assetsTotal.isNormalized
  assetsAvailable_norm : v.assetsAvailable.isNormalized
  assetsMaximum_norm : ∀ m ∈ v.assetsMaximum, m.isNormalized
  sharesTotal_norm : v.sharesTotal.isNormalized
  lossUnrealized_norm : v.lossUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ v.sharesTotal.toRat
  sharesTotal_int : v.sharesTotal.toRat.den = 1
  scale_integral : v.numericType.isIntegral = true → v.scale = 0
  scale_le : v.scale.toNat ≤ 18

/-- The vault invariant (XLS-0065 §4.5), stated on the exact values of the
stored fields. The `lossUnrealized_nonneg` clause is included as intended by
the spec. The fact that the modeled operations keep `lossUnrealized` at zero is
a reachability corollary (`Vault.Reachable`), not a validity clause. -/
structure Vault.Valid (v : Vault) : Prop where
  assetsTotal_nonneg : 0 ≤ v.assetsTotal.toRat
  assetsAvailable_nonneg : 0 ≤ v.assetsAvailable.toRat
  assetsAvailable_le : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat
  assetsMaximum_pos : ∀ m ∈ v.assetsMaximum, 0 < m.toRat
  empty_shares : v.sharesTotal.toRat = 0 → v.assetsTotal.toRat = 0 ∧ v.assetsAvailable.toRat = 0
  cap : ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat ≤ m.toRat
  lossUnrealized_nonneg : 0 ≤ v.lossUnrealized.toRat
  lossUnrealized_le : v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
  withdraw_nav_nonneg : 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat

/-- A lawful vault is a well-formed representation that satisfies the
invariant. -/
structure Vault.Lawful (v : Vault) : Prop where
  wf : v.WF
  valid : v.Valid

/-- A vault bundled with its lawfulness proof. Constructed only by
`Vault.validate` or by the lifted operations; the proof is erased at runtime. -/
def LawfulVault : Type := {v : Vault // v.Lawful}

/-- Raw vault of a lawful vault. -/
def LawfulVault.val (v : LawfulVault) : Vault := Subtype.val v

/-- Lawfulness proof of a lawful vault. -/
def LawfulVault.lawful (v : LawfulVault) : v.val.Lawful := Subtype.property v

/-- The untrusted-boundary check: promote a raw vault to a `LawfulVault` if it is
lawful. TODO: derive the `Decidable` instance so this is usable without
`Classical`. -/
def Vault.validate (v : Vault) [Decidable v.Lawful] : Option LawfulVault :=
  if h : v.Lawful then some ⟨v, h⟩ else none

end XRPL.Model.SingleAssetVault
