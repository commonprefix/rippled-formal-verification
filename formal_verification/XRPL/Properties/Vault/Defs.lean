import XRPL.Model.Vault.Vault

/-! # Single-asset vault state validity -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The vault state in exact arithmetic -/
structure Vault.Exact where
  assetsTotal : ℚ
  assetsAvailable : ℚ
  assetsMaximum : Option ℚ
  sharesTotal : ℕ
  lossUnrealized : ℚ

/-- The exact value of a vault state. Total: `sharesTotal` falls back to `0`-like
junk when the stored `Number` is not a nonnegative integer; `Vault.WF` rules that
out. -/
def Vault.toExact (v : Vault) : Vault.Exact where
  assetsTotal := v.assetsTotal.toRat
  assetsAvailable := v.assetsAvailable.toRat
  assetsMaximum := v.assetsMaximum.map Number.toRat
  sharesTotal := v.sharesTotal.toRat.num.toNat
  lossUnrealized := v.lossUnrealized.toRat

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

/-- `toExact`'s shares projection is faithful on well-formed records: casting the
`ℕ` value back to `ℚ` recovers the stored value. -/
theorem Vault.WF.toExact_sharesTotal (v : Vault) (h : v.WF) :
    ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat := by
  show ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = v.sharesTotal.toRat
  set q := v.sharesTotal.toRat with hq
  have hden : q.den = 1 := h.sharesTotal_int
  have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr h.sharesTotal_nonneg
  have hcast : (q.num : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd; simpa using hnd
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum_nn, hcast]

/-- The `Vault.Exact` counterpart of `Vault.hasCap`: a cap is configured. -/
def Vault.Exact.hasCap (s : Vault.Exact) : Prop := s.assetsMaximum ≠ none

/-- The model's cap test agrees with the exact-layer one. -/
theorem Vault.WF.hasCap_iff (v : Vault) :
    v.hasCap = true ↔ v.toExact.hasCap := by
  unfold Vault.hasCap Vault.Exact.hasCap Vault.toExact
  cases hm : v.assetsMaximum with
  | none => simp
  | some m => simp

/-- The vault invariant (XLS-0065 §4.5). The `lossUnrealized_nonneg` clause is
included as intended by the spec. The fact that the modeled operations keep
`lossUnrealized` at zero is a reachability corollary (`Vault.Reachable`), not a
validity clause. -/
structure Vault.Exact.Valid (s : Vault.Exact) : Prop where
  assetsTotal_nonneg : 0 ≤ s.assetsTotal
  assetsAvailable_nonneg : 0 ≤ s.assetsAvailable
  assetsAvailable_le : s.assetsAvailable ≤ s.assetsTotal
  assetsMaximum_pos : ∀ m ∈ s.assetsMaximum, 0 < m
  empty_shares : s.sharesTotal = 0 → s.assetsTotal = 0 ∧ s.assetsAvailable = 0
  cap : ∀ m ∈ s.assetsMaximum, s.assetsTotal ≤ m
  lossUnrealized_nonneg : 0 ≤ s.lossUnrealized
  lossUnrealized_le : s.lossUnrealized ≤ s.assetsTotal - s.assetsAvailable
  withdraw_nav_nonneg : 0 ≤ s.assetsTotal - s.lossUnrealized

/-- A lawful vault is a well-formed representation whose exact value satisfies
the invariant. -/
structure Vault.Lawful (v : Vault) : Prop where
  wf : v.WF
  valid : v.toExact.Valid

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
