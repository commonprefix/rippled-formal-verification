import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- The vault tracks only the asset's `numericType` (integral vs fractional), not its account or
-- currency. Shares are always integral (an MPT), so they need no field.
structure RawVault where
  assetsTotal : Number
  assetsAvailable : Number
  assetsReserved : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number

-- Detect an overflow error surfaced by arithmetic ops.
def isOverflow (e : Error) : Bool := match e with | .overflow => true | _ => false

/-- Representation well-formed of the raw record. The per-issuance shares
bound (`OutstandingAmount ≤ MaximumAmount`) is not stated here: the issuance's
`MaximumAmount` is not part of this record. -/
structure RawVault.WF (rv : RawVault) : Prop where
  assetsTotal_norm : rv.assetsTotal.isNormalized
  assetsAvailable_norm : rv.assetsAvailable.isNormalized
  assetsMaximum_norm : ∀ m ∈ rv.assetsMaximum, m.isNormalized
  sharesTotal_norm : rv.sharesTotal.isNormalized
  lossUnrealized_norm : rv.lossUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ rv.sharesTotal.toRat
  sharesTotal_int : rv.sharesTotal.toRat.den = 1
  scale_integral : rv.numericType.isIntegral = true → rv.scale = 0
  scale_le : rv.scale.toNat ≤ 18
  -- `assetsTotal - assetsAvailable` must be computable, so overflow doesn't happen
  assetsTotal_sub_ok : ∃ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d

/-- The vault invariant (XLS-0065 §4.5) stated with the modeled `Number` operators -/
structure RawVault.Valid (rv : RawVault) : Prop where
  assetsTotal_nonneg : Number.zero.operator_le rv.assetsTotal = true
  assetsAvailable_nonneg : Number.zero.operator_le rv.assetsAvailable = true
  assetsAvailable_le : rv.assetsAvailable.operator_le rv.assetsTotal = true
  assetsMaximum_pos : ∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true
  empty_shares : rv.sharesTotal = Number.zero →
    rv.assetsTotal = Number.zero ∧ rv.assetsAvailable = Number.zero
  cap : ∀ m ∈ rv.assetsMaximum, rv.assetsTotal.operator_le m = true
  lossUnrealized_nonneg : Number.zero.operator_le rv.lossUnrealized = true
  lossUnrealized_le : ∀ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d →
    rv.lossUnrealized.operator_le d = true
  withdraw_nav_nonneg : rv.lossUnrealized.operator_le rv.assetsTotal = true

-- Deciding `WF` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.WF :=
  decidable_of_iff
    (rv.assetsTotal.isNormalized ∧ rv.assetsAvailable.isNormalized ∧
      (∀ m ∈ rv.assetsMaximum, m.isNormalized) ∧ rv.sharesTotal.isNormalized ∧
      rv.lossUnrealized.isNormalized ∧ 0 ≤ rv.sharesTotal.toRat ∧ rv.sharesTotal.toRat.den = 1 ∧
      (rv.numericType.isIntegral = true → rv.scale = 0) ∧ rv.scale.toNat ≤ 18 ∧
      (∃ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩⟩

-- Deciding `Valid` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.Valid :=
  decidable_of_iff
    (Number.zero.operator_le rv.assetsTotal = true ∧
      Number.zero.operator_le rv.assetsAvailable = true ∧
      rv.assetsAvailable.operator_le rv.assetsTotal = true ∧
      (∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true) ∧
      (rv.sharesTotal = Number.zero → rv.assetsTotal = Number.zero ∧ rv.assetsAvailable = Number.zero) ∧
      (∀ m ∈ rv.assetsMaximum, rv.assetsTotal.operator_le m = true) ∧
      Number.zero.operator_le rv.lossUnrealized = true ∧
      (∀ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d →
        rv.lossUnrealized.operator_le d = true) ∧
      rv.lossUnrealized.operator_le rv.assetsTotal = true)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- A `Vault` extends `RawVault` with proofs that the representation is
well-formed (`wf`) and satisfies the invariant (`valid`, in Number operators). -/
structure Vault extends RawVault where
  wf : toRawVault.WF
  valid : toRawVault.Valid

/-- Build a lawful vault from a raw vault, or reject. -/
def RawVault.to_lawful (rv : RawVault) : Except Error Vault :=
  if h : rv.WF ∧ rv.Valid then .ok { toRawVault := rv, wf := h.1, valid := h.2 } else .error .notLawful

def Vault.isInsolvent (v : Vault) : Bool :=
  v.assetsTotal.mantissa_ = 0 && v.sharesTotal.signum = 1

def Vault.assetsRounded (v : Vault) : Prop :=
  STAmount.isRounded v.numericType v.assetsTotal ∨
  STAmount.isRounded v.numericType v.assetsAvailable ∨
  STAmount.isRounded v.numericType v.assetsReserved ∨
  STAmount.isRounded v.numericType v.lossUnrealized ∨
  ∃ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m

end XRPL.Model.SingleAssetVault
