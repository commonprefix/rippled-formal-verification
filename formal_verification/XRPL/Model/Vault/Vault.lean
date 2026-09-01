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

-- exponent of a Number represented as an STAmount. Models the function `scale` from xrpld.
def exponent (amount : Number) (nt : NumericType) : Except Error Int := do
  let a ← STAmount.ofNumber nt amount .to_nearest
  return a.exponent

/-- Representation well-formed of the raw record. The per-issuance shares
bound (`OutstandingAmount ≤ MaximumAmount`) is not stated here: the issuance's
`MaximumAmount` is not part of this record. -/
structure RawVault.WF (v : RawVault) : Prop where
  assetsTotal_norm : v.assetsTotal.isNormalized
  assetsAvailable_norm : v.assetsAvailable.isNormalized
  assetsMaximum_norm : ∀ m ∈ v.assetsMaximum, m.isNormalized
  sharesTotal_norm : v.sharesTotal.isNormalized
  lossUnrealized_norm : v.lossUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ v.sharesTotal.toRat
  sharesTotal_int : v.sharesTotal.toRat.den = 1
  scale_integral : v.numericType.isIntegral = true → v.scale = 0
  scale_le : v.scale.toNat ≤ 18
  -- `assetsTotal - assetsAvailable` must be computable, so overflow doesn't happen
  assetsTotal_sub_ok : ∃ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d

/-- The vault invariant (XLS-0065 §4.5) stated with the modeled `Number` operators -/
structure RawVault.Valid (v : RawVault) : Prop where
  assetsTotal_nonneg : Number.zero.operator_le v.assetsTotal = true
  assetsAvailable_nonneg : Number.zero.operator_le v.assetsAvailable = true
  assetsAvailable_le : v.assetsAvailable.operator_le v.assetsTotal = true
  assetsMaximum_pos : ∀ m ∈ v.assetsMaximum, Number.zero.operator_lt m = true
  empty_shares : v.sharesTotal = Number.zero →
    v.assetsTotal = Number.zero ∧ v.assetsAvailable = Number.zero
  cap : ∀ m ∈ v.assetsMaximum, v.assetsTotal.operator_le m = true
  lossUnrealized_nonneg : Number.zero.operator_le v.lossUnrealized = true
  lossUnrealized_le : ∀ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d →
    v.lossUnrealized.operator_le d = true
  withdraw_nav_nonneg : v.lossUnrealized.operator_le v.assetsTotal = true

-- Deciding `WF` reduces to the conjunction of its clauses, each decidable above.
instance (v : RawVault) : Decidable v.WF :=
  decidable_of_iff
    (v.assetsTotal.isNormalized ∧ v.assetsAvailable.isNormalized ∧
      (∀ m ∈ v.assetsMaximum, m.isNormalized) ∧ v.sharesTotal.isNormalized ∧
      v.lossUnrealized.isNormalized ∧ 0 ≤ v.sharesTotal.toRat ∧ v.sharesTotal.toRat.den = 1 ∧
      (v.numericType.isIntegral = true → v.scale = 0) ∧ v.scale.toNat ≤ 18 ∧
      (∃ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩⟩

-- Deciding `Valid` reduces to the conjunction of its clauses, each decidable above.
instance (v : RawVault) : Decidable v.Valid :=
  decidable_of_iff
    (Number.zero.operator_le v.assetsTotal = true ∧
      Number.zero.operator_le v.assetsAvailable = true ∧
      v.assetsAvailable.operator_le v.assetsTotal = true ∧
      (∀ m ∈ v.assetsMaximum, Number.zero.operator_lt m = true) ∧
      (v.sharesTotal = Number.zero → v.assetsTotal = Number.zero ∧ v.assetsAvailable = Number.zero) ∧
      (∀ m ∈ v.assetsMaximum, v.assetsTotal.operator_le m = true) ∧
      Number.zero.operator_le v.lossUnrealized = true ∧
      (∀ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d →
        v.lossUnrealized.operator_le d = true) ∧
      v.lossUnrealized.operator_le v.assetsTotal = true)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- A `LawfulVault` extends `RawVault` with proofs that the representation is
well-formed (`wf`) and satisfies the invariant (`valid`, in Number operators). -/
structure LawfulVault extends RawVault where
  wf : toRawVault.WF
  valid : toRawVault.Valid

/-- Build a lawful vault from a raw vault, or reject. -/
def RawVault.to_lawful (v : RawVault) : Except Error LawfulVault :=
  if h : v.WF ∧ v.Valid then .ok { toRawVault := v, wf := h.1, valid := h.2 } else .error .notLawful

def LawfulVault.isInsolvent (lv : LawfulVault) : Bool :=
  lv.assetsTotal.mantissa_ = 0 && lv.sharesTotal.signum = 1

def LawfulVault.assetsRounded (lv : LawfulVault) : Prop :=
  STAmount.isRounded lv.numericType lv.assetsTotal ∨
  STAmount.isRounded lv.numericType lv.assetsAvailable ∨
  STAmount.isRounded lv.numericType lv.assetsReserved ∨
  STAmount.isRounded lv.numericType lv.lossUnrealized ∨
  ∃ m ∈ lv.assetsMaximum, STAmount.isRounded lv.numericType m

end XRPL.Model.SingleAssetVault
