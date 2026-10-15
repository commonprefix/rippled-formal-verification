import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.AssetPool

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Lending (PoolPhase)

-- The dates of a closed-ended vault. An open-ended vault has no schedule.
structure VaultSchedule where
  subscriptionDate : UInt32
  redemptionDate : UInt32
  deriving DecidableEq, Repr

structure RawVault where
  assetsAvailable : Number
  assetsDeployed : Number
  assetsReserved : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number
  yieldUnrealized : Number
  schedule : Option VaultSchedule
  earlyExitFeeRate : Option TenthBips32
  ownerCanBlockDeposit : Bool
  depositBlocked : Bool

structure VaultAmounts where
  assets : STAmount
  shares : STAmount

def minInvestmentPeriod : Nat := 180 -- seconds
def maxInvestmentPeriod : Nat := 30 * 31_556_952 -- seconds, 30 years of 365.2425 days

def vaultDefaultIOUScale : UInt8 := 6
def vaultMaximumIOUScale : UInt8 := 10
def maxEarlyExitFeeRate : TenthBips32 := 100_000 -- 100%

-- the investment period
def VaultSchedule.hasValidGap (s : VaultSchedule) : Bool :=
  s.subscriptionDate.toNat + minInvestmentPeriod ≤ s.redemptionDate.toNat &&
    s.redemptionDate.toNat < s.subscriptionDate.toNat + maxInvestmentPeriod

def RawVault.baseExponent (rv : RawVault) : Int :=
  rv.numericType.baseExponent rv.scale

-- C++ `getAssetsTotal`
def RawVault.assetsTotal (rv : RawVault) : Except Error Number :=
  rv.assetsAvailable.operator_add rv.assetsDeployed .downward

def RawVault.phase (rv : RawVault) (parentCloseTime : UInt32) : PoolPhase :=
  match rv.schedule with
  | none => .noPhase
  | some s =>
    let hasSubscriptionExpired : Bool := parentCloseTime > s.subscriptionDate
    let hasRedemptionExpired : Bool := parentCloseTime ≥ s.redemptionDate

    if !hasSubscriptionExpired then .subscription
    else if !hasRedemptionExpired then .investment
    else .redemption

def RawVault.earlyExitFeeRateAt (rv : RawVault) (parentCloseTime : UInt32) : TenthBips32 :=
  match rv.earlyExitFeeRate with
  | some rate => if rv.phase parentCloseTime == .investment then rate else 0
  | none => 0

/-- Representation well-formed of the raw record. -/
structure RawVault.WF (rv : RawVault) : Prop where
  assetsAvailable_norm : rv.assetsAvailable.isNormalized
  assetsDeployed_norm : rv.assetsDeployed.isNormalized
  assetsReserved_norm : rv.assetsReserved.isNormalized
  assetsMaximum_norm : ∀ m ∈ rv.assetsMaximum, m.isNormalized
  sharesTotal_norm : rv.sharesTotal.isNormalized
  lossUnrealized_norm : rv.lossUnrealized.isNormalized
  yieldUnrealized_norm : rv.yieldUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ rv.sharesTotal.toRat
  sharesTotal_int : rv.sharesTotal.toRat.den = 1
  scale_integral : rv.numericType.isIntegral = true → rv.scale = 0
  scale_le : rv.scale ≤ vaultMaximumIOUScale

/-- The vault invariant stated with the modeled `Number` operators -/
structure RawVault.Valid (rv : RawVault) : Prop where
  assetsAvailable_nonneg : Number.zero.operator_le rv.assetsAvailable = true
  assetsDeployed_nonneg : Number.zero.operator_le rv.assetsDeployed = true
  assetsReserved_nonneg : Number.zero.operator_le rv.assetsReserved = true
  lossUnrealized_nonneg : Number.zero.operator_le rv.lossUnrealized = true
  yieldUnrealized_nonneg : Number.zero.operator_le rv.yieldUnrealized = true
  assetsMaximum_pos : ∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true
  empty_shares : rv.sharesTotal = Number.zero →
    rv.assetsAvailable = Number.zero ∧ rv.assetsDeployed = Number.zero
  lossUnrealized_le : rv.lossUnrealized.operator_le rv.assetsDeployed = true
  assetsDeployed_representable : STAmount.isRounded rv.numericType rv.assetsDeployed = false
  assetsReserved_le : rv.assetsReserved.operator_le rv.assetsDeployed = true
  sharesTotal_representable : STAmount.isRounded .int64 rv.sharesTotal = false
  depositBlocked_owner : rv.depositBlocked = true → rv.ownerCanBlockDeposit = true
  schedule_gap : ∀ s ∈ rv.schedule, s.hasValidGap = true
  earlyExitFeeRate_closedEnded : rv.earlyExitFeeRate.isSome = true → rv.schedule.isSome = true
  earlyExitFeeRate_le : ∀ r ∈ rv.earlyExitFeeRate, r ≤ maxEarlyExitFeeRate

-- Deciding `WF` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.WF :=
  decidable_of_iff
    (rv.assetsAvailable.isNormalized ∧ rv.assetsDeployed.isNormalized ∧
      rv.assetsReserved.isNormalized ∧ (∀ m ∈ rv.assetsMaximum, m.isNormalized) ∧
      rv.sharesTotal.isNormalized ∧ rv.lossUnrealized.isNormalized ∧ rv.yieldUnrealized.isNormalized ∧
      0 ≤ rv.sharesTotal.toRat ∧ rv.sharesTotal.toRat.den = 1 ∧
      (rv.numericType.isIntegral = true → rv.scale = 0) ∧ rv.scale ≤ vaultMaximumIOUScale)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

-- Deciding `Valid` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.Valid :=
  decidable_of_iff
    (Number.zero.operator_le rv.assetsAvailable = true ∧
      Number.zero.operator_le rv.assetsDeployed = true ∧
      Number.zero.operator_le rv.assetsReserved = true ∧
      Number.zero.operator_le rv.lossUnrealized = true ∧
      Number.zero.operator_le rv.yieldUnrealized = true ∧
      (∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true) ∧
      (rv.sharesTotal = Number.zero →
        rv.assetsAvailable = Number.zero ∧ rv.assetsDeployed = Number.zero) ∧
      rv.lossUnrealized.operator_le rv.assetsDeployed = true ∧
      STAmount.isRounded rv.numericType rv.assetsDeployed = false ∧
      rv.assetsReserved.operator_le rv.assetsDeployed = true ∧
      STAmount.isRounded .int64 rv.sharesTotal = false ∧
      (rv.depositBlocked = true → rv.ownerCanBlockDeposit = true) ∧
      (∀ s ∈ rv.schedule, s.hasValidGap = true) ∧
      (rv.earlyExitFeeRate.isSome = true → rv.schedule.isSome = true) ∧
      (∀ r ∈ rv.earlyExitFeeRate, r ≤ maxEarlyExitFeeRate))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩⟩

/-- A `Vault` extends `RawVault` with proofs that the representation is
well-formed (`wf`) and satisfies the invariant (`valid`, in Number operators). -/
structure Vault extends RawVault where
  wf : toRawVault.WF
  valid : toRawVault.Valid

structure VaultWithAmounts extends VaultAmounts where
  vault' : Vault

/-- Build a lawful vault from a raw vault, or reject. -/
def RawVault.to_lawful (rv : RawVault) : Except Error Vault :=
  if h : rv.WF ∧ rv.Valid then .ok { toRawVault := rv, wf := h.1, valid := h.2 } else .error .notLawful

def Vault.isInsolvent (v : Vault) : Bool :=
  v.assetsAvailable.mantissa_ = 0 && v.assetsDeployed.mantissa_ = 0 && v.sharesTotal.signum = 1

def Vault.assetsRounded (v : Vault) : Prop :=
  STAmount.isRounded v.numericType v.assetsAvailable ∨
  STAmount.isRounded v.numericType v.assetsDeployed ∨
  STAmount.isRounded v.numericType v.assetsReserved ∨
  STAmount.isRounded v.numericType v.lossUnrealized ∨
  STAmount.isRounded v.numericType v.yieldUnrealized ∨
  ∃ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m

end XRPL.Model.SingleAssetVault
