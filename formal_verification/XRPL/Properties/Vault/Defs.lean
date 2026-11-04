import XRPL.Model.Vault.Vault
import XRPL.Properties.Protocol.STAmount.Common.Representable

/-! # Single-asset vault state validity (exact-rational view) -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The vault state in exact arithmetic -/
structure RawVault.Exact where
  assetsAvailable : ℚ
  assetsDeployed : ℚ
  assetsReserved : ℚ
  assetsMaximum : Option ℚ
  numericType : NumericType
  scale : UInt8
  sharesTotal : ℕ
  lossUnrealized : ℚ
  yieldUnrealized : ℚ
  schedule : Option VaultSchedule
  earlyExitFeeRate : Option ℕ
  ownerCanBlockDeposit : Bool
  depositBlocked : Bool

/-- The exact value of a vault state. A negative share count reads `0` and a fractional one reads its numerator.
`RawVault.WF` rules both out. -/
def RawVault.toExact (rv : RawVault) : RawVault.Exact where
  assetsAvailable := rv.assetsAvailable.toRat
  assetsDeployed := rv.assetsDeployed.toRat
  assetsReserved := rv.assetsReserved.toRat
  assetsMaximum := rv.assetsMaximum.map Number.toRat
  numericType := rv.numericType
  scale := rv.scale
  sharesTotal := rv.sharesTotal.toRat.num.toNat
  lossUnrealized := rv.lossUnrealized.toRat
  yieldUnrealized := rv.yieldUnrealized.toRat
  schedule := rv.schedule
  earlyExitFeeRate := rv.earlyExitFeeRate.map UInt32.toNat
  ownerCanBlockDeposit := rv.ownerCanBlockDeposit
  depositBlocked := rv.depositBlocked

/-- The vault total, the exact sum of the available and deployed assets. -/
def RawVault.Exact.assetsTotal (s : RawVault.Exact) : ℚ :=
  s.assetsAvailable + s.assetsDeployed

/-- On a well-formed record the share count `toExact` reads casts back to the stored value. -/
lemma RawVault.WF.toExact_sharesTotal (rv : RawVault) (h : rv.WF) :
    ((rv.toExact.sharesTotal : ℕ) : ℚ) = rv.sharesTotal.toRat := by
  show ((rv.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = rv.sharesTotal.toRat
  set q := rv.sharesTotal.toRat with hq
  have hden : q.den = 1 := h.sharesTotal_int
  have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr h.sharesTotal_nonneg
  have hcast : (q.num : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd; simpa using hnd
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum_nn, hcast]

/-- The vault invariant (XLS-0065 §4.5) in exact rationals. On a well-formed representation it is
the operator `RawVault.Valid` (`RawVault.valid_iff_exact`). -/
structure RawVault.Exact.Valid (s : RawVault.Exact) : Prop where
  assetsAvailable_nonneg : 0 ≤ s.assetsAvailable
  assetsDeployed_nonneg : 0 ≤ s.assetsDeployed
  assetsReserved_nonneg : 0 ≤ s.assetsReserved
  lossUnrealized_nonneg : 0 ≤ s.lossUnrealized
  yieldUnrealized_nonneg : 0 ≤ s.yieldUnrealized
  assetsMaximum_pos : ∀ m ∈ s.assetsMaximum, 0 < m
  empty_shares : s.sharesTotal = 0 → s.assetsAvailable = 0 ∧ s.assetsDeployed = 0
  lossUnrealized_le : s.lossUnrealized ≤ s.assetsDeployed
  assetsDeployed_representable : STAmount.Representable s.numericType s.assetsDeployed
  assetsReserved_le : s.assetsReserved ≤ s.assetsDeployed
  sharesTotal_representable : s.sharesTotal ≤ 2 ^ 63 - 1
  depositBlocked_owner : s.depositBlocked = true → s.ownerCanBlockDeposit = true
  schedule_gap : ∀ sch ∈ s.schedule, sch.hasValidGap = true
  earlyExitFeeRate_closedEnded : s.earlyExitFeeRate.isSome = true → s.schedule.isSome = true
  earlyExitFeeRate_le : ∀ r ∈ s.earlyExitFeeRate, r ≤ maxEarlyExitFeeRate.toNat
  assetsAvailable_representable : STAmount.Representable s.numericType s.assetsAvailable
  assetsAvailable_onGrid : ∃ k : ℤ, s.assetsAvailable = k * 10 ^ s.numericType.baseExponent s.scale

end XRPL.Model.SingleAssetVault
