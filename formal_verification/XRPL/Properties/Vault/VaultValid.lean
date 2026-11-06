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
  have hval := Number.toRat_of_nonneg x hneg
  set m := x.mantissa_.toNat
  set e := x.exponent_
  set d := (s - e).toNat with hd
  constructor
  · intro hmod
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
    refine ⟨(q : ℤ) * 10 ^ (e - s).toNat, ?_⟩
    have hde : (d : ℤ) + e = ((e - s).toNat : ℤ) + s := by omega
    rw [hval, hq]
    push_cast
    rw [← zpow_natCast (10 : ℚ) d, ← zpow_natCast (10 : ℚ) (e - s).toNat]
    calc (10 : ℚ) ^ (d : ℤ) * q * 10 ^ e = q * 10 ^ ((d : ℤ) + e) := by rw [zpow_add₀ (by norm_num)]; ring
      _ = q * 10 ^ (((e - s).toNat : ℤ) + s) := by rw [hde]
      _ = q * 10 ^ ((e - s).toNat : ℤ) * 10 ^ s := by rw [zpow_add₀ (by norm_num)]; ring
  · rintro ⟨k, hk⟩
    rw [hval] at hk
    by_cases hes : s ≤ e
    · rw [show d = 0 by omega, pow_zero, Nat.mod_one]
    push Not at hes
    have hdz : (d : ℤ) = s - e := by omega
    have hm : (m : ℚ) = k * 10 ^ (d : ℤ) := by
      have he : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
      rw [hdz, zpow_sub₀ (by norm_num), eq_comm, mul_div_assoc', div_eq_iff he.ne', ← hk]
    have hmi : (m : ℤ) = k * 10 ^ d := by
      have : (m : ℚ) = ((k * 10 ^ d : ℤ) : ℚ) := by rw [hm]; push_cast; rw [zpow_natCast]
      exact_mod_cast this
    have hdvd : ((10 ^ d : ℕ) : ℤ) ∣ (m : ℤ) := ⟨k, by rw [hmi]; push_cast; ring⟩
    exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp hdvd)

/-- On a well-formed representation the operator invariant `RawVault.Valid` and the exact-rational
invariant coincide. `WF` is needed because the operators read only normalized `Number`s exactly. -/
theorem RawVault.valid_iff_exact (rv : RawVault) (hwf : rv.WF) :
    rv.Valid ↔ rv.toExact.Valid := by
  constructor
  · intro hv
    have hAA : 0 ≤ rv.assetsAvailable.toRat := by
      have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.assetsAvailable_norm).mp hv.assetsAvailable_nonneg
      rwa [Number.toRat_zero] at this
    have hAD : 0 ≤ rv.assetsDeployed.toRat := by
      have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.assetsDeployed_norm).mp hv.assetsDeployed_nonneg
      rwa [Number.toRat_zero] at this
    refine
      { assetsAvailable_nonneg := ?_
        assetsDeployed_nonneg := hAD
        assetsReserved_nonneg := ?_
        lossUnrealized_nonneg := ?_
        yieldUnrealized_nonneg := ?_
        assetsMaximum_pos := ?_
        empty_shares := ?_
        lossUnrealized_le := ?_
        assetsDeployed_representable := ?_
        assetsReserved_le := ?_
        sharesTotal_representable := ?_
        depositBlocked_owner := hv.depositBlocked_owner
        schedule_gap := hv.schedule_gap
        earlyExitFeeRate_closedEnded := ?_
        earlyExitFeeRate_le := ?_
        assetsAvailable_representable := ?_
        assetsAvailable_onGrid := ?_ }
    · have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.assetsAvailable_norm).mp hv.assetsAvailable_nonneg
      rwa [Number.toRat_zero] at this
    · have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.assetsReserved_norm).mp hv.assetsReserved_nonneg
      rwa [Number.toRat_zero] at this
    · have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.lossUnrealized_norm).mp hv.lossUnrealized_nonneg
      rwa [Number.toRat_zero] at this
    · have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.yieldUnrealized_norm).mp hv.yieldUnrealized_nonneg
      rwa [Number.toRat_zero] at this
    · intro m hm
      show 0 < m
      obtain ⟨m0, hm0, hval⟩ := Option.mem_map.mp hm
      have hm0norm := hwf.assetsMaximum_norm m0 hm0
      have := (operator_lt_iff _ _ Number.zero_isNormalized
          hm0norm).mp (hv.assetsMaximum_pos m0 hm0)
      rw [Number.toRat_zero] at this
      rwa [← hval]
    · intro hsh
      have hsh0 : rv.sharesTotal.toRat = 0 := by
        have h := RawVault.WF.toExact_sharesTotal rv hwf
        rw [hsh] at h; simpa using h.symm
      have hszero : rv.sharesTotal = Number.zero :=
        (Number.toRat_eq_zero_iff_eq_zero hwf.sharesTotal_norm).mp hsh0
      obtain ⟨hA, hD⟩ := hv.empty_shares hszero
      exact ⟨by show rv.assetsAvailable.toRat = 0; rw [hA, Number.toRat_zero],
             by show rv.assetsDeployed.toRat = 0; rw [hD, Number.toRat_zero]⟩
    · exact (operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsDeployed_norm).mp hv.lossUnrealized_le
    · -- assetsDeployed is an amount of the asset
      exact (STAmount.isRounded_eq_false_iff _ _ hwf.assetsDeployed_norm hAD).mp
        hv.assetsDeployed_representable
    · exact (operator_le_iff _ _ hwf.assetsReserved_norm hwf.assetsDeployed_norm).mp hv.assetsReserved_le
    · -- sharesTotal fits an MPT amount
      have hcast := RawVault.WF.toExact_sharesTotal rv hwf
      rcases (STAmount.isRounded_eq_false_iff _ _ hwf.sharesTotal_norm hwf.sharesTotal_nonneg).mp
          hv.sharesTotal_representable with h0 | ⟨-, k, -, hk, hval⟩
      · have : rv.toExact.sharesTotal = 0 := by exact_mod_cast hcast.trans h0
        omega
      · have : rv.toExact.sharesTotal = k := by exact_mod_cast hcast.trans hval
        omega
    · -- a fee only on a closed-ended vault
      intro h
      exact hv.earlyExitFeeRate_closedEnded (by simpa [RawVault.toExact] using h)
    · -- the fee is at most 100%
      intro r hr
      obtain ⟨r0, hr0, rfl⟩ := Option.mem_map.mp hr
      exact UInt32.le_iff_toNat_le.mp (hv.earlyExitFeeRate_le r0 hr0)
    · exact (STAmount.isRounded_eq_false_iff _ _ hwf.assetsAvailable_norm hAA).mp hv.assetsAvailable_representable
    · rcases hv.assetsAvailable_onGrid with h0 | hmod
      · exact ⟨0, by show rv.assetsAvailable.toRat = _; rw [h0, Number.toRat_zero]; simp⟩
      · exact (Number.mod_grid_iff _ _ (Number.negative_false_of_nonneg _ hwf.assetsAvailable_norm hAA)).mp hmod
  · intro he
    refine
      { assetsAvailable_nonneg := ?_
        assetsDeployed_nonneg := ?_
        assetsReserved_nonneg := ?_
        lossUnrealized_nonneg := ?_
        yieldUnrealized_nonneg := ?_
        assetsMaximum_pos := ?_
        empty_shares := ?_
        lossUnrealized_le := ?_
        assetsDeployed_representable := ?_
        assetsReserved_le := ?_
        sharesTotal_representable := ?_
        depositBlocked_owner := he.depositBlocked_owner
        schedule_gap := he.schedule_gap
        earlyExitFeeRate_closedEnded := ?_
        earlyExitFeeRate_le := ?_
        assetsAvailable_representable := ?_
        assetsAvailable_onGrid := ?_ }
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.assetsAvailable_norm, Number.toRat_zero]
      exact he.assetsAvailable_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.assetsDeployed_norm, Number.toRat_zero]
      exact he.assetsDeployed_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.assetsReserved_norm, Number.toRat_zero]
      exact he.assetsReserved_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.lossUnrealized_norm, Number.toRat_zero]
      exact he.lossUnrealized_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.yieldUnrealized_norm, Number.toRat_zero]
      exact he.yieldUnrealized_nonneg
    · intro m hm
      rw [operator_lt_iff _ _ Number.zero_isNormalized
          (hwf.assetsMaximum_norm m hm), Number.toRat_zero]
      exact he.assetsMaximum_pos m.toRat (Option.mem_map_of_mem _ hm)
    · intro hsz
      have hsh : rv.toExact.sharesTotal = 0 := by
        show rv.sharesTotal.toRat.num.toNat = 0
        rw [hsz, Number.toRat_zero]; rfl
      obtain ⟨hA, hD⟩ := he.empty_shares hsh
      exact ⟨(Number.toRat_eq_zero_iff_eq_zero hwf.assetsAvailable_norm).mp hA,
             (Number.toRat_eq_zero_iff_eq_zero hwf.assetsDeployed_norm).mp hD⟩
    · exact (operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsDeployed_norm).mpr he.lossUnrealized_le
    · exact (STAmount.isRounded_eq_false_iff _ _ hwf.assetsDeployed_norm he.assetsDeployed_nonneg).mpr
        he.assetsDeployed_representable
    · exact (operator_le_iff _ _ hwf.assetsReserved_norm hwf.assetsDeployed_norm).mpr he.assetsReserved_le
    · -- sharesTotal fits an MPT amount
      rw [STAmount.isRounded_eq_false_iff _ _ hwf.sharesTotal_norm hwf.sharesTotal_nonneg]
      have hcap := he.sharesTotal_representable
      exact Or.inr ⟨by decide, rv.toExact.sharesTotal, le_of_le_of_eq hcap (by decide), hcap,
        (RawVault.WF.toExact_sharesTotal rv hwf).symm⟩
    · intro h
      exact he.earlyExitFeeRate_closedEnded (by simpa [RawVault.toExact] using h)
    · intro r hr
      exact UInt32.le_iff_toNat_le.mpr (he.earlyExitFeeRate_le r.toNat (Option.mem_map_of_mem _ hr))
    · exact (STAmount.isRounded_eq_false_iff _ _ hwf.assetsAvailable_norm he.assetsAvailable_nonneg).mpr
        he.assetsAvailable_representable
    · exact Or.inr ((Number.mod_grid_iff _ _ (Number.negative_false_of_nonneg _ hwf.assetsAvailable_norm
        he.assetsAvailable_nonneg)).mpr he.assetsAvailable_onGrid)

/-- The exact-rational invariant of a lawful vault, derived from its operator
proof and well-formedness. -/
theorem Vault.exact (v : Vault) : v.toExact.Valid :=
  (RawVault.valid_iff_exact v.toRawVault v.wf).mp v.valid

/-- When `to_lawful` accepts a raw state, the returned vault is that state, and the state is
well-formed and valid. -/
theorem RawVault.to_lawful_ok {rv : RawVault} {v : Vault}
    (h : rv.to_lawful = .ok v) : v.toRawVault = rv ∧ rv.WF ∧ rv.Valid := by
  unfold RawVault.to_lawful at h
  split at h
  · rename_i hcond; injection h with h'; exact ⟨by rw [← h'], hcond.1, hcond.2⟩
  · exact absurd h (by simp)

/-- A well-formed, valid raw state passes `to_lawful` unchanged. -/
theorem RawVault.to_lawful_ok_of {rv : RawVault} (hwf : rv.WF) (hvalid : rv.Valid) :
    ∃ v, rv.to_lawful = .ok v ∧ v.toRawVault = rv := by
  refine ⟨⟨rv, hwf, hvalid⟩, ?_, rfl⟩
  unfold RawVault.to_lawful; rw [dif_pos ⟨hwf, hvalid⟩]

end XRPL.Model.SingleAssetVault
