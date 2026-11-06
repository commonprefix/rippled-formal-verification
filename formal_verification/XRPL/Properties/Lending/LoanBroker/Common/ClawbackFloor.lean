import XRPL.Properties.Lending.LoanBroker.Common.CoverExact
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # A clawback debits the request floored to whole base units

On a broker in the Open zone a clawback debits the request, capped at the cover above the minimum
cover, floored to whole base units of the vault. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private sub_exact from XRPL.Properties.Lending.Common.SumRounding

/-- The amount a clawback asks for, in exact arithmetic: all cover above `minimumCover` when no amount
or a zero amount is given, otherwise the amount, capped at that excess. -/
def LoanBroker.clawTarget (lb : LoanBroker) (minimumCover : ℚ) (amount : Option STAmount) : ℚ :=
  match amount with
  | none => lb.toExact.coverAvailable - minimumCover
  | some a =>
    if a.isZero then lb.toExact.coverAvailable - minimumCover
    else min a.toRat (lb.toExact.coverAvailable - minimumCover)

/-- A clawback never targets more than the cover above `minimumCover`. -/
lemma LoanBroker.clawTarget_le (lb : LoanBroker) (minimumCover : ℚ) (amount : Option STAmount) :
    lb.clawTarget minimumCover amount ≤ lb.toExact.coverAvailable - minimumCover := by
  unfold LoanBroker.clawTarget
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · exact min_le_right _ _

/-- In the Open zone, the cover minus a grid amount between zero and the cover, rounded down, is exact and
a whole number of base units. -/
lemma LoanBroker.OpenZone.sub_downward_exact (lb : LoanBroker) (v : Vault) (hz : lb.OpenZone v.baseExponent)
    (m mx : Number) (hmg : Number.OnGrid v.baseExponent m) (hm0 : 0 ≤ m.toRat)
    (hle : m.toRat ≤ lb.coverAvailable.toRat) (hsub : lb.coverAvailable.operator_sub m .downward = .ok mx) :
    mx.toRat = lb.coverAvailable.toRat - m.toRat ∧
      ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ mx.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨kA, hkA, hkAv⟩ := Number.OnGrid.units_le _ _ hz.cover hA0 hz.coverLimit
  obtain ⟨km, -, hkmv⟩ := Number.OnGrid.units_le _ _ hmg hm0 (hle.trans hz.coverLimit)
  have hkm : km ≤ kA := by
    have : (km : ℚ) * 10 ^ v.baseExponent ≤ kA * 10 ^ v.baseExponent := hkmv ▸ hkAv ▸ hle
    exact_mod_cast le_of_mul_le_mul_right this hp
  have hd : lb.coverAvailable.toRat - m.toRat = ((kA - km : ℕ) : ℚ) * 10 ^ v.baseExponent := by
    rw [hkAv, hkmv, Nat.cast_sub hkm]; ring
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (kA - km : ℕ) v.baseExponent
    ⟨by omega, by omega⟩ (Vault.baseExponent_grid v).2
  have hmxv := sub_exact _ _ _ w .downward lb.wf.coverAvailable_norm hmg.1 hA0 hm0 hsub hw
    (by rw [hwv, hd, Int.cast_natCast])
  exact ⟨hmxv, kA - km, by omega, by rw [hmxv, hd]⟩

/-- The rounding of a clawback in the Open zone returns the capped request floored to whole base
units. -/
lemma LoanBroker.roundedCoverClawback_floor (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (c : STAmount) (minimumCover : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover)
    (hrc : (lb.roundedCoverClawback v amount).run = .ok (.ok c)) :
    c.toRat = (⌊lb.clawTarget minimumCover.toRat amount / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  obtain ⟨m', mx, claw, claw', hm', hsub, hsig, hclaw, hof, hcl, hnz⟩ :=
    LoanBroker.roundedCoverClawback_ok lb v amount _ hrc
  have hmm : m' = minimumCover := Except.ok.inj (hm'.symm.trans hmin)
  rw [hmm] at hsub

  -- the minimum cover is a whole number of base units, not negative
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  have hm0 := LoanBroker.minimumCover_nonneg lb _ _ (by omega) hmin
  have hmg := minimumBrokerCover_onGrid _ _ _ _ _ ⟨by omega, by omega⟩ (fun h => (hint h).le) hmin

  -- the cap is exactly the cover above the minimum, a whole number of base units
  obtain ⟨hmxp, hmxm⟩ := (signum_pos_iff mx).mp hsig
  have hmxn : mx.isNormalized := operator_sub_isNormalized _ _ _ .downward lb.wf.coverAvailable_norm hmn hsub hmxm
  have hmx0 : 0 ≤ mx.toRat := Number.toRat_nonneg_of_nonnegative mx hmxp
  -- the cap is the difference rounded down and is not negative, so the cover is at least the minimum cover
  have hmle : minimumCover.toRat ≤ lb.coverAvailable.toRat := by
    obtain ⟨n, hn, hdn⟩ := operator_sub_rounded_downward _ _ _ lb.wf.coverAvailable_norm hmn hsub hmxm
    have := Number.lower_le _ n hn
    linarith
  obtain ⟨hmxv, k, hkle, hk⟩ := LoanBroker.OpenZone.sub_downward_exact lb v hz _ _ hmg hm0 hmle hsub

  have hmxc : ∀ st, STAmount.ofNumber lb.numericType mx .to_nearest = .ok st → st.toRat = mx.toRat := by
    intro st hst
    by_cases hi : lb.numericType.isIntegral = true
    · have hden : mx.toRat.den = 1 := by rw [hk, hint hi, zpow_zero, mul_one]; simp
      exact STAmount.ofNumber_integral_exact _ mx _ st hi hmxn hden hst
    · have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
      rw [hfr] at hst
      refine STAmount.ofNumber_eq_of_isRounded_false _ mx st hmxn hmx0 ?_ hst
      rw [STAmount.isRounded_eq_false_iff _ mx hmxn hmx0, hk]
      exact STAmount.representable_fractional_of_units k _ (by omega) (by omega) (by omega)

  -- the capped request is the target, and the asset stores it exactly
  have key : claw.isNormalized ∧ 0 ≤ claw.toRat ∧ claw.toRat ≤ mx.toRat ∧
      claw.toRat = lb.clawTarget minimumCover.toRat amount ∧ claw'.toRat = claw.toRat := by
    have hcap : claw = mx → claw.isNormalized ∧ 0 ≤ claw.toRat ∧ claw.toRat ≤ mx.toRat ∧
        claw.toRat = lb.toExact.coverAvailable - minimumCover.toRat ∧ claw'.toRat = claw.toRat := by
      rintro rfl
      exact ⟨hmxn, hmx0, le_rfl, hmxv, hmxc _ hof⟩
    cases amount with
    | none =>
      have h := hcap (Except.ok.inj hclaw).symm
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    | some a =>
      by_cases hza : a.isZero = true
      · have hcm : claw = mx := by
          simp only [LoanBroker.clawRequest, hza, if_true] at hclaw
          exact (Except.ok.inj hclaw).symm
        have h := hcap hcm
        simp only [LoanBroker.clawTarget, hza, if_true]
        exact h
      · obtain ⟨hac, hat, ha0⟩ := hreq a rfl
        have hc : a.Canonical := hac.resolve_right hza
        simp only [LoanBroker.clawRequest, hza, Bool.false_eq_true, if_false] at hclaw
        obtain ⟨mag, hmag, hclaw⟩ := bind_ok_peel _ _ _ hclaw
        have hcm : claw = if mag.operator_gt mx = true then mx else mag := (Except.ok.inj hclaw).symm
        obtain ⟨hmagv, hmagn⟩ := STAmount.CanonicalOrZero.toNumber_exact hac mag hmag
        simp only [LoanBroker.clawTarget, hza, Bool.false_eq_true, if_false]
        by_cases hgt : mag.operator_gt mx = true
        · rw [if_pos hgt] at hcm
          have hlt : mx.toRat < a.toRat := hmagv ▸ (operator_gt_iff mag mx hmagn hmxn).mp hgt
          have h := hcap hcm
          refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
          rw [h.2.2.2.1, min_eq_right]
          exact (h.2.2.2.1 ▸ hcm ▸ hlt).le
        · rw [if_neg hgt] at hcm
          rw [hcm] at hof ⊢
          have hle : a.toRat ≤ mx.toRat := by
            rw [← hmagv]; exact not_lt.mp (by rw [← operator_gt_iff mag mx hmagn hmxn]; exact hgt)
          refine ⟨hmagn, by rw [hmagv]; exact ha0, by rw [hmagv]; exact hle, ?_, ?_⟩
          · rw [hmagv, min_eq_left]
            exact hle.trans (le_of_eq hmxv)
          · rw [hmagv]
            exact STAmount.ofNumber_to_nearest_eq_of_canonical _ mag claw' a hmagn (by rw [hmagv]; exact ha0)
              (STAmount.Canonical.exactCanonical a hc) hat hmagv hof
  obtain ⟨hclawn, hclaw0, hclawle, hT, hcv⟩ := key
  rw [← hT, ← hcv]
  have hclaw'0 : 0 ≤ claw'.toRat := hcv ▸ hclaw0
  obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof

  by_cases hi : lb.numericType.isIntegral = true
  · -- an XRP or MPT clamp returns the magnitude, a whole number of units
    have hneg : claw'.operator_neg.integral = true := by
      rw [STAmount.operator_neg_integral, STAmount.integral, hty]; exact hi
    rw [clampToSumExponent_integral _ _ _ hneg, Except.ok.injEq] at hcl
    have hmag := (clamp_magnitude claw'.operator_neg).2.2.2
    rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hclaw'0] at hmag
    obtain ⟨iv, -, hiv⟩ := STAmount.ofNumber_integral_toRat _ claw _ claw' hi
      (Number.negative_false_of_nonneg claw hclawn hclaw0) hof
    rw [hmag, hiv, hint hi, zpow_zero, div_one, mul_one, Int.floor_intCast]
  · -- an IOU clamp floors onto the grid of the cover it leaves, the base grid in the Open zone
    have hfr : claw'.integral = false := by
      unfold STAmount.integral; rw [hty]; simpa using hi
    obtain ⟨dN, e, hdN, hps, -, hfl⟩ := clampToSumExponent_debit_floor _ _ _ _ hcz hfr hclaw'0
      v.baseExponent_range ((STAmount.isZero_eq_false_iff c).mp hnz) hcl
    suffices he : e = v.baseExponent by rw [← he]; exact hfl
    obtain ⟨s, hs, hne'⟩ := postSumExponent_reduces _ _ _ _ _ hps
    obtain ⟨hdv, hdn⟩ := hcz.operator_neg.toNumber_exact dN hdN
    rw [STAmount.operator_neg_toRat] at hdv
    have hr1 := operator_add_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hdn hs
    rw [hdv, ← sub_eq_add_neg] at hr1
    have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ lb.wf.coverAvailable_norm hdn hs
    -- the cover it leaves is between zero and the cover
    have hcle : claw'.toRat ≤ lb.coverAvailable.toRat := by rw [hcv]; linarith
    have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s _ hr1 (by linarith)
    have hsle : s.toRat ≤ lb.coverAvailable.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized s _ hr1 _ lb.wf.coverAvailable_norm (by linarith)
    have hnt' : claw'.operator_neg.numericType = .fractional := (STAmount.operator_neg_fczr _ (hcz.fracCanonZero hfr)).1
    rw [hnt'] at hne'
    -- so the sum stays below `10^(16 + b)` and keeps the base exponent
    exact numberExponent_at_base s _ .fractional e hsn hs0 (by omega) (fun h => absurd h (by decide))
      (LoanBroker.OpenZone.lt_pow_sixteen lb _ hz _ hsle) hne'

/-- A clawback in the Open zone debits the capped request floored to whole base units. -/
lemma LoanBroker.coverClawback_floor (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat =
      (⌊lb.clawTarget minimumCover.toRat amount / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent :=
  LoanBroker.roundedCoverClawback_floor lb v amount _ minimumCover hz hnt hmax hreq hmin
    (LoanBroker.coverClawback_exact lb v amount res hz hmax hok).1

end XRPL.Model.Lending
