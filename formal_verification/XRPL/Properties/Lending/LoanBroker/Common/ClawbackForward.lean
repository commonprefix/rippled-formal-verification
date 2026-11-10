import XRPL.Properties.Lending.LoanBroker.Common.ClawbackFloor
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits
import XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal
import XRPL.Properties.Lending.Loan.Common.RoundTotal

/-! # When a clawback succeeds

On a broker in the Open zone that does not hold XRP and has cover above the minimum, a clawback of whole base units,
or of all the excess, passes its checks and succeeds. Past its checks a clawback can only fail as notLawful. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private STAmount.ofNumber_integral_small from XRPL.Properties.Lending.Loan.Common.Grid

variable {α : Type} [AssetPool α]

/-- A whole number of base units, at most a cover in the Open zone, converts to the asset exactly. -/
lemma LoanBroker.ofNumber_units (lb : LoanBroker) (b : Int) (hz : lb.OpenZone b)
    (hb : -10 ≤ b ∧ b ≤ 0) (hint : lb.numericType.isIntegral = true → b = 0) (x : Number) (k : ℕ)
    (hx : x.isNormalized) (hxv : x.toRat = (k : ℚ) * 10 ^ b) (hle : x.toRat ≤ lb.coverAvailable.toRat) :
    ∃ st, STAmount.ofNumber lb.numericType x .to_nearest = .ok st ∧ st.toRat = x.toRat := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hx0 : 0 ≤ x.toRat := by rw [hxv]; positivity
  have hk : k ≤ 9 * 10 ^ 15 := by
    have : (k : ℚ) * 10 ^ b ≤ 9 * 10 ^ 15 * 10 ^ b := hxv ▸ hle.trans hz.coverLimit
    exact_mod_cast le_of_mul_le_mul_right this hp
  -- the asset stores the value, the way it stores the cover
  have hrep : STAmount.isRounded lb.numericType x = false := by
    refine STAmount.isRounded_false_of_units _ _ _ k hx hxv hk hb hint ?_
    intro hi hk0
    have hkA : (k : ℚ) ≤ lb.toExact.coverAvailable := by
      rw [hxv, hint hi, zpow_zero, mul_one] at hle; exact hle
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    exact ⟨LoanBroker.OpenZone.maxOffset_nonneg lb b hz hi (by linarith),
      by exact_mod_cast hkA.trans (LoanBroker.OpenZone.cover_le_maxValue lb b hz hi)⟩
  obtain ⟨st, hst⟩ := STAmount.ofNumber_ok_of_isRounded_false _ x hrep
  exact ⟨st, hst, STAmount.ofNumber_eq_of_isRounded_false _ x st hx hx0 hrep hst⟩

/-- Clamping a positive whole number of base units, at most a cover in the Open zone, keeps an amount
that is not zero. -/
private lemma LoanBroker.clamp_units (lb : LoanBroker) (v : Vault) (hz : lb.OpenZone v.baseExponent)
    (d : STAmount) (hd : d.CanonicalOrZero) (k : ℕ) (hk : 1 ≤ k)
    (hdv : d.toRat = (k : ℚ) * 10 ^ v.baseExponent) (hle : d.toRat ≤ lb.coverAvailable.toRat) :
    ∃ c, clampToSumExponent lb.coverAvailable d.operator_neg v.baseExponent = .ok c ∧ c.isZero = false := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hd0 : 0 < d.toRat := by rw [hdv]; exact mul_pos (Nat.cast_pos.mpr (by omega)) hp
  have hdz : d.mValue ≠ 0 := fun h => hd0.ne' ((STAmount.toRat_eq_zero_iff d).mpr h)
  have habs := STAmount.abs_operator_neg_of_pos d hd0
  by_cases hi : d.operator_neg.integral = true
  · -- an XRP or MPT clamp returns the magnitude
    refine ⟨_, clampToSumExponent_integral _ _ _ hi, ?_⟩
    rw [habs]
    exact (STAmount.isZero_eq_false_iff d).mpr hdz
  -- an IOU clamp rounds the magnitude onto the grid of the cover it leaves, the base grid
  have hfr : d.operator_neg.integral = false := by simpa using hi
  have hdf : d.FracCanonZero := hd.fracCanonZero ((STAmount.operator_neg_integral d).symm.trans hfr)
  have hdi : d.IOUCanonical := hdf.2.resolve_right hdz
  have hnf := STAmount.operator_neg_fczr d hdf
  have hAn := lb.wf.coverAvailable_norm
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hA9 := LoanBroker.OpenZone.cover_le lb _ hz hbhi
  obtain ⟨dN, hdN, hdNn, hdNe⟩ := hnf.toNumber_ok .to_nearest
  have hdNv := (hd.operator_neg.toNumber_exact dN hdN).1
  rw [STAmount.operator_neg_toRat] at hdNv
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_exp _ _ .to_nearest hAn hdNn
    (Number.exponent_headroom_of_lt _ hAn hA0 (by linarith)) hdNe
  have hr1 := operator_add_rounded_to_nearest _ _ _ hAn hdNn hs
  rw [hdNv, ← sub_eq_add_neg] at hr1
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAn hdNn hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s _ hr1 (by linarith)
  have hsle : s.toRat ≤ lb.coverAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized s _ hr1 _ hAn (by linarith)
  obtain ⟨e, he⟩ : ∃ e, numberExponent s v.baseExponent .fractional = .ok e := by
    unfold numberExponent
    by_cases hsz : s.operator_eq Number.zero = true
    · rw [if_pos hsz]; exact ⟨_, rfl⟩
    · rw [if_neg hsz]
      obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s .downward hsn
        (by rw [abs_of_nonneg hs0]; linarith [show (9 : ℚ) * 10 ^ 15 < 10 ^ 90 by norm_num])
      rw [hst]; exact ⟨_, rfl⟩
  have heb : e = v.baseExponent := numberExponent_at_base s _ .fractional e hsn hs0 (by omega)
    (fun h => absurd h (by decide)) (LoanBroker.OpenZone.lt_pow_sixteen lb _ hz _ hsle) he
  have hps : postSumExponent lb.coverAvailable dN v.baseExponent d.operator_neg.numericType =
      .ok v.baseExponent := by
    have hnte : d.operator_neg.numericType = .fractional := hnf.1
    simp only [postSumExponent, hs, hnte, bind, Except.bind]
    rw [he, heb]
  -- the magnitude is the amount, already on the base grid
  obtain ⟨c, hc⟩ := STAmount.roundToExponent_ok_any d v.baseExponent .towards_zero hdi
    (STAmount.mIsNegative_false_of_pos d hd0) (by omega) (by omega)
  have hR := STAmount.roundToExponent_rounded_of_scale d c v.baseExponent .towards_zero hdi (by omega) (by omega) hc
  simp only [RoundsToRepresentableAt] at hR
  change c.toRat = _ at hR
  rw [if_pos hd0.le, hdv, mul_div_assoc, div_self hp.ne', mul_one, Int.floor_natCast] at hR
  refine ⟨c, ?_, ?_⟩
  · simp only [clampToSumExponent, hfr, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hdN, hps, habs]
    exact hc
  · have hc0 : c.toRat ≠ 0 := by
      rw [hR]; exact mul_ne_zero (by exact_mod_cast (by omega : (k : ℤ) ≠ 0)) hp.ne'
    exact (STAmount.isZero_eq_false_iff c).mpr (mt (STAmount.toRat_eq_zero_iff c).mpr hc0)

/-- Clawing back a whole number of base units, or all the cover above the minimum, from a broker that does not
hold XRP passes the checks while CoverAvailable is above the minimum cover. -/
lemma LoanBroker.canCoverClawback_of_units (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (minimumCover : Number) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hk : ∀ a ∈ amount, ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hroom : minimumCover.toRat < lb.toExact.coverAvailable) :
    lb.canCoverClawback v amount = .ok .tesSUCCESS := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAn := lb.wf.coverAvailable_norm
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hroom' : minimumCover.toRat < lb.coverAvailable.toRat := hroom
  have hA9 := LoanBroker.OpenZone.cover_le lb _ hz hbhi

  -- the minimum cover is a whole number of base units, not negative
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  have hm0 := LoanBroker.minimumCover_nonneg lb _ _ (by omega) hmin
  have hmg := minimumBrokerCover_onGrid _ _ _ _ _ ⟨by omega, by omega⟩ (fun h => (hint h).le) hmin

  -- the cap is the cover above the minimum, exactly, a positive whole number of base units
  obtain ⟨mx, hsub⟩ := Number.operator_sub_ok_of_lt _ _ .downward hAn hmn hA0 (by linarith) hm0
    (by linarith)
  obtain ⟨hmxv, km, -, hkm⟩ := LoanBroker.OpenZone.sub_downward_exact lb v hz _ _ hmg hm0 hroom'.le hsub
  have hmxn := Number.operator_sub_isNormalized_any _ _ _ _ hAn hmn hsub
  have hmx0 : 0 < mx.toRat := by rw [hmxv]; linarith
  have hsig : 0 < mx.signum := (signum_pos_iff mx).mpr ⟨Number.negative_false_of_nonneg mx hmxn hmx0.le,
    fun h0 => by rw [Number.toRat_eq_zero_of_mantissa_zero mx h0] at hmx0; exact lt_irrefl _ hmx0⟩

  -- the clawback takes the request capped at the cap, a positive whole number of base units
  obtain ⟨claw, hclaw, hcn, k, hk1, hkle, hkv⟩ : ∃ claw, LoanBroker.clawRequest mx amount = .ok claw ∧
      claw.isNormalized ∧ ∃ k : ℕ, 1 ≤ k ∧ claw.toRat ≤ mx.toRat ∧
        claw.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
    have hcap : ∃ k : ℕ, 1 ≤ k ∧ mx.toRat ≤ mx.toRat ∧ mx.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
      have hkm0 : (0 : ℚ) < km := pos_of_mul_pos_left (hkm ▸ hmx0) hp.le
      exact ⟨km, by exact_mod_cast hkm0, le_rfl, hkm⟩
    cases amount with
    | none => exact ⟨mx, rfl, hmxn, hcap⟩
    | some a =>
      by_cases hza : a.isZero = true
      · exact ⟨mx, by simp [LoanBroker.clawRequest, hza], hmxn, hcap⟩
      · obtain ⟨hac, -, ha0⟩ := hreq a rfl
        obtain ⟨ka, hka⟩ := hk a rfl
        obtain ⟨mag, hmag, hmagv, hmagn⟩ := STAmount.toNumber_canonical_exact a .to_nearest (hac.resolve_right hza)
        -- an amount that is not zero is at least one base unit
        have hka1 : 1 ≤ ka := by
          have hpos := (STAmount.isZero_eq_false_iff_pos a ha0).mp (by simpa using hza)
          rw [hka] at hpos
          exact_mod_cast pos_of_mul_pos_left hpos hp.le
        refine ⟨if mag.operator_gt mx = true then mx else mag,
          by simp [LoanBroker.clawRequest, hza, hmag, bind, Except.bind, Except.pure], ?_⟩
        split_ifs with hgt
        · exact ⟨hmxn, hcap⟩
        · exact ⟨hmagn, ka, hka1, not_lt.mp (by rwa [← operator_gt_iff mag mx hmagn hmxn]),
            by rw [hmagv, hka]⟩

  -- the asset stores the claw exactly, and the clamp keeps an amount that is not zero
  have hkA : claw.toRat ≤ lb.coverAvailable.toRat := by linarith
  obtain ⟨claw', hof, hcv⟩ := LoanBroker.ofNumber_units lb _ hz ⟨hblo, hbhi⟩ hint claw k hcn hkv hkA
  have hcz : claw'.CanonicalOrZero := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1
  obtain ⟨c, hcl, hnz⟩ := LoanBroker.clamp_units lb v hz claw' hcz k hk1 (by rw [hcv, hkv])
    (by rw [hcv]; exact hkA)
  exact LoanBroker.canCoverClawback_success_proof lb v amount hxrp c
    (LoanBroker.roundedCoverClawback_rounded_proof lb v amount minimumCover mx claw claw' c hmin hsub hsig
      hclaw hof hcl hnz)

/-- Proof body of the never-throws part of the clawback line of `LoanBroker.cover_total`. -/
lemma LoanBroker.coverClawback_total_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    -- CoverAvailable is an asset balance, and every IOU amount is below 10^96
    (hcap : lb.toExact.coverAvailable < 10 ^ 96) :
    (∃ res, (lb.coverClawback pool amount).run = .ok (.ok res)) ∨
      (lb.coverClawback pool amount).run = .error .notLawful := by
  obtain ⟨-, c, hrc⟩ := (LoanBroker.canCoverClawback_ok_iff lb pool amount).mp hcan
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, _⟩ := LoanBroker.roundedCoverClawback_ok lb pool amount c hrc
  have hAn := lb.wf.coverAvailable_norm
  have hAe := Number.exponent_headroom_of_lt _ hAn lb.exact.coverAvailable_nonneg hcap

  -- the debit converts to a `Number` with room below the largest exponent
  obtain ⟨cN, hcN, hcn, hce⟩ : ∃ cN, c.toNumber .to_nearest = .ok cN ∧ cN.isNormalized ∧
      cN.exponent_ + 22 ≤ maxExponent := by
    by_cases hi : lb.numericType.isIntegral = true
    · -- an XRP or MPT debit is the magnitude of the clawed amount, a whole number below `2^63`
      obtain ⟨hic, -⟩ := STAmount.ofNumber_integral_canonical _ _ _ claw' hi hof
      have hsz := STAmount.ofNumber_integral_small _ _ _ claw' hi hof
      obtain ⟨hnt, hno, hnv⟩ := STAmount.operator_neg_fields claw'
      have hni : claw'.operator_neg.integral = true := (STAmount.operator_neg_integral claw').trans hic.is_integral
      obtain ⟨ht, ho, hv⟩ := clampToSumExponent_integral_fields _ _ _ _ hni hcl
      have hcic : c.IntegralCanonical :=
        ⟨by rw [ht, hnt]; exact hic.is_integral, by rw [ho, hno]; exact hic.offset_zero,
          by rw [hv, hnv, ht, hnt]; exact hic.in_range⟩
      have hcsz : c.mValue.toNat ≤ 2 ^ 63 - 1 := by rw [hv, hnv]; exact hsz
      obtain ⟨cN, hcN, hcv, hcn⟩ := STAmount.toNumber_integral_small_exact c _ hcic hcsz
      have hc0 : 0 ≤ c.toRat := by
        rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
        rw [← hcl, (clamp_magnitude _).2.2.2]
        exact abs_nonneg _
      have hclt : c.toRat < 10 ^ 96 := by
        have habs := STAmount.abs_toRat c
        rw [hcic.offset_zero, zpow_zero, mul_one] at habs
        have h63 : (c.mValue.toNat : ℚ) < 2 ^ 63 := by exact_mod_cast (by omega : c.mValue.toNat < 2 ^ 63)
        linarith [le_abs_self c.toRat, show (2 : ℚ) ^ 63 < 10 ^ 96 by norm_num]
      exact ⟨cN, hcN, hcn,
        Number.exponent_headroom_of_lt _ hcn (by rw [hcv]; exact hc0) (by rw [hcv]; exact hclt)⟩
    · -- an IOU debit is canonical or zero
      have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
      rw [hfr] at hof
      exact (clampToSumExponent_frac_shape _ _ _ _
        (STAmount.operator_neg_fczr _ (STAmount.ofNumber_fractional_fczr _ _ _ hof)) hcl).toNumber_ok .to_nearest

  -- the debit always computes, and the broker re-check fails only on a negative cover
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_exp _ _ .to_nearest hAn hcn hAe hce
  by_cases hneg : Number.zero.operator_le c' = true
  · have hc'n := operator_sub_isNormalized_to_nearest_sz _ _ _ hAn hcn hsub
    have hc'0 : 0 ≤ c'.toRat := by
      have h := (operator_le_iff _ _ Number.zero_isNormalized hc'n).mp hneg
      rwa [Number.toRat_zero] at h
    obtain ⟨lb', htl, -⟩ := LoanBroker.withCover_lawful lb c' hc'n hc'0
    left
    refine ⟨⟨c, lb'⟩, ?_⟩
    unfold LoanBroker.coverClawback LoanBroker.applyCoverTransaction
    unfold_ter
    rw [show lb.roundedCoverClawback pool amount = .ok (.ok c) from hrc]
    simp [hcN, hsub, htl]
  · exact Or.inr (LoanBroker.coverClawback_negative_cover_proof lb pool amount c cN c' hrc hcN hsub
      (by simpa using hneg))

/-- Proof body of the never-notLawful part of the clawback line of `LoanBroker.cover_total`. -/
lemma LoanBroker.coverClawback_lawful_total_proof (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS) :
    ∃ res, (lb.coverClawback v amount).run = .ok (.ok res) := by
  obtain ⟨-, c, hrc⟩ := (LoanBroker.canCoverClawback_ok_iff lb v amount).mp hcan
  obtain ⟨m, _, _, claw', hm, _, _, _, hof, hcl, hnz⟩ := LoanBroker.roundedCoverClawback_ok lb v amount c hrc
  have hfl := LoanBroker.roundedCoverClawback_floor lb v amount c m hz hnt hmax hreq hm hrc
  have hm0 := LoanBroker.minimumCover_nonneg lb _ _ v.baseExponent_range.2 hm

  -- the debit is a canonical amount, at most the cover above the minimum
  have hcz : claw'.CanonicalOrZero := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hcz.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  obtain ⟨cN, hcN, hcv, hcn⟩ := STAmount.toNumber_canonical_exact c .to_nearest
    (hcc.resolve_right (by rw [hnz]; decide))
  have hT : lb.clawTarget m.toRat amount ≤ lb.coverAvailable.toRat - m.toRat := LoanBroker.clawTarget_le lb _ amount
  have hfle : c.toRat ≤ lb.clawTarget m.toRat amount := by rw [hfl]; exact (floor_units_bounds _ _).1
  have hcle : cN.toRat ≤ lb.coverAvailable.toRat := by rw [hcv]; linarith

  -- so the debit leaves a cover that is not negative
  have hA9 := LoanBroker.OpenZone.cover_le lb _ hz v.baseExponent_bounds.2.1
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt _ _ .to_nearest lb.wf.coverAvailable_norm hcn
    lb.exact.coverAvailable_nonneg (by linarith) (by rw [hcv]; exact hc0) (by linarith)
  have hge : lb.coverAvailable.operator_lt cN = false :=
    (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hcn).mpr hcle
  obtain ⟨lb', hrun, -⟩ := LoanBroker.coverClawback_success_proof lb v amount c cN c' hrc hcN hge hsub
  exact ⟨_, hrun⟩

end XRPL.Model.Lending
