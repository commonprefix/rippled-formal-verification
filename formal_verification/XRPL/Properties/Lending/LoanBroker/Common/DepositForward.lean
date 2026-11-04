import XRPL.Properties.Lending.LoanBroker.Common.DepositFloor
import XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal

/-! # A deposit of whole base units passes its checks

On a broker in the Open zone, depositing a nonzero whole number of base units of the vault that
keeps the cover within the Open limit passes every check of `canCoverDeposit`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- An asset maximum that fits the largest stored mantissa is at most `2^63 - 1`. -/
private lemma maxValue_le_pow63 (nt : NumericType) (h : nt.maxValue.toNat ≤ maxRep.toNat) :
    (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 - 1 := by
  have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
  rw [← hm]
  exact_mod_cast h

/-- Depositing a nonzero whole number of base units that keeps the cover within the Open limit passes
the checks. -/
lemma LoanBroker.canCoverDeposit_of_units (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hk : ∃ k : ℕ, 0 < k ∧ amount.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    -- an XRP or MPT asset accepts whole amounts (offset 0)
    (hoff : lb.numericType.isIntegral = true → (0 : Int) ≤ lb.numericType.maxOffset)
    (hroom : lb.toExact.coverAvailable + amount.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) :
    lb.canCoverDeposit v amount = .ok .tesSUCCESS := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  have hsr := (Vault.baseExponent_grid v).2
  obtain ⟨k, hk0, hkv⟩ := hk
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hpow16 : (10 : ℚ) ^ (16 + v.baseExponent) = (10 : ℚ) ^ 16 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  have hA := lb.wf.coverAvailable_norm
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hroom' : lb.coverAvailable.toRat + amount.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := hroom
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk0
  have ha0 : 0 < amount.toRat := by rw [hkv]; nlinarith
  obtain ⟨aN, hanum, hav, han⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
  have hc0 : 0 ≤ aN.toRat := by rw [hav]; exact ha0.le

  obtain ⟨j, -, hAv⟩ := Number.OnGrid.units_le _ _ hz.cover hA0 hz.coverLimit
  have hjc : lb.coverAvailable.toRat = ((j : ℤ) : ℚ) * 10 ^ v.baseExponent := by rw [hAv, Int.cast_natCast]

  -- the rounding credits the amount itself
  obtain ⟨r, rN, hr, hrN, hrNn, hrNr, hrNv⟩ : ∃ r rN,
      sumRoundAndSubtract lb.coverAvailable aN v.baseExponent lb.numericType .downward = .ok r ∧
        r.toNumber .to_nearest = .ok rN ∧ rN.isNormalized ∧ rN.toRat = r.toRat ∧ rN.toRat = amount.toRat := by
    by_cases hi : lb.numericType.isIntegral = true
    · -- an XRP or MPT amount within the maximum converts exactly
      have hai : amount.integral = true := by unfold STAmount.integral; rw [hat]; exact hi
      obtain ⟨hic, hmr⟩ := hc.1 hai
      rw [hat] at hmr
      have hden : aN.toRat.den = 1 := by rw [hav]; exact STAmount.IntegralCanonical.den_eq_one amount hic
      have hneg := Number.negative_false_of_nonneg aN han hc0
      have hmaxq := maxValue_le_pow63 _ hmr
      have hle : aN.toRat ≤ lb.numericType.maxValue.toNat := by
        have := hcap hi
        change lb.coverAvailable.toRat + amount.toRat ≤ _ at this
        rw [hav]; linarith
      obtain ⟨r, hof⟩ := STAmount.ofNumber_integral_ok_of_le _ aN .downward hi (hoff hi) han hneg hden
        (by linarith) hle
      have hr : sumRoundAndSubtract lb.coverAvailable aN v.baseExponent lb.numericType .downward = .ok r := by
        unfold sumRoundAndSubtract
        rw [if_pos hi]
        simp only [bind_pure]
        exact hof
      obtain ⟨hcan, hrnt⟩ := STAmount.ofNumber_integral_canonical _ aN .downward r hi hof
      obtain ⟨rN, hrN, hrNv, hrNn, -⟩ := STAmount.toNumber_integral_exact r .to_nearest hcan
        (by rw [hrnt]; exact hmr)
      refine ⟨r, rN, hr, hrN, hrNn, hrNv, ?_⟩
      rw [hrNv, STAmount.ofNumber_integral_exact _ aN _ _ hi han hden hof, hav]
    · -- an IOU sum with room below `10^(16 + b)` lands on the base grid
      have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
      rw [hfr]
      have hlt : lb.coverAvailable.toRat + aN.toRat ≤ 10 ^ 16 * 10 ^ v.baseExponent - 10 ^ v.baseExponent := by
        rw [hav]; linarith
      obtain ⟨r, hr, hrf⟩ := sumRoundAndSubtract_frac_downward_ok _ aN _ hA han hA0 hc0 ⟨hblo, hbhi⟩ hlt
      obtain ⟨rN, hrN, -, -⟩ := hrf.toNumber_ok .to_nearest
      obtain ⟨-, hrx⟩ := sumRoundAndSubtract_downward_le _ _ _ _ r hA hA0 han hc0 v.baseExponent_range hr
      obtain ⟨hrNv, hrNn⟩ := hrx rN hrN
      have hfl := sumRoundAndSubtract_at_base _ _ _ r j hA hAv han hc0 ⟨by omega, hbhi⟩
        (by rw [hpow16]; exact hlt) hr
      refine ⟨r, rN, hr, hrN, hrNn, hrNv, ?_⟩
      rw [hrNv, hfl, hav, hkv, mul_div_cancel_right₀ _ hp.ne', Int.floor_natCast]
      push_cast
      ring
  have hr0 : 0 < r.toRat := by rw [← hrNr, hrNv]; exact ha0
  have hrun : (lb.roundedCoverAmount v amount).run = .ok (.ok r) := by
    rw [LoanBroker.roundedCoverAmount_run lb v amount aN r hanum hr,
      if_neg (not_le.mpr ((STAmount.signum_pos_iff_toRat_pos r).mpr hr0))]

  -- the cover plus the credit is exact on the base grid
  have hrNg : rN.toRat = ((k : ℤ) : ℚ) * 10 ^ v.baseExponent := by rw [hrNv, hkv]; push_cast; ring
  have hsum : lb.coverAvailable.toRat + rN.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
    rw [hrNv]; exact hroom'
  have h96 : (9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) < 10 ^ 96 := by nlinarith
  have hjk : (j : ℤ) + k ≤ 9 * 10 ^ 15 := by
    have h1 : (((j : ℤ) + k : ℤ) : ℚ) * 10 ^ v.baseExponent ≤ (9 * 10 ^ 15 : ℤ) * 10 ^ v.baseExponent := by
      push_cast; rw [add_mul, ← hAv]; rw [hrNg] at hsum; push_cast at hsum; linarith
    exact_mod_cast le_of_mul_le_mul_right h1 hp
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_lt _ rN .to_nearest hA hrNn hA0 (by linarith)
    (by linarith) (by linarith)
  have hsv := Number.operator_add_toRat_of_grid _ _ _ j k _ hA hrNn hjc hrNg ⟨by omega, by omega⟩ hsr hs
  have hsA : s.toRat = lb.coverAvailable.toRat + amount.toRat := by rw [hsv, hjc, hkv]; push_cast; ring
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hA hrNn hs
  have hs0 : 0 ≤ s.toRat := by rw [hsA]; linarith

  -- the sum keeps the base exponent
  obtain ⟨e, he⟩ : ∃ e, numberExponent s v.baseExponent lb.numericType = .ok e := by
    unfold numberExponent
    by_cases hz0 : s.operator_eq Number.zero = true
    · rw [if_pos hz0]; exact ⟨_, rfl⟩
    rw [if_neg hz0]
    obtain ⟨st, hst⟩ : ∃ st, STAmount.ofNumber lb.numericType s .downward = .ok st := by
      by_cases hi : lb.numericType.isIntegral = true
      · have hden : s.toRat.den = 1 := by
          rw [hsv, hint hi, zpow_zero, mul_one]; exact Rat.den_intCast _
        have := hcap hi
        change lb.coverAvailable.toRat + amount.toRat ≤ _ at this
        have hai : amount.integral = true := by unfold STAmount.integral; rw [hat]; exact hi
        have hmr := (hc.1 hai).2
        rw [hat] at hmr
        have hmaxq := maxValue_le_pow63 _ hmr
        exact STAmount.ofNumber_integral_ok_of_le _ s .downward hi (hoff hi) hsn
          (Number.negative_false_of_nonneg s hsn hs0) hden (by linarith) (by linarith)
      · have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
        rw [hfr]
        obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s .downward hsn
          (by rw [abs_of_nonneg hs0]; nlinarith)
        exact ⟨st, hst⟩
    rw [hst]
    exact ⟨_, rfl⟩
  have heb := numberExponent_at_base s _ _ e hsn hs0 (by omega) hint (by rw [hpow16]; nlinarith) he
  subst heb
  have hps : postSumExponent lb.coverAvailable rN (AssetPool.baseExponent v) lb.numericType =
      .ok (AssetPool.baseExponent v) := by
    unfold postSumExponent
    rw [hs]
    exact he

  -- rounded toward zero, the sum stays within the Open limit
  obtain ⟨t, ht⟩ := Number.operator_add_ok_of_lt _ rN .towards_zero hA hrNn hA0 (by linarith)
    (by linarith) (by linarith)
  obtain ⟨L, hL, hLn, hLv⟩ := Vault.openLimit_value v
  have htn := Number.operator_add_isNormalized_any _ _ _ _ hA hrNn ht
  have htle : t.toRat ≤ L.toRat := by
    obtain ⟨l, hlo, htv⟩ := operator_add_rounded_towards_zero _ _ _ hA hrNn ht
    rw [if_pos (by linarith)] at hlo
    rw [htv, hLv]
    linarith [Number.lower_le _ l hlo]
  have hgt : t.operator_gt L = false := by
    cases h : t.operator_gt L
    · rfl
    · have := (operator_gt_iff _ _ htn hLn).mp h
      linarith
  have hcheck : lb.checkCoverOpenLimit v r = .ok .tesSUCCESS := by
    unfold LoanBroker.checkCoverOpenLimit
    rw [show AssetPool.openLimit v = v.openLimit from rfl, hrN]
    simp only [bind, Except.bind, hps, bne_self_eq_false, ht, hL, hgt]
    rfl
  unfold LoanBroker.canCoverDeposit
  rw [hrun]
  exact hcheck

end XRPL.Model.Lending
