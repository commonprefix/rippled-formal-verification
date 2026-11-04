import XRPL.Properties.Lending.LoanBroker.Common.CoverExact

/-! # A deposit credits the amount floored to whole base units

On a broker in the Open zone a deposit that passes its check credits the amount floored to whole base units: the
sum with the cover stays below `10^(16 + b)`, so its floor lands on the base grid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private add_downward_ge from XRPL.Properties.Lending.Common.SumRounding

/-- A downward IOU conversion keeps a grid point of at most 16 digits that lies below its source. -/
private lemma ofNumber_frac_downward_ge_units (n : Number) (st : STAmount) (k : ℕ) (e : ℤ) (hn : n.isNormalized)
    (hk1 : 1 ≤ k) (hk : k < 10 ^ 16) (he : (-81 : ℤ) ≤ e) (hle : (k : ℚ) * 10 ^ e ≤ n.toRat)
    (h : STAmount.ofNumber .fractional n .downward = .ok st) : (k : ℚ) * 10 ^ e ≤ st.toRat := by
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hk1q : (1 : ℚ) ≤ k := by exact_mod_cast hk1
  have hpos : (10 : ℚ) ^ e ≤ n.toRat := by nlinarith
  have hn0 : 0 ≤ n.toRat := le_trans hp.le hpos
  have hm : n.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n h0] at hpos; linarith
  have hsz : st.mValue ≠ 0 := by
    intro hz
    have h81 := STAmount.ofNumber_fractional_zero_below_min .fractional n st .downward rfl hn
      (Number.negative_false_of_nonneg n hn hn0) hm h hz
    have : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) he
    linarith
  have hfl := STAmount.ofNumber_iou_downward_floor n st hn hm hn0 h hsz
  change st.toRat = (⌊n.toRat / 10 ^ (n.exponent_ + 3)⌋ : ℚ) * 10 ^ (n.exponent_ + 3) at hfl
  obtain ⟨s, hs⟩ : ∃ s, s = n.exponent_ + 3 := ⟨_, rfl⟩
  rw [← hs] at hfl
  have hps : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  rw [hfl]
  by_cases hse : s ≤ e
  · -- the grid point is a whole number of units of the source's grid
    have hsplit : (10 : ℚ) ^ e = ((10 ^ (e - s).toNat : ℕ) : ℚ) * 10 ^ s := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      congr 1
      omega
    have hK : ((k * 10 ^ (e - s).toNat : ℕ) : ℤ) ≤ ⌊n.toRat / 10 ^ s⌋ := by
      rw [Int.le_floor, le_div_iff₀ hps]
      rw [hsplit] at hle
      push_cast at hle ⊢
      linarith
    have hKq : (((k * 10 ^ (e - s).toNat : ℕ) : ℤ) : ℚ) ≤ (⌊n.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast hK
    push_cast at hKq
    calc (k : ℚ) * 10 ^ e = (k * 10 ^ (e - s).toNat) * 10 ^ s := by rw [hsplit]; push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKq hps.le
  · -- on a coarser grid the source holds at least `10^15` units of it
    push Not at hse
    have hbig := Number.pow_exponent_add_le_toRat n hn hn0 hm
    have h15 : (10 : ℚ) ^ (n.exponent_ + 18) = 10 ^ 15 * 10 ^ s := by
      rw [hs, show n.exponent_ + 18 = 15 + (n.exponent_ + 3) by ring, zpow_add₀ (by norm_num)]
      norm_num
    have hK : (10 ^ 15 : ℤ) ≤ ⌊n.toRat / 10 ^ s⌋ := by
      rw [Int.le_floor, le_div_iff₀ hps]
      push_cast
      linarith
    have hKq : ((10 ^ 15 : ℤ) : ℚ) ≤ (⌊n.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast hK
    push_cast at hKq
    have hes : (10 : ℚ) * 10 ^ e ≤ 10 ^ s := by
      rw [show (10 : ℚ) * 10 ^ e = 10 ^ (e + 1) by rw [zpow_add_one₀ (by norm_num)]; ring]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hkq : (k : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hk.le
    calc (k : ℚ) * 10 ^ e ≤ 10 ^ 16 * 10 ^ e := mul_le_mul_of_nonneg_right hkq hp.le
      _ = 10 ^ 15 * (10 * 10 ^ e) := by ring
      _ ≤ 10 ^ 15 * 10 ^ s := mul_le_mul_of_nonneg_left hes (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hKq hps.le

/-- Rounding down onto the grid of `10^e` keeps a point of that grid, of at most 16 digits, that lies below the
value. -/
private lemma roundToNumericType_frac_downward_ge_units (x c : Number) (k : ℕ) (e : ℤ) (hx : x.isNormalized)
    (hk1 : 1 ≤ k) (hk : k < 10 ^ 16) (he : (-81 : ℤ) ≤ e ∧ e ≤ 80) (hle : (k : ℚ) * 10 ^ e ≤ x.toRat)
    (h : STAmount.roundToNumericType .fractional x .downward (some e) = .ok c) : (k : ℚ) * 10 ^ e ≤ c.toRat := by
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber .fractional x .downward with
  | error err => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    have hret := ofNumber_frac_downward_ge_units x ret k e hx hk1 hk he.1 hle hof
    have hint : ret.integral = false := by
      unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ _ hof]; rfl
    simp only [hint, Bool.false_eq_true, if_false] at h
    cases hre : STAmount.roundToExponent ret e .downward with
    | error err => rw [hre] at h; exact absurd h (by simp)
    | ok rounded =>
      rw [hre] at h
      simp only at h
      have hrz : ret.mValue ≠ 0 := fun h0 => by
        rw [STAmount.toRat_eq_zero_of_mValue_zero ret h0] at hret
        have : (0 : ℚ) < k := Nat.cast_pos.mpr (by omega)
        nlinarith
      have hnz : x.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional x _ ret hof hrz
      obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hnz
      have hc := (STAmount.ofNumber_iou_ok_facts x _ ret hlo hhi (Number.exponent_ge_min x hx hnz) hof hrz).1
      have hrnd := STAmount.roundToExponent_rounded_of_scale ret rounded e .downward hc he.1 he.2 hre
      change rounded.toRat = (⌊ret.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e at hrnd
      have hK : (k : ℤ) ≤ ⌊ret.toRat / 10 ^ e⌋ := by
        rw [Int.le_floor, le_div_iff₀ hp]; exact_mod_cast hret
      have hKq : (k : ℚ) ≤ (⌊ret.toRat / 10 ^ e⌋ : ℚ) := by exact_mod_cast hK
      have hrv : (k : ℚ) * 10 ^ e ≤ rounded.toRat := by
        rw [hrnd]; exact mul_le_mul_of_nonneg_right hKq hp.le
      -- the rounded amount converts back exactly
      have hfc := STAmount.roundToExponent_fczr ret rounded e .downward
        (STAmount.ofNumber_fractional_fczr x _ ret hof) hre
      rcases hfc.2 with hc' | hz'
      · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact rounded .downward hc'
        rw [hsn, Except.ok.injEq] at h
        rw [← h, hv]; exact hrv
      · rw [(STAmount.toNumber_zero_facts rounded _ c hz' h).1]; exact hrv

/-- A deposit in the Open zone credits the amount floored to whole base units. -/
lemma LoanBroker.coverDeposit_floor (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.amount'.toRat = (⌊amount.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  obtain ⟨hr, -, hr0, -, hcov'⟩ := LoanBroker.coverDeposit_exact lb v amount res hz hnt hc hpos hcan hok
  obtain ⟨aN, hanum, hs, -⟩ := LoanBroker.roundedCoverAmount_ok lb v amount res.amount' hr
  obtain ⟨hav, han⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hc) aN hanum
  change sumRoundAndSubtract lb.coverAvailable aN v.baseExponent lb.numericType .downward = .ok res.amount' at hs
  have hA := lb.wf.coverAvailable_norm
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hc0 : 0 ≤ aN.toRat := by rw [hav]; exact hpos.le
  rw [← hav]

  -- an XRP or MPT credit is the amount itself, a whole number of units
  by_cases hi : lb.numericType.isIntegral = true
  · have hb0 : v.baseExponent = 0 := hint hi
    unfold sumRoundAndSubtract at hs
    rw [if_pos hi] at hs
    simp only [bind_pure] at hs
    have hai : amount.integral = true := by unfold STAmount.integral; rw [hat]; exact hi
    have hden : aN.toRat.den = 1 := by rw [hav]; exact STAmount.IntegralCanonical.den_eq_one amount (hc.1 hai).1
    rw [STAmount.ofNumber_integral_exact _ aN _ _ hi han hden hs, hb0]
    obtain ⟨z, hzv⟩ : ∃ z : ℤ, aN.toRat = z := ⟨aN.toRat.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
    rw [hzv]
    simp
  have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
  rw [hfr] at hs

  -- the deposit check keeps the cover plus the credit within the Open limit
  have hAr : lb.coverAvailable.toRat + res.amount'.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
    have h1 : res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + res.amount'.toRat := hcov'
    rw [← h1]
    exact le_trans (LoanBroker.coverDeposit_le lb v amount res hz.cover hint hcan hok) (max_le hz.coverLimit le_rfl)
  have hAL : lb.coverAvailable.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := hz.coverLimit

  have hs' := hs
  unfold sumRoundAndSubtract at hs'
  rw [if_neg (by decide)] at hs'
  obtain ⟨_, -, hs'⟩ := bind_ok_peel _ _ _ hs'
  obtain ⟨E, hE, hs'⟩ := bind_ok_peel _ _ _ hs'
  obtain ⟨sum, hsum, hs'⟩ := bind_ok_peel _ _ _ hs'
  obtain ⟨sum', hsum', hs'⟩ := bind_ok_peel _ _ _ hs'
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ hs'
  obtain ⟨hbE, -, hE80⟩ := postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE
  obtain ⟨s0, hs0, hE'⟩ := postSumExponent_reduces _ _ _ _ _ hE
  have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA han hs0
  have hR0 := operator_add_rounded_to_nearest _ _ _ hA han hs0
  have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA han hs0 (by linarith)
  rcases eq_or_lt_of_le hbE with hEb | hEb
  · -- the sum keeps the base exponent, so the exact sum stays below `10^(16 + b)`
    rw [← hEb] at hE hE'
    have hlt : lb.coverAvailable.toRat + aN.toRat < (10 : ℚ) ^ (16 + v.baseExponent) := by
      by_contra hge
      push Not at hge
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (16 + v.baseExponent)
        (by constructor <;> norm_num) ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
      have hws := Number.RoundsToRepresentable.ge_of_le hR0 (Or.inl rfl) w hw
        (by rw [hwv]; push_cast; linarith)
      rw [hwv] at hws
      push_cast at hws
      have := numberExponent_frac_of_le s0 v.baseExponent v.baseExponent (v.baseExponent + 1) hs0n (by omega)
        (by rw [show v.baseExponent + 1 + 15 = 16 + v.baseExponent by ring]; linarith) hE'
      omega
    obtain ⟨k, -, hkA⟩ := Number.OnGrid.units_le _ _ hz.cover hA0 hAL
    exact sumRoundAndSubtract_at_base_of_exponent _ _ _ _ k hA hkA han hc0 ⟨by omega, hbhi⟩ hE hlt hs

  -- a coarser posterior exponent means a sum of at least `10^(E + 15)`
  exfalso
  obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 _ E hs0n hs00 (by omega) hE' hEb
  have hu : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  have hE15 : (10 : ℚ) ^ (E + 15) = 10 ^ 15 * 10 ^ E := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have hbu : (10 : ℚ) * 10 ^ v.baseExponent ≤ 10 ^ E := by
    rw [show (10 : ℚ) * 10 ^ v.baseExponent = 10 ^ (v.baseExponent + 1) by rw [zpow_add_one₀ (by norm_num)]; ring]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hL : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ≤ 9 * 10 ^ 14 * 10 ^ E := by linarith
  have hEr : minExponent + 18 ≤ E ∧ E ≤ maxExponent - 1 :=
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩

  -- the exact sum is past the last grid point of `10^E` below `10^(E + 15)`
  obtain ⟨w1, hw1, hw1v⟩ := Number.exists_normalized_int_mul_pow 999999999999999 E (by constructor <;> norm_num) hEr
  have hX : w1.toRat ≤ lb.coverAvailable.toRat + aN.toRat := by
    by_contra hgt
    push Not at hgt
    have := Number.RoundsToRepresentable.le_of_ge hR0 (Or.inl rfl) w1 hw1 hgt.le
    rw [hw1v] at this
    push_cast at this
    linarith

  -- the downward sum and its floor onto the grid of `10^E` keep that grid point
  have hS := add_downward_ge _ _ _ w1 hA han hA0 hc0 hsum hw1 hX
  rw [hw1v] at hS
  have hsn := Number.operator_add_isNormalized_any _ _ _ _ hA han hsum
  have hS' := roundToNumericType_frac_downward_ge_units sum sum' 999999999999999 E hsn (by norm_num)
    (by norm_num) ⟨by omega, hE80⟩ (by push_cast at hS ⊢; exact hS) hsum'
  push_cast at hS'

  -- the credit is positive, so the difference with the cover is too
  have hs'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ hs'n hA hd
  have hrd := STAmount.ofNumber_downward_le_max .fractional d res.amount' hdn (by simp [NumericType.isIntegral]) hst
  have hd0 : 0 < d.toRat := by
    by_contra h0
    push Not at h0
    rw [max_eq_right h0] at hrd
    linarith
  have hdm : d.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hd0; exact lt_irrefl _ hd0
  have hRd := operator_sub_rounded_downward _ _ _ hs'n hA hd hdm

  -- a grid point of `10^E` below the difference survives both downward steps
  have hkeep : ∀ k : ℕ, 1 ≤ k → k < 10 ^ 16 →
      (k : ℚ) * 10 ^ E ≤ sum'.toRat - lb.coverAvailable.toRat → (k : ℚ) * 10 ^ E ≤ res.amount'.toRat := by
    intro k hk1 hk hle
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow k E (by constructor <;> omega) hEr
    have hwd := Number.RoundsToRepresentable.ge_of_le hRd (Or.inr (Or.inr rfl)) w hw
      (by rw [hwv]; push_cast; exact hle)
    rw [hwv] at hwd
    push_cast at hwd
    exact ofNumber_frac_downward_ge_units d res.amount' k E hdn hk1 hk (by omega) hwd hst

  -- either way the credit takes the cover past the Open limit
  by_cases hD : (10 : ℚ) ^ 15 * 10 ^ E ≤ sum'.toRat - lb.coverAvailable.toRat
  · have := hkeep (10 ^ 15) (by norm_num) (by norm_num) (by push_cast; exact hD)
    push_cast at this
    linarith
  push Not at hD
  obtain ⟨D, hDv⟩ : ∃ D, D = sum'.toRat - lb.coverAvailable.toRat := ⟨_, rfl⟩
  rw [← hDv] at hD hkeep
  have hm0 : 0 ≤ ⌊D / 10 ^ E⌋ := Int.floor_nonneg.mpr (div_nonneg (by linarith) hu.le)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ⌊D / 10 ^ E⌋ := ⟨_, Int.toNat_of_nonneg hm0⟩
  obtain ⟨hm1, hm2⟩ := floor_units_bounds D E
  rw [← hm] at hm1 hm2
  push_cast at hm1 hm2
  have hmlt : m < 10 ^ 16 := by
    have : (m : ℚ) < 10 ^ 15 := lt_of_mul_lt_mul_right (hm1.trans_lt hD) hu.le
    have : m < 10 ^ 15 := by exact_mod_cast this
    omega
  have hmge : 1 ≤ m := by
    have h1 : (99999999999999 : ℚ) * 10 ^ E < ((m : ℚ) + 1) * 10 ^ E := by linarith
    have h2 : (99999999999999 : ℚ) < (m : ℚ) + 1 := lt_of_mul_lt_mul_right h1 hu.le
    have h3 : (1 : ℚ) ≤ m := by linarith
    exact_mod_cast h3
  have := hkeep m hmge hmlt hm1
  linarith

end XRPL.Model.Lending
