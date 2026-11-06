import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps

/-! # The cover a default pays lands exactly on AssetsAvailable

A default floors AssetsAvailable + covered amount at the scale of the sum and credits the difference. That credit
is exact on a reachable ledger, whether the vault is coarsened or not: AssetsAvailable' = AssetsAvailable + credit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private add_downward_ge_any from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private sub_exact from XRPL.Properties.Lending.Common.SumRounding
open private STAmount.ofNumber_iou_downward_floor_value STAmount.ofNumber_frac_of_representable
  from XRPL.Properties.Lending.Loan.Common.SetValue

/-- `10^a · 10^s` as one power. -/
private lemma pow_add_nat (a : ℕ) (s : ℤ) : (10 : ℚ) ^ (s + a) = ((10 ^ a : ℕ) : ℚ) * 10 ^ s := by
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]; push_cast; ring

/-- Rounding a sum down at a scale floors it onto a grid. The result is a whole number of `10^G` units, fewer
than `10^16` of them, where `G` is the scale or the grid of the sum's 16th digit, whichever is coarser. -/
private lemma roundDown_shape (sum sum' : Number) (E : Int) (hsn : sum.isNormalized) (hs0 : 0 ≤ sum.toRat)
    (hE : -81 ≤ E ∧ E ≤ 80)
    (h : STAmount.roundToNumericType .fractional sum .downward (some E) = .ok sum') :
    ∃ (G : Int) (j : ℕ), E ≤ G ∧ G ≤ 80 ∧ (sum.mantissa_ ≠ 0 → sum.exponent_ + 3 ≤ G) ∧ j < 10 ^ 16 ∧
      sum'.toRat = (j : ℚ) * 10 ^ G ∧ sum'.toRat ≤ sum.toRat ∧ sum.toRat < sum'.toRat + 10 ^ G ∧
      (G = E ∨ 10 ^ 15 ≤ j) := by
  have hle := (STAmount.roundToNumericType_downward_le sum sum' E hsn hs0 ⟨by omega, hE.2⟩ h).2.1
  unfold STAmount.roundToNumericType at h
  cases hret : STAmount.ofNumber .fractional sum .downward with
  | error e => rw [hret] at h; cases h
  | ok ret =>
  rw [hret] at h
  simp only at h
  have hretf := STAmount.ofNumber_fractional_fczr sum _ ret hret
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  rw [if_neg (by rw [hret_int]; decide)] at h
  cases hrd : STAmount.roundToExponent ret E .downward with
  | error e => rw [hrd] at h; cases h
  | ok rd =>
  rw [hrd] at h
  simp only at h
  have hrdf := STAmount.roundToExponent_fczr ret rd E .downward hretf hrd
  have hv := STAmount.FracCanonZero.toNumber_val hrdf .downward sum' h
  by_cases hrz : ret.mValue = 0
  · -- a zero 16-digit amount comes from a sum too small to reach the scale
    have hrr : rd = ret := by
      unfold STAmount.roundToExponent at hrd
      simp only [hret_int, Bool.false_eq_true, if_false, STAmount.isZero, hrz, beq_self_eq_true, if_true,
        Except.ok.injEq] at hrd
      exact hrd.symm
    have hs'0 : sum'.toRat = 0 := by rw [hv, hrr, STAmount.toRat_eq_zero_of_mValue_zero ret hrz]
    refine ⟨E, 0, le_rfl, hE.2, fun hm => ?_, by norm_num, by rw [hs'0]; simp, hle, ?_, Or.inl rfl⟩
    · have : sum.exponent_ < -99 := by
        by_contra hc
        exact STAmount.ofNumber_iou_ne_zero_of_exponent sum _ ret hsn hm (by omega) hret hrz
      omega
    · rw [hs'0, zero_add]
      by_cases hm : sum.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero sum hm]; exact zpow_pos (by norm_num) _
      have hlt : sum.exponent_ < -99 := by
        by_contra hc
        exact STAmount.ofNumber_iou_ne_zero_of_exponent sum _ ret hsn hm (by omega) hret hrz
      obtain ⟨-, hhi⟩ := hsn.mantissaBounds_nat hm
      have hmq : (sum.mantissa_.toNat : ℚ) < 10 ^ (19 : ℤ) := by norm_num; exact_mod_cast hhi
      have hsv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsn hs0)
      have hpe : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
      calc sum.toRat = sum.mantissa_.toNat * 10 ^ sum.exponent_ := hsv
        _ < 10 ^ (19 : ℤ) * 10 ^ sum.exponent_ := mul_lt_mul_of_pos_right hmq hpe
        _ = 10 ^ (19 + sum.exponent_) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        _ ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) (by omega)
  · have hnz : sum.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional sum _ ret hret hrz
    obtain ⟨hlo, hhi⟩ := hsn.mantissaBounds_nat hnz
    have hc := (STAmount.ofNumber_iou_ok_facts sum _ ret hlo hhi (Number.exponent_ge_min sum hsn hnz) hret hrz).1
    obtain ⟨hfl, hexp⟩ := STAmount.ofNumber_iou_downward_floor_value sum ret hsn hnz hs0 hret hrz
    have hrnd := STAmount.roundToExponent_rounded_of_scale ret rd E .downward hc hE.1 hE.2 hrd
    change rd.toRat = (⌊ret.toRat / 10 ^ E⌋ : ℚ) * 10 ^ E at hrnd
    have hs3 : sum.exponent_ + 3 ≤ 80 := by
      have := hc.exp_hi; rw [show ret.mOffset = ret.exponent from rfl, hexp] at this; exact this
    have hp3 : (0 : ℚ) < 10 ^ (sum.exponent_ + 3) := zpow_pos (by norm_num) _
    set X := ⌊sum.toRat / 10 ^ (sum.exponent_ + 3)⌋ with hX
    have hX0 : 0 ≤ X := Int.floor_nonneg.mpr (div_nonneg hs0 hp3.le)
    have hXlt : X < 10 ^ 16 := by
      have hm : (sum.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
      have hsv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsn hs0)
      have hlt : sum.toRat / 10 ^ (sum.exponent_ + 3) < 10 ^ 16 := by
        rw [div_lt_iff₀ hp3, hsv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        have : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
        norm_num
        nlinarith
      have := Int.floor_lt.mpr (show sum.toRat / 10 ^ (sum.exponent_ + 3) < ((10 ^ 16 : ℤ) : ℚ) by
        push_cast; exact hlt)
      exact this
    by_cases hsE : sum.exponent_ + 3 ≤ E
    · -- the scale is the coarser grid: the result is the floor of the sum there
      have hp : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
      have hY0 : 0 ≤ ⌊sum.toRat / 10 ^ E⌋ := Int.floor_nonneg.mpr (div_nonneg hs0 hp.le)
      have hY : ((⌊sum.toRat / 10 ^ E⌋.toNat : ℕ) : ℚ) = (⌊sum.toRat / 10 ^ E⌋ : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hY0
      have hs'v : sum'.toRat = (⌊sum.toRat / 10 ^ E⌋ : ℚ) * 10 ^ E := by
        rw [hv, hrnd, hfl, floor_grid_floor_of_le _ _ _ hsE]
      refine ⟨E, ⌊sum.toRat / 10 ^ E⌋.toNat, le_rfl, hE.2, fun _ => hsE, ?_, by rw [hs'v, hY], hle, ?_, Or.inl rfl⟩
      · have hYle : ⌊sum.toRat / 10 ^ E⌋ ≤ X := by
          rw [hX]
          apply Int.floor_mono
          exact div_le_div_of_nonneg_left hs0 hp3 (zpow_le_zpow_right₀ (by norm_num) hsE)
        omega
      · rw [hs'v]
        have := Int.lt_floor_add_one (sum.toRat / 10 ^ E)
        rw [div_lt_iff₀ hp] at this
        linarith
    · -- the 16th digit is the coarser grid: the floor at the scale keeps the 16-digit floor
      push Not at hsE
      have hrdv : rd.toRat = ret.toRat := by
        rw [hrnd, hfl]
        have hsplit : (10 : ℚ) ^ (sum.exponent_ + 3) =
            ((10 ^ (sum.exponent_ + 3 - E).toNat : ℕ) : ℚ) * 10 ^ E := by
          rw [← pow_add_nat]; congr 1; omega
        have hp : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
        rw [hsplit]
        have : (X : ℚ) * (((10 ^ (sum.exponent_ + 3 - E).toNat : ℕ) : ℚ) * 10 ^ E) / 10 ^ E =
            ((X * (10 ^ (sum.exponent_ + 3 - E).toNat : ℕ) : ℤ) : ℚ) := by
          field_simp; push_cast; ring
        rw [this, Int.floor_intCast]
        push_cast
        ring
      have hXn : ((X.toNat : ℕ) : ℚ) = (X : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hX0
      have hs'v : sum'.toRat = (X : ℚ) * 10 ^ (sum.exponent_ + 3) := by rw [hv, hrdv, hfl]
      -- the sum has 19 digits, so its 16-digit floor has 16
      have hX15 : 10 ^ 15 ≤ X := by
        have hsv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsn hs0)
        have hmq : (10 : ℚ) ^ (18 : ℤ) ≤ sum.mantissa_.toNat := by norm_num; exact_mod_cast hlo
        have hge : ((10 ^ 15 : ℤ) : ℚ) ≤ sum.toRat / 10 ^ (sum.exponent_ + 3) := by
          rw [le_div_iff₀ hp3, hsv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
          have hpe : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
          push_cast
          nlinarith
        exact Int.le_floor.mpr hge
      refine ⟨sum.exponent_ + 3, X.toNat, hsE.le, hs3, fun _ => le_rfl, by omega, by rw [hs'v, hXn], hle, ?_,
        Or.inr (by omega)⟩
      rw [hs'v]
      have := Int.lt_floor_add_one (sum.toRat / 10 ^ (sum.exponent_ + 3))
      rw [div_lt_iff₀ hp3] at this
      linarith

/-- A whole number of grid units, at most `10^16` of them, converts to an IOU exactly, in every mode and for
either sign: the 19-digit mantissa ends in three zeros. -/
private lemma ofNumber_frac_exact_of_units (d : Number) (g : Int) (K : ℤ) (mode : rounding_mode) (st : STAmount)
    (hd : d.isNormalized) (hdv : d.toRat = (K : ℚ) * 10 ^ g) (hK : K.natAbs ≤ 10 ^ 16)
    (hg : -10 ≤ g ∧ g ≤ 80) (hedge : K.natAbs = 10 ^ 16 → g ≤ 79)
    (h : STAmount.ofNumber .fractional d mode = .ok st) : st.toRat = d.toRat := by
  have hpg : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  by_cases hK0 : K = 0
  · have hd0 : d = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hd).mp (by rw [hdv, hK0]; simp)
    rw [hd0, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at h
    rw [← h, hd0, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero _ rfl]
  have hm0 : d.mantissa_ ≠ 0 := fun h0 => hK0 (by
    rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hdv
    exact_mod_cast (mul_eq_zero.mp hdv.symm).resolve_right hpg.ne')
  obtain ⟨hlo, hhi⟩ := hd.mantissaBounds_nat hm0
  set M := d.mantissa_.toNat with hM
  set x := d.exponent_ with hx
  have hpx : (0 : ℚ) < 10 ^ x := zpow_pos (by norm_num) _

  have hMK : (M : ℚ) * 10 ^ x = (K.natAbs : ℚ) * 10 ^ g := by
    rw [hM, hx, ← abs_toRat_eq d, hdv, abs_mul, abs_of_pos hpg, Nat.cast_natAbs, Int.cast_abs]
  have hxg : x + 2 ≤ g := by
    have h1 : (10 : ℚ) ^ (x + 18) ≤ 10 ^ (g + 16) := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      have hM18 : (10 : ℚ) ^ (18 : ℤ) ≤ M := by norm_num; exact_mod_cast hlo
      have hK16 : (K.natAbs : ℚ) ≤ 10 ^ (16 : ℤ) := by
        rw [show (10 : ℚ) ^ (16 : ℤ) = ((10 ^ 16 : ℕ) : ℚ) by norm_num]; exact_mod_cast hK
      calc (10 : ℚ) ^ x * 10 ^ (18 : ℤ) ≤ 10 ^ x * M := mul_le_mul_of_nonneg_left hM18 hpx.le
        _ = K.natAbs * 10 ^ g := by rw [mul_comm, hMK]
        _ ≤ 10 ^ (16 : ℤ) * 10 ^ g := mul_le_mul_of_nonneg_right hK16 hpg.le
        _ = 10 ^ g * 10 ^ (16 : ℤ) := mul_comm _ _
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
    omega
  have hgx : g ≤ x + 18 := by
    have h1 : (10 : ℚ) ^ g < 10 ^ (x + 19) := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      have hM19 : (M : ℚ) < 10 ^ (19 : ℤ) := by norm_num; exact_mod_cast hhi
      have hK1 : (1 : ℚ) ≤ K.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hK0
      calc (10 : ℚ) ^ g ≤ K.natAbs * 10 ^ g := le_mul_of_one_le_left hpg.le hK1
        _ = M * 10 ^ x := hMK.symm
        _ < 10 ^ (19 : ℤ) * 10 ^ x := mul_lt_mul_of_pos_right hM19 hpx
        _ = 10 ^ x * 10 ^ (19 : ℤ) := mul_comm _ _
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
    omega
  set t := (g - x).toNat with ht
  have htg : (t : ℤ) = g - x := by rw [ht]; omega
  have hMnat : M = K.natAbs * 10 ^ t := by
    have hsplit : (10 : ℚ) ^ g = ((10 ^ t : ℕ) : ℚ) * 10 ^ x := by rw [← pow_add_nat]; congr 1; omega
    rw [hsplit, ← mul_assoc] at hMK
    have := mul_right_cancel₀ hpx.ne' hMK
    exact_mod_cast this
  have hmod : M % 1000 = 0 := by
    by_cases ht3 : 3 ≤ t
    · rw [hMnat]
      apply Nat.mod_eq_zero_of_dvd
      exact Dvd.dvd.mul_left (by rw [show t = 3 + (t - 3) by omega, pow_add]; exact Dvd.intro _ rfl) _
    · have ht2 : t = 2 := by omega
      rw [ht2] at hMnat
      have : K.natAbs = 10 ^ 16 := by omega
      rw [hMnat, this]
      norm_num
  have hedge' : x + 3 ≤ 80 := by
    by_cases ht3 : 3 ≤ t
    · omega
    · have ht2 : t = 2 := by omega
      rw [ht2] at hMnat
      have := hedge (by omega)
      omega

  have hm3 : ((d.mantissa_ / 10 / 10 / 10).toNat : ℚ) * 10 ^ (x + 3) = (M : ℚ) * 10 ^ x := by
    rw [m_div_thousand_toNat, ← hM, Nat.cast_div (Nat.dvd_of_mod_eq_zero hmod) (by norm_num),
      zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    norm_num
    ring
  cases hneg : d.negative_
  · rw [STAmount.ofNumber_fractional_of_trailing_zeros d mode hd hm0 hneg hmod (by omega) hedge',
      Except.ok.injEq] at h
    rw [← h, STAmount.toRat_of_nonneg _ rfl, Number.toRat_of_nonneg d hneg]
    exact hm3
  · rw [STAmount.ofNumber_fractional_of_trailing_zeros_neg d mode hd hm0 hneg hmod (by omega) hedge',
      Except.ok.injEq] at h
    rw [← h, STAmount.toRat_of_neg _ rfl, Number.toRat_of_neg d hneg]
    simp only at hm3 ⊢
    rw [hm3]

/-- The IOU credit lands exactly, on the floor of the sum. AssetsAvailable' is AssetsAvailable plus the credit,
the downward sum floored onto a grid `10^G` no finer than the exponent of AssetsAvailable'. -/
private lemma sumRoundAndSubtract_credit_core (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded .fractional A = false)
    (hAg : ∃ k : ℕ, A.toRat = k * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hcle : c.toRat ≤ 10 ^ 16 * 10 ^ b) (hb : -10 ≤ b ∧ b ≤ 0)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    ∃ (E G : Int) (j : ℕ) (sum : Number), postSumExponent A c b .fractional = .ok E ∧
      A.operator_add c .downward = .ok sum ∧ b ≤ E ∧ E ≤ G ∧ G ≤ 80 ∧ j < 10 ^ 16 ∧
      a'.toRat = (j : ℚ) * 10 ^ G ∧ a'.toRat = A.toRat + cr.toRat ∧ sum.toRat < a'.toRat + 10 ^ G ∧
      (G = E ∨ 10 ^ 15 ≤ j) := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  obtain ⟨-, hcrx⟩ := sumRoundAndSubtract_downward_le A c b .fractional st hA hA0 hc hc0 ⟨by omega, by omega⟩ h
  obtain ⟨hcrv, hcrn⟩ := hcrx cr hcr
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ h
  have hErange := postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE

  have hsumn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsum
  obtain ⟨hsle, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  obtain ⟨G, j, hEG, hG80, hsG, hj, hsum'v, hs'le, hsfl, hGj⟩ :=
    roundDown_shape sum sum' E hsumn hs0 ⟨by omega, hErange.2.2⟩ hsum'
  have hsum'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  have hs'0 : 0 ≤ sum'.toRat := by rw [hsum'v]; positivity

  obtain ⟨g, kA, hbg, hgG, hkA, hAv⟩ : ∃ (g : Int) (kA : ℕ), b ≤ g ∧ g ≤ G ∧ kA < 10 ^ 16 ∧
      A.toRat = kA * 10 ^ g := by
    rcases (STAmount.isRounded_eq_false_iff _ A hA hA0).mp hArep with h0 | ⟨m, e, hmlo, hmhi, helo, hehi, hv⟩
    · exact ⟨G, 0, by omega, le_rfl, by norm_num, by rw [h0]; simp⟩
    · have hpe : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
      have hm15 : (10 : ℚ) ^ (15 : ℤ) ≤ m := by norm_num; exact_mod_cast hmlo
      have hApos : 0 < A.toRat := by rw [hv]; nlinarith
      have hAsum : A.toRat ≤ sum.toRat := add_downward_ge_any A c sum A hA hc hsum hA hApos (by linarith)
      have hsm : sum.mantissa_ ≠ 0 := fun h0 => by
        rw [Number.toRat_eq_zero_of_mantissa_zero sum h0] at hAsum; linarith
      -- the sum reaches AssetsAvailable, so its 16th digit is no finer than AssetsAvailable's
      have heG : e ≤ G := by
        have h3 := hsG hsm
        obtain ⟨-, hhi⟩ := hsumn.mantissaBounds_nat hsm
        have hsv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsumn hs0)
        have h1 : (10 : ℚ) ^ (e + 15) < 10 ^ (sum.exponent_ + 19) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
          have hm19 : (sum.mantissa_.toNat : ℚ) < 10 ^ (19 : ℤ) := by norm_num; exact_mod_cast hhi
          have hps : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
          calc (10 : ℚ) ^ e * 10 ^ (15 : ℤ) ≤ A.toRat := by
                rw [hv, mul_comm]; exact mul_le_mul_of_nonneg_right hm15 hpe.le
            _ ≤ sum.toRat := hAsum
            _ = sum.mantissa_.toNat * 10 ^ sum.exponent_ := hsv
            _ < 10 ^ (19 : ℤ) * 10 ^ sum.exponent_ := mul_lt_mul_of_pos_right hm19 hps
            _ = 10 ^ sum.exponent_ * 10 ^ (19 : ℤ) := mul_comm _ _
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
        omega
      obtain ⟨a, ha⟩ := hAg
      by_cases hbe : b ≤ e
      · exact ⟨e, m, hbe, heG, hmhi, hv⟩
      · push Not at hbe
        refine ⟨b, a, le_rfl, by omega, ?_, ha⟩
        have hlt : (a : ℚ) * 10 ^ b < 10 ^ 16 * 10 ^ b := by
          rw [← ha, hv]
          calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := mul_lt_mul_of_pos_right (by exact_mod_cast hmhi) hpe
            _ ≤ 10 ^ 16 * 10 ^ b :=
              mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hbe.le) (by positivity)
        have := lt_of_mul_lt_mul_right hlt hp.le
        exact_mod_cast this
  have hpg : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _

  have hsplit : (10 : ℚ) ^ G = ((10 ^ (G - g).toNat : ℕ) : ℚ) * 10 ^ g := by
    rw [← pow_add_nat]; congr 1; omega
  set K : ℤ := ((j * 10 ^ (G - g).toNat : ℕ) : ℤ) - kA with hK
  have hKv : sum'.toRat - A.toRat = (K : ℚ) * 10 ^ g := by
    rw [hsum'v, hAv, hsplit, hK]; push_cast; ring
  have hKhi : (K : ℚ) * 10 ^ g ≤ 10 ^ 16 * 10 ^ b := by rw [← hKv]; linarith
  have hKhi' : K ≤ 10 ^ 16 := by
    have h1 : (K : ℚ) * 10 ^ g ≤ 10 ^ 16 * 10 ^ g :=
      hKhi.trans (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hbg) (by positivity))
    have := le_of_mul_le_mul_right h1 hpg
    exact_mod_cast this
  have hKlo : -(kA : ℤ) ≤ K := by rw [hK]; omega
  have hedge : K.natAbs = 10 ^ 16 → g ≤ 79 := by
    intro hK16
    have hKeq : K = 10 ^ 16 := by omega
    rw [hKeq] at hKhi
    push_cast at hKhi
    have := le_of_mul_le_mul_left hKhi (by positivity)
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp this
    omega

  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow K g ⟨by omega, by omega⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hdv : d.toRat = sum'.toRat - A.toRat := sub_exact sum' A d w _ hsum'n hA hs'0 hA0 hd hw (by rw [hwv, hKv])
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ hsum'n hA hd
  have hstv : st.toRat = d.toRat :=
    ofNumber_frac_exact_of_units d g K _ st hdn (by rw [hdv, hKv]) (by omega) ⟨by omega, by omega⟩ hedge hst

  have hsumv : A.toRat + cr.toRat = sum'.toRat := by rw [hcrv, hstv, hdv]; ring
  have haav := Number.operator_add_exact_of_fits hA hcrn haa ⟨sum', hsum'n, hsumv.symm⟩
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ hA hcrn haa
  have haa0 : 0 ≤ aa.toRat := by rw [haav, hsumv]; exact hs'0
  have hrep : STAmount.isRounded .fractional aa = false := by
    rw [STAmount.isRounded_eq_false_iff _ _ haan haa0, haav, hsumv, hsum'v]
    exact STAmount.representable_fractional_of_units j G hj (by omega) hG80
  have ha'v : a'.toRat = A.toRat + cr.toRat := by
    rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep ha', haav]
  refine ⟨E, G, j, sum, hE, hsum, hErange.1, hEG, hG80, hj, by rw [ha'v, hsumv, hsum'v], ha'v, ?_, hGj⟩
  rw [ha'v, hsumv]
  exact hsfl

/-- The IOU credit lands exactly. When AssetsAvailable is an amount the asset stores, a whole number of base
units, and the amount added is at most `10^16` base units, AssetsAvailable' is AssetsAvailable plus the credit. -/
lemma sumRoundAndSubtract_credit_exact (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded .fractional A = false)
    (hAg : ∃ k : ℕ, A.toRat = k * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hcle : c.toRat ≤ 10 ^ 16 * 10 ^ b) (hb : -10 ≤ b ∧ b ≤ 0)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    a'.toRat = A.toRat + cr.toRat :=
  (sumRoundAndSubtract_credit_core A c b st cr aa a' hA hA0 hArep hAg hc hc0 hcle hb h hcr haa ha').choose_spec
    |>.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.1

/-- The IOU credit floors the sum at the scale of AssetsAvailable'. When AssetsAvailable plus the amount added is
also a `Number`, the credit falls short of the amount by less than one unit of the new scale. -/
lemma sumRoundAndSubtract_credit_floor (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded .fractional A = false)
    (hAg : ∃ k : ℕ, A.toRat = k * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hcle : c.toRat ≤ 10 ^ 16 * 10 ^ b) (hb : -10 ≤ b ∧ b ≤ 0)
    (hfit : ∃ w : Number, w.isNormalized ∧ w.toRat = A.toRat + c.toRat)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    a'.toRat = A.toRat + cr.toRat ∧ ∀ e, numberExponent a' b .fractional = .ok e →
      A.toRat + c.toRat - a'.toRat < 10 ^ e := by
  obtain ⟨E, G, j, sum, hE, hsum, hbE, hEG, hG80, hj, ha'j, ha'v, hsfl, hGj⟩ :=
    sumRoundAndSubtract_credit_core A c b st cr aa a' hA hA0 hArep hAg hc hc0 hcle hb h hcr haa ha'
  refine ⟨ha'v, fun e he => ?_⟩
  obtain ⟨w, hw, hwv⟩ := hfit
  have hpG : (0 : ℚ) < 10 ^ G := zpow_pos (by norm_num) _
  have ha'0 : 0 ≤ a'.toRat := by rw [ha'j]; positivity
  obtain ⟨hsle, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  have hsumv : sum.toRat = A.toRat + c.toRat := by
    rcases eq_or_lt_of_le (add_nonneg hA0 hc0) with h0 | hpos
    · linarith
    · have hle := add_downward_ge_any A c sum w hA hc hsum hw (by linarith) (le_of_eq hwv)
      rw [hwv] at hle
      exact le_antisymm hsle hle
  have hlt : A.toRat + c.toRat - a'.toRat < 10 ^ G := by rw [← hsumv]; linarith
  have hjG : G = b ∨ 10 ^ 15 ≤ j := by
    rcases hGj with hGE | hj15
    · rcases eq_or_lt_of_le hbE with hEb | hEb
      · exact Or.inl (by rw [hGE, hEb])
      · right
        obtain ⟨s0, hs0, hne⟩ := postSumExponent_reduces _ _ _ _ _ hE
        have hs0v := Number.operator_add_exact_of_fits hA hc hs0 ⟨w, hw, hwv⟩
        have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
        obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b E hs0n (by rw [hs0v]; linarith) (by omega) hne hEb
        rw [hs0v] at hbig
        subst hGE
        have hjq : ((10 ^ 15 - 1 : ℤ) : ℚ) < ((j : ℤ) : ℚ) := by
          have h1 : (10 : ℚ) ^ (G + 15) = 10 ^ 15 * 10 ^ G := by rw [zpow_add₀ (by norm_num)]; norm_num; ring
          rw [← hsumv] at hbig
          rw [ha'j] at hsfl
          push_cast
          nlinarith
        have := Int.cast_lt.mp hjq
        omega
    · exact Or.inr hj15
  have hGe : G ≤ e := by
    rcases hjG with hGb | hj15
    · rw [hGb]; exact numberExponent_ge _ _ _ _ he
    · -- `a'` is a 16-digit amount at `G`, so rounding it down to 16 digits keeps `G`
      have ha'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ ha'
      unfold numberExponent at he
      have hnz : a'.operator_eq Number.zero = false := by
        rw [Bool.eq_false_iff]
        intro hz
        have := Number.mantissa_eq_zero_of_operator_eq_zero hz
        rw [Number.toRat_eq_zero_of_mantissa_zero a' this] at ha'j
        have : (0 : ℚ) < (j : ℚ) * 10 ^ G := by
          have : (0 : ℚ) < j := by exact_mod_cast (show 0 < j by omega)
          positivity
        linarith
      simp only [hnz, Bool.false_eq_true, if_false] at he
      cases hst' : STAmount.ofNumber .fractional a' .downward with
      | error err => rw [hst'] at he; simp [bind, Except.bind] at he
      | ok st' =>
        rw [hst'] at he
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he
        obtain ⟨-, -, -, hexp⟩ := STAmount.ofNumber_frac_of_representable a' .downward st' j G ha'n ha'0
          (Or.inr (Or.inr rfl)) ⟨hj15, hj⟩ (by omega) ha'j hst'
        rw [← he, hexp]
        exact le_max_right _ _
  exact lt_of_lt_of_le hlt (zpow_le_zpow_right₀ (by norm_num) hGe)

/-- An XRP or MPT credit lands exactly while AssetsAvailable plus the amount added stays below `2^63` units:
both are whole units, so their sum is a `Number` the asset stores. -/
lemma sumRoundAndSubtract_credit_exact_integral (A c : Number) (b : Int) (nt : NumericType) (st : STAmount)
    (cr aa a' : Number) (hint : nt.isIntegral = true) (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hArep : STAmount.isRounded nt A = false) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hb : -96 ≤ b ∧ b ≤ 80) (hfit : A.toRat + c.toRat < 2 ^ 63)
    (h : sumRoundAndSubtract A c b nt .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType nt aa .to_nearest = .ok a') :
    a'.toRat = A.toRat + cr.toRat := by
  obtain ⟨hstle, hcrx⟩ := sumRoundAndSubtract_downward_le A c b nt st hA hA0 hc hc0 hb h
  obtain ⟨hcrv, hcrn⟩ := hcrx cr hcr
  unfold sumRoundAndSubtract at h
  rw [if_pos hint] at h
  obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl : x = st := Except.ok.inj h

  have hneg := Number.negative_false_of_nonneg c hc hc0
  obtain ⟨iv, -, hiv⟩ := STAmount.ofNumber_integral_toRat nt c _ x hint hneg hx
  have hst0 := STAmount.ofNumber_nonneg nt c _ x hc hneg hx
  obtain ⟨kA, hkA⟩ : ∃ kA : ℕ, A.toRat = kA := by
    rcases (STAmount.isRounded_eq_false_iff _ A hA hA0).mp hArep with h0 | hr
    · exact ⟨0, by rw [h0]; simp⟩
    · cases nt with
      | integral mv mo ms msh => obtain ⟨-, k, -, -, hk⟩ := hr; exact ⟨k, hk⟩
      | fractional => exact absurd hint (by decide)
  have hiv0 : 0 ≤ iv.toInt := by
    have : (0 : ℚ) ≤ iv.toInt := by rw [← hiv]; exact hst0
    exact_mod_cast this

  -- the sum is a `Number` below `2^63`, so the asset stores it
  have hsumv : A.toRat + cr.toRat = ((kA + iv.toInt : ℤ) : ℚ) := by rw [hcrv, hiv, hkA]; push_cast; ring
  have hlt : kA + iv.toInt < 2 ^ 63 := by
    have : ((kA + iv.toInt : ℤ) : ℚ) < 2 ^ 63 := by rw [← hsumv, hcrv]; linarith
    exact_mod_cast this
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_of_int (kA + iv.toInt) (by omega)
  have haav := Number.operator_add_exact_of_fits hA hcrn haa ⟨w, hw, by rw [hwv, hsumv]⟩
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ hA hcrn haa
  have haa0 : 0 ≤ aa.toRat := by rw [haav, hsumv]; exact_mod_cast (show (0 : ℤ) ≤ kA + iv.toInt by omega)
  have hden : aa.toRat.den = 1 := by rw [haav, hsumv]; exact Rat.den_intCast _
  have hrep := STAmount.isRounded_eq_false_of_integral_round nt aa a' hint haan haa0 hden ha'
  rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep ha', haav]

/-- A default credits its cover to AssetsAvailable exactly. AssetsAvailable is stored whole base units, the principal
at most `10^16` of them, and on XRP or MPT AssetsAvailable plus the principal or the cover is below `2^63` units. -/
lemma Loan.manageDefault_cash_exact (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) (hnt : loan.broker.numericType = v.numericType)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (haa : ∃ a : ℕ, v.assetsAvailable.toRat = a * 10 ^ v.baseExponent)
    (hpo : loan.principalOutstanding.toRat ≤ 10 ^ 16 * 10 ^ v.baseExponent)
    (hfit : v.numericType.isIntegral = true →
      v.assetsAvailable.toRat + loan.principalOutstanding.toRat < 2 ^ 63 ∨
        v.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountToPool.toRat := by
  obtain ⟨_, _, _, raw, _, -, hdc, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨mc, liq, c, st, hmc, hliq, hc, hsr, hcr⟩ := Loan.defaultCover_parts loan v _ hdc
  obtain ⟨aa', _, _, _, _, hs, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have haa' : r.pool'.assetsAvailable = aa' := by
    rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl, hpool, hraw]
  rw [haa']
  obtain ⟨aa, h1, h2⟩ := hs.cash

  have hb := loan.broker.exact
  have hpo0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨hmcn, hmc0⟩ := tenthBipsOfValue_upward_facts _ _ _ loan.broker.wf.debtTotal_norm hb.debtTotal_nonneg hmc
  obtain ⟨hliqn, hliq0⟩ := tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq
  obtain ⟨hm1, hm1n⟩ := Number.min_toRat _ _ hliqn loan.wf.principalOutstanding_norm
  obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ _ hm1n loan.broker.wf.coverAvailable_norm
  have hcap0 : 0 ≤ (Number.min (Number.min liq loan.principalOutstanding) loan.broker.coverAvailable).toRat := by
    rw [hm2, hm1]; exact le_min (le_min hliq0 hpo0) hb.coverAvailable_nonneg
  obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n hcap0 hc
  rw [hm2, hm1] at hcle
  have hcpo : c.toRat ≤ loan.principalOutstanding.toRat := hcle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcca : c.toRat ≤ loan.broker.coverAvailable.toRat := hcle.trans (min_le_right _ _)
  rw [hnt] at hsr
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  cases hntv : v.numericType with
  | fractional =>
    rw [hntv] at hsr h2 hst
    exact sumRoundAndSubtract_credit_exact _ _ _ _ _ _ _ v.wf.assetsAvailable_norm hA0 hst haa hcn hc0
      (by linarith) ⟨hblo, hbhi⟩ hsr hcr h1 h2
  | integral mv mo ms msh =>
    have hint : v.numericType.isIntegral = true := by rw [hntv]; rfl
    have hfit' : v.assetsAvailable.toRat + c.toRat < 2 ^ 63 := by
      rcases hfit hint with h | h <;> linarith
    rw [hntv] at hsr h2 hst hint
    exact sumRoundAndSubtract_credit_exact_integral _ _ _ _ _ _ _ _ hint v.wf.assetsAvailable_norm hA0 hst hcn hc0
      (Vault.baseExponent_range v) hfit' hsr hcr h1 h2

variable (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan) (hat : l.LoanAt i loan)
include hr hat

/-- On a reachable ledger a default credits its cover to AssetsAvailable exactly, coarsened vault or not. An
MPT vault also needs AssetsAvailable plus the broker's cover below `2^63` units. -/
lemma LendingLedger.Reachable.default_cash_exact (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    r.pool'.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + r.amountToPool.toRat := by
  obtain ⟨p, hp, hpv, -⟩ := hr.loanAt_principal hat
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hpo : loan.principalOutstanding.toRat ≤ 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hp10.le
  refine Loan.manageDefault_cash_exact loan l.vault r hok (hr.loanAt_scale hat).2 hr.availableStored
    (hr.assetsAvailable_units hr.holdsAsset) hpo (fun hint => ?_)
  obtain ⟨-, -, hbint⟩ := Vault.baseExponent_bounds l.vault
  rcases hr.holdsAsset with hf | hn | hi
  · rw [hf] at hint; exact absurd hint (by decide)
  · -- XRP: AssetsAvailable is at most `10^17` drops and the principal at most `10^16`
    left
    have hA := hr.availableStored
    rw [hn] at hA
    have hb0 := hbint hint
    rw [hb0, zpow_zero, mul_one] at hpo
    rcases (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm
      l.vault.exact.assetsAvailable_nonneg).mp hA with h0 | ⟨-, k, hk, -, hkv⟩
    · rw [h0]; linarith
    · have hk' : (k : ℚ) ≤ 10 ^ 17 := by
        have : k ≤ 10 ^ 17 := by simpa [NumericType.native] using hk
        exact_mod_cast this
      rw [hkv]; linarith
  · exact Or.inr (hsupply hi)

/-- The default step of the vault part of `Lending.default_updates`, read on the default's result. -/
lemma LendingLedger.manageDefault_vault_exact_proof (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    r.pool'.toExact.assetsTotal =
        l.vault.toExact.assetsTotal - (loan.principalOutstanding.toRat - r.amountToPool.toRat) ∧
      r.pool'.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + r.amountToPool.toRat := by
  have haa' := hr.default_cash_exact l i loan hat r hok hsupply
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan l.vault r hok
  have hd := Number.operator_sub_exact_of_fits l.vault.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm
    hs.deployed (hr.deployed_fits hat)
  refine ⟨?_, haa'⟩
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat -
      (loan.principalOutstanding.toRat - r.amountToPool.toRat)
  rw [haa', hd]
  ring

/-- Proof body of the impaired share value part of `Lending.default_updates`. -/
lemma LendingLedger.default_impaired_share_value_exact_proof (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    r.pool'.shareValue - l.vault.shareValue =
      (l.vault.lossUnrealized.toRat - r.pool'.lossUnrealized.toRat -
        (loan.principalOutstanding.toRat - r.amountToPool.toRat)) / l.vault.toExact.sharesTotal := by
  obtain ⟨hat', -⟩ := LendingLedger.manageDefault_vault_exact_proof l hr i loan hat r hok hsupply
  have hst := Loan.manageDefault_sharesTotal loan l.vault r hok
  have hS : r.pool'.toExact.sharesTotal = l.vault.toExact.sharesTotal := by
    show r.pool'.sharesTotal.toRat.num.toNat = l.vault.sharesTotal.toRat.num.toNat
    rw [hst]
  show (r.pool'.toExact.assetsTotal - r.pool'.toExact.lossUnrealized) / r.pool'.toExact.sharesTotal -
    (l.vault.toExact.assetsTotal - l.vault.toExact.lossUnrealized) / l.vault.toExact.sharesTotal = _
  rw [hS, hat']
  show (_ - r.pool'.lossUnrealized.toRat) / _ - (_ - l.vault.lossUnrealized.toRat) / _ = _
  ring

/-- Proof body of the share value part of `Lending.default_updates`. -/
lemma LendingLedger.default_share_value_exact_proof (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r)) (himp : loan.isImpaired = false)
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    l.vault.shareValue - r.pool'.shareValue =
      (loan.principalOutstanding.toRat - r.amountToPool.toRat) / l.vault.toExact.sharesTotal := by
  have h := LendingLedger.default_impaired_share_value_exact_proof l hr i loan hat r hok hsupply
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan l.vault r hok
  have hl := hs.loss
  simp only [Loan.defaultChange, himp, Bool.false_eq_true, ↓reduceIte] at hl
  rw [Number.eq_of_add_zero hl, sub_self, zero_sub, neg_div] at h
  linarith

end XRPL.Model.Lending
