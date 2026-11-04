import XRPL.Properties.Protocol.Common.TenthBips
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Protocol.Number.Div.Common.Decompose
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # The early-exit fee and the payout after it

A withdrawal charges the early-exit fee with `tenthBipsOfValue`, rounding up twice, and rounds
the payout left after it down into the asset. The fee exceeds the exact share of the priced amount
by at most two upward `Number` steps, and a downward IOU conversion floors onto the 16-digit grid. -/

namespace XRPL.Model.Protocol

/-- The early-exit fee is at least the exact share of the value, and at most `3·10⁻¹⁸` of it
above. The rate multiplies the value, then unity divides it, each rounding up. -/
lemma tenthBipsOfValue_upward_bounds (d : Number) (rate : TenthBips32) (fee : Number)
    (hd : d.isNormalized) (h0 : 0 ≤ d.toRat) (hsmall : d.toRat = 0 ∨ (10 : ℚ) ^ (-1000 : ℤ) ≤ d.toRat)
    (hok : tenthBipsOfValue d rate .upward = .ok fee) :
    d.toRat * rate.toNat / 100000 ≤ fee.toRat ∧
      fee.toRat ≤ d.toRat * rate.toNat / 100000 * (1 + 3 / 10 ^ 18) := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu : ((kTenthBipsPerUnity.toNat : ℕ) : ℚ) = 100000 := by rfl
  rw [hu] at huv
  have hun0 : ¬ kTenthBipsPerUnity.toNumber.operator_eq Number.zero = true := by
    intro h
    have := (operator_eq_iff _ _ hun Number.zero_isNormalized).mp h
    rw [huv, Number.toRat_zero] at this
    norm_num at this
  unfold tenthBipsOfValue at hok
  dsimp only at hok
  obtain ⟨p, hp, hok⟩ := bind_ok_peel _ _ _ hok
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hp
  have hr0 : (0 : ℚ) ≤ rate.toNat := by positivity
  by_cases htz : d.toRat * rate.toNat = 0
  · -- a zero product gives a zero fee
    have hpm : p.mantissa_ = 0 := by
      by_contra hpm
      obtain ⟨hdm, hrm⟩ := operator_mul_operands_ne_zero hd hrn hp hpm
      have h1 := Number.toRat_ne_zero_of_mantissa_ne_zero d hdm
      have h2 := Number.toRat_ne_zero_of_mantissa_ne_zero _ hrm
      rw [hrv] at h2
      exact (mul_ne_zero h1 h2) htz
    have hfm : fee.mantissa_ = 0 := by
      by_contra hfm
      exact operator_div_numerator_ne_zero_sz _ _ _ _ hun0 hok hfm hpm
    rw [Number.toRat_eq_zero_of_mantissa_zero fee hfm, htz]
    norm_num
  -- a positive product stays clear of the `Number` underflow, so both steps round up
  have hdpos : 0 < d.toRat := lt_of_le_of_ne h0 (fun h => htz (by rw [← h]; ring))
  have hrpos : (0 : ℚ) < rate.toNat := lt_of_le_of_ne hr0 (fun h => htz (by rw [← h]; ring))
  have hd1000 : (10 : ℚ) ^ (-1000 : ℤ) ≤ d.toRat := hsmall.resolve_left (ne_of_gt hdpos)
  have hr1 : (1 : ℚ) ≤ rate.toNat := by
    have : 0 < rate.toNat := by exact_mod_cast hrpos
    exact_mod_cast this
  have htruth : (10 : ℚ) ^ (-1000 : ℤ) ≤ d.toRat * rate.toNat := by nlinarith
  have htiny : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) < (10 : ℚ) ^ (-1005 : ℤ) := by
    unfold minExponent
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  have h1005 : (10 : ℚ) ^ (-1005 : ℤ) < 10 ^ (-1000 : ℤ) := zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  have hdm : d.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero d h] at hdpos; exact lt_irrefl _ hdpos
  have hrm : rate.toNumber.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hrv; rw [← hrv] at hrpos; exact lt_irrefl _ hrpos
  have hpm : p.mantissa_ ≠ 0 := by
    intro hpm
    have h := operator_mul_underflow_truth_small d rate.toNumber p .upward hd hrn hdm hrm hp hpm
    rw [hrv, abs_of_pos (mul_pos hdpos hrpos)] at h
    linarith
  obtain ⟨hplo, hphi⟩ := operator_mul_rounds_upward d rate.toNumber p hd hrn hp hpm
  change d.toRat * rate.toNumber.toRat ≤ p.toRat at hplo
  change p.toRat - d.toRat * rate.toNumber.toRat ≤ |d.toRat * rate.toNumber.toRat| * _ at hphi
  rw [hrv] at hplo hphi
  rw [abs_of_pos (mul_pos hdpos hrpos)] at hphi
  have hum : kTenthBipsPerUnity.toNumber.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at huv; norm_num at huv
  have hfm : fee.mantissa_ ≠ 0 := by
    intro hfm
    have h := operator_div_underflow_truth_small p _ fee .upward hpn hun hpm hum hok hfm
    rw [huv, abs_of_pos (div_pos (lt_of_lt_of_le (mul_pos hdpos hrpos) hplo) (by norm_num))] at h
    have : (10 : ℚ) ^ (-1005 : ℤ) ≤ p.toRat / 100000 := by
      rw [le_div_iff₀ (by norm_num)]
      have h5 : (10 : ℚ) ^ (-1005 : ℤ) * 100000 = 10 ^ (-1000 : ℤ) := by
        rw [show (100000 : ℚ) = 10 ^ (5 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]; norm_num
      linarith
    linarith
  obtain ⟨hflo, hfhi⟩ := operator_div_rounds_upward p _ fee hpn hun hok hfm
  change p.toRat / kTenthBipsPerUnity.toNumber.toRat ≤ fee.toRat at hflo
  change fee.toRat - p.toRat / kTenthBipsPerUnity.toNumber.toRat ≤
    |p.toRat / kTenthBipsPerUnity.toNumber.toRat| * _ at hfhi
  rw [huv] at hflo hfhi
  have hp0 : 0 < p.toRat := by linarith [mul_pos hdpos hrpos]
  rw [abs_of_pos (div_pos hp0 (by norm_num))] at hfhi
  set T := d.toRat * (rate.toNat : ℚ) with hT
  have hT0 : 0 < T := mul_pos hdpos hrpos
  refine ⟨by rw [div_le_iff₀ (by norm_num)] at hflo ⊢; nlinarith, ?_⟩
  -- `(1 + 10/(2⁶³+2))·(1 + 11/(2⁶³-18))` is below `1 + 3·10⁻¹⁸`
  have hp' : p.toRat ≤ T * (1 + 10 / (2 ^ 63 + 2)) := by nlinarith
  have hf' : fee.toRat ≤ p.toRat / 100000 * (1 + 11 / (2 ^ 63 - 18)) := by nlinarith
  have hk : (1 + 10 / (2 ^ 63 + 2 : ℚ)) * (1 + 11 / (2 ^ 63 - 18)) ≤ 1 + 3 / 10 ^ 18 := by norm_num
  calc fee.toRat ≤ p.toRat / 100000 * (1 + 11 / (2 ^ 63 - 18)) := hf'
    _ ≤ T * (1 + 10 / (2 ^ 63 + 2)) / 100000 * (1 + 11 / (2 ^ 63 - 18)) := by gcongr
    _ = T / 100000 * ((1 + 10 / (2 ^ 63 + 2 : ℚ)) * (1 + 11 / (2 ^ 63 - 18))) := by ring
    _ ≤ T / 100000 * (1 + 3 / 10 ^ 18) := by gcongr

/-- `⌊M / 1000⌋` is the quotient. -/
private lemma floor_div_thousand (M : ℕ) : ⌊(M : ℚ) / 1000⌋ = ((M / 1000 : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff, Int.cast_natCast]
  have hq : (M : ℚ) = 1000 * ((M / 1000 : ℕ) : ℚ) + ((M % 1000 : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod M 1000).symm
  have hr1 : ((M % 1000 : ℕ) : ℚ) < 1000 := by exact_mod_cast Nat.mod_lt M (by norm_num)
  have hr0 : (0 : ℚ) ≤ ((M % 1000 : ℕ) : ℚ) := by positivity
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- A downward or towards-zero fractional `ofNumber` of a nonnegative source is the floor of the source on the grid
`10 ^ (exponent + 3)`, three digits above its 19-digit mantissa. -/
lemma STAmount.ofNumber_iou_floor (n : Number) (result : STAmount) (mode : rounding_mode)
    (hmode : mode = .downward ∨ mode = .towards_zero) (hn : n.isNormalized)
    (hn0 : n.mantissa_ ≠ 0) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) (hresult : result.mValue ≠ 0) :
    result.toRat = (⌊n.toRat / 10 ^ (n.exponent_ + 3)⌋ : ℚ) * 10 ^ (n.exponent_ + 3) := by
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  have hneg := Number.negative_false_of_nonneg n hn h0
  have hexp := STAmount.ofNumber_iou_success_exp_range n mode result hb.1 hb.2 hemin hok hresult
  obtain ⟨mant, exp, hnr, hval, -⟩ := STAmount.ofNumber_iou_snap_pos .fractional n mode result
    rfl hneg hb.1 hb.2 hemin hexp hok hresult
  obtain ⟨hfloor, -⟩ := normalizeToRange_16_floor_pos n mant exp mode hmode hneg hb.1 hb.2
    (by omega) hexp hnr
  have hnv : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := by
    rw [← abs_of_nonneg h0]
    exact abs_toRat_eq n
  have hdiv : n.toRat / 10 ^ (n.exponent_ + 3) = (n.mantissa_.toNat : ℚ) / 1000 := by
    rw [hnv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    field_simp
    norm_num
  rw [hval, hfloor, hdiv, floor_div_thousand]
  norm_cast

/-- A downward fractional `ofNumber` rounds down onto the 16-digit grid of its source, at scale
`10 ^ (exponent + 3)`. -/
lemma STAmount.ofNumber_iou_downward_floor (n : Number) (result : STAmount) (hn : n.isNormalized)
    (hn0 : n.mantissa_ ≠ 0) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n .downward = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsToRepresentableAt result n.toRat (n.exponent_ + 3) .downward :=
  STAmount.ofNumber_iou_floor n result .downward (Or.inl rfl) hn hn0 h0 hok hresult

/-- The `Number` of a canonical IOU amount sits three digits below it: its 19-digit mantissa
carries three more digits than the amount's 16. -/
private lemma STAmount.IOUCanonical.number_exponent (P : STAmount) (hP : P.IOUCanonical) (hpos : 0 < P.toRat)
    (n : Number) (hn : n.isNormalized) (hv : n.toRat = P.toRat) : n.exponent_ + 3 = P.exponent := by
  obtain ⟨hP1, hP2⟩ := STAmount.IOUCanonical.toRat_bounds P hP hpos
  have hpp : (0 : ℚ) < 10 ^ P.exponent := zpow_pos (by norm_num) _
  have hnm : n.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n h0] at hv; linarith
  obtain ⟨hm_lo, hm_hi⟩ := hn.mantissaBounds_nat hnm
  have hlo : (10 : ℚ) ^ 18 ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_lo
  have hhi : (n.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hm_hi
  have hnv : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ :=
    Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn (by rw [hv]; exact hpos.le))
  have hep : (0 : ℚ) < 10 ^ n.exponent_ := zpow_pos (by norm_num) _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- too small an exponent puts the `Number` below the amount
    have h1 : (10 : ℚ) ^ (n.exponent_ + 19) ≤ 10 ^ (P.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (n.exponent_ + 19) = 10 ^ 19 * 10 ^ n.exponent_ := by
      rw [zpow_add₀ (by norm_num)]; norm_num; ring
    nlinarith
  · -- too large an exponent puts it above
    have h1 : (10 : ℚ) ^ (P.exponent + 16) ≤ 10 ^ (n.exponent_ + 18) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (n.exponent_ + 18) = 10 ^ 18 * 10 ^ n.exponent_ := by
      rw [zpow_add₀ (by norm_num)]; norm_num; ring
    nlinarith

/-- A downward conversion of a canonical amount's own value returns that amount. -/
lemma STAmount.ofNumber_downward_self (nt : NumericType) (P : STAmount) (hP : P.ExactCanonical)
    (hPt : P.mNumericType = nt) (hpos : 0 < P.toRat) (n : Number) (hn : n.isNormalized)
    (hv : n.toRat = P.toRat) (Y : STAmount) (hok : STAmount.ofNumber nt n .downward = .ok Y)
    (hY : Y.mValue ≠ 0) : Y = P := by
  have hYv : Y.toRat = P.toRat := by
    rcases hP with hiou | ⟨hic, -⟩
    · -- the floor of the amount on its own grid is the amount
      have hfr : nt = .fractional := hPt ▸ hiou.is_fractional
      subst hfr
      have hfl : Y.toRat = (⌊n.toRat / 10 ^ (n.exponent_ + 3)⌋ : ℚ) * 10 ^ (n.exponent_ + 3) :=
        STAmount.ofNumber_iou_downward_floor n Y hn
          (fun h0 => by rw [Number.toRat_eq_zero_of_mantissa_zero n h0] at hv; linarith) (by rw [hv]; exact hpos.le)
          hok hY
      rw [hfl, STAmount.IOUCanonical.number_exponent P hiou hpos n hn hv, hv]
      have hneg := STAmount.mIsNegative_false_of_pos P hpos
      have hPv : P.toRat = ((P.mValue.toNat : ℤ) : ℚ) * 10 ^ P.exponent := by
        rw [STAmount.toRat_of_nonneg P hneg]; push_cast; rfl
      have hpp : (10 : ℚ) ^ P.exponent ≠ 0 := (zpow_pos (by norm_num) _).ne'
      rw [hPv, mul_div_cancel_right₀ _ hpp, Int.floor_intCast]
    · have hint : nt.isIntegral = true := by rw [← hPt]; exact hic.is_integral
      rw [STAmount.ofNumber_integral_exact nt n .downward Y hint hn (by rw [hv]; exact hic.den_eq_one) hok, hv]
  have hYc := STAmount.ofNumber_exactCanonical nt n .downward Y hn (by rw [hv]; exact hpos.le) hok hY
  exact STAmount.eq_of_exactCanonical Y P hYc hP (by rw [STAmount.ofNumber_mNumericType _ _ _ _ hok, hPt]) hY hYv

end XRPL.Model.Protocol
