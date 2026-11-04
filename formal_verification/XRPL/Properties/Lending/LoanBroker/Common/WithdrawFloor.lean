import XRPL.Properties.Lending.LoanBroker.Common.CoverExact

/-! # A withdrawal debits the amount floored to whole base units

On a broker in the Open zone a withdrawal that passes its check debits the amount floored to whole base units: the
difference with the cover stays below `10^(16 + b)`, so the clamp lands on the base grid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A post-sum exponent above the floor marks a large sum of either sign: its size reaches
`10^(e + 15)` less one step of `10^e`. -/
private lemma numberExponent_frac_abs_lower (n : Number) (b e : Int) (hn : n.isNormalized) (hb : -100 ≤ b)
    (hok : numberExponent n b .fractional = .ok e) (hgt : b < e) :
    (10 : ℚ) ^ (e + 15) - 10 ^ e ≤ |n.toRat| := by
  unfold numberExponent at hok
  by_cases hz : n.operator_eq Number.zero = true
  · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at hok
    omega
  simp only [hz, Bool.false_eq_true, if_false] at hok
  have hnz : n.mantissa_ ≠ 0 := by
    intro hm
    rw [Number.eq_zero_of_mantissa_zero n hn hm] at hz
    exact hz (by decide)
  cases ha : STAmount.ofNumber .fractional n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok r =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hmax : max b r.exponent = e := hok
    have hre : r.exponent = e := by rcases max_cases b r.exponent with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    -- a zero conversion has exponent -100, which cannot sit above the floor
    have hr0 : r.mValue ≠ 0 := by
      intro h0
      have := (STAmount.ofNumber_frac_exp_range .fractional n .downward r rfl ha).1 h0
      have hge := le_max_left b r.exponent
      omega
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hnz
    have hemin := Number.exponent_ge_min n hn hnz
    obtain ⟨hrc, hexp⟩ := STAmount.ofNumber_iou_ok_facts n .downward r hlo hhi hemin ha hr0
    obtain ⟨hulp, hle⟩ :=
      STAmount.ofNumber_iou_within_ulp .fractional n .downward r rfl hlo hhi hemin hexp ha hr0
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    -- the 16-digit conversion has at least 16 digits at its exponent
    have hr15 : (10 : ℚ) ^ (e + 15) ≤ |r.toRat| := by
      have hm : (10 : ℚ) ^ 15 ≤ (r.mValue.toNat : ℚ) := by exact_mod_cast hrc.mant_lo
      rw [STAmount.abs_toRat, show r.mOffset = e from hre, zpow_add₀ (by norm_num), mul_comm, zpow_ofNat]
      exact mul_le_mul_of_nonneg_right hm hp.le
    -- and sits within one step `10^e` of the sum
    have hstep : (10 : ℚ) ^ (n.exponent_ + 3) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have := abs_sub_abs_le_abs_sub r.toRat n.toRat
    linarith

/-- A withdrawal in the Open zone debits the amount floored to whole base units. -/
lemma LoanBroker.coverWithdraw_floor (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    res.amount'.toRat = (⌊amount.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨-, -, hbint⟩ := v.baseExponent_bounds
  obtain ⟨hblo, hbhi⟩ := v.baseExponent_range
  obtain ⟨hcl, ⟨j, hj⟩, ha0, -, haA, -⟩ := LoanBroker.coverWithdraw_exact lb v amount res hz hc hpos hcan hok
  by_cases hint : amount.integral = true
  · -- an integral amount passes the clamp whole, on a vault with base exponent zero
    have hb0 : v.baseExponent = 0 := hbint (by rw [hnt, ← hat]; exact hint)
    rw [clampToSumExponent_integral _ _ _ ((STAmount.operator_neg_integral amount).trans hint), Except.ok.injEq,
      STAmount.abs_operator_neg_of_pos amount hpos] at hcl
    rw [← hcl] at hj ⊢
    rw [hj, hb0]
    simp
  -- a fractional amount is floored onto the grid of the difference with the cover
  have hfr : amount.integral = false := by simpa using hint
  have hiou : amount.IOUCanonical := hc.2 hfr
  have hnz : res.amount'.mValue ≠ 0 := fun h0 => ha0.ne' ((STAmount.toRat_eq_zero_iff _).mpr h0)
  obtain ⟨aN, e, haN, hps, hbe, hv⟩ := clampToSumExponent_debit_floor lb.coverAvailable amount res.amount'
    v.baseExponent (Or.inl hc) hfr hpos.le v.baseExponent_range hnz hcl
  suffices he : e = v.baseExponent by rw [hv, he]
  -- that grid is the base grid: a coarser one needs a difference of at least 16 digits
  by_contra hne
  have hgt : v.baseExponent < e := lt_of_le_of_ne hbe (Ne.symm hne)
  rw [show amount.operator_neg.numericType = .fractional from hiou.operator_neg.is_fractional] at hps
  obtain ⟨-, he96, he80⟩ := postSumExponent_range _ _ _ _ _ hblo hbhi hps
  obtain ⟨s, hs, hse⟩ := postSumExponent_reduces _ _ _ _ _ hps
  obtain ⟨haNv, haNn⟩ :=
    STAmount.CanonicalOrZero.toNumber_exact (STAmount.CanonicalOrZero.operator_neg (Or.inl hc)) aN haN
  rw [STAmount.operator_neg_toRat] at haNv
  have hAn := lb.wf.coverAvailable_norm
  have hR := operator_add_rounded_to_nearest _ _ _ hAn haNn hs
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAn haNn hs
  have hbig := numberExponent_frac_abs_lower s v.baseExponent e hsn (by omega) hse hgt
  have hpe : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have h15 : (10 : ℚ) ^ (e + 15) = 10 ^ 15 * 10 ^ e := by
    rw [zpow_add₀ (by norm_num), mul_comm, zpow_ofNat]
  have hA : lb.coverAvailable.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := hz.coverLimit
  have haA' : res.amount'.toRat ≤ lb.coverAvailable.toRat := haA
  rcases le_or_gt 0 s.toRat with hs0 | hs0
  · -- a sum that is not negative stays at most the cover, below `10^(e + 15)`
    have hsA : s.toRat ≤ lb.coverAvailable.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized s _ hR _ hAn (by rw [haNv]; linarith)
    have hbe' : (10 : ℚ) ^ v.baseExponent * 10 ≤ 10 ^ e := by
      rw [← zpow_add_one₀ (by norm_num)]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [abs_of_nonneg hs0] at hbig
    linarith
  · -- a negative sum stays within one step `10^e` of zero, as the debit leaves less than a step
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) e (by constructor <;> norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hlt : amount.toRat < res.amount'.toRat + 10 ^ e := by
      have h := Int.lt_floor_add_one (amount.toRat / 10 ^ e)
      rw [div_lt_iff₀ hpe] at h
      rw [hv]; linarith
    have hws : w.toRat ≤ s.toRat := Number.RoundsToRepresentable.ge_of_le hR (Or.inl rfl) w hw
      (by rw [hwv, haNv]; push_cast; linarith)
    rw [abs_of_neg hs0] at hbig
    rw [hwv] at hws
    push_cast at hws
    linarith

end XRPL.Model.Lending
