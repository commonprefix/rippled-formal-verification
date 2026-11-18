import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetChecks
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayRoom

/-! # The re-amortization of an overpayment computes its loan values

An overpayment re-amortizes the loan for a reduced principal, which need not be an amount of the asset and can be
zero. The values of the re-amortized loan compute as those of a LoanSet do, and the new PeriodicPayment is at most
the old one, because it comes from a principal at most the theoretical one through the same payment factor. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_ge rn_nonneg Number.ofInt64_one_toRat from XRPL.Properties.Lending.Loan.Common.SetLawful
open private computePaymentFactor_ge Number.eq_zero_of_toRat Number.div_zero_error
  from XRPL.Properties.Lending.Loan.Common.PaymentFactor
open private LoanValueSteps mgmt_toNat_le STAmount.roundsInRange_of_le_max STAmount.le_max_of_roundsInRange
  STAmount.roundToNumericType_integral_of_inRange STAmount.ofNumber_fractional_exponent_le
  loanPrincipalFromPeriodicPayment_normalized_of_ok
  from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetValue
open private STAmount.roundToNumericType_of_inRange STAmount.roundToNumericType_upward_unit
  from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetChecks

local notation "ε" => Number.nearestError

/-- A to-nearest sum of two numbers within their bounds computes, within the sum of the bounds plus one. -/
lemma Number.reamAdd (x y : Number) (bx bz : ℚ) (hx : x.isNormalized) (hy : y.isNormalized)
    (hbx : |x.toRat| ≤ bx) (hby : |y.toRat| ≤ bz) (hcap : bx + bz ≤ 10 ^ 18) :
    ∃ r, x.operator_add y .to_nearest = .ok r ∧ r.isNormalized ∧ |r.toRat| ≤ bx + bz + 1 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨r, hr⟩ := Number.operator_add_ok_of_abs x y .to_nearest hx hy
    (by linarith [abs_nonneg y.toRat, show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    (by linarith [abs_nonneg x.toRat, show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
  refine ⟨r, hr, Number.operator_add_isNormalized_to_nearest_sz _ _ _ hx hy hr, ?_⟩
  have h1 := (Number.add_near _ _ _ hx hy hr).abs_le
  have h2 := abs_add_le x.toRat y.toRat
  have h3 : |x.toRat + y.toRat| * ε ≤ 1 := by
    calc |x.toRat + y.toRat| * ε ≤ 10 ^ 18 * (1 / 10 ^ 18) := by gcongr; linarith
      _ = 1 := by norm_num
  linarith

/-- A to-nearest difference of two numbers within their bounds computes, within the sum of the bounds plus one. -/
lemma Number.reamSub (x y : Number) (bx bz : ℚ) (hx : x.isNormalized) (hy : y.isNormalized)
    (hbx : |x.toRat| ≤ bx) (hby : |y.toRat| ≤ bz) (hcap : bx + bz ≤ 10 ^ 18) :
    ∃ r, x.operator_sub y .to_nearest = .ok r ∧ r.isNormalized ∧ |r.toRat| ≤ bx + bz + 1 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨r, hr⟩ := Number.operator_sub_ok_of_abs x y .to_nearest hx hy
    (by linarith [abs_nonneg y.toRat, show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    (by linarith [abs_nonneg x.toRat, show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
  refine ⟨r, hr, Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hx hy hr, ?_⟩
  have h1 := (Number.sub_near _ _ _ hx hy hr).abs_le
  have h2 := abs_sub x.toRat y.toRat
  have h3 : |x.toRat - y.toRat| * ε ≤ 1 := by
    calc |x.toRat - y.toRat| * ε ≤ 10 ^ 18 * (1 / 10 ^ 18) := by gcongr; linarith
      _ = 1 := by norm_num
  linarith

/-- A principal at most the theoretical one of a PeriodicPayment gives a PeriodicPayment at most that one, times two
roundings: both go through the same payment factor. -/
lemma loanPeriodicPayment_le_of_principal_le (pp rate rp : Number) (n : UInt32) (tpo pp' : Number)
    (hpp : pp.isNormalized) (hpp0 : 0 ≤ pp.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hrp : rp.isNormalized) (hrp0 : 0 ≤ rp.toRat)
    (htpo : loanPrincipalFromPeriodicPayment pp rate n = .ok tpo) (hle : rp.toRat ≤ tpo.toRat)
    (h : loanPeriodicPayment rp rate n = .ok pp') : pp'.toRat ≤ pp.toRat * (1 + ε) ^ 2 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have h1e : 0 < 1 - ε := by linarith
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hzero : pp' = Number.zero → pp'.toRat ≤ pp.toRat * (1 + ε) ^ 2 := fun hz => by
    rw [hz, Number.toRat_zero]; positivity
  unfold loanPeriodicPayment at h
  by_cases hc : (rp.operator_eq Number.zero || n == 0) = true
  · rw [if_pos hc] at h
    have h' : (Except.ok Number.zero : Except Error Number) = .ok pp' := h
    exact hzero (Except.ok.inj h').symm
  rw [if_neg hc] at h
  dsimp only at h
  have hn0 : ¬ (n == 0) = true := fun hn => hc (by simp [hn])
  have hn1 : (1 : ℚ) ≤ n.toNat := by
    have hne : n ≠ 0 := by simpa using hn0
    have : n.toNat ≠ 0 := fun h0 => hne (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hNpos : (0 : ℚ) < n.toNat := by linarith
  unfold loanPrincipalFromPeriodicPayment at htpo
  dsimp only at htpo
  split at htpo
  · rename_i hpr0
    exact absurd hpr0 hn0
  obtain ⟨_, -, htpo⟩ := bind_ok_peel _ _ _ htpo
  by_cases hz : rate.operator_eq Number.zero = true
  · -- no interest: the payment is the principal over `n`, the principal `n` payments
    rw [if_pos hz] at h htpo
    have h1 := (Number.div_near _ _ _ hrp hN h).le (by rw [hNv]; positivity)
    have h2 := (Number.mul_near _ _ _ hpp hN htpo).le (by rw [hNv]; positivity)
    rw [hNv] at h1 h2
    calc pp'.toRat ≤ rp.toRat / n.toNat * (1 + ε) := h1
      _ ≤ pp.toRat * n.toNat * (1 + ε) / n.toNat * (1 + ε) := by gcongr; linarith
      _ = pp.toRat * (1 + ε) ^ 2 := by field_simp
  · rw [if_neg hz] at h htpo
    have hr : 0 < rate.toRat := by
      rcases lt_or_eq_of_le hr0 with h' | h'
      · exact h'
      · exact absurd ((Number.operator_eq_iff rate Number.zero hrate Number.zero_isNormalized).mpr
          (by rw [Number.toRat_zero]; exact h'.symm)) hz
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨f', hf', htpo⟩ := bind_ok_peel _ _ _ htpo
    rw [hf] at hf'
    obtain rfl := Except.ok.inj hf'
    have hfN := computePaymentFactor_isNormalized rate _ n f hrate hN hf
    have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) htpo
    obtain ⟨hf1, -⟩ := computePaymentFactor_ge rate n f hrate hr hf hfne
    have hfpos : 0 < f.toRat := lt_of_lt_of_le (by positivity) hf1
    have h1 := (Number.mul_near _ _ _ hrp hfN h).le (mul_nonneg hrp0 hfpos.le)
    have h2 := (Number.div_near _ _ _ hpp hfN htpo).le (div_nonneg hpp0 hfpos.le)
    calc pp'.toRat ≤ rp.toRat * f.toRat * (1 + ε) := h1
      _ ≤ pp.toRat / f.toRat * (1 + ε) * f.toRat * (1 + ε) := by gcongr; linarith
      _ = pp.toRat * (1 + ε) ^ 2 := by field_simp

/-- XRP or an MPT: the rounded values compute for a principal of zero or more, as `loanValueSteps_integral`. -/
private lemma loanValueSteps_integral0 (nt : NumericType) (hnt : nt = NumericType.native ∨ nt = NumericType.int64)
    (amount principal : Number) (mode : rounding_mode) (mgmt : TenthBips16) (minScale : Int)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hscale : -10 ≤ minScale ∧ minScale ≤ 0)
    (hmgmt : mgmt.toNat ≤ 10000) (hamountN : amount.isNormalized) (hamount0 : 0 ≤ amount.toRat)
    (hamountM : amount.toRat ≤ nt.maxValue.toNat) (hp : principal.isNormalized) (hpos : 0 ≤ principal.toRat)
    (hstR : STAmount.RoundsInRange nt .to_nearest principal.toRat) :
    ∃ amountSt tvo rp ti mfo, LoanValueSteps nt amount principal mode mgmt minScale amountSt tvo rp ti mfo := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hM17n : 10 ^ 17 ≤ nt.maxValue.toNat := by rcases hnt with rfl | rfl <;> decide
  have hM17 : (10 : ℚ) ^ 17 ≤ nt.maxValue.toNat := by exact_mod_cast hM17n
  have hM63n : nt.maxValue.toNat ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
  have hM63 : (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hM63n
  have hmbn' : nt.mantissaBound = nt.maxValue.toNat + 1 := by rcases hnt with rfl | rfl <;> decide
  have hmb : (nt.mantissaBound : ℚ) = nt.maxValue.toNat + 1 := by rw [hmbn']; push_cast; ring
  have hmbn : nt.mantissaBound ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
  have hin := STAmount.roundsInRange_of_le_max nt hnt mode amount.toRat hamount0 hamountM

  -- the total value as an amount, at exponent zero
  obtain ⟨amountSt, hst⟩ :=
    (STAmount.ofNumber_ok_iff nt amount mode hamountN (Or.inr hnt) (Or.inl hamount0)).mpr hin
  have hoff := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint hst).1.offset_zero
  have hls : max minScale amountSt.exponent = 0 := by
    unfold STAmount.exponent; rw [hoff]; exact max_eq_right hscale.2

  -- the rounded total value and principal
  obtain ⟨tvo, htvo⟩ :=
    STAmount.roundToNumericType_integral_of_inRange nt hnt amount mode (some 0) hamountN hamount0 hin
  obtain ⟨rp, hrp⟩ :=
    STAmount.roundToNumericType_integral_of_inRange nt hnt principal .to_nearest (some 0) hp hpos hstR
  have htvoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hrpN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrp
  have htvo0 := STAmount.roundToNumericType_some_nonneg nt amount tvo mode 0 hamountN hamount0 hmode
    ⟨by norm_num, by norm_num⟩ htvo
  have hrp0 := STAmount.roundToNumericType_some_nonneg nt principal rp .to_nearest 0 hp hpos (Or.inl rfl)
    ⟨by norm_num, by norm_num⟩ hrp
  have htvolt := STAmount.roundToNumericType_int_lt_bound nt hint amount tvo mode (some 0) hamountN hamount0 htvo
  have hrplt := STAmount.roundToNumericType_int_lt_bound nt hint principal rp .to_nearest (some 0) hp hpos hrp
  obtain ⟨-, ⟨k, hk⟩, -, -⟩ :=
    STAmount.roundToNumericType_int_grid nt hint amount tvo mode (some 0) hamountN hamount0 hmode htvo
  have hk63 : k < 2 ^ 63 := by
    have : (k : ℚ) < nt.mantissaBound := by rw [← hk]; exact htvolt
    have : k < nt.mantissaBound := by exact_mod_cast this
    omega
  rw [hmb] at htvolt hrplt

  -- the interest
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs tvo rp .to_nearest htvoN hrpN
    (by rw [abs_of_nonneg htvo0]; linarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hrp0]; linarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 200 by norm_num])
  have htiN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ htvoN hrpN hti
  have htiabs : |ti.toRat| ≤ (nt.maxValue.toNat + 1) * (1 + ε) := by
    refine le_trans (Number.sub_near _ _ _ htvoN hrpN hti).abs_le ?_
    gcongr
    rw [abs_le]; constructor <;> linarith

  -- the fee is at most a tenth of it
  obtain ⟨raw, hraw, hrawN, hrawabs⟩ := tenthBipsOfValue_ok_of_abs ti mgmt.toTenthBips32 htiN
    (lt_of_le_of_lt htiabs (by nlinarith [show (2 : ℚ) ^ 63 + 1 < 10 ^ 180 by norm_num]))
  have hrawM : |raw.toRat| + 1 ≤ nt.maxValue.toNat := by
    have h3 : (1 + ε) * (1 + ε) ^ 2 ≤ 2 := by nlinarith
    have hq := mgmt_toNat_le mgmt hmgmt
    have : |raw.toRat| ≤ (nt.maxValue.toNat + 1) * (1 + ε) * 10000 / 100000 * (1 + ε) ^ 2 :=
      le_trans hrawabs (by gcongr)
    nlinarith
  obtain ⟨mfo, hmfo, hmfoN, hmfoabs⟩ :=
    STAmount.roundToNumericType_integral_ok_abs nt raw .downward (some 0) hnt hrawN hrawM

  refine ⟨amountSt, tvo, rp, ti, mfo, hst, ?_, ?_, hti, ?_, ?_, fun _ => hls, htvoN, htvo0, ⟨k, hk63, ?_⟩, hmfoN,
    ?_⟩
  · rw [hls]; exact htvo
  · rw [hls]; exact hrp
  · rw [hls]; unfold computeManagementFee; rw [hraw, ok_bind, hmfo]
  · rw [hls]; norm_num
  · rw [hls, hk]; simp
  · linarith [show (2 : ℚ) ^ 63 * 2 + 1 < 10 ^ 100 by norm_num]

/-- An IOU: the rounded values compute for a raw total value below `10^42` and a principal below `10^16`. -/
private lemma loanValueSteps_frac0 (amount principal : Number) (mode : rounding_mode) (mgmt : TenthBips16)
    (minScale : Int) (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward)
    (hscale : -10 ≤ minScale ∧ minScale ≤ 0) (hmgmt : mgmt.toNat ≤ 10000) (hamountN : amount.isNormalized)
    (hamount0 : 0 ≤ amount.toRat) (hamountlt : amount.toRat < 10 ^ 42) (hp : principal.isNormalized)
    (hpos : 0 ≤ principal.toRat) (hp16 : principal.toRat < 10 ^ 20) :
    ∃ amountSt tvo rp ti mfo,
      LoanValueSteps .fractional amount principal mode mgmt minScale amountSt tvo rp ti mfo := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have habs : |amount.toRat| = amount.toRat := abs_of_nonneg hamount0
  have hpabs : |principal.toRat| = principal.toRat := abs_of_nonneg hpos

  -- the total value as an amount, at an exponent of at most 30
  obtain ⟨amountSt, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr amount mode hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 90 by norm_num])
  have hexp := STAmount.ofNumber_fractional_exponent_le amount mode amountSt hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 45 by norm_num]) hst
  obtain ⟨ls, hlsdef⟩ : ∃ ls, max minScale amountSt.exponent = ls := ⟨_, rfl⟩
  have hls : -10 ≤ ls ∧ ls ≤ 30 := by
    rw [← hlsdef]; exact ⟨le_max_of_le_left hscale.1, max_le (by linarith [hscale.2]) hexp⟩
  have hp10 : (10 : ℚ) ^ ls ≤ 10 ^ 30 := by
    have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hls.2
    norm_num at this ⊢
    exact this
  have hp0 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _

  -- the rounded total value and principal
  obtain ⟨tvo, htvo, htvoN, htvoabs⟩ := STAmount.roundToNumericType_frac_ok_abs amount mode ls hamountN
    (by rw [habs]; linarith [show (10 : ℚ) ^ 42 < 10 ^ 90 by norm_num]) ⟨by omega, by omega⟩
  obtain ⟨rp, hrp, hrpN, hrpabs⟩ := STAmount.roundToNumericType_frac_ok_abs principal .to_nearest ls hp
    (by rw [hpabs]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 90 by norm_num]) ⟨by omega, by omega⟩
  have htvo0 := STAmount.roundToNumericType_some_nonneg .fractional amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ htvo
  have hexp' : ∀ st, STAmount.ofNumber .fractional amount mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ ls :=
    fun st hst2 _ => by
      rw [hst, Except.ok.injEq] at hst2
      rw [← hst2, ← hlsdef]; exact le_max_right _ _
  obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_frac_grid amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ hexp' htvo
  have hle := STAmount.roundToNumericType_frac_le amount tvo mode ls hamountN hamount0 hmode
    ⟨by omega, by omega⟩ hexp' htvo
  have hk63 : k < 2 ^ 63 := by
    rw [hk] at hle
    have : k ≤ 10 ^ 16 - 1 := by exact_mod_cast le_of_mul_le_mul_right hle hp0
    omega
  rw [habs] at htvoabs
  rw [hpabs] at hrpabs

  -- the interest
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs tvo rp .to_nearest htvoN hrpN
    (by linarith [show (2 : ℚ) * 10 ^ 42 + 10 ^ 30 < 10 ^ 200 by norm_num])
    (by linarith [show (2 : ℚ) * 10 ^ 20 + 10 ^ 30 < 10 ^ 200 by norm_num])
  have htiN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ htvoN hrpN hti
  have htiabs : |ti.toRat| ≤ 10 ^ 44 := by
    refine le_trans (Number.sub_near _ _ _ htvoN hrpN hti).abs_le ?_
    have h1 : |tvo.toRat - rp.toRat| ≤ |tvo.toRat| + |rp.toRat| := abs_sub _ _
    have h2 : |tvo.toRat - rp.toRat| ≤ 10 ^ 43 := by
      linarith [show (2 : ℚ) * 10 ^ 42 + 10 ^ 30 + (2 * 10 ^ 20 + 10 ^ 30) ≤ 10 ^ 43 by norm_num]
    calc |tvo.toRat - rp.toRat| * (1 + ε) ≤ 10 ^ 43 * 2 := by gcongr; linarith
      _ ≤ 10 ^ 44 := by norm_num

  -- the fee is at most a tenth of it
  obtain ⟨raw, hraw, hrawN, hrawabs⟩ := tenthBipsOfValue_ok_of_abs ti mgmt.toTenthBips32 htiN
    (lt_of_le_of_lt htiabs (by norm_num))
  have hraw45 : |raw.toRat| ≤ 10 ^ 44 := by
    have h2 : (1 + ε) ^ 2 ≤ 2 := by nlinarith
    have hq := mgmt_toNat_le mgmt hmgmt
    calc |raw.toRat| ≤ |ti.toRat| * mgmt.toTenthBips32.toNat / 100000 * (1 + ε) ^ 2 := hrawabs
      _ ≤ 10 ^ 44 * 10000 / 100000 * 2 := by gcongr
      _ ≤ 10 ^ 44 := by norm_num
  obtain ⟨mfo, hmfo, hmfoN, hmfoabs⟩ := STAmount.roundToNumericType_frac_ok_abs raw .downward ls hrawN
    (lt_of_le_of_lt hraw45 (by norm_num)) ⟨by omega, by omega⟩

  refine ⟨amountSt, tvo, rp, ti, mfo, ?_⟩
  unfold LoanValueSteps
  rw [hlsdef]
  refine ⟨hst, htvo, hrp, hti, ?_, hls, fun h => absurd h (by decide), htvoN, htvo0, ⟨k, hk63, hk⟩, hmfoN, ?_⟩
  · unfold computeManagementFee; rw [hraw, ok_bind, hmfo]
  · linarith [show (2 : ℚ) * 10 ^ 44 + 10 ^ 30 < 10 ^ 100 by norm_num]

/-- The loan values of a re-amortization compute, with the sizes a LoanSet's values have. The principal is zero or
more and within the asset, and `V` bounds PeriodicPayment × PaymentRemaining within the asset. -/
lemma computeLoanPropertiesFromPeriodicRate_computes (principal rate : Number) (ir : TenthBips32)
    (interval n : UInt32) (mgmt : TenthBips16) (nt : NumericType) (minScale : Int)
    (hrate : loanPeriodicRate ir interval = .ok rate) (hp : principal.isNormalized) (h0 : 0 ≤ principal.toRat)
    (hp20 : principal.toRat < 10 ^ 20) (hir : ir.toNat ≤ 100000) (hiv : 60 ≤ interval.toNat) (hn0 : n ≠ 0)
    (hk : n.toNat * interval.toNat < 2 ^ 32) (hmgmt : mgmt.toNat ≤ 10000)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hscale : -10 ≤ minScale ∧ minScale ≤ 0)
    (hpmax : nt.isIntegral = true → principal.toRat ≤ nt.maxValue.toNat) (V : ℚ) (hV : V ≤ 4 * 10 ^ 41)
    (hVmax : nt.isIntegral = true → V ≤ nt.maxValue.toNat)
    (hvalue : ∀ pp : Number, loanPeriodicPayment principal rate n = .ok pp → pp.toRat * n.toNat ≤ V) :
    ∃ props, computeLoanPropertiesFromPeriodicRate principal rate n mgmt nt minScale = .ok props ∧
      props.SetSizes nt ∧ loanPeriodicPayment principal rate n = .ok props.periodicPayment := by
  have hint_cases : nt = .fractional ∨ (nt = NumericType.native ∨ nt = NumericType.int64) := hnt
  have hM63 : nt.isIntegral = true → (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by
    intro hi
    have : nt.maxValue.toNat ≤ 2 ^ 63 := by
      rcases hnt with rfl | rfl | rfl
      · cases hi
      all_goals decide
    exact_mod_cast this
  have hrN := loanPeriodicRate_isNormalized ir interval rate hrate
  have hr0 := loanPeriodicRate_nonneg ir interval rate hrate

  -- the periodic payment, zero for a zero principal
  obtain ⟨pp, hpp, hppN, hpp0, hpple⟩ : ∃ pp, loanPeriodicPayment principal rate n = .ok pp ∧ pp.isNormalized ∧
      0 ≤ pp.toRat ∧ pp.toRat ≤ principal.toRat * 10 ^ 16 := by
    rcases eq_or_lt_of_le h0 with hz | hpos
    · have hpz : principal = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hp).mp hz.symm
      have hzz : Number.zero.operator_eq Number.zero = true := (Number.operator_eq_iff_eq _ _).mpr rfl
      refine ⟨Number.zero, ?_, Number.zero_isNormalized, by rw [Number.toRat_zero], by
        rw [Number.toRat_zero]; positivity⟩
      unfold loanPeriodicPayment
      rw [hpz, hzz]
      rfl
    · exact loanPeriodicPayment_range principal rate ir interval n hrate hir hiv hn0 hk hp hpos
        (by linarith [show (10 : ℚ) ^ 20 < 10 ^ 100 by norm_num])
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hn32 : (n.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast n.toNat_lt
  have hnn : n.toNat ≠ 0 := fun h0 => hn0 (UInt32.toNat_inj.mp (by simpa using h0))
  have hn1 : (1 : ℚ) ≤ n.toNat := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnn
  have hpp36 : pp.toRat < 10 ^ 36 := by nlinarith

  -- the raw total value
  obtain ⟨amount, hamount⟩ := Number.operator_mul_ok_of_abs pp (Number.ofInt64 n.toInt64) (valueMode rate) hppN hN
    (by rw [abs_of_nonneg hpp0]; linarith [show (10 : ℚ) ^ 36 < 10 ^ 200 by norm_num])
    (by rw [hNv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num])
  have hamountN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamount
  have hmode : valueMode rate = .to_nearest ∨ valueMode rate = .upward ∨ valueMode rate = .downward :=
    (valueMode_cases rate).elim Or.inl (fun h => Or.inr (Or.inl h))
  have hamount0 : 0 ≤ amount.toRat := by
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamount h0
      have := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by
        rw [Number.toRat_zero, hNv]; positivity)
      rwa [Number.toRat_zero] at this
  have hamount_le : ∀ w : Number, w.isNormalized → pp.toRat * n.toNat ≤ w.toRat → amount.toRat ≤ w.toRat := by
    intro w hw hle
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]; exact le_trans (by positivity) hle
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamount h0
      exact hR.le_of_ge hmode w hw (by rw [hNv]; exact hle)

  -- the rounded values, by asset
  obtain ⟨amountSt, tvo, rp, ti, mfo, hst', htvo, hrp, hti, hmfo, hls, hlsi, htvoN, htvo0, hunits, hmfoN, hmfoabs⟩ :
      ∃ amountSt tvo rp ti mfo,
        LoanValueSteps nt amount principal (valueMode rate) mgmt minScale amountSt tvo rp ti mfo := by
    rcases hint_cases with hfr | hnt'
    · subst hfr
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 5 41 (by norm_num)
        (by unfold minExponent maxExponent; norm_num)
      have hlt : amount.toRat < 10 ^ 42 := by
        have := hamount_le w hw (by
          rw [hwv]
          calc pp.toRat * n.toNat ≤ V := hvalue pp hpp
            _ ≤ 4 * 10 ^ 41 := hV
            _ ≤ ((5 : ℤ) : ℚ) * 10 ^ (41 : ℤ) := by norm_num)
        rw [hwv] at this
        norm_num at this ⊢
        linarith
      exact loanValueSteps_frac0 amount principal _ mgmt minScale hmode hscale hmgmt hamountN hamount0 hlt hp h0 hp20
    · have hint : nt.isIntegral = true := by rcases hnt' with rfl | rfl <;> rfl
      have hM := hM63 hint
      have hMn : nt.maxValue.toNat < 2 ^ 63 := by rcases hnt' with rfl | rfl <;> decide
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (nt.maxValue.toNat : ℤ) 0
        ⟨by have : (0 : ℤ) ≤ (nt.maxValue.toNat : ℤ) := by positivity
            linarith, by exact_mod_cast hMn⟩
        (by unfold minExponent maxExponent; norm_num)
      have hwv' : w.toRat = (nt.maxValue.toNat : ℚ) := by rw [hwv]; simp
      have hle : amount.toRat ≤ nt.maxValue.toNat := by
        have := hamount_le w hw (by rw [hwv']; exact le_trans (hvalue pp hpp) (hVmax hint))
        rwa [hwv'] at this
      exact loanValueSteps_integral0 nt hnt' amount principal _ mgmt minScale hmode hscale hmgmt hamountN hamount0
        hle hp h0 (STAmount.roundsInRange_of_le_max nt hnt' .to_nearest _ h0 (hpmax hint))

  -- the principal part of the first payment
  have hpp100 : pp.toRat < 10 ^ 100 := by linarith [show (10 : ℚ) ^ 36 < 10 ^ 100 by norm_num]
  obtain ⟨tpo, htpo⟩ := loanPrincipalFromPeriodicPayment_computes pp rate ir interval n hrate hir hiv hk hppN hpp0
    hpp100
  have hone : (1 : UInt32) ≤ n := by
    rw [UInt32.le_iff_toNat_le]
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  have hsub : n.subChecked 1 = .ok (n - 1) := UInt32.subChecked_of_le hone
  have hpred : (n - 1).toNat ≤ n.toNat := by
    rw [UInt32.toNat_sub_of_le n 1 hone]; omega
  have hk' : (n - 1).toNat * interval.toNat < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hpred) hk
  obtain ⟨tpo', htpo'⟩ := loanPrincipalFromPeriodicPayment_computes pp rate ir interval (n - 1) hrate hir hiv hk'
    hppN hpp0 hpp100
  have htpoN := loanPrincipalFromPeriodicPayment_normalized_of_ok pp rate n tpo hppN hrN htpo
  have htpoN' := loanPrincipalFromPeriodicPayment_normalized_of_ok pp rate (n - 1) tpo' hppN hrN htpo'
  obtain ⟨htpo0, htpole, -⟩ := loanPrincipalFromPeriodicPayment_le_payments pp rate n tpo hppN hpp0 hrN hr0 htpo
  obtain ⟨htpo0', htpole', -⟩ :=
    loanPrincipalFromPeriodicPayment_le_payments pp rate (n - 1) tpo' hppN hpp0 hrN hr0 htpo'
  have hpredq : ((n - 1).toNat : ℚ) ≤ n.toNat := by exact_mod_cast hpred
  have hbig : (70 : ℚ) * 2 ^ 32 * 10 ^ 36 < 10 ^ 200 := by norm_num
  have htpolt : |tpo.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htpo0]
    have : 70 * (n.toNat : ℚ) * pp.toRat ≤ 70 * 2 ^ 32 * 10 ^ 36 := by gcongr
    linarith
  have htpolt' : |tpo'.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htpo0']
    have : 70 * ((n - 1).toNat : ℚ) * pp.toRat ≤ 70 * 2 ^ 32 * 10 ^ 36 := by gcongr; linarith
    linarith
  obtain ⟨first, hfirst⟩ := Number.operator_sub_ok_of_abs tpo tpo' .to_nearest htpoN htpoN' htpolt htpolt'

  let props : LoanProperties :=
    { periodicPayment := pp
      totalValueOutstanding := tvo
      managementFeeOutstanding := mfo
      loanScale := max minScale amountSt.exponent
      principalOutstanding := rp
      firstPaymentPrincipal := first }
  refine ⟨props, ?_, ?_, hpp⟩
  · unfold computeLoanPropertiesFromPeriodicRate
    rw [hpp, ok_bind]
    dsimp only
    rw [hamount, ok_bind, hst', ok_bind, htvo, ok_bind, hrp, ok_bind, hti, ok_bind, hmfo, ok_bind, htpo, ok_bind]
    rw [hsub, ok_bind]
    rw [htpo', ok_bind, hfirst, ok_bind]
    rfl
  · exact { periodicPayment_norm := hppN
            periodicPayment_nonneg := hpp0
            periodicPayment_lt := hpp36
            periodicPayment_max := fun hint => by
              have := le_trans (hvalue pp hpp) (hVmax hint)
              nlinarith
            totalValue_norm := htvoN
            totalValue_nonneg := htvo0
            totalValue_units := hunits
            managementFee_norm := hmfoN
            managementFee_abs := hmfoabs
            loanScale_range := hls
            loanScale_integral := hlsi }

/-- The amortization guards compute on values of the sizes a LoanSet computed, whichever interest they expect. -/
lemma LoanProperties.amortizationGuards_computes (props : LoanProperties) (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hsz : props.SetSizes nt)
    (principal : Number) (hp : principal.isNormalized) (hpabs : |principal.toRat| < 10 ^ 200)
    (expect : Bool) (n : UInt32) : ∃ t, props.amortizationGuards principal expect n nt = .ok t := by
  obtain ⟨k, hk63, hk⟩ := hsz.totalValue_units
  obtain ⟨hlslo, hlshi⟩ := hsz.loanScale_range
  have htvoN := hsz.totalValue_norm
  have htvo0 := hsz.totalValue_nonneg
  have hppN := hsz.periodicPayment_norm
  have hpp0 := hsz.periodicPayment_nonneg
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  have hp10le : (10 : ℚ) ^ props.loanScale ≤ 10 ^ 30 := by
    have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hlshi
    norm_num at this ⊢
    exact this
  have hkq : (k : ℚ) ≤ 2 ^ 63 - 1 := by
    have h1 : k + 1 ≤ 2 ^ 63 := hk63
    have h2 : (k : ℚ) + 1 ≤ 2 ^ 63 := by exact_mod_cast h1
    linarith
  have htvoabs : |props.totalValueOutstanding.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htvo0, hk]
    calc (k : ℚ) * 10 ^ props.loanScale ≤ (2 ^ 63 - 1) * 10 ^ 30 := by gcongr
      _ < 10 ^ 200 := by norm_num

  -- the interest and the rounded payment
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs props.totalValueOutstanding principal .to_nearest htvoN hp
    htvoabs hpabs
  have hppin : STAmount.RoundsInRange nt .upward props.periodicPayment.toRat := by
    rcases hnt with rfl | hnt'
    · simp only [STAmount.RoundsInRange]
      have := hsz.periodicPayment_lt
      exact ⟨by linarith, by linarith [show (10 : ℚ) ^ 36 ≤ 9999999999999999 * 10 ^ 80 by norm_num]⟩
    · exact STAmount.roundsInRange_of_le_max nt hnt' .upward _ hpp0
        (hsz.periodicPayment_max (by rcases hnt' with rfl | rfl <;> rfl))
  obtain ⟨rp, hrp⟩ := STAmount.roundToNumericType_of_inRange nt hnt props.periodicPayment .upward props.loanScale
    hppN hpp0 hppin ⟨by omega, by omega⟩
  have hrpN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrp
  have hrp0 := STAmount.roundToNumericType_some_nonneg nt _ rp .upward props.loanScale hppN hpp0
    (Or.inr (Or.inl rfl)) ⟨by omega, by omega⟩ hrp

  -- the amortization guards
  cases hz : rp.operator_eq Number.zero with
  | true =>
    unfold LoanProperties.amortizationGuards
    simp only [bind, Except.bind, pure, Except.pure, hti, hrp, hz]
    split_ifs <;> exact ⟨_, rfl⟩
  | false =>
    -- a payment that is not zero is at least one unit, so the payment count is below `2^63`
    have hrpne : rp.toRat ≠ 0 := fun h0' => by
      have := (Number.operator_eq_iff rp Number.zero hrpN Number.zero_isNormalized).mpr (by
        rw [h0', Number.toRat_zero])
      rw [hz] at this; cases this
    have hunit : (10 : ℚ) ^ props.loanScale ≤ rp.toRat :=
      (STAmount.roundToNumericType_upward_unit nt hnt _ rp props.loanScale hppN hpp0 ⟨by omega, by omega⟩
        hsz.loanScale_integral hrp).resolve_left hrpne
    have hrppos : 0 < rp.toRat := lt_of_lt_of_le hp10 hunit
    obtain ⟨ratio, hratio⟩ := Number.operator_div_ok_of_abs props.totalValueOutstanding rp .upward htvoN hrpN
      htvoabs (by
        rw [abs_of_nonneg hrp0]
        refine le_trans ?_ hunit
        exact zpow_le_zpow_right₀ (by norm_num) (by omega))
    have hratioN := Number.operator_div_isNormalized _ _ ratio _ htvoN hrpN hratio
    have hq0 : 0 ≤ props.totalValueOutstanding.toRat / rp.toRat := div_nonneg htvo0 hrp0
    have hqle : props.totalValueOutstanding.toRat / rp.toRat ≤ 2 ^ 63 - 1 := by
      rw [div_le_iff₀ hrppos, hk]
      calc (k : ℚ) * 10 ^ props.loanScale ≤ (2 ^ 63 - 1) * 10 ^ props.loanScale := by gcongr
        _ ≤ (2 ^ 63 - 1) * rp.toRat := by gcongr
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (2 ^ 63 - 1) 0 (by norm_num)
      (by unfold minExponent maxExponent; norm_num)
    have hwv' : w.toRat = 2 ^ 63 - 1 := by rw [hwv]; norm_num
    have hratio0 : 0 ≤ ratio.toRat ∧ ratio.toRat ≤ 2 ^ 63 - 1 := by
      by_cases hm : ratio.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm]; norm_num
      · have hR := Number.operator_div_rounded_upward _ _ _ htvoN hrpN hratio hm
        refine ⟨?_, ?_⟩
        · have := hR.ge_of_le (Or.inr (Or.inl rfl)) Number.zero Number.zero_isNormalized (by
            rw [Number.toRat_zero]; exact hq0)
          rwa [Number.toRat_zero] at this
        · have := hR.le_of_ge (Or.inr (Or.inl rfl)) w hw (by rw [hwv']; exact hqle)
          rwa [hwv'] at this
    have hneg := Number.negative_false_of_nonneg ratio hratioN hratio0.1
    obtain ⟨c, hc⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos ratio .upward hneg
      (Number.exponent_le_zero_of_cap ratio hratioN hneg hratio0.2)
    unfold LoanProperties.amortizationGuards
    simp only [bind, Except.bind, pure, Except.pure, hti, hrp, hz, hratio, hc]
    split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.Lending
