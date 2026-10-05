import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.Common.TenthBips

/-! # Proof bodies for the minimum cover theorems

The minimum cover is `debtTotal` times `coverRateMinimum`, rounded up, converted
to the vault asset and rounded up to the vault scale. This file holds the facts
the cover operations share and the proofs `LoanBroker.lean` delegates to. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The minimum cover is always a normalized `Number`. -/
lemma minimumBrokerCover_isNormalized (nt : NumericType) (debtTotal : Number)
    (coverRateMinimum : TenthBips32) (e : Int) (m : Number)
    (hok : minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m) : m.isNormalized := by
  unfold minimumBrokerCover at hok
  obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
  exact STAmount.roundToNumericType_isNormalized _ _ _ _ m hok

/-- With no debt the minimum cover is zero at every vault scale. -/
lemma minimumBrokerCover_zero_debt (nt : NumericType) (rate : TenthBips32) (e : Int) :
    minimumBrokerCover nt Number.zero rate e = .ok Number.zero := by
  unfold minimumBrokerCover
  rw [tenthBipsOfValue_zero, ok_bind]
  exact STAmount.roundToNumericType_zero nt e

/-- On a lawful broker, the cover floor holds exactly when `coverAvailable` is
at least the minimum cover. -/
lemma LoanBroker.hasMinimumCover_iff (lb : LoanBroker) (e : Int) (m : Number)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok m) :
    lb.HasMinimumCover e ↔ m.toRat ≤ lb.toExact.coverAvailable := by
  unfold LoanBroker.HasMinimumCover RawLoanBroker.hasMinimumCover
  simp only [hmin, ok_bind, pure_eq, Except.ok.injEq]
  exact operator_le_iff m lb.coverAvailable (minimumBrokerCover_isNormalized _ _ _ _ _ hmin)
    lb.wf.coverAvailable_norm

/-- The cover floor only reads the numeric type, `debtTotal`,
`coverRateMinimum` and `coverAvailable`. A broker with the same first three and
at least as much cover keeps it. -/
lemma LoanBroker.hasMinimumCover_of_cover_le (lb lb' : LoanBroker) (e : Int)
    (hnt : lb'.numericType = lb.numericType) (hdebt : lb'.debtTotal = lb.debtTotal)
    (hrate : lb'.coverRateMinimum = lb.coverRateMinimum)
    (hle : lb.toExact.coverAvailable ≤ lb'.toExact.coverAvailable)
    (h : lb.HasMinimumCover e) : lb'.HasMinimumCover e := by
  have h' := h
  unfold LoanBroker.HasMinimumCover RawLoanBroker.hasMinimumCover at h'
  obtain ⟨m, hm, _⟩ := bind_ok_peel _ _ _ h'
  have hm' : minimumBrokerCover lb'.numericType lb'.debtTotal lb'.coverRateMinimum e = .ok m := by
    rw [hnt, hdebt, hrate]; exact hm
  rw [LoanBroker.hasMinimumCover_iff lb e m hm] at h
  rw [LoanBroker.hasMinimumCover_iff lb' e m hm']
  exact le_trans h hle

/-- **Proof body of `minimumBrokerCover_scale_monotone`.** -/
lemma minimumBrokerCover_scale_monotone_proof (nt : NumericType) (debtTotal : Number)
    (coverRateMinimum : TenthBips32) (e e' : Int) (m m' : Number)
    (hle : e ≤ e') (he : -96 ≤ e) (he' : e' ≤ 80)
    (hm : minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m)
    (hm' : minimumBrokerCover nt debtTotal coverRateMinimum e' = .ok m')
    (hnz : m ≠ Number.zero) (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat := by
  unfold minimumBrokerCover at hm hm'
  obtain ⟨raw, hraw, hm⟩ := bind_ok_peel _ _ _ hm
  rw [hraw, ok_bind] at hm'
  unfold STAmount.roundToNumericType at hm hm'
  cases hret : STAmount.ofNumber nt raw .upward with
  | error err => rw [hret] at hm; exact absurd hm (by simp)
  | ok ret =>
    rw [hret] at hm hm'
    dsimp only at hm hm'
    by_cases hint : ret.integral = true
    · -- an integral asset ignores the vault scale
      rw [if_pos hint] at hm hm'
      rw [hm, Except.ok.injEq] at hm'
      rw [hm']
    rw [if_neg hint] at hm hm'
    -- the converted amount is canonical or zero
    have hfc : ret.FracCanonZero := by
      cases nt with
      | integral mv mo ms msh =>
        exact absurd (STAmount.ofNumber_integral_canonical _ _ _ ret rfl hret).1.is_integral hint
      | fractional => exact STAmount.ofNumber_fractional_fczr raw .upward ret hret
    obtain ⟨hfr, hcz⟩ := hfc
    -- a nonzero minimum cover is the exact value of a canonical rounded amount
    have hval (s : Int) (q : STAmount) (n : Number)
        (hq : ret.roundToExponent s .upward = .ok q) (hn : q.toNumber .upward = .ok n)
        (hn0 : n ≠ Number.zero) :
        n.toRat = q.toRat ∧ ret.IOUCanonical ∧ q.mValue ≠ 0 := by
      obtain ⟨hqfr, hqcz⟩ := STAmount.roundToExponent_fczr ret q s .upward ⟨hfr, hcz⟩ hq
      have hq0 : q.mValue ≠ 0 := by
        intro h0
        have hqi : q.integral = false := by unfold STAmount.integral; rw [hqfr]; rfl
        rw [STAmount.toNumber_zero_fractional q .upward hqi h0, Except.ok.injEq] at hn
        exact hn0 hn.symm
      obtain ⟨n', hn', hv, _⟩ :=
        STAmount.toNumber_exact_canonical q .upward (Or.inl (hqcz.resolve_right hq0))
      rw [hn, Except.ok.injEq] at hn'
      subst hn'
      -- a zero amount passes through rounding unchanged
      have hretc : ret.IOUCanonical := by
        refine hcz.resolve_right fun h0 => hq0 ?_
        have hpass : ret.roundToExponent s .upward = .ok ret :=
          STAmount.roundToExponent_eq_self ret s .upward
            (Or.inr (Or.inl (by unfold STAmount.isZero; rw [h0]; rfl)))
        rw [hpass, Except.ok.injEq] at hq
        rw [← hq]
        exact h0
      exact ⟨hv, hretc, hq0⟩
    cases hr : ret.roundToExponent e .upward with
    | error err => rw [hr] at hm; exact absurd hm (by simp)
    | ok r =>
      cases hr' : ret.roundToExponent e' .upward with
      | error err => rw [hr'] at hm'; exact absurd hm' (by simp)
      | ok r' =>
        rw [hr] at hm
        rw [hr'] at hm'
        dsimp only at hm hm'
        obtain ⟨hmv, hretc, hr0⟩ := hval e r m hr hm hnz
        obtain ⟨hmv', _, hr0'⟩ := hval e' r' m' hr' hm' hnz'
        -- both are `ret` rounded up, onto the `10^e` and the coarser `10^e'` grid
        have hup := STAmount.roundToExponent_rounded ret r e .upward hretc he (by omega) hr0 hr
        have hup' :=
          STAmount.roundToExponent_rounded ret r' e' .upward hretc (by omega) he' hr0' hr'
        rw [hmv, hmv']
        exact RoundsToRepresentableAt.upward_mono r r' ret.toRat e e' hle hup hup'

/-- At one vault scale, a larger debt times rate never gives a smaller minimum
cover, when the larger minimum cover is nonzero. -/
private lemma minimumBrokerCover_le_of_prod_le (nt : NumericType) (d d' : Number)
    (rate rate' : TenthBips32) (e : Int) (m m' : Number)
    (hd : d.isNormalized) (hd' : d'.isNormalized) (h0 : 0 ≤ d.toRat) (h0' : 0 ≤ d'.toRat)
    (hprod : d.toRat * rate.toNumber.toRat ≤ d'.toRat * rate'.toNumber.toRat)
    (he : -96 ≤ e) (he' : e ≤ 80)
    (hm : minimumBrokerCover nt d rate e = .ok m)
    (hm' : minimumBrokerCover nt d' rate' e = .ok m')
    (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat := by
  unfold minimumBrokerCover at hm hm'
  obtain ⟨raw, hraw, hk⟩ := bind_ok_peel _ _ _ hm
  obtain ⟨raw', hraw', hk'⟩ := bind_ok_peel _ _ _ hm'
  clear hm hm'
  obtain ⟨hrn, hr0⟩ := tenthBipsOfValue_upward_facts d _ raw hd h0 hraw
  obtain ⟨hrn', hr0'⟩ := tenthBipsOfValue_upward_facts d' _ raw' hd' h0' hraw'
  unfold STAmount.roundToNumericType at hk hk'
  cases hret : STAmount.ofNumber nt raw .upward with
  | error err => rw [hret] at hk; exact absurd hk (by simp)
  | ok ret =>
    cases hret' : STAmount.ofNumber nt raw' .upward with
    | error err => rw [hret'] at hk'; exact absurd hk' (by simp)
    | ok ret' =>
      rw [hret] at hk
      rw [hret'] at hk'
      dsimp only at hk hk'
      cases nt with
      | integral mv mo ms msh =>
        -- an XRP or MPT minimum cover is the scaled debt rounded up to a whole number
        have hnt : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
        have hint (q : STAmount) (x : Number)
            (hq : STAmount.ofNumber (.integral mv mo ms msh) x .upward = .ok q) :
            q.integral = true :=
          (STAmount.ofNumber_integral_canonical _ _ _ q hnt hq).1.is_integral
        rw [if_pos (hint ret raw hret)] at hk
        rw [if_pos (hint ret' raw' hret')] at hk'
        have hceil (x : Number) (q : STAmount) (n : Number) (hxn : x.isNormalized)
            (hx0 : 0 ≤ x.toRat)
            (hq : STAmount.ofNumber (.integral mv mo ms msh) x .upward = .ok q)
            (hn : q.toNumber .upward = .ok n) :
            ∃ z : ℤ, n.toRat = z ∧ x.toRat ≤ z ∧ (z : ℚ) < x.toRat + 1 ∧ n.isNormalized := by
          have hneg := Number.negative_false_of_nonneg x hxn hx0
          obtain ⟨iv, hr, hres⟩ := STAmount.ofNumber_integral_toRat _ x .upward q hnt hneg hq
          obtain ⟨hlo, hhi⟩ := Number.to_rep_upward_ceil x iv hxn hneg hr
          have hic := (STAmount.ofNumber_integral_canonical _ _ _ q hnt hq).1
          have hsz : q.mValue.toNat ≤ 2 ^ 63 - 1 := by
            by_cases hq0 : q.mValue = 0
            · rw [hq0]
              decide
            · rcases STAmount.ofNumber_exactCanonical _ x .upward q hxn hx0 hq hq0 with
                hiou | ⟨_, hs⟩
              · have hf := hiou.is_fractional
                rw [STAmount.ofNumber_mNumericType _ _ _ _ hq] at hf
                exact absurd hf (by simp)
              · exact hs
          obtain ⟨sn, hsn, hsv, hsnn⟩ := STAmount.toNumber_integral_small_exact q .upward hic hsz
          rw [hn, Except.ok.injEq] at hsn
          subst hsn
          exact ⟨iv.toInt, by rw [hsv, hres], hlo, hhi, hsnn⟩
        obtain ⟨z, hz, _, hzhi, _⟩ := hceil raw ret m hrn hr0 hret hk
        obtain ⟨z', hz', hzlo', hzhi', hmn'⟩ := hceil raw' ret' m' hrn' hr0' hret' hk'
        -- the larger minimum cover is nonzero, so its scaled debt is too
        have hraw0' : raw'.mantissa_ ≠ 0 := by
          intro h0r
          apply hnz'
          apply (Number.toRat_eq_zero_iff_eq_zero hmn').mp
          rw [Number.toRat_eq_zero_of_mantissa_zero raw' h0r] at hzlo' hzhi'
          have h1 : 0 ≤ z' := by exact_mod_cast hzlo'
          have h2 : z' < 1 := by
            have : (z' : ℚ) < 1 := by linarith
            exact_mod_cast this
          rw [hz', show z' = 0 by omega]
          simp
        have hmono := tenthBipsOfValue_upward_le d d' _ _ raw raw' hd hd' h0 hprod hraw hraw' hraw0'
        rw [hz, hz']
        have hlt : (z : ℚ) < z' + 1 := by linarith
        have hlt' : z < z' + 1 := by exact_mod_cast hlt
        exact_mod_cast (show z ≤ z' by omega)
      | fractional =>
        -- an IOU minimum cover is the scaled debt rounded up to 16 digits, then up to the
        -- vault scale
        have hfr (q : STAmount) (x : Number)
            (hq : STAmount.ofNumber .fractional x .upward = .ok q) : q.integral = false := by
          unfold STAmount.integral
          rw [STAmount.ofNumber_mNumericType _ _ _ _ hq]
          rfl
        rw [if_neg (by rw [hfr ret raw hret]; decide)] at hk
        rw [if_neg (by rw [hfr ret' raw' hret']; decide)] at hk'
        obtain ⟨hfra, hcza⟩ := STAmount.ofNumber_fractional_fczr raw .upward ret hret
        obtain ⟨hfrb, hczb⟩ := STAmount.ofNumber_fractional_fczr raw' .upward ret' hret'
        -- a zero amount passes through the vault-scale rounding unchanged
        have hpass (q : STAmount) (h0q : q.mValue = 0) : q.roundToExponent e .upward = .ok q :=
          STAmount.roundToExponent_eq_self q e .upward
            (Or.inr (Or.inl (by unfold STAmount.isZero; rw [h0q]; rfl)))
        cases hr : ret.roundToExponent e .upward with
        | error err => rw [hr] at hk; exact absurd hk (by simp)
        | ok r =>
          cases hr' : ret'.roundToExponent e .upward with
          | error err => rw [hr'] at hk'; exact absurd hk' (by simp)
          | ok r' =>
            rw [hr] at hk
            rw [hr'] at hk'
            dsimp only at hk hk'
            -- the larger side is nonzero all the way back
            obtain ⟨hrfr', hrcz'⟩ :=
              STAmount.roundToExponent_fczr ret' r' e .upward ⟨hfrb, hczb⟩ hr'
            have hr'0 : r'.mValue ≠ 0 := by
              intro h0r
              apply hnz'
              rw [STAmount.toNumber_zero_fractional r' .upward
                (by unfold STAmount.integral; rw [hrfr']; rfl) h0r, Except.ok.injEq] at hk'
              exact hk'.symm
            have hret'0 : ret'.mValue ≠ 0 := by
              intro h0q
              apply hr'0
              rw [hpass ret' h0q, Except.ok.injEq] at hr'
              rw [← hr']
              exact h0q
            have hraw0' : raw'.mantissa_ ≠ 0 :=
              STAmount.ofNumber_iou_mantissa_ne_zero .fractional raw' .upward ret' rfl hret' hret'0
            have hmono :=
              tenthBipsOfValue_upward_le d d' _ _ raw raw' hd hd' h0 hprod hraw hraw' hraw0'
            obtain ⟨n', hn', hv', _⟩ := STAmount.toNumber_exact_canonical r' .upward
              (Or.inl (hrcz'.resolve_right hr'0))
            rw [hk', Except.ok.injEq] at hn'
            subst hn'
            have hu' : r'.toRat = (⌈ret'.toRat / 10 ^ e⌉ : ℚ) * 10 ^ e :=
              STAmount.roundToExponent_rounded ret' r' e .upward (hczb.resolve_right hret'0) he he'
                hr'0 hr'
            have hc' : ret'.toRat =
                (⌈raw'.toRat / 10 ^ (raw'.exponent_ + 3)⌉ : ℚ) * 10 ^ (raw'.exponent_ + 3) :=
              STAmount.ofNumber_iou_upward_ceil raw' ret' hrn' hraw0' hr0' hret' hret'0
            rw [hv']
            by_cases hr0m : r.mValue = 0
            · -- the smaller minimum cover is zero, and the larger one is not negative
              obtain ⟨hrfr, _⟩ := STAmount.roundToExponent_fczr ret r e .upward ⟨hfra, hcza⟩ hr
              rw [STAmount.toNumber_zero_fractional r .upward
                (by unfold STAmount.integral; rw [hrfr]; rfl) hr0m, Except.ok.injEq] at hk
              rw [← hk, Number.toRat_zero, hu']
              have h1 := le_ceil_grid ret'.toRat e
              have h2 := le_ceil_grid raw'.toRat (raw'.exponent_ + 3)
              rw [← hc'] at h2
              linarith
            · -- both sides are nonzero: two ceilings, each keeping the order
              obtain ⟨_, hrcz⟩ := STAmount.roundToExponent_fczr ret r e .upward ⟨hfra, hcza⟩ hr
              have hret0 : ret.mValue ≠ 0 := by
                intro h0q
                apply hr0m
                rw [hpass ret h0q, Except.ok.injEq] at hr
                rw [← hr]
                exact h0q
              have hraw0 : raw.mantissa_ ≠ 0 :=
                STAmount.ofNumber_iou_mantissa_ne_zero .fractional raw .upward ret rfl hret hret0
              obtain ⟨n, hn, hv, _⟩ := STAmount.toNumber_exact_canonical r .upward
                (Or.inl (hrcz.resolve_right hr0m))
              rw [hk, Except.ok.injEq] at hn
              subst hn
              have hu : r.toRat = (⌈ret.toRat / 10 ^ e⌉ : ℚ) * 10 ^ e :=
                STAmount.roundToExponent_rounded ret r e .upward (hcza.resolve_right hret0) he he'
                  hr0m hr
              have hc : ret.toRat =
                  (⌈raw.toRat / 10 ^ (raw.exponent_ + 3)⌉ : ℚ) * 10 ^ (raw.exponent_ + 3) :=
                STAmount.ofNumber_iou_upward_ceil raw ret hrn hraw0 hr0 hret hret0
              have hpos : 0 < raw.toRat := lt_of_le_of_ne hr0
                (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero raw hraw0))
              have hs := Number.exponent_le_of_le raw raw' hrn hrn' hraw0 hpos hmono
              -- the 16-digit roundings keep the order, even when the larger one is coarser
              have hretle : ret.toRat ≤ ret'.toRat := by
                rw [hc, hc']
                exact le_trans (ceil_grid_le_of_le _ _ _ hmono)
                  (ceil_grid_le_of_scale_le _ _ _ (by omega))
              rw [hv, hu, hu']
              exact ceil_grid_le_of_le _ _ e hretle

/-- **Proof body of `minimumBrokerCover_debt_monotone`.** -/
lemma minimumBrokerCover_debt_monotone_proof (nt : NumericType) (d d' : Number)
    (coverRateMinimum : TenthBips32) (e : Int) (m m' : Number)
    (hd : d.isNormalized) (hd' : d'.isNormalized) (h0 : 0 ≤ d.toRat)
    (hle : d.toRat ≤ d'.toRat) (he : -96 ≤ e) (he' : e ≤ 80)
    (hm : minimumBrokerCover nt d coverRateMinimum e = .ok m)
    (hm' : minimumBrokerCover nt d' coverRateMinimum e = .ok m')
    (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat :=
  minimumBrokerCover_le_of_prod_le nt d d' _ _ e m m' hd hd' h0 (le_trans h0 hle)
    (mul_le_mul_of_nonneg_right hle (TenthBips32.toNumber_nonneg coverRateMinimum)) he he' hm
    hm' hnz'

/-- **Proof body of `minimumBrokerCover_rate_monotone`.** -/
lemma minimumBrokerCover_rate_monotone_proof (nt : NumericType) (debtTotal : Number)
    (rate rate' : TenthBips32) (e : Int) (m m' : Number)
    (hd : debtTotal.isNormalized) (h0 : 0 ≤ debtTotal.toRat) (hle : rate.toNat ≤ rate'.toNat)
    (he : -96 ≤ e) (he' : e ≤ 80)
    (hm : minimumBrokerCover nt debtTotal rate e = .ok m)
    (hm' : minimumBrokerCover nt debtTotal rate' e = .ok m')
    (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat := by
  have hr : rate.toNumber.toRat ≤ rate'.toNumber.toRat := by
    rw [(TenthBips32.toNumber_facts rate).2, (TenthBips32.toNumber_facts rate').2]
    exact_mod_cast hle
  exact minimumBrokerCover_le_of_prod_le nt debtTotal debtTotal rate rate' e m m' hd hd h0 h0
    (mul_le_mul_of_nonneg_left hr h0) he he' hm hm' hnz'

/-- Below the finest IOU scale the vault scale no longer matters: every canonical
IOU amount already sits on the grid. -/
private lemma minimumBrokerCover_below_min (nt : NumericType) (debtTotal : Number)
    (rate : TenthBips32) (e : Int) (he : e ≤ -96) :
    minimumBrokerCover nt debtTotal rate e = minimumBrokerCover nt debtTotal rate (-96) := by
  unfold minimumBrokerCover
  cases hraw : tenthBipsOfValue debtTotal rate .upward with
  | error err => rfl
  | ok raw =>
    rw [ok_bind, ok_bind]
    unfold STAmount.roundToNumericType
    cases hret : STAmount.ofNumber nt raw .upward with
    | error err => rfl
    | ok ret =>
      dsimp only
      by_cases hint : ret.integral = true
      · rw [if_pos hint, if_pos hint]
      rw [if_neg hint, if_neg hint]
      -- the converted amount is canonical or zero, so both scales leave it alone
      have hfc : ret.FracCanonZero := by
        cases nt with
        | integral mv mo ms msh =>
          exact absurd (STAmount.ofNumber_integral_canonical _ _ _ ret rfl hret).1.is_integral hint
        | fractional => exact STAmount.ofNumber_fractional_fczr raw .upward ret hret
      have hpass (s : Int) (hs : s ≤ -96) : ret.roundToExponent s .upward = .ok ret := by
        apply STAmount.roundToExponent_eq_self
        rcases hfc.2 with hc | h0
        · exact Or.inr (Or.inr (by have := hc.exp_lo; show s ≤ ret.mOffset; omega))
        · exact Or.inr (Or.inl (by unfold STAmount.isZero; rw [h0]; rfl))
      rw [hpass e he, hpass (-96) le_rfl]

/-- The minimum cover of a nonnegative debt is not negative, at every vault scale up
to `10^80`. -/
private lemma minimumBrokerCover_nonneg (nt : NumericType) (debtTotal : Number) (rate : TenthBips32)
    (e : Int) (m : Number) (hd : debtTotal.isNormalized) (h0 : 0 ≤ debtTotal.toRat)
    (he : e ≤ 80) (hm : minimumBrokerCover nt debtTotal rate e = .ok m) : 0 ≤ m.toRat := by
  -- in the IOU range it is at least the zero minimum cover of no debt
  have key (e' : Int) (m' : Number) (hlo : -96 ≤ e') (hhi : e' ≤ 80)
      (hm' : minimumBrokerCover nt debtTotal rate e' = .ok m') : 0 ≤ m'.toRat := by
    by_cases hz : m' = Number.zero
    · rw [hz, Number.toRat_zero]
    have h := minimumBrokerCover_le_of_prod_le nt Number.zero debtTotal rate rate e' Number.zero
      m' Number.zero_isNormalized hd (by rw [Number.toRat_zero]) h0
      (by rw [Number.toRat_zero, zero_mul]; exact mul_nonneg h0 (TenthBips32.toNumber_nonneg rate))
      hlo hhi (minimumBrokerCover_zero_debt nt rate e') hm' hz
    rwa [Number.toRat_zero] at h
  by_cases hlo : -96 ≤ e
  · exact key e m hlo he hm
  · exact key (-96) m le_rfl (by norm_num)
      (by rw [← minimumBrokerCover_below_min nt debtTotal rate e (by omega)]; exact hm)

/-- A broker's minimum cover at the vault scale is not negative. -/
lemma LoanBroker.minimumCover_nonneg {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (e : Int) (m : Number) (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok m) :
    0 ≤ m.toRat := by
  have he : e ≤ 80 := by rcases numberExponent_range _ _ e hexp with h | h <;> omega
  exact minimumBrokerCover_nonneg _ _ _ e m lb.wf.debtTotal_norm lb.exact.debtTotal_nonneg he hm

end XRPL.Model.Lending
