import XRPL.Properties.Lending.LoanBroker.Common.CoverAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverUnit
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin

/-! # Proof bodies for the `LoanBroker.coverDeposit` theorems

Proofs for the theorems in `LoanBrokerCoverDeposit.lean`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- **Proof body of `coverDeposit_credit`.** -/
lemma LoanBroker.coverDeposit_credit_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat := by
  have hc := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc).1
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hamt : res.amount' = r :=
    LoanBroker.applyCoverTransaction_amount' lb _ r res happ
  rw [hamt] at hc hexact ⊢
  rw [(LoanBroker.applyCoverTransaction_credit_value lb r res happ hc hexact).1]
  ring

/-- **Proof body of `coverDeposit_credit_integral`.** -/
lemma LoanBroker.coverDeposit_credit_integral_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = amount.toRat := by
  have hamt := LoanBroker.coverDeposit_amount_integral lb amount res hok hint.is_integral
  rw [← hamt]
  apply LoanBroker.coverDeposit_credit_proof lb amount res hok (Or.inr ⟨hint, hsz⟩)
  rw [hamt]
  have hden := Rat.den_one_add _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  have hcov : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  have habs := STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le amount hint hsz
  exact Number.exists_of_int _ hden (by linarith [neg_abs_le amount.toRat]) hbound

/-- **Proof body of `coverDeposit_credit_le_amount`.** -/
lemma LoanBroker.coverDeposit_credit_le_amount_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat := by
  rw [LoanBroker.coverDeposit_credit_proof lb amount res hok hc hexact]
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hamt : res.amount' = r :=
    LoanBroker.applyCoverTransaction_amount' lb _ r res happ
  rw [hamt]
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hrr
  exact (LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hc.iouCanonical hexp hrr).1

/-- **Proof body of `coverDeposit_increases_cover`.** -/
lemma LoanBroker.coverDeposit_increases_cover_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable := by
  have hcr := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc).1
  have hr0 := (LoanBroker.coverDeposit_amount_bounds lb amount res hok hc hnn).1
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  rw [hamt] at hcr hr0
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of r m hcr hm
  show lb.coverAvailable.toRat ≤ res.loanBroker'.toRawLoanBroker.coverAvailable.toRat
  rw [hraw]
  exact operator_add_ge_of_ge_normalized _ _ _ _ lb.wf.coverAvailable_norm hmn hadd
    lb.wf.coverAvailable_norm (by rw [hmv]; linarith)

/-- CoverAvailable itself, converted to the vault asset, sits at the cover scale, so the deposit
rounding keeps it whole. -/
private lemma LoanBroker.roundedCoverAmount_whole (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) : lb.roundedCoverAmount s = .ok (.rounded s) := by
  have hscale : numberExponent lb.coverAvailable lb.numericType = .ok s.exponent := by
    simp [numberExponent, hs]
  have hsg : s.signum ≠ 0 := by
    have hb : (s.mValue == 0) = false := by simpa using hnz
    unfold STAmount.signum
    rw [hb, if_neg Bool.false_ne_true]
    split <;> decide
  have hdown : roundToCoverScale lb.numericType lb.coverAvailable s .downward = .ok s := by
    rw [roundToCoverScale_eq _ _ _ _ _ hscale]
    exact STAmount.roundToExponent_eq_self _ _ _ (Or.inr (Or.inr le_rfl))
  simp [LoanBroker.roundedCoverAmount, hdown, hsg]

/-- `coverDeposit_increase_possible` with a nonzero cover: the amount is CoverAvailable itself in the
vault asset. -/
private lemma LoanBroker.coverDeposit_increase_possible_nonzero (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + s.toRat) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult), lb.coverDeposit amount = .ok (.ok res) ∧
      lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hc : s.ExactCanonical := STAmount.ofNumber_exactCanonical _ _ .to_nearest s hcn hcov0 hs hnz
  have hnn : 0 ≤ s.toRat :=
    STAmount.ofNumber_nonneg _ _ _ s hcn (Number.negative_false_of_nonneg _ hcn hcov0) hs
  have hpos : 0 < s.toRat := lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero s hnz))
  have hcap := LoanBroker.cover_lt_cap_of_ofNumber lb s hs hnz
  have hscap : s.toRat < 10 ^ 96 :=
    lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt s hc)
  -- two amounts below `10^96` add without error, so the deposit succeeds
  obtain ⟨m, hm, hmv, hmn⟩ := STAmount.toNumber_exact_canonical s .to_nearest hc
  obtain ⟨c', hadd⟩ := Number.operator_add_ok_of_lt lb.coverAvailable m .to_nearest hcn hmn hcov0
    hcap (by rw [hmv]; exact hnn) (by rw [hmv]; exact hscap)
  obtain ⟨lb', htl, _⟩ := LoanBroker.credit_lawful lb m c' hmn (by rw [hmv]; exact hnn) hadd
  have hok : lb.coverDeposit s = .ok (.ok { amount' := s, loanBroker' := lb' }) := by
    simp [LoanBroker.coverDeposit, LoanBroker.applyCoverTransaction,
      LoanBroker.roundedCoverAmount_whole lb s hs hnz, hm, hadd, htl]
  refine ⟨s, _, hok, ?_⟩
  have hup := LoanBroker.coverDeposit_credit_proof lb s _ hok hc hexact
  dsimp only at hup ⊢
  linarith

/-- `coverDeposit_increase_possible` with an empty cover, one that rounds to zero in the vault asset:
the amount is one whole unit of the asset, one drop for XRP. The unit is lifted to the cover scale if
that is coarser. The cover is below one unit, and the nearest-rounded sum is at least the unit. -/
private lemma LoanBroker.coverDeposit_increase_possible_empty (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hz : s.mValue = 0)
    (hone : lb.numericType.isIntegral = true → 1 ≤ lb.numericType.maxValue.toNat) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult), lb.coverDeposit amount = .ok (.ok res) ∧
      lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hneg : lb.coverAvailable.negative_ = false := Number.negative_false_of_nonneg _ hcn hcov0
  have hscale : numberExponent lb.coverAvailable lb.numericType = .ok s.exponent := by
    simp [numberExponent, hs]
  have hs0 : s.toRat = 0 := by unfold STAmount.toRat; simp [hz]
  -- a unit of the asset: canonical, nonzero, at or above the cover scale, worth more than the cover
  suffices h : ∃ u : STAmount, u.ExactCanonical ∧ u.mIsNegative = false ∧ u.mValue ≠ 0 ∧
      s.exponent ≤ u.exponent ∧ lb.coverAvailable.toRat < u.toRat ∧ u.toRat < 10 ^ 96 by
    obtain ⟨u, huc, hun, hu0, hle, hlt, hucap⟩ := h
    have hcap : lb.coverAvailable.toRat < 10 ^ 96 := lt_trans hlt hucap
    have hunn : 0 ≤ u.toRat := by rw [STAmount.toRat_of_nonneg u hun]; positivity
    have hsg : u.signum ≠ 0 := by
      have hb : (u.mValue == 0) = false := by simpa using hu0
      unfold STAmount.signum
      rw [hb, if_neg Bool.false_ne_true]
      split <;> decide
    have hdown : roundToCoverScale lb.numericType lb.coverAvailable u .downward = .ok u := by
      rw [roundToCoverScale_eq _ _ _ _ _ hscale]
      exact STAmount.roundToExponent_eq_self _ _ _ (Or.inr (Or.inr hle))
    have hrounded : lb.roundedCoverAmount u = .ok (.rounded u) := by
      simp [LoanBroker.roundedCoverAmount, hdown, hsg]
    obtain ⟨m, hm, hmv, hmn⟩ := STAmount.toNumber_exact_canonical u .to_nearest huc
    obtain ⟨c', hadd⟩ := Number.operator_add_ok_of_lt lb.coverAvailable m .to_nearest hcn hmn hcov0
      hcap (by rw [hmv]; exact hunn) (by rw [hmv]; exact hucap)
    obtain ⟨lb', htl, hraw⟩ := LoanBroker.credit_lawful lb m c' hmn (by rw [hmv]; exact hunn) hadd
    have hok : lb.coverDeposit u = .ok (.ok { amount' := u, loanBroker' := lb' }) := by
      simp [LoanBroker.coverDeposit, LoanBroker.applyCoverTransaction, hrounded, hm, hadd, htl]
    refine ⟨u, _, hok, ?_⟩
    show lb.coverAvailable.toRat < lb'.toRawLoanBroker.coverAvailable.toRat
    rw [hraw]
    -- rounding to nearest never lands below the unit, a Number below the exact sum
    have hge := operator_add_ge_of_ge_normalized _ _ _ m hcn hmn hadd hmn (by linarith)
    rw [hmv] at hge
    exact lt_of_lt_of_le hlt hge
  by_cases hint : lb.numericType.isIntegral = true
  · -- XRP or MPT: the cover rounds to zero, so it is at most half a drop, and one drop passes
    have hic := (STAmount.ofNumber_integral_canonical _ _ _ s hint hs).1
    have hhalf := STAmount.ofNumber_integral_within_half _ _ s hint hcn hneg hs
    rw [hs0] at hhalf
    set u : STAmount := ⟨lb.numericType, 1, 0, false⟩ with hu_def
    have huc : u.IntegralCanonical := ⟨hint, rfl, by show (1 : UInt64).toNat ≤ _; exact hone hint⟩
    have huv : u.toRat = 1 := by
      rw [STAmount.toRat_of_nonneg u rfl]
      show (((1 : UInt64).toNat : ℕ) : ℚ) * 10 ^ (0 : ℤ) = 1
      simp
    refine ⟨u, Or.inr ⟨huc, by show (1 : UInt64).toNat ≤ 2 ^ 63 - 1; decide⟩, rfl,
      by show (1 : UInt64) ≠ 0; decide, ?_, ?_, ?_⟩
    · have := hic.offset_zero
      show s.mOffset ≤ 0
      omega
    · rw [huv]; linarith [(abs_le.mp hhalf).1]
    · rw [huv]; norm_num
  · -- an IOU: the cover rounds to zero, so it is below `10^-81`, and one whole token passes
    have hfr : lb.numericType = .fractional := by
      cases h : lb.numericType with
      | integral mv mo ms msh => exact absurd (show lb.numericType.isIntegral = true by rw [h]; rfl) hint
      | fractional => rfl
    have hs80 : s.mOffset ≤ 80 := by
      rcases STAmount.ofNumber_fractional_offset _ _ _ s hfr hs with h | ⟨_, h⟩ <;> omega
    have hs' : STAmount.ofNumber .fractional lb.coverAvailable .to_nearest = .ok s := by
      rw [← hfr]; exact hs
    have hlt1 : lb.coverAvailable.toRat < 1 := by
      by_cases hm0 : lb.coverAvailable.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm0]; norm_num
      · have hexp : lb.coverAvailable.exponent_ ≤ -100 := by
          by_contra hcon
          exact STAmount.ofNumber_iou_ne_zero_of_exponent _ .to_nearest s hcn hm0 (by omega) hs' hz
        have hb := mantissaBounds_nat_of (hcn.mantissaBounds hm0)
        have habs := abs_toRat_eq lb.coverAvailable
        rw [abs_of_nonneg hcov0] at habs
        rw [habs]
        have hm : (lb.coverAvailable.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hb.2
        have hp : (10 : ℚ) ^ lb.coverAvailable.exponent_ ≤ (10 : ℚ) ^ (-100 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) hexp
        have h2 : (10 : ℚ) ^ 19 * (10 : ℚ) ^ (-100 : ℤ) < 1 := by norm_num
        calc (lb.coverAvailable.mantissa_.toNat : ℚ) * 10 ^ lb.coverAvailable.exponent_
            ≤ (lb.coverAvailable.mantissa_.toNat : ℚ) * (10 : ℚ) ^ (-100 : ℤ) :=
              mul_le_mul_of_nonneg_left hp (by positivity)
          _ < 10 ^ 19 * (10 : ℚ) ^ (-100 : ℤ) := mul_lt_mul_of_pos_right hm (by positivity)
          _ < 1 := h2
    have hkMin : kMinValue.toNat = 10 ^ 15 := by decide
    set u : STAmount := ⟨.fractional, kMinValue, max s.exponent (-15), false⟩ with hu_def
    have huc : u.IOUCanonical :=
      ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
        by show (-96 : ℤ) ≤ max s.exponent (-15); exact le_trans (by norm_num) (le_max_right _ _),
        by show max s.exponent (-15) ≤ 80; exact max_le hs80 (by norm_num)⟩
    have hu1 : (1 : ℚ) ≤ u.toRat := by
      rw [STAmount.toRat_of_nonneg u rfl]
      show (1 : ℚ) ≤ (kMinValue.toNat : ℚ) * 10 ^ max s.exponent (-15)
      rw [hkMin]; push_cast
      have h1 : (10 : ℚ) ^ (-15 : ℤ) ≤ (10 : ℚ) ^ max s.exponent (-15) :=
        zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _)
      calc (1 : ℚ) = 10 ^ 15 * (10 : ℚ) ^ (-15 : ℤ) := by norm_num
        _ ≤ 10 ^ 15 * (10 : ℚ) ^ max s.exponent (-15) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hucap : u.toRat < 10 ^ 96 := by
      rw [STAmount.toRat_of_nonneg u rfl]
      show (kMinValue.toNat : ℚ) * 10 ^ max s.exponent (-15) < 10 ^ 96
      rw [hkMin]; push_cast
      have h1 : (10 : ℚ) ^ max s.exponent (-15) ≤ (10 : ℚ) ^ (80 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (max_le hs80 (by norm_num))
      have h2 : (10 : ℚ) ^ 15 * (10 : ℚ) ^ (80 : ℤ) < 10 ^ 96 := by norm_num
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    exact ⟨u, Or.inl huc, rfl, by show kMinValue ≠ 0; decide,
      by show s.exponent ≤ max s.exponent (-15); exact le_max_left _ _, lt_of_lt_of_le hlt1 hu1, hucap⟩

/-- **Proof body of `coverDeposit_increase_possible`.** The amount is CoverAvailable itself in the
vault asset, or one whole unit of the asset when the cover is empty. -/
lemma LoanBroker.coverDeposit_increase_possible_proof (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hone : lb.numericType.isIntegral = true → 1 ≤ lb.numericType.maxValue.toNat)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + s.toRat) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult), lb.coverDeposit amount = .ok (.ok res) ∧
      lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable := by
  by_cases hz : s.mValue = 0
  · exact LoanBroker.coverDeposit_increase_possible_empty lb s hs hz hone
  · exact LoanBroker.coverDeposit_increase_possible_nonzero lb s hs hz hexact

/-- **Proof body of `coverDeposit_total`.** -/
lemma LoanBroker.coverDeposit_total_proof (lb : LoanBroker) (amount r : STAmount)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r)) (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) (hcap : lb.toExact.coverAvailable + r.toRat < 10 ^ 96) :
    ∃ res, lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = r := by
  have hcr := (LoanBroker.roundedCoverAmount_exactCanonical lb amount r hc hrounded).1
  have hr0 := LoanBroker.roundedCoverAmount_nonneg lb amount r hc.iouCanonical hnn hrounded
  obtain ⟨m, hm, hmv, hmn⟩ := STAmount.toNumber_exact_canonical r .to_nearest hcr
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hcn := lb.wf.coverAvailable_norm
  have hm0 : 0 ≤ m.toRat := by rw [hmv]; exact hr0
  change lb.coverAvailable.toRat + r.toRat < 10 ^ 96 at hcap
  obtain ⟨c', hadd⟩ := Number.operator_add_ok_of_lt lb.coverAvailable m .to_nearest hcn hmn hcov0
    (by linarith) hm0 (by rw [hmv]; linarith)
  obtain ⟨lb', htl, _⟩ := LoanBroker.credit_lawful lb m c' hmn hm0 hadd
  refine ⟨{ amount' := r, loanBroker' := lb' }, ?_, rfl⟩
  simp [LoanBroker.coverDeposit, LoanBroker.applyCoverTransaction, hrounded, hm, hadd, htl]

/-- **Proof body of `coverDeposit_keeps_minimum`.** -/
lemma LoanBroker.coverDeposit_keeps_minimum_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) (hmin : lb.HasMinimumCover e) :
    res.loanBroker'.HasMinimumCover e := by
  have hf := LoanBroker.coverDeposit_fixed_fields lb amount res hok
  exact LoanBroker.hasMinimumCover_of_cover_le lb res.loanBroker' e hf.numericType hf.debtTotal
    hf.coverRateMinimum
    (LoanBroker.coverDeposit_increases_cover_proof lb amount res hok hc hnn) hmin

/-- **Proof body of `coverDeposit_empty`.** -/
lemma LoanBroker.coverDeposit_empty_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hzero : lb.coverAvailable = Number.zero)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hat : amount.mNumericType = lb.numericType) :
    res.amount' = amount ∧ res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  obtain ⟨q, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hq := (LoanBroker.roundedCoverAmount_rounded_inv lb amount q hrr).1
  unfold roundToCoverScale at hq
  obtain ⟨e, he, hq⟩ := bind_ok_peel _ _ _ hq
  have hamt := LoanBroker.applyCoverTransaction_amount' lb _ q res happ
  -- an empty cover leaves the amount alone
  have hsame : q = amount := by
    refine STAmount.roundToExponent_ok_eq_self amount q e .downward ?_ hq
    rcases id hc with hia | ⟨hia, _⟩
    · -- an empty IOU cover sits at scale `10^-100`, below every IOU amount
      have hnt : lb.numericType = .fractional := by rw [← hat]; exact hia.is_fractional
      rw [hzero, hnt] at he
      unfold numberExponent at he
      rw [STAmount.ofNumber_fractional_zero] at he
      have he100 : e = -100 := by
        simp only [ok_bind, pure_eq, Except.ok.injEq] at he
        exact he.symm
      refine Or.inr (Or.inr ?_)
      have := hia.exp_lo
      show e ≤ amount.mOffset
      omega
    · exact Or.inl hia.is_integral
  rw [hsame] at hamt
  refine ⟨hamt, ?_⟩
  -- the empty cover plus the amount is the amount
  have h0 : lb.toExact.coverAvailable = 0 := by
    show lb.coverAvailable.toRat = 0
    rw [hzero, Number.toRat_zero]
  obtain ⟨aN, _, hav, han⟩ := STAmount.toNumber_exact_canonical amount .to_nearest hc
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hok hc
    ⟨aN, han, by rw [hamt, hav, h0]; ring⟩
  rw [hamt] at hup
  linarith

/-- A deposit of an IOU amount takes a whole number of units of the cover scale. -/
private lemma LoanBroker.coverDeposit_amount_grid (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.coverDeposit amount = .ok (.ok res)) (hiou : amount.IOUCanonical) :
    ∃ k : ℤ, res.amount'.toRat = (k : ℚ) * (10 : ℚ) ^ e := by
  have hround := LoanBroker.coverDeposit_amount_of_exp lb amount res e hexp hok
  by_cases hge : e ≤ amount.exponent
  · -- an amount on a grid at least as fine as the cover scale passes unchanged
    rw [STAmount.roundToExponent_ok_eq_self amount res.amount' e .downward
      (Or.inr (Or.inr hge)) hround]
    obtain ⟨z, hz⟩ := STAmount.exists_int_grid amount
    obtain ⟨d, hd⟩ : ∃ d : ℕ, amount.exponent = e + d := ⟨(amount.exponent - e).toNat, by omega⟩
    refine ⟨z * 10 ^ d, ?_⟩
    rw [hz, hd, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    ring
  · -- otherwise it is truncated onto the `10 ^ e` grid
    have hrange : (-96 : ℤ) ≤ e ∧ e ≤ 80 := by
      rcases numberExponent_range _ _ e hexp with h100 | hr
      · have := hiou.exp_lo
        have hem : amount.exponent = amount.mOffset := rfl
        omega
      · exact hr
    exact ⟨_, STAmount.roundToExponent_rounded amount res.amount' e .downward hiou hrange.1
      hrange.2 (LoanBroker.coverDeposit_amount_nonzero lb amount res hok) hround⟩

/-- The amount a deposit takes is already on the cover grid: rounding it to the cover scale again
keeps its value. -/
private lemma LoanBroker.coverDeposit_amount_on_grid (lb : LoanBroker) (amount amount'' : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hround : lb.roundedCoverAmount res.amount' = .ok (.rounded amount'')) :
    amount''.toRat = res.amount'.toRat := by
  obtain ⟨hrc, hrt⟩ := LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc
  by_cases hint : res.amount'.integral = true
  · rw [LoanBroker.roundedCoverAmount_integral_proof lb res.amount' amount'' hint hround]
  have hriou := hrc.iouCanonical (by simpa using hint)
  have hamtF : amount.integral = false := by
    unfold STAmount.integral at hint ⊢
    rw [← hrt]
    simpa using hint
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb _ _ hround
  obtain ⟨k, hk⟩ := LoanBroker.coverDeposit_amount_grid lb amount res e hexp hok
    (hc.iouCanonical hamtF)
  obtain ⟨hr2, hnz2⟩ := LoanBroker.roundedCoverAmount_rounded_inv lb _ _ hround
  rw [roundToCoverScale_eq _ _ _ _ e hexp] at hr2
  by_cases hge : e ≤ res.amount'.exponent
  · rw [STAmount.roundToExponent_ok_eq_self _ _ e .downward (Or.inr (Or.inr hge)) hr2]
  have hrange : (-96 : ℤ) ≤ e ∧ e ≤ 80 := by
    rcases numberExponent_range _ _ e hexp with h100 | hr
    · have := hriou.exp_lo
      have hem : res.amount'.exponent = res.amount'.mOffset := rfl
      omega
    · exact hr
  have hmv : amount''.mValue ≠ 0 := fun h0 => hnz2 (by simp [STAmount.signum, h0])
  have h := STAmount.roundToExponent_rounded _ _ e .downward hriou hrange.1 hrange.2 hmv hr2
  change amount''.toRat = (⌊res.amount'.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e at h
  rw [h, hk, mul_div_assoc, div_self (zpow_ne_zero _ (by norm_num)), mul_one, Int.floor_intCast]

/-- A deposit's applied delta: the new `coverAvailable` minus the old, taken with `Number`
arithmetic and converted to an amount of the vault asset, is the amount the deposit took. -/
private lemma LoanBroker.coverDeposit_delta_value (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (deltaCover : Number) (deltaAmount : STAmount)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hat : amount.mNumericType = lb.numericType)
    (hnn : 0 ≤ amount.toRat)
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable)
    (hbound : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hsub : res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest =
      .ok deltaCover)
    (hda : STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount) :
    deltaCover.isNormalized ∧ 0 ≤ deltaCover.toRat ∧ deltaAmount.toRat = res.amount'.toRat := by
  have hCn := lb.wf.coverAvailable_norm
  have hC0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  obtain ⟨a, hac, hat', hav⟩ := hrep
  change a.toRat = lb.coverAvailable.toRat at hav
  -- the deposit takes `r` and adds it to the cover as the `Number` `m`
  obtain ⟨hrc, hrt⟩ := LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc
  have hrnz := LoanBroker.coverDeposit_amount_nonzero lb amount res hok
  have hrnn := (LoanBroker.coverDeposit_amount_bounds lb amount res hok hc hnn).1
  have hrpos : 0 < res.amount'.toRat :=
    lt_of_le_of_ne hrnn (Ne.symm (STAmount.toRat_ne_zero _ hrnz))
  have hrnt : res.amount'.mNumericType = lb.numericType := hrt.trans hat
  obtain ⟨r0, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_credit_inv lb r0 res happ
  rw [← hamt] at hm
  have hnew : res.loanBroker'.coverAvailable = c' := by
    show res.loanBroker'.toRawLoanBroker.coverAvailable = c'
    rw [hraw]
  rw [hnew] at hsub
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of _ m hrc hm
  have hcn : c'.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ hCn hmn hadd
  have hdn : deltaCover.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ hcn hCn hsub
  refine ⟨hdn, ?_⟩
  -- when the exact sum is a `Number`, nothing rounds
  have hexact : (∃ w : Number, w.isNormalized ∧
      w.toRat = lb.coverAvailable.toRat + res.amount'.toRat) →
      0 ≤ deltaCover.toRat ∧ deltaAmount.toRat = res.amount'.toRat := by
    rintro ⟨w, hw, hwv⟩
    have hc'v : c'.toRat = lb.coverAvailable.toRat + m.toRat :=
      Number.RoundsToRepresentable.eq_of_representable c' _
        (operator_add_rounded_to_nearest _ _ _ hCn hmn hadd) w hw (by rw [hwv, hmv])
    have hdv : deltaCover.toRat = res.amount'.toRat := by
      have h := Number.RoundsToRepresentable.eq_of_representable deltaCover _
        (operator_sub_rounded_to_nearest _ _ _ hcn hCn hsub) m hmn (by rw [hc'v]; ring)
      rw [h, hc'v, hmv]
      ring
    refine ⟨by rw [hdv]; exact hrnn, ?_⟩
    exact STAmount.ofNumber_to_nearest_eq_of_canonical _ deltaCover deltaAmount res.amount' hdn
      (by rw [hdv]; exact hrnn) hrc hrnt hdv hda
  by_cases hnt : lb.numericType.isIntegral = true
  · -- XRP and MPT: whole values whose sum is below `2^63`
    apply hexact
    have hamtI : amount.integral = true := by unfold STAmount.integral; rw [hat]; exact hnt
    have hra : res.amount' = amount :=
      LoanBroker.coverDeposit_amount_integral lb amount res hok hamtI
    have hic : a.IntegralCanonical := by
      rcases hac with hiou | ⟨hic, _⟩
      · have := hiou.is_fractional
        rw [hat'] at this
        rw [this] at hnt
        exact absurd hnt (by decide)
      · exact hic
    have hric : res.amount'.IntegralCanonical := by
      rcases hrc with hiou | ⟨hic, _⟩
      · have := hiou.is_fractional
        rw [hrnt] at this
        rw [this] at hnt
        exact absurd hnt (by decide)
      · exact hic
    have hCd : lb.coverAvailable.toRat.den = 1 := by
      rw [← hav]; exact STAmount.IntegralCanonical.den_eq_one a hic
    have hrd : res.amount'.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one _ hric
    have hCz := Rat.coe_int_num_of_den_eq_one hCd
    have hrz := Rat.coe_int_num_of_den_eq_one hrd
    have hlt : lb.coverAvailable.toRat + res.amount'.toRat < 2 ^ 63 := by
      rw [hra]; exact hbound hnt
    have h1 : ((lb.coverAvailable.toRat.num + res.amount'.toRat.num : ℤ) : ℚ) < 2 ^ 63 := by
      push_cast; rw [hCz, hrz]; exact hlt
    have h2 : (0 : ℚ) ≤ ((lb.coverAvailable.toRat.num + res.amount'.toRat.num : ℤ) : ℚ) := by
      push_cast; rw [hCz, hrz]; linarith
    have h1' : lb.coverAvailable.toRat.num + res.amount'.toRat.num < 2 ^ 63 := by exact_mod_cast h1
    have h2' : 0 ≤ lb.coverAvailable.toRat.num + res.amount'.toRat.num := by exact_mod_cast h2
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_of_int
      (lb.coverAvailable.toRat.num + res.amount'.toRat.num)
      (by have := Int.natAbs_of_nonneg h2'; omega)
    exact ⟨w, hw, by rw [hwv]; push_cast; rw [hCz, hrz]⟩
  -- IOU
  have hfr : lb.numericType = .fractional := by
    cases h : lb.numericType with
    | integral _ _ _ _ => rw [h] at hnt; exact absurd rfl hnt
    | fractional => rfl
  have hriou : res.amount'.IOUCanonical :=
    hrc.iouCanonical (by unfold STAmount.integral; rw [hrnt, hfr]; rfl)
  have hamtF : amount.integral = false := by unfold STAmount.integral; rw [hat, hfr]; rfl
  by_cases hCz : lb.coverAvailable.toRat = 0
  · -- an empty cover: the sum is the amount itself
    exact hexact ⟨m, hmn, by rw [hmv, hCz, zero_add]⟩
  have haiou : a.IOUCanonical := hac.iouCanonical (by unfold STAmount.integral; rw [hat', hfr]; rfl)
  have hCpos : 0 < lb.coverAvailable.toRat := lt_of_le_of_ne hC0 (Ne.symm hCz)
  obtain ⟨halo, _⟩ := STAmount.IOUCanonical.toRat_bounds a haiou (hav ▸ hCpos)
  have hCmin : (10 : ℚ) ^ (-81 : ℤ) ≤ lb.coverAvailable.toRat := by
    have : (10 : ℚ) ^ (-81 : ℤ) ≤ (10 : ℚ) ^ (a.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by have := haiou.exp_lo; show (-81 : ℤ) ≤ a.mOffset + 15; omega)
    rw [← hav]; linarith
  by_cases hsmall : res.amount'.toRat ≤ 9 * lb.coverAvailable.toRat
  · -- at most nine times the cover: the sum has at most 17 digits on the cover grid
    apply hexact
    obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r0 hrr
    obtain ⟨k, hk⟩ := LoanBroker.coverDeposit_amount_grid lb amount res e hexp hok
      (hc.iouCanonical hamtF)
    -- the cover scale is the exponent of the cover's canonical amount `a`
    have hae : a.exponent = e := by
      unfold numberExponent at hexp
      obtain ⟨s, hs, hse⟩ := bind_ok_peel _ _ _ hexp
      simp only [pure_eq, Except.ok.injEq] at hse
      have hsv := STAmount.ofNumber_to_nearest_eq_of_canonical _ _ s a hCn hC0 hac hat'
        hav.symm hs
      have hsnz : s.mValue ≠ 0 := fun h0 => hCz (by
        rw [← hav, ← hsv]; unfold STAmount.toRat; simp [h0])
      have hsc := STAmount.ofNumber_exactCanonical _ _ .to_nearest s hCn hC0 hs hsnz
      have hsa := STAmount.eq_of_exactCanonical s a hsc hac
        ((STAmount.ofNumber_mNumericType _ _ _ _ hs).trans hat'.symm) hsnz hsv
      rw [← hsa, hse]
    obtain ⟨za, hza⟩ := STAmount.exists_int_grid a
    rw [hae] at hza halo
    have hp : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
    obtain ⟨_, hahi⟩ := STAmount.IOUCanonical.toRat_bounds a haiou (hav ▸ hCpos)
    rw [hae] at hahi
    -- `0 < za < 10^16` and `0 < k ≤ 9 za`
    have hpow16 : (10 : ℚ) ^ (e + 16) = 10 ^ 16 * (10 : ℚ) ^ e := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    rw [hpow16, hza] at hahi
    have hza_hi : (za : ℚ) < 10 ^ 16 := by
      by_contra h
      push Not at h
      nlinarith
    have hza_pos : (0 : ℚ) < za := by
      by_contra h
      push Not at h
      have : (za : ℚ) * (10 : ℚ) ^ e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hp.le
      rw [← hza, hav] at this
      linarith
    have hk_pos : (0 : ℚ) < k := by
      by_contra h
      push Not at h
      have : (k : ℚ) * (10 : ℚ) ^ e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hp.le
      rw [← hk] at this
      linarith
    have hk_le : (k : ℚ) ≤ 9 * za := by
      have h9 : (k : ℚ) * (10 : ℚ) ^ e ≤ 9 * za * (10 : ℚ) ^ e := by
        rw [← hk, mul_assoc, ← hza, hav]; exact hsmall
      exact le_of_mul_le_mul_right h9 hp
    have hza_hi' : za < 10 ^ 16 := by exact_mod_cast hza_hi
    have hza_pos' : 0 < za := by exact_mod_cast hza_pos
    have hk_pos' : 0 < k := by exact_mod_cast hk_pos
    have hk_le' : k ≤ 9 * za := by exact_mod_cast hk_le
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (za + k) e
      ⟨by norm_num; omega, by norm_num; omega⟩
      ⟨by have := haiou.exp_lo; rw [← hae]; unfold minExponent; show _ ≤ a.mOffset; omega,
        by have := haiou.exp_hi; rw [← hae]; unfold maxExponent; show a.mOffset ≤ _; omega⟩
    exact ⟨w, hw, by rw [hwv, ← hav, hza, hk]; push_cast; ring⟩
  -- more than nine times the cover: the two roundings stay far below the last digit of `r`
  push Not at hsmall
  obtain ⟨ε, hε⟩ : ∃ ε : ℚ, ε = 6 / (2 ^ 63 - 3 : ℚ) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; norm_num
  have hε16 : ε * 10 ^ 16 ≤ 1 / 100 := by rw [hε]; norm_num
  have hεr : ε * res.amount'.toRat ≤ res.amount'.toRat / 1000 := by
    have : ε ≤ 1 / 1000 := by rw [hε]; norm_num
    nlinarith
  have hCne : lb.coverAvailable.mantissa_ ≠ 0 := fun h =>
    hCz (Number.toRat_eq_zero_of_mantissa_zero _ h)
  have hmne : m.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hmv; linarith
  -- the sum `c'` is within `ε` of `lb.coverAvailable.toRat + res.amount'.toRat`
  have hc'ge : m.toRat ≤ c'.toRat :=
    operator_add_ge_of_ge_normalized _ _ _ _ hCn hmn hadd hmn (by linarith)
  have hc'ne : c'.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hc'ge; linarith
  have hnotneg : ¬ lb.coverAvailable.operator_eq m.operator_neg := by
    intro h
    have := (operator_eq_iff _ _ hCn (Number.operator_neg_isNormalized m hmn)).mp h
    rw [Number.toRat_neg] at this
    linarith
  have hadd' := operator_add_rounds_to_nearest _ _ _ hCn hmn hCne hmne hnotneg hadd hc'ne
  simp only [RoundsWithin, RatValued.toRat] at hadd'
  rw [hmv, abs_of_pos (show (0 : ℚ) < lb.coverAvailable.toRat + res.amount'.toRat by linarith)] at hadd'
  obtain ⟨hs1, hs2⟩ := abs_le.mp hadd'
  rw [← hε] at hs1 hs2
  have hQ : (lb.coverAvailable.toRat + res.amount'.toRat) * ε ≤ 2 * (ε * res.amount'.toRat) := by nlinarith
  have hcC_lo : res.amount'.toRat - 2 * (ε * res.amount'.toRat) ≤ c'.toRat - lb.coverAvailable.toRat := by linarith
  have hcC_hi : c'.toRat - lb.coverAvailable.toRat ≤ res.amount'.toRat + 2 * (ε * res.amount'.toRat) := by linarith
  have hcC_pos : 0 < c'.toRat - lb.coverAvailable.toRat := by linarith
  -- the difference is within `ε` of `c' - lb.coverAvailable.toRat`
  have hneq : ¬ c'.operator_eq lb.coverAvailable := by
    intro h
    have := (operator_eq_iff _ _ hcn hCn).mp h
    linarith
  obtain ⟨hrlo, hrhi⟩ := STAmount.IOUCanonical.toRat_bounds _ hriou hrpos
  have hpr : (0 : ℚ) < (10 : ℚ) ^ res.amount'.exponent := zpow_pos (by norm_num) _
  obtain ⟨f, hf, hfv⟩ := Number.exists_normalized_int_mul_pow 1 (res.amount'.exponent + 14)
    ⟨by norm_num, by norm_num⟩
    ⟨by have := hriou.exp_lo; unfold minExponent; show _ ≤ res.amount'.mOffset + 14; omega,
      by have := hriou.exp_hi; unfold maxExponent; show res.amount'.mOffset + 14 ≤ _; omega⟩
  have hpow : (10 : ℚ) ^ (res.amount'.exponent + 15) =
      10 * (10 : ℚ) ^ (res.amount'.exponent + 14) := by
    rw [show res.amount'.exponent + 15 = (res.amount'.exponent + 14) + 1 by ring,
      zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
    ring
  have hfle : f.toRat ≤ c'.toRat - lb.coverAvailable.toRat := by
    rw [hfv]; push_cast; rw [one_mul]
    have : (10 : ℚ) ^ (res.amount'.exponent + 14) ≤ res.amount'.toRat / 10 := by
      rw [hpow] at hrlo; linarith
    linarith
  have hdge : f.toRat ≤ deltaCover.toRat :=
    operator_sub_ge_of_ge_normalized _ _ _ _ hcn hCn hsub hf hfle
  have hfpos : 0 < f.toRat := by rw [hfv]; push_cast; rw [one_mul]; exact zpow_pos (by norm_num) _
  have hdne : deltaCover.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hdge; linarith
  have hsub' := operator_sub_rounds_to_nearest _ _ _ hcn hCn hc'ne hCne hneq hsub hdne
  simp only [RoundsWithin, RatValued.toRat] at hsub'
  rw [← hε, abs_of_pos hcC_pos] at hsub'
  obtain ⟨hd1, hd2⟩ := abs_le.mp hsub'
  have hR : (c'.toRat - lb.coverAvailable.toRat) * ε ≤ 2 * (ε * res.amount'.toRat) := by
    have h1 := mul_le_mul_of_nonneg_right hcC_hi hε0.le
    have hεs : ε ≤ 1 / 1000 := by rw [hε]; norm_num
    have h2 : ε * (ε * res.amount'.toRat) ≤ 1 / 1000 * (ε * res.amount'.toRat) :=
      mul_le_mul_of_nonneg_right hεs (mul_nonneg hε0.le hrnn)
    linarith only [h1, h2, mul_nonneg hε0.le hrnn]
  -- so `|d - res.amount'.toRat| ≤ 4 ε res.amount'.toRat`, below a twentieth of a unit of `res.amount'.toRat`
  have hd_lo : res.amount'.toRat - 4 * (ε * res.amount'.toRat) ≤ deltaCover.toRat := by linarith
  have hd_hi : deltaCover.toRat ≤ res.amount'.toRat + 4 * (ε * res.amount'.toRat) := by linarith
  have hunit : 4 * (ε * res.amount'.toRat) < (1 / 2 : ℚ) * (10 : ℚ) ^ (res.amount'.exponent - 1) := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    have hr16 : res.amount'.toRat < 10 ^ 16 * (10 : ℚ) ^ res.amount'.exponent := by
      have : (10 : ℚ) ^ (res.amount'.exponent + 16) = 10 ^ 16 * (10 : ℚ) ^ res.amount'.exponent := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      linarith
    have : ε * res.amount'.toRat < ε * (10 ^ 16 * (10 : ℚ) ^ res.amount'.exponent) :=
      mul_lt_mul_of_pos_left hr16 hε0
    nlinarith
  have hnear : |deltaCover.toRat - res.amount'.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (res.amount'.exponent - 1) :=
    abs_lt.mpr ⟨by linarith only [hd_lo, hunit], by linarith only [hd_hi, hunit]⟩
  have hd0 : 0 ≤ deltaCover.toRat := by linarith
  refine ⟨hd0, ?_⟩
  -- the result is nonzero: the difference is above `10^-81`
  have hdexp : (-99 : ℤ) ≤ deltaCover.exponent_ := by
    by_contra h
    push Not at h
    have hdabs := abs_toRat_eq deltaCover
    rw [abs_of_nonneg hd0] at hdabs
    have hb := mantissaBounds_nat_of (hdn.mantissaBounds hdne)
    have hmh : (deltaCover.mantissa_.toNat : ℚ) < ((10 ^ 19 : ℕ) : ℚ) := by exact_mod_cast hb.2
    push_cast at hmh
    have h19 : deltaCover.toRat < (10 : ℚ) ^ (deltaCover.exponent_ + 19) := by
      rw [hdabs, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
      rw [mul_comm]
      exact mul_lt_mul_of_pos_left hmh (zpow_pos (by norm_num) _)
    have h81 : (10 : ℚ) ^ (deltaCover.exponent_ + 19) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hp81 : (0 : ℚ) < (10 : ℚ) ^ (-81 : ℤ) := zpow_pos (by norm_num) _
    linarith only [h19, h81, hCmin, hsmall, hd_lo, hεr, hp81]
  have hda' : STAmount.ofNumber .fractional deltaCover .to_nearest = .ok deltaAmount := by
    rw [← hfr]; exact hda
  have hdanz := STAmount.ofNumber_iou_ne_zero_of_exponent _ _ _ hdn hdne hdexp hda'
  exact STAmount.ofNumber_to_nearest_eq_of_near_canonical _ _ _ _ hdn hd0 hrc hrnt hrpos hnear
    hda hdanz

/-- **Proof body of `coverDeposit_applied_delta`.** -/
lemma LoanBroker.coverDeposit_applied_delta_proof (lb : LoanBroker) (amount amount'' : STAmount)
    (res : LoanBrokerCoverResult) (deltaCover : Number) (deltaAmount : STAmount)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hat : amount.mNumericType = lb.numericType)
    (hnn : 0 ≤ amount.toRat)
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable)
    (hbound : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hround : lb.roundedCoverAmount res.amount' = .ok (.rounded amount''))
    (hsub : res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest =
      .ok deltaCover)
    (hda : STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount) :
    amount''.operator_eq res.amount' = true ∧ deltaAmount.operator_eq res.amount' = true := by
  obtain ⟨hrc, hrt⟩ := LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc
  have hrnz := LoanBroker.coverDeposit_amount_nonzero lb amount res hok
  -- a canonical amount of the same type and value is the amount itself
  have heq : ∀ x : STAmount, x.ExactCanonical → x.mNumericType = res.amount'.mNumericType →
      x.toRat = res.amount'.toRat → x.operator_eq res.amount' = true := by
    intro x hx hxt hxv
    rw [← STAmount.eq_of_exactCanonical res.amount' x hrc hx hxt.symm hrnz hxv.symm]
    simp [STAmount.operator_eq, STAmount.areComparable]
  obtain ⟨hgc, hgt⟩ := LoanBroker.roundedCoverAmount_exactCanonical lb _ _ hrc hround
  obtain ⟨hdn, hd0, hdv⟩ := LoanBroker.coverDeposit_delta_value lb amount res deltaCover
    deltaAmount hok hc hat hnn hrep hbound hsub hda
  have hdanz : deltaAmount.mValue ≠ 0 := fun h0 => STAmount.toRat_ne_zero _ hrnz (by
    rw [← hdv]; unfold STAmount.toRat; simp [h0])
  refine ⟨heq _ hgc hgt
    (LoanBroker.coverDeposit_amount_on_grid lb amount amount'' res hok hc hround), heq _ ?_ ?_ hdv⟩
  · exact STAmount.ofNumber_exactCanonical _ _ .to_nearest _ hdn hd0 hda hdanz
  · rw [STAmount.ofNumber_mNumericType _ _ _ _ hda, hrt, hat]

end XRPL.Model.Lending
