import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Protocol.Number.Add.Common.Downward.AlgorithmicFacts
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.NumberBridge

/-! # The LoanScale of a new loan

The Open-limit check keeps AssetsAvailable plus the new interest below `9·10^15` base units plus half a unit.
A loan whose total value had 16 digits above the base scale would carry more interest than that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The computed AssetsTotal is a normalized `Number` at least AssetsAvailable. -/
private lemma Vault.assetsTotal_ge_available (v : Vault) (assetsTotal : Number) (h : v.assetsTotal = .ok assetsTotal) :
    assetsTotal.isNormalized ∧ v.assetsAvailable.toRat ≤ assetsTotal.toRat := by
  have hAA := v.wf.assetsAvailable_norm
  have hAD := v.wf.assetsDeployed_norm
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  unfold RawVault.assetsTotal at h
  by_cases hd : v.assetsDeployed.mantissa_ = 0
  · -- nothing deployed: the total is the cash
    rw [Number.eq_zero_of_mantissa_zero _ hAD hd, Number.operator_add_zero_right] at h
    obtain rfl := Except.ok.inj h
    exact ⟨hAA, le_refl _⟩
  by_cases ha : v.assetsAvailable.mantissa_ = 0
  · -- no cash: the total is the deployed amount
    have h' := h
    unfold Number.operator_add at h'
    rw [Number.operator_eq_zero_false_of_mantissa_ne _ hd, if_neg Bool.false_ne_true,
      Number.eq_zero_of_mantissa_zero _ hAA ha, if_pos (by decide)] at h'
    obtain rfl := Except.ok.inj h'
    rw [Number.toRat_eq_zero_of_mantissa_zero _ ha]
    exact ⟨hAD, hAD0⟩
  -- both nonzero and nonnegative: a same-sign sum, which never flushes to zero
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hna := Number.negative_false_of_nonneg _ hAA hAA0
  have hnd := Number.negative_false_of_nonneg _ hAD hAD0
  have hnz : ¬ v.assetsAvailable.operator_eq v.assetsDeployed.operator_neg = true := by
    simp [Number.operator_eq, Number.operator_neg, hd, hna, hnd]
  obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_downward _ _ _ hAA hAD ha hd
    (by rw [hna, hnd]) hnz h
  obtain ⟨n, hlo, hval⟩ := operator_add_rounded_downward _ _ _ hAA hAD h hspec.result_mant_ne
  refine ⟨hspec.result_norm, ?_⟩
  rw [hval]
  exact Number.lower_tight _ n hlo _ hAA (by linarith)

/-- What the Open-limit check lets through. When it passes for `x`, AssetsAvailable, YieldUnrealized
and the computed AssetsTotal, each plus `x`, are below the limit `9·10^15` base units plus half a unit. -/
lemma Vault.exceedsOpenLimit_false_bound (v : Vault) (x : Number) (hx : x.isNormalized)
    (h : v.exceedsOpenLimit x = .ok false) :
    v.assetsAvailable.toRat + x.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) ∧
      v.yieldUnrealized.toRat + x.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) ∧
      ∀ atot, v.assetsTotal = .ok atot →
        atot.toRat + x.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) := by
  have hbase := Vault.baseExponent_scale_range v
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at h
  obtain ⟨atot, hat, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨s₁, hs₁, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨capacity, hcap, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨limit, hlim, h⟩ := bind_ok_peel _ _ _ h
  have hgt : capacity.operator_gt limit = false := by
    simp only [pure, Except.pure, Except.ok.injEq] at h; exact h
  obtain ⟨hatN, hatge⟩ := Vault.assetsTotal_ge_available v atot hat
  have hat0 : 0 ≤ atot.toRat := le_trans v.exact.assetsAvailable_nonneg hatge
  obtain ⟨n₁, hlo₁, hs₁v⟩ := operator_add_rounded_towards_zero _ _ _ hatN v.wf.yieldUnrealized_norm hs₁
  rw [if_pos (by linarith)] at hlo₁
  have hs₁ge : atot.toRat ≤ s₁.toRat := by
    rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ atot hatN (by linarith)
  have hYge : v.yieldUnrealized.toRat ≤ s₁.toRat := by
    rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ _ v.wf.yieldUnrealized_norm (by linarith)
  have hs₁N : s₁.isNormalized := by
    by_cases hY : v.yieldUnrealized.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero _ v.wf.yieldUnrealized_norm hY, Number.operator_add_zero_right,
        Except.ok.injEq] at hs₁
      rw [← hs₁]; exact hatN
    · have hYpos : 0 < v.yieldUnrealized.toRat :=
        lt_of_le_of_ne hY0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hY))
      exact operator_add_isNormalized _ _ _ .towards_zero hatN v.wf.yieldUnrealized_norm hs₁ (fun h0 => by
        have := Number.toRat_eq_zero_of_mantissa_zero s₁ h0; linarith)
  -- the limit is `9·10^15` base units
  obtain ⟨w, hw, hwv, hwn⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest (by decide)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hww : limit = w := by
    unfold XRPL.Model.SingleAssetVault.Vault.openLimit at hlim
    exact Except.ok.inj (hlim.symm.trans hw)
  subst hww
  have key : ∀ y : ℚ, y ≤ s₁.toRat →
      y + x.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) := by
    intro y hy
    by_contra hge
    push Not at hge
    obtain ⟨m, hm, hmv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 16 + 5) (v.baseExponent - 1)
      (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
    have htruth : m.toRat ≤ s₁.toRat + x.toRat := by
      rw [hmv]; push_cast at hge ⊢; linarith
    have hm0 : 0 < m.toRat := by rw [hmv]; push_cast; positivity
    obtain ⟨n, hlo, hcapv⟩ := operator_add_rounded_towards_zero _ _ _ hs₁N hx hcap
    rw [if_pos (by linarith)] at hlo
    have hmn := Number.lower_tight _ n hlo m hm htruth
    have hlt : limit.toRat < capacity.toRat := by
      rw [hcapv]
      refine lt_of_lt_of_le ?_ hmn
      rw [hwv, hmv, show (15 + v.baseExponent) = 16 + (v.baseExponent - 1) by ring,
        zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      push_cast
      nlinarith [zpow_pos (by norm_num : (0 : ℚ) < 10) (v.baseExponent - 1)]
    have hcap0 : capacity.mantissa_ ≠ 0 := by
      intro h0
      have := Number.toRat_eq_zero_of_mantissa_zero capacity h0
      rw [hcapv] at this
      linarith [lt_of_lt_of_le hm0 hmn]
    have hcapN := operator_add_isNormalized _ _ _ .towards_zero hs₁N hx hcap hcap0
    have : capacity.operator_gt limit = true := (operator_lt_iff _ _ hwn hcapN).mpr hlt
    rw [this] at hgt
    exact absurd hgt (by decide)
  refine ⟨key _ (hatge.trans hs₁ge), key _ hYge, fun atot' hat' => ?_⟩
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  exact key _ hs₁ge

/-- The interest of the new loan, read exactly. On the LoanScale grid the two subtractions of
`LoanState.build` are exact while the values stay below `2^63` units. -/
lemma LoanState.build_interestDue_grid (tvo p mfo : Number) (s : ℤ) (a j m : ℕ) (state : LoanState)
    (htN : tvo.isNormalized) (hpN : p.isNormalized) (hmN : mfo.isNormalized)
    (hav : tvo.toRat = (a : ℚ) * 10 ^ s) (hjv : p.toRat = (j : ℚ) * 10 ^ s) (hmv : mfo.toRat = (m : ℚ) * 10 ^ s)
    (ha : a < 2 ^ 63) (hja : j ≤ a) (hm : m < 2 ^ 63)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (h : LoanState.build tvo p mfo = .ok state) :
    state.interestDue.isNormalized ∧ state.interestDue.toRat = tvo.toRat - p.toRat - mfo.toRat := by
  unfold LoanState.build at h
  obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_ok_peel _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hdv := Number.operator_sub_toRat_of_grid _ _ d a j s htN hpN (by rw [hav]; norm_cast)
    (by rw [hjv]; norm_cast) (by omega) hs hd
  have hdN := operator_sub_isNormalized_to_nearest_sz _ _ d htN hpN hd
  have hiv := Number.operator_sub_toRat_of_grid _ _ i ((a : ℤ) - j) m s hdN hmN hdv
    (by rw [hmv]; norm_cast) (by omega) hs hi
  refine ⟨operator_sub_isNormalized_to_nearest_sz _ _ i hdN hmN hi, ?_⟩
  show i.toRat = _
  rw [hiv, hav, hjv, hmv]
  push_cast
  ring

/-- An integral vault has base exponent `0`. -/
lemma Vault.baseExponent_integral (v : Vault) (h : v.numericType.isIntegral = true) : v.baseExponent = 0 := by
  unfold XRPL.Model.SingleAssetVault.Vault.baseExponent NumericType.baseExponent
  rw [if_pos h]

/-- The loan value rounds to nearest or up. -/
lemma valueMode_cases (rate : Number) : valueMode rate = .to_nearest ∨ valueMode rate = .upward := by
  unfold valueMode; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `PP × n` in the loan-value mode rounds to a neighbouring `Number`. -/
lemma operator_mul_rounded_valueMode (rate x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_mul y (valueMode rate) = .ok r) (hr : r.mantissa_ ≠ 0) :
    r.RoundsToRepresentable (x.toRat * y.toRat) (valueMode rate) := by
  rcases valueMode_cases rate with h | h <;> rw [h] at hok ⊢
  · exact operator_mul_rounded_to_nearest _ _ _ hx hy hok
  · exact operator_mul_rounded_upward _ _ _ hx hy hok hr

/-- Proof body of the LoanScale line of `Lending.create_updates`. -/
lemma Loan.create_loanScale_proof (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.loan'.loanScale = v.baseExponent := by
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  rw [hLS, hls]
  apply max_eq_left
  by_contra hgt
  push Not at hgt
  have hls' : props.loanScale = amountSt.exponent := by rw [hls]; exact max_eq_right hgt.le
  have hbase := Vault.baseExponent_scale_range v
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  cases hnt' : broker.numericType with
  | integral mv mo ms msh =>
    -- an integral amount sits at exponent `0`, the base exponent of an integral vault
    rw [hnt'] at hst'
    have hoff := (STAmount.ofNumber_integral_canonical _ _ _ amountSt rfl hst').1.offset_zero
    have hb0 := Vault.baseExponent_integral v (by rw [← hnt, hnt']; rfl)
    have : amountSt.exponent = 0 := hoff
    omega
  | fractional =>
    rw [hnt'] at hst' htvo hpo hmfo hst hint
    have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
    have hppN : props.periodicPayment.isNormalized := hPP ▸ hwf.periodicPayment_norm
    have hpoN : props.principalOutstanding.isNormalized := hPO ▸ hwf.principalOutstanding_norm
    have hmfN : props.managementFeeOutstanding.isNormalized := hMF ▸ hwf.managementFeeOutstanding_norm
    have hpp0 : 0 < props.periodicPayment.toRat := by
      have := hex.periodicPayment_pos; simp only [RawLoan.toExact] at this; rwa [hPP] at this
    obtain ⟨ti', hsub, hgt0, -, -, -, htv0, -⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
    have htv0' : 0 < props.totalValueOutstanding.toRat := (Number.signum_pos_iff_toRat htvN).mp htv0
    have hmode : valueMode rate = .to_nearest ∨ valueMode rate = .upward ∨ valueMode rate = .downward :=
      (valueMode_cases rate).elim Or.inl (fun h => Or.inr (Or.inl h))
    -- `PP × n` is a nonzero nonnegative `Number`, and its 16-digit amount is not zero
    have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toUInt64.toInt64
    have hNv := Number.ofInt64_count schedule.paymentTotal
    have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
    have hamt_ne : amount.mantissa_ ≠ 0 := by
      intro h0
      have hof := STAmount.ofNumber_fractional_zero (valueMode rate)
      rw [← Number.eq_zero_of_mantissa_zero amount hamtN h0] at hof
      rw [STAmount.roundToNumericType_frac_of_zero _ _ _ _ _ hof rfl htvo] at htv0'
      exact lt_irrefl _ htv0'
    have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamt hamt_ne
    have hamt0 : 0 ≤ amount.toRat := by
      have := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero, hNv]; positivity)
      rwa [Number.toRat_zero] at this
    have hst0 : amountSt.mValue ≠ 0 := by
      intro h0
      rw [STAmount.roundToNumericType_frac_of_zero _ _ _ _ _ hst' h0 htvo] at htv0'
      exact lt_irrefl _ htv0'
    obtain ⟨hc, -, -, -, -⟩ := STAmount.ofNumber_frac_stage amount _ amountSt hamtN hamt0 hmode hst' hst0
    have hstnn : 0 ≤ amountSt.toRat := STAmount.ofNumber_nonneg _ _ _ _ hamtN
      (Number.negative_false_of_nonneg amount hamtN hamt0) hst'
    have hsneg := STAmount.mIsNegative_false_of_nonneg amountSt hstnn hst0
    -- the total value is that amount, a whole number `a` of LoanScale units with `10^15 ≤ a < 10^16`
    set a := amountSt.mValue.toNat with ha
    have hstv : amountSt.toRat = (a : ℚ) * 10 ^ props.loanScale := by
      rw [STAmount.toRat_of_nonneg amountSt hsneg, hls']; rfl
    have htvv : props.totalValueOutstanding.toRat = (a : ℚ) * 10 ^ props.loanScale := by
      rw [STAmount.roundToNumericType_frac_of_grid amount _ _ _ amountSt hmode ⟨by omega, hhi⟩ hst' hst0 hc hstnn
        hls'.symm.le a hstv htvo, hstv]
    have ha15 : 10 ^ 15 ≤ a := hc.mant_lo
    have ha16 : a < 10 ^ 16 := hc.mant_hi
    obtain ⟨j, hj⟩ := isRounded_grid .fractional principal props.loanScale hp hpos.le hst ⟨by omega, hhi⟩ hint
      (hnt' ▸ hchecks.exact principal List.mem_cons_self)
    have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hj; simp at hj; linarith
      · exact h0
    have hja : j ≤ a := by
      by_cases hir : rates.interestRate = 0
      · have h1 := Loan.create_zero_rate_proof broker v principal rates fees schedule allowsOverpayment pending r
          hp (hnt' ▸ hst) hok hir
        simp only [RawLoan.toExact] at h1
        rw [hTV, htvv, hj] at h1
        have : (a : ℚ) = j := mul_right_cancel₀ hp10.ne' h1
        exact le_of_eq (by exact_mod_cast this.symm)
      · have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti' htvN hp hsub
        have hR' := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
        by_contra hc'
        push Not at hc'
        have h1 : props.totalValueOutstanding.toRat - principal.toRat ≤ 0 := by
          rw [htvv, hj]
          have : (a : ℚ) ≤ j := by exact_mod_cast hc'.le
          nlinarith
        have := Number.roundsToRepresentable_nonpos ti' _ hR' h1
        have := (Number.signum_pos_iff_toRat htiN).mp (hgt0 hir)
        linarith
    have hj16 : j < 10 ^ 16 := lt_of_le_of_lt hja ha16
    have hpov : props.principalOutstanding.toRat = principal.toRat :=
      STAmount.roundToNumericType_representable_grid .fractional principal _ .to_nearest props.loanScale hp hpos.le
        (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj (fun _ => hj16) hpo
    -- the fee is at most a tenth of the interest plus `10^-3` of a unit
    set K := a - j with hK
    have hKv : ti.toRat = (K : ℚ) * 10 ^ props.loanScale := by
      have hs : minExponent + 18 ≤ props.loanScale ∧ props.loanScale ≤ maxExponent - 1 := by
        unfold minExponent maxExponent; omega
      rw [Number.operator_sub_toRat_of_grid _ _ ti a j props.loanScale htvN hpoN (by rw [htvv]; norm_cast)
        (by rw [hpov, hj]; norm_cast) (by omega) hs hti, hK]
      push_cast [Nat.cast_sub hja]; ring
    have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
    obtain ⟨-, -, hmf_hi, ⟨mm, hmm⟩⟩ := computeManagementFee_bounds .fractional ti _ K broker.managementFeeRate
      props.loanScale (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) hKv (by omega) hR10
      ⟨hlo, hhi⟩ hint (fun _ => by omega) hmfo
    have hmf_hi' := hmf_hi (by omega)
    set D := (K * broker.managementFeeRate.toNat + 99) / 100 with hD
    have hD : D ≤ 100 * K + 1 := by
      have : K * broker.managementFeeRate.toNat ≤ K * 10000 := Nat.mul_le_mul_left K hR10
      omega
    have hpow3 : (10 : ℚ) ^ props.loanScale = 1000 * 10 ^ (props.loanScale - 3) := by
      rw [show props.loanScale = (props.loanScale - 3) + 3 by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num; ring
    have hp3 : (0 : ℚ) < 10 ^ (props.loanScale - 3) := zpow_pos (by norm_num) _
    have hmfq : props.managementFeeOutstanding.toRat ≤ ((100 * K + 1 : ℕ) : ℚ) * 10 ^ (props.loanScale - 3) :=
      hmf_hi'.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hp3.le)
    have hmm63 : mm < 2 ^ 63 := by
      have h1 : (mm : ℚ) * 1000 ≤ ((100 * K + 1 : ℕ) : ℚ) := by
        have := hmfq
        rw [hmm, hpow3, ← mul_assoc] at this
        exact le_of_mul_le_mul_right this hp3
      have h2 : mm * 1000 ≤ 100 * K + 1 := by exact_mod_cast h1
      omega
    have hiv := LoanState.build_interestDue_grid _ _ _ props.loanScale a j mm loanState htvN hp hmfN htvv hj hmm
      (by omega) hja hmm63 (by unfold minExponent maxExponent; omega) hchecks.state
    -- AssetsAvailable plus that interest would be past the Open limit
    have hopen := (Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiv.1 hchecks.open_zone).1
    have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
      have h1 := hchecks.funds
      by_contra hc'
      push Not at hc'
      rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
      exact absurd h1 (by decide)
    have hscale : (10 : ℚ) ^ (v.baseExponent - 1) ≤ 10 * 10 ^ (props.loanScale - 3) := by
      have h1 : (10 : ℚ) ^ (v.baseExponent - 1) = 10 * 10 ^ (v.baseExponent - 2) := by
        rw [show v.baseExponent - 1 = (v.baseExponent - 2) + 1 by ring, zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by norm_num)
    have hunits : (9 * 10 ^ 16 + 99 / 10 : ℚ) * 10 ^ (v.baseExponent - 1) ≤
        v.assetsAvailable.toRat + loanState.interestDue.toRat := by
      rw [hiv.2, htvv, hj, hpow3]
      have hKq : (K : ℚ) = a - j := by rw [hK]; push_cast [Nat.cast_sub hja]; ring
      have hmf : props.managementFeeOutstanding.toRat ≤ (100 * (a - j : ℚ) + 1) * 10 ^ (props.loanScale - 3) := by
        rw [← hKq]; push_cast at hmfq; exact hmfq
      have ha' : (10 : ℚ) ^ 15 ≤ a := by exact_mod_cast ha15
      have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj1
      have hpb : (0 : ℚ) < 10 ^ (v.baseExponent - 1) := zpow_pos (by norm_num) _
      have hfunds' : (j : ℚ) * (1000 * 10 ^ (props.loanScale - 3)) ≤ v.assetsAvailable.toRat := by
        rw [← hpow3, ← hj]; exact hfunds
      have hgoal : (9 * 10 ^ 16 + 99 / 10 : ℚ) * 10 ^ (v.baseExponent - 1) ≤
          (900 * a + 100 * j - 1) * 10 ^ (props.loanScale - 3) := by
        calc (9 * 10 ^ 16 + 99 / 10 : ℚ) * 10 ^ (v.baseExponent - 1)
            ≤ (9 * 10 ^ 16 + 99 / 10 : ℚ) * (10 * 10 ^ (props.loanScale - 3)) :=
              mul_le_mul_of_nonneg_left hscale (by norm_num)
          _ = (9 * 10 ^ 17 + 99 : ℚ) * 10 ^ (props.loanScale - 3) := by ring
          _ ≤ (900 * a + 100 * j - 1) * 10 ^ (props.loanScale - 3) :=
              mul_le_mul_of_nonneg_right (by nlinarith) hp3.le
      nlinarith
    push_cast at hopen
    have hlt : (90000000000000005 : ℚ) * 10 ^ (v.baseExponent - 1) <
        (9 * 10 ^ 16 + 99 / 10 : ℚ) * 10 ^ (v.baseExponent - 1) :=
      mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)
    linarith

/-- A new loan's total value is at least PrincipalRequested. -/
lemma Loan.create_principal_le_value (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault) (hp : principal.isNormalized)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    principal.toRat ≤ r.loan'.toExact.totalValueOutstanding := by
  by_cases hir : rates.interestRate = 0
  · exact le_of_eq (Loan.create_zero_rate_proof broker v principal rates fees schedule allowsOverpayment pending r
      hp hst hok hir).symm
  · have h1 := Loan.create_covers_principal_proof broker v principal rates fees schedule allowsOverpayment pending r
      hp hst hok hir
    have h2 := Loan.create_value_lower_bound_proof broker v principal rates fees schedule allowsOverpayment pending r
      hok hir
    linarith

end XRPL.Model.Lending
