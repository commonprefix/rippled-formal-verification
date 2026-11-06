import XRPL.Properties.Lending.Loan.Common.PrincipalLeft

/-! # A re-amortization keeps PeriodicPayment from vanishing

The extra principal of an overpayment is a whole number of LoanScale units, so a re-amortization that passes charges
a PeriodicPayment of at least `10^-40` on a loan whose LoanScale is at least `-10`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.tryOverpayment from XRPL.Model.Lending.Loan.LoanPay
open private Number.max_isNormalized' from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Number.max_val from XRPL.Properties.Lending.Loan.Common.InterestDue
open private LoanState.buildTheoretical_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private computeLoanPropertiesFromPeriodicRate_pp from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces

local notation "ε" => Number.nearestError

/-- A positive amount on a grid is at least one unit of it. -/
private lemma Number.OnGrid.unit_le {s : Int} {x : Number} (hx : Number.OnGrid s x) (h0 : 0 < x.toRat) :
    (10 : ℚ) ^ s ≤ x.toRat := by
  obtain ⟨-, k, hk⟩ := hx
  have hD : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hk0 : (0 : ℚ) < k := by
    by_contra hc
    push Not at hc
    rw [hk] at h0
    nlinarith
  have hk1 : (1 : ℚ) ≤ k := by
    have : 0 < k := Int.cast_pos.mp hk0
    exact_mod_cast this
  rw [hk]
  nlinarith

/-- A re-amortization that passes charges a PeriodicPayment of at least `10^-40`, on a loan whose LoanScale is
at least `-10`. The theoretical principal less the extra principal is a positive multiple of `10^-28`. -/
private lemma Loan.tryOverpayment_periodic_ge (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -10 ≤ l.loanScale) (hδg : Number.OnGrid l.loanScale opc.principalDelta)
    (hδ0 : 0 < opc.principalDelta.toRat) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    1 / 10 ^ 40 ≤ re.periodicPayment.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hunit := hδg.unit_le hδ0
  have hδN := hδg.1
  obtain ⟨-, k, hk⟩ := hδg
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  rename_i _ rate hrate _ st hst _ th hth _ de hde _ rp0 hrp0 _ props hprops _ s1 hs1 _ s2 hs2 _ pin hpin _ gi hgi
    _ pmf hpmf _ s3 hs3 _ po hpo _ int hintr _ tvo htvo _ tvo' htvo' _ mfo hmfo _ s4 hs4 _ dl hdl _ io hio _ g hg
    hgs _ _ _ hsig _ hle _ hneg _ _ fee hfee hw
  obtain ⟨hrN, h0r, hlow, -⟩ := Loan.periodicRate_bounds l rate hrate
  -- the re-amortized principal is positive, or the new PeriodicPayment would be zero
  have hthN := (LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm hrN hth).2.1
  have hrp0N := operator_sub_isNormalized_to_nearest_sz _ _ _ hthN hδN hrp0
  have hmaxN := Number.max_isNormalized' hrp0N Number.zero_isNormalized
  have hpp := computeLoanPropertiesFromPeriodicRate_pp _ _ _ _ _ _ _ hprops
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hmaxN hrN hpp
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at hsig
  have hpp0 := (Number.signum_pos_iff_toRat hppN).mp hsig.1.1
  have hrp : 0 < rp0.toRat := by
    by_contra hle0
    push Not at hle0
    have hmax : rp0.max Number.zero = Number.zero := by
      have hv := Number.max_val _ _ hrp0N Number.zero_isNormalized
      rw [Number.toRat_zero, max_eq_right hle0] at hv
      exact (Number.toRat_eq_zero_iff_eq_zero hmaxN).mp hv
    rw [hmax] at hpp
    have h0 : loanPeriodicPayment Number.zero rate l.paymentRemaining = .ok Number.zero := by
      simp [loanPeriodicPayment, show Number.zero.operator_eq Number.zero = true from rfl]
    rw [h0, Except.ok.injEq] at hpp
    rw [← hpp, Number.toRat_zero] at hpp0
    exact lt_irrefl _ hpp0
  have hthδ : opc.principalDelta.toRat < th.principalOutstanding.toRat := by
    by_contra hle1
    push Not at hle1
    have := Number.roundsToRepresentable_nonpos _ _
      (operator_sub_rounded_to_nearest _ _ _ hthN hδN hrp0) (by linarith)
    linarith
  -- the theoretical principal is at least `10^-10`, so its exponent is at least `-28`
  have hth0 : 0 < th.principalOutstanding.toRat := lt_trans hδ0 hthδ
  have hm0 : th.principalOutstanding.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_iff.mpr h0] at hth0; exact lt_irrefl _ hth0
  have hmb := mantissaBounds_nat_of (hthN.mantissaBounds hm0)
  have hxv := Number.toRat_of_nonneg _ (Number.negative_false_of_nonneg _ hthN hth0.le)
  have he28 : -28 ≤ th.principalOutstanding.exponent_ := by
    by_contra hlt
    push Not at hlt
    have hsmall : th.principalOutstanding.toRat < 10 ^ (-10 : ℤ) := by
      rw [hxv]
      calc (th.principalOutstanding.mantissa_.toNat : ℚ) * 10 ^ th.principalOutstanding.exponent_
          < 10 ^ (19 : ℕ) * 10 ^ th.principalOutstanding.exponent_ :=
            mul_lt_mul_of_pos_right (by exact_mod_cast hmb.2) (zpow_pos (by norm_num) _)
        _ ≤ 10 ^ (19 : ℕ) * 10 ^ (-29 : ℤ) := by
            gcongr
            · norm_num
            · omega
        _ = 10 ^ (-10 : ℤ) := by norm_num
    have : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ l.loanScale := zpow_le_zpow_right₀ (by norm_num) hlo
    linarith
  -- the difference is a positive whole number of `10^g` with `g = min e s ≥ -28`
  obtain ⟨a, ha⟩ : ∃ a : ℕ, th.principalOutstanding.exponent_ =
      min th.principalOutstanding.exponent_ l.loanScale + a :=
    ⟨(th.principalOutstanding.exponent_ - min th.principalOutstanding.exponent_ l.loanScale).toNat, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, l.loanScale = min th.principalOutstanding.exponent_ l.loanScale + b :=
    ⟨(l.loanScale - min th.principalOutstanding.exponent_ l.loanScale).toNat, by omega⟩
  set gg := min th.principalOutstanding.exponent_ l.loanScale with hgg
  have hD : (0 : ℚ) < 10 ^ gg := zpow_pos (by norm_num) _
  set c : ℤ := (th.principalOutstanding.mantissa_.toNat : ℤ) * 10 ^ a - k * 10 ^ b with hc
  have hcv : th.principalOutstanding.toRat - opc.principalDelta.toRat = (c : ℚ) * 10 ^ gg := by
    rw [hxv, hk, hc]
    conv_lhs => rw [ha, hb]
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast,
      zpow_natCast]
    push_cast; ring
  have hc0 : (0 : ℚ) < c := by
    have : (0 : ℚ) < (c : ℚ) * 10 ^ gg := by rw [← hcv]; linarith
    exact pos_of_mul_pos_left this hD.le
  have hc1 : (1 : ℚ) ≤ c := by
    have : (0 : ℤ) < c := by exact_mod_cast hc0
    exact_mod_cast this
  have hdiff : (1 : ℚ) / 10 ^ 28 ≤ th.principalOutstanding.toRat - opc.principalDelta.toRat := by
    rw [hcv]
    calc (1 : ℚ) / 10 ^ 28 = 10 ^ (-28 : ℤ) := by norm_num
      _ ≤ 10 ^ gg := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ (c : ℚ) * 10 ^ gg := le_mul_of_one_le_left hD.le hc1
  -- so the re-amortized principal and the new PeriodicPayment are not small
  have hrpge := (Number.sub_near _ _ _ hthN hδN hrp0).ge (ne_of_gt hrp) (by linarith)
  have hmaxv : (rp0.max Number.zero).toRat = rp0.toRat := by
    rw [Number.max_val _ _ hrp0N Number.zero_isNormalized, Number.toRat_zero, max_eq_left hrp.le]
  have hB : 1 / 10 ^ 28 * (1 - ε) ≤ (rp0.max Number.zero).toRat := by
    rw [hmaxv]
    calc 1 / 10 ^ 28 * (1 - ε) ≤ (th.principalOutstanding.toRat - opc.principalDelta.toRat) * (1 - ε) := by
          gcongr; linarith
      _ ≤ rp0.toRat := hrpge
  have hge := loanPeriodicPayment_ge _ _ _ _ _ (mul_nonneg (by norm_num) (by linarith)) hmaxN hB hrN h0r hlow
    (ne_of_gt hpp0) hpp
  show 1 / 10 ^ 40 ≤ props.periodicPayment.toRat
  calc (1 : ℚ) / 10 ^ 40 ≤ 1 / 10 ^ 28 * (1 - 1 / 10 ^ 18) * (1 - 1 / 10 ^ 18) ^ 4 / (3 * 2 ^ 32) := by norm_num
    _ ≤ 1 / 10 ^ 28 * (1 - ε) * (1 - ε) ^ 4 / (3 * 2 ^ 32) := by
        have : (0 : ℚ) ≤ 1 / 10 ^ 28 * (1 - ε) := mul_nonneg (by norm_num) (by linarith)
        gcongr
    _ ≤ _ := hge

end XRPL.Model.Lending
