import XRPL.Properties.Lending.Loan.Common.FullPaymentSize

/-! # What an early payoff costs against the remaining schedule

With no CloseInterestRate a payoff charges PrincipalOutstanding, the accrued interest floored and ClosePaymentFee. With
ClosePaymentFee at most LoanServiceFee and one period of interest booked, that is at most the payments left. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.fullComponents roundAndSplitInterest Loan.unimpairIfImpaired from XRPL.Model.Lending.Loan.LoanPay
open private Loan.payInstalment_parts computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps
open private Number.OnGrid.unitsAt from XRPL.Properties.Lending.Loan.Common.FullPaymentSize

local notation "ε" => Number.nearestError

/-- A full payment's totalPaid is the totalDue of the loan's payoff components. -/
private lemma Loan.fullPay_parts (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v .full amount now).run = .ok (.ok p)) :
    ∃ pc, Loan.fullComponents loan now = .ok pc ∧ pc.totalDue = .ok p.totalPaid := by
  simp only [Loan.payInstalments] at hp
  unfold_ter at hp
  walk_ok
  rename_i a hu _ _ pc hpc _ hpi
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨l1, p1⟩ := a
  simp only at hl hpc hpi
  subst hl
  obtain ⟨hdue, -, -⟩ :=
    Loan.payInstalment_parts loan.unimpaired p1 pc amount p (by simp only [ExceptT.run]; exact hpi)
  exact ⟨pc, by rw [← Loan.fullComponents_unimpaired]; exact hpc, hdue⟩

/-- With no CloseInterestRate the interest of a payoff is the interest accrued since the last payment, at most one
period on the theoretical principal plus three roundings up. -/
private lemma computeFullPaymentInterest_le_period (tpo rate : Number) (now interval prev start : UInt32) (fi : Number)
    (htpo : tpo.isNormalized) (htpo0 : 0 ≤ tpo.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hdue : now.toNat ≤ (if prev < start then start else prev).toNat + interval.toNat)
    (h : computeFullPaymentInterest tpo rate now interval prev start 0 = .ok fi) :
    fi.toRat ≤ tpo.toRat * rate.toRat * (1 + ε) ^ 3 := by
  unfold computeFullPaymentInterest at h
  obtain ⟨acc, hacc, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨-, -, hle⟩ := loanAccruedInterest_le_period tpo rate now start prev interval acc htpo htpo0 hrate hr0 hdue
    hacc
  simp only [beq_self_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind, Number.operator_add_zero_right,
    Except.ok.injEq] at h
  rw [← h]
  exact hle

/-- A fee of `2^62` units or more absorbs the rounding of a sum that adds the fee to at most `1.5·10^18` units. -/
private lemma large_fee_bound (X B C u e vpi uf cfm due : ℚ) (hu : 0 < u) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 10 ^ 18)
    (hX0 : 0 ≤ X) (hXb : X ≤ 10 ^ 16 + 2 + 143 * (10 ^ 16 + 1)) (hB0 : 0 ≤ B) (hBb : B ≤ 143 * (10 ^ 16 + 1))
    (hC : 2 ^ 62 ≤ C) (hvpi : vpi = X * u) (hcfm : cfm ≤ (C * u + B * u) * (1 + e))
    (huf : uf ≤ cfm * (1 + e)) (hdue : due ≤ max (vpi + uf) 0 * (1 + e)) : due ≤ 2 * C * u := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have h1 : uf ≤ (C + B) * u * ((1 + e) * (1 + e)) := by
    calc uf ≤ cfm * (1 + e) := huf
      _ ≤ (C * u + B * u) * (1 + e) * (1 + e) := mul_le_mul_of_nonneg_right hcfm (by linarith)
      _ = (C + B) * u * ((1 + e) * (1 + e)) := by ring
  have h2 : max (vpi + uf) 0 ≤ X * u + (C + B) * u * ((1 + e) * (1 + e)) := by
    refine max_le (by rw [hvpi]; linarith) ?_
    have : 0 ≤ (C + B) * u * ((1 + e) * (1 + e)) := by positivity
    have : 0 ≤ X * u := mul_nonneg hX0 hu.le
    linarith
  have he3 : (1 + e) * (1 + e) * (1 + e) ≤ 1 + 4 * e := by
    have hee : e * e ≤ e * (1 / 10 ^ 18) := mul_le_mul_of_nonneg_left he1 he0
    have heee : e * e * e ≤ e * e := by nlinarith [mul_nonneg he0 he0]
    nlinarith
  have h3 : (X * u + (C + B) * u * ((1 + e) * (1 + e))) * (1 + e) ≤ (X * (1 + e) + (C + B) * (1 + 4 * e)) * u := by
    have : (X * u + (C + B) * u * ((1 + e) * (1 + e))) * (1 + e) =
        (X * (1 + e) + (C + B) * ((1 + e) * (1 + e) * (1 + e))) * u := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hu.le
    have : (C + B) * ((1 + e) * (1 + e) * (1 + e)) ≤ (C + B) * (1 + 4 * e) :=
      mul_le_mul_of_nonneg_left he3 (by linarith)
    linarith
  have h4 : X * (1 + e) + (C + B) * (1 + 4 * e) ≤ 2 * C := by
    have : X * e ≤ X * (1 / 10 ^ 18) := mul_le_mul_of_nonneg_left he1 hX0
    have : (C + B) * e ≤ (C + B) * (1 / 10 ^ 18) := mul_le_mul_of_nonneg_left he1 (by linarith)
    nlinarith
  calc due ≤ max (vpi + uf) 0 * (1 + e) := hdue
    _ ≤ (X * u + (C + B) * u * ((1 + e) * (1 + e))) * (1 + e) := mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ (X * (1 + e) + (C + B) * (1 + 4 * e)) * u := h3
    _ ≤ 2 * C * u := mul_le_mul_of_nonneg_right h4 hu.le

/-- Proof body of `fullPayment_cheaper`. -/
lemma Loan.fullPayment_cheaper_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (hreach : loan.Reachable t) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments v .full amount now).run = .ok (.ok p))
    (hclose : loan.rates.closeInterestRate = 0)
    (hfee : loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat)
    (hcover : ∀ rate tpo : Number, loan.periodicRate = .ok rate →
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo →
      tpo.toRat * rate.toRat ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat) :
    p.totalPaid.toRat ≤
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat := by
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hint0 := hreach.loanScale_integral
  have hu0 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  -- the checks: the payoff is not late and the loan has two or more payments left
  have hchk := (Loan.payInstalments_ok loan v .full amount now p hp).1
  have hnl : now ≤ loan.nextPaymentDueDate := by
    have := hchk.not_late (by decide)
    rw [UInt32.lt_iff_toNat_lt] at this
    rw [UInt32.le_iff_toNat_le]; omega
  have hn : 2 ≤ loan.paymentRemaining.toNat := by
    have h1 := hchk.more_than_one
    rw [UInt32.le_iff_toNat_le] at h1
    simp at h1; omega
  have hl0 : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn
  obtain ⟨pc, hpc, hdue⟩ := Loan.fullPay_parts loan v amount now p hp
  obtain ⟨rate, tpo, fi, net, split, state, cf, ppi, tracked, cfm, uf, ui, hrate, htpo, hfi, hsplit,
    hstate, hcf, hppi, htracked, hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv loan now pc hpc
  obtain ⟨fl, hfloor, hsp, hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  obtain ⟨hfN, hf0, hfB⟩ := hreach.fullInterest_le now rate tpo fi hnl hn hrate htpo hfi
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrate
  have hr0 := loanPeriodicRate_nonneg _ _ rate hrate
  obtain ⟨htpo0, -, -⟩ := loanPrincipalFromPeriodicPayment_le_payments _ _ _ _ loan.wf.periodicPayment_norm
    loan.exact.periodicPayment_pos.le hrN hr0 htpo
  have htpoN : tpo.isNormalized := by
    unfold loanPrincipalFromPeriodicPayment at htpo
    dsimp only at htpo
    split at htpo
    · simp only [pure, Except.pure, Except.ok.injEq] at htpo; subst htpo; exact Number.zero_isNormalized
    · obtain ⟨_, -, htpo⟩ := bind_ok_peel _ _ _ htpo
      split at htpo
      · exact Number.operator_mul_isNormalized _ _ _ _ loan.wf.periodicPayment_norm (Number.ofInt64_isNormalized _)
          htpo
      · obtain ⟨f, hf, htpo⟩ := bind_ok_peel _ _ _ htpo
        exact Number.operator_div_isNormalized _ _ _ _ loan.wf.periodicPayment_norm
          (computePaymentFactor_isNormalized rate _ _ f hrN (Number.ofInt64_isNormalized _) hf) htpo
  have hdueT : now.toNat ≤ (if loan.previousPaymentDueDate < loan.schedule.startDate then loan.schedule.startDate
      else loan.previousPaymentDueDate).toNat + loan.schedule.paymentInterval.toNat :=
    le_trans (UInt32.le_iff_toNat_le.mp hnl) (hreach.paymentRoom.lastDue hl0)
  rw [hclose] at hfi
  have hacc := computeFullPaymentInterest_le_period tpo rate now _ _ _ fi htpoN htpo0 hrN hr0 hdueT hfi
  have hcov := hcover rate tpo hrate htpo
  -- the floored interest `a`, its fee `b ≤ a` and ClosePaymentFee `c`, in LoanScale units
  have hfiN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfloor
  have hfi0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfN hf0 (Or.inr (Or.inr rfl)) hs81 hfloor
  have hfi_le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfN hf0 hs81 hfloor
  obtain ⟨a, hav, hav'⟩ := Number.OnGrid.unitsAt (STAmount.roundToNumericType_onGrid _ _ _ _ _ hs81 hint hfloor) hfi0
  obtain ⟨gfee, hfee0, hfee_le⟩ := computeManagementFee_le _ _ _ _ _ hfiN hfi0 loan.broker.managementFeeRate_le
    hs81 hint hsp
  obtain ⟨b, hbv, hbv'⟩ := Number.OnGrid.unitsAt gfee hfee0
  have hab : b ≤ a := by
    have : (b : ℚ) * 10 ^ loan.loanScale ≤ (a : ℚ) * 10 ^ loan.loanScale := by rw [← hbv', ← hav']; exact hfee_le
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have ha : a ≤ 143 * (10 ^ 16 + 1) := by
    have : (a : ℚ) * 10 ^ loan.loanScale ≤ ((143 * (10 ^ 16 + 1) : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hav']; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  obtain ⟨-, -, gcf⟩ := Loan.Reachable.fees_onGrid hreach
  have hcf0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hrep := hreach.fees_representable loan.fees.closePaymentFee (by simp [LoanFees.amountFields])
  have hcfv := STAmount.roundToNumericType_of_representable _ _ _ _ loan.wf.closePaymentFee_norm hcf0 hs81 hint0 hrep
    gcf hcf
  have gcf' : Number.OnGrid loan.loanScale cf :=
    ⟨STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf, by obtain ⟨-, k, hk⟩ := gcf; exact ⟨k, by rw [hcfv, hk]⟩⟩
  obtain ⟨c, hcv, hcv'⟩ := Number.OnGrid.unitsAt gcf' (by rw [hcfv]; exact hcf0)
  obtain ⟨tN, pN, mN, -, -, -, htv, hpv, hmv, hiv, hge, h1, hpo, hm1⟩ := Loan.state_units loan state hstate
  have hTv : loan.totalValueOutstanding.toRat = (tN : ℚ) * 10 ^ loan.loanScale := by rw [← h1]; exact htv.val
  have hPv : loan.principalOutstanding.toRat = (pN : ℚ) * 10 ^ loan.loanScale := by rw [← hpo]; exact hpv.val
  have ht : tN ≤ 10 ^ 16 + 1 := by
    have hT := hreach.totalValue_le
    have : (tN : ℚ) * 10 ^ loan.loanScale ≤ ((10 ^ 16 + 1 : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hTv]; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have hat : (a : ℤ) ≤ (tN : ℤ) - pN := by
    have h3 : (1 + ε) ^ 3 ≤ 1 + 6 * ε := by
      have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
      push_cast at this; linarith
    have hle : (a : ℚ) * 10 ^ loan.loanScale ≤ ((tN : ℚ) - pN) * 10 ^ loan.loanScale * (1 + ε) ^ 3 := by
      rw [← hav']
      calc fl.toRat ≤ fi.toRat := hfi_le
        _ ≤ tpo.toRat * rate.toRat * (1 + ε) ^ 3 := hacc
        _ ≤ (loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat) * (1 + ε) ^ 3 := by gcongr
        _ = ((tN : ℚ) - pN) * 10 ^ loan.loanScale * (1 + ε) ^ 3 := by rw [hTv, hPv]; ring
    have hle' : (a : ℚ) ≤ ((tN : ℚ) - pN) * (1 + ε) ^ 3 := by
      refine le_of_mul_le_mul_right ?_ hu0
      rw [show ((tN : ℚ) - pN) * (1 + ε) ^ 3 * 10 ^ loan.loanScale = ((tN : ℚ) - pN) * 10 ^ loan.loanScale * (1 + ε) ^ 3
        by ring]
      exact hle
    have hlt : (a : ℚ) < (tN : ℚ) - pN + 1 := by
      rcases le_total ((tN : ℚ) - pN) 0 with h0 | h0
      · have : ((tN : ℚ) - pN) * (1 + ε) ^ 3 ≤ (tN : ℚ) - pN := by
          nlinarith [one_le_pow₀ (show (1 : ℚ) ≤ 1 + ε by linarith) (n := 3)]
        linarith
      · have htq : ((tN : ℚ) - pN) ≤ 10 ^ 16 + 1 := by
          have : (pN : ℚ) ≥ 0 := by positivity
          have : (tN : ℚ) ≤ 10 ^ 16 + 1 := by exact_mod_cast ht
          linarith
        nlinarith
    have : (a : ℤ) < (tN : ℤ) - pN + 1 := by exact_mod_cast hlt
    omega
  -- LoanServiceFee covers ClosePaymentFee on each of the two or more payments left
  have hsf0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hn2 : (2 : ℚ) ≤ loan.paymentRemaining.toNat := by exact_mod_cast hn
  have hcu : cf.toRat = (c : ℚ) * 10 ^ loan.loanScale := hcv'
  have hcfe : cf.toRat = loan.fees.closePaymentFee.toRat := hcfv
  have hrhs : (tN : ℚ) * 10 ^ loan.loanScale + 2 * ((c : ℚ) * 10 ^ loan.loanScale) ≤
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat := by
    rw [hTv, ← hcu, hcfe]; nlinarith
  -- totalDue adds the value cleared, the interest beyond interestDue and the fees beyond the management fee
  unfold PaymentComponents.totalDue at hdue
  obtain ⟨vpi, hvpi, hd⟩ := bind_ok_peel _ _ _ hdue
  dsimp only at hvpi hd
  have hs := Loan.loanScale_bounds loan
  have hppi' := UnitsAt.add hpv hiv (by constructor <;> omega) hs hppi
  have htr := UnitsAt.add hppi' hmv (by constructor <;> omega) hs htracked
  have hnet' := UnitsAt.sub hav hbv (by constructor <;> omega) hs hnet
  have hui' := UnitsAt.sub hnet' hiv (by constructor <;> omega) hs hui
  have hvpi' := UnitsAt.add htr hui' (by constructor <;> omega) hs hvpi
  have h3 : (1 + ε) ^ 3 ≤ 1 + 6 * ε := by
    have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
    push_cast at this; linarith
  by_cases hc : c < 2 ^ 62
  · -- every sum is exact: totalDue is PrincipalOutstanding + floored interest + ClosePaymentFee
    have hcfm' := UnitsAt.add hcv hbv (by constructor <;> omega) hs hcfm
    have huf' := UnitsAt.sub hcfm' hmv (by constructor <;> omega) hs huf
    have hd' := UnitsAt.add hvpi' huf' (by constructor <;> omega) hs hd
    have hval : p.totalPaid.toRat = ((pN : ℚ) + a + c) * 10 ^ loan.loanScale := by
      rw [hd'.val]; push_cast; ring
    have hat' : (a : ℚ) ≤ (tN : ℚ) - pN := by exact_mod_cast hat
    rw [hval]
    nlinarith
  · -- a ClosePaymentFee of `2^62` units or more dwarfs the rounding of the fee sums
    push Not at hc
    have hC : (2 : ℚ) ^ 62 ≤ c := by exact_mod_cast hc
    have hcfN := gcf'.1
    have hspN := gfee.1
    have hcfm0 : 0 ≤ cfm.toRat := operator_add_nonneg _ _ _ hcfN hspN hcfm (by rw [hcu]; positivity)
    have hcfmN := operator_add_isNormalized_to_nearest_sz _ _ _ hcfN hspN hcfm
    have hcfm_le := (Number.add_near _ _ _ hcfN hspN hcfm).le (by rw [hcu]; positivity)
    have hufN := operator_sub_isNormalized_to_nearest_sz _ _ _ hcfmN hmv.norm huf
    have huf_le := (Number.sub_near _ _ _ hcfmN hmv.norm huf).le_max
    have hd_le := (Number.add_near _ _ _ hvpi'.norm hufN hd).le_max
    have hM0 : 0 ≤ state.managementFeeDue.toRat := by rw [hmv.val]; positivity
    have huf_le' : uf.toRat ≤ cfm.toRat * (1 + ε) := by
      refine le_trans huf_le (mul_le_mul_of_nonneg_right ?_ (by linarith))
      exact max_le (by linarith) hcfm0
    have hX : vpi.toRat =
        (((pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) : ℤ) : ℚ) * 10 ^ loan.loanScale :=
      hvpi'.val
    have hXv : vpi.toRat = ((pN : ℚ) + mN + a - b) * 10 ^ loan.loanScale := by rw [hX]; push_cast; ring
    have hpm : (pN : ℚ) + mN ≤ 10 ^ 16 + 2 := by
      have : (pN : ℤ) + mN ≤ 10 ^ 16 + 2 := by omega
      exact_mod_cast this
    have haq : (a : ℚ) ≤ 143 * (10 ^ 16 + 1) := by exact_mod_cast ha
    have hbq : (b : ℚ) ≤ a := by exact_mod_cast hab
    have hX0 : 0 ≤ (pN : ℚ) + mN + a - b := by
      have h0 : (0 : ℚ) ≤ (pN : ℚ) + mN := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith only [h0, hbq]
    have hsp : split.toRat = (b : ℚ) * 10 ^ loan.loanScale := hbv'
    have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
    have hXb : (pN : ℚ) + mN + a - b ≤ 10 ^ 16 + 2 + 143 * (10 ^ 16 + 1) := by linarith only [hpm, haq, hb0]
    have hle := large_fee_bound ((pN : ℚ) + mN + a - b) b c (10 ^ loan.loanScale) ε vpi.toRat uf.toRat cfm.toRat
      p.totalPaid.toRat hu0 he.le he' hX0 hXb hb0 (by linarith only [hbq, haq]) hC hXv
      (by rw [hcu, hsp] at hcfm_le; exact hcfm_le) huf_le' hd_le
    have ht0 : (0 : ℚ) ≤ (tN : ℚ) * 10 ^ loan.loanScale := mul_nonneg (Nat.cast_nonneg _) hu0.le
    linarith only [hle, ht0, hrhs]

end XRPL.Model.Lending
