import XRPL.Properties.Lending.Loan.Common.FullPaymentSize
import XRPL.Properties.Lending.Loan.Common.PayPrincipal

/-! # How much principal and interest a payment of a reachable loan pays

A payment pays as interest the loan's own interest, late interest of at most 138 times PrincipalOutstanding, the
payoff interest or an overpayment's interest. With the principal that is at most `300·(10^16 + 1)` LoanScale units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.doPayment
  UnsettledPayment.payInstalments UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.overpaymentComponents
  roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Loan.lateComponents_parts computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private UnsettledPayment.payInstalments_interestPaid Loan.tryOverpayment_interestDue_le
  from XRPL.Properties.Lending.Loan.Common.InterestMonotone
open private Loan.lateComponents_scheduled Loan.scheduledComponents_sound Loan.payInstalments_below
  from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.unimpaired_same from XRPL.Properties.Lending.Loan.Common.InterestDue

local notation "ε" => Number.nearestError

/-- Rounding to nearest at a scale gives at most twice the value, plus one unit, plus one. A rounding that
keeps sixteen digits moves the value by at most half of its last digit. -/
lemma STAmount.roundToNumericType_to_nearest_le (nt : NumericType) (x T : Number) (s : ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType nt x .to_nearest (some s) = .ok T) :
    T.toRat ≤ 2 * x.toRat + 10 ^ s + 1 := by
  have hu : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    obtain ⟨hgf, -, -, -⟩ := STAmount.roundToNumericType_int_grid _ rfl x T .to_nearest _ hx h0 (Or.inl rfl) hok
    have h1 := hgf.le_ceil h0
    simp only [zpow_zero, div_one, mul_one] at h1
    have h2 : (⌈x.toRat⌉ : ℚ) < x.toRat + 1 := Int.ceil_lt_add_one _
    linarith
  | fractional =>
    rw [hnt] at hok
    by_cases hexp : ∀ st, STAmount.ofNumber .fractional x .to_nearest = .ok st → st.mValue ≠ 0 → st.exponent ≤ s
    · obtain ⟨hgf, -, -, -⟩ := STAmount.roundToNumericType_frac_grid x T .to_nearest s hx h0 (Or.inl rfl) hs hexp hok
      have h1 := hgf.le_ceil h0
      have h2 : (⌈x.toRat / 10 ^ s⌉ : ℚ) < x.toRat / 10 ^ s + 1 := Int.ceil_lt_add_one _
      have h3 : (⌈x.toRat / 10 ^ s⌉ : ℚ) * 10 ^ s ≤ x.toRat + 10 ^ s := by
        have := mul_le_mul_of_nonneg_right h2.le hu.le
        rw [add_mul, div_mul_cancel₀ _ hu.ne'] at this
        linarith
      linarith
    · push Not at hexp
      obtain ⟨st, hst, hmv, hlt⟩ := hexp
      -- the amount keeps its exponent above the scale, so the rounding at the scale leaves it alone
      unfold STAmount.roundToNumericType at hok
      rw [hst] at hok
      simp only at hok
      have hty := STAmount.ofNumber_mNumericType _ _ _ st hst
      have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
      rw [if_neg (by rw [hint]; decide)] at hok
      have hre : STAmount.roundToExponent st s .to_nearest = .ok st := by
        unfold STAmount.roundToExponent
        rw [if_neg (by rw [hint]; decide), if_neg (by unfold STAmount.isZero; simpa using hmv),
          if_pos (le_of_lt hlt)]
      rw [hre] at hok
      simp only at hok
      have hc := STAmount.ofNumber_exactCanonical _ _ _ st hx h0 hst hmv
      have hiou := hc.iouCanonical hint
      obtain ⟨hTv, -⟩ := STAmount.toNumber_exact_of st T hc hok
      have hneg := Number.negative_false_of_nonneg x hx h0
      have hst0 := STAmount.ofNumber_nonneg _ _ _ st hx hneg hst
      have hpos : 0 < st.toRat := by
        rcases lt_or_eq_of_le hst0 with h' | h'
        · exact h'
        · exfalso
          have habs := STAmount.abs_toRat st
          rw [← h', abs_zero] at habs
          have : (st.mValue.toNat : ℚ) = 0 := by
            have hp : (0 : ℚ) < 10 ^ st.mOffset := zpow_pos (by norm_num) _
            nlinarith [show (0 : ℚ) ≤ st.mValue.toNat from by positivity]
          exact hmv (by exact_mod_cast UInt64.toNat_inj.mp (by exact_mod_cast this))
      obtain ⟨hlo, -⟩ := hiou.toRat_bounds st hpos
      have hhalf := STAmount.ofNumber_to_nearest_within_half _ _ st hx h0 hst hmv
      have h15 : (10 : ℚ) ^ (st.exponent + 15) = 10 ^ st.exponent * 10 ^ 15 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      rw [h15] at hlo
      have hle := (abs_le.mp hhalf).2
      rw [hTv]
      nlinarith [zpow_pos (show (0 : ℚ) < 10 by norm_num) st.exponent]

/-- A periodic rate of at most 100% over at most `2^32` seconds is at most 137. -/
private lemma loanPeriodicRate_le_cap (ir : TenthBips32) (interval : UInt32) (rate : Number)
    (hir : ir.toNat ≤ 100000) (h : loanPeriodicRate ir interval = .ok rate) :
    rate.isNormalized ∧ 0 ≤ rate.toRat ∧ rate.toRat ≤ 137 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have heq : loanPeriodicRate ir interval =
      (tenthBipsOfValue (Number.ofInt64 interval.toUInt64.toInt64) ir .to_nearest) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨tb, htb, h⟩ := bind_ok_peel _ _ _ h
  have hin := Number.ofInt64_isNormalized interval.toUInt64.toInt64
  have hiv := Number.ofInt64_count interval
  obtain ⟨htbN, htb0, htble⟩ := tenthBipsOfValue_le_share _ _ _ hin (by rw [hiv]; positivity) htb
  obtain ⟨hyn, hyv⟩ := TenthBips32.toNumber_facts (31536000 : UInt32)
  have hy : secondsInYear = TenthBips32.toNumber (31536000 : UInt32) := rfl
  rw [hy] at h
  have hyv' : ((31536000 : UInt32).toNat : ℚ) = 31536000 := rfl
  refine ⟨Number.operator_div_isNormalized _ _ _ _ htbN hyn h,
    rn_nonneg (operator_div_rounded_to_nearest _ _ _ htbN hyn h) (by rw [hyv, hyv']; positivity), ?_⟩
  have hle := (Number.div_near _ _ _ htbN hyn h).le (by rw [hyv, hyv']; positivity)
  rw [hyv, hyv'] at hle
  rw [hiv] at htble
  have hI : (interval.toNat : ℚ) ≤ 2 ^ 32 := by exact_mod_cast interval.toNat_lt.le
  have hr : (ir.toNat : ℚ) / 100000 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast hir
  have h3 := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
  push_cast at h3
  have hpow : (1 + ε) ^ 2 * (1 + ε) = (1 + ε) ^ 3 := by ring
  calc rate.toRat ≤ tb.toRat / 31536000 * (1 + ε) := hle
    _ ≤ interval.toNat * (ir.toNat / 100000) * (1 + ε) ^ 2 / 31536000 * (1 + ε) := by gcongr
    _ = interval.toNat * (ir.toNat / 100000) / 31536000 * ((1 + ε) ^ 2 * (1 + ε)) := by ring
    _ ≤ 2 ^ 32 * 1 / 31536000 * (1 + 6 * ε) := by
        rw [hpow]; gcongr; linarith
    _ ≤ 137 := by nlinarith

/-- The late interest is at most 138 times PrincipalOutstanding. -/
private lemma loanLatePaymentInterest_le (l : Loan) (now : UInt32) (li : Number)
    (h : loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate = .ok li) :
    li.isNormalized ∧ 0 ≤ li.toRat ∧ li.toRat ≤ 138 * l.principalOutstanding.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hzero : li = Number.zero → li.isNormalized ∧ 0 ≤ li.toRat ∧ li.toRat ≤ 138 * l.principalOutstanding.toRat :=
    fun hz => by subst hz; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], by
      rw [Number.toRat_zero]; positivity⟩
  unfold loanLatePaymentInterest at h
  by_cases h1 : l.principalOutstanding.operator_eq Number.zero = true
  · simp only [h1, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact hzero h.symm
  by_cases h2 : (l.rates.lateInterestRate == 0) = true
  · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq, bind, Except.bind] at h
    exact hzero h.symm
  by_cases h3 : now ≤ l.nextPaymentDueDate
  · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq, bind,
      Except.bind] at h
    exact hzero h.symm
  simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, bind, Except.bind] at h
  split at h
  · cases h
  rename_i rate hrate
  obtain ⟨hrN, hr0, hr137⟩ := loanPeriodicRate_le_cap _ _ rate l.exact.lateInterestRate_cap hrate
  have hle := (Number.mul_near _ _ _ l.wf.principalOutstanding_norm hrN h).le (mul_nonneg hP0 hr0)
  refine ⟨Number.operator_mul_isNormalized _ _ _ _ l.wf.principalOutstanding_norm hrN h,
    rn_nonneg (operator_mul_rounded_to_nearest _ _ _ l.wf.principalOutstanding_norm hrN h) (mul_nonneg hP0 hr0), ?_⟩
  calc li.toRat ≤ l.principalOutstanding.toRat * rate.toRat * (1 + ε) := hle
    _ ≤ l.principalOutstanding.toRat * 137 * (1 + 1 / 10 ^ 18) := by gcongr
    _ ≤ 138 * l.principalOutstanding.toRat := by nlinarith

/-- The untracked interest of a late instalment is at most `276` times PrincipalOutstanding plus one unit and one,
times one rounding. The late interest is rounded at LoanScale and its management fee comes off it. -/
private lemma Loan.lateComponents_interest_le (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (h : Loan.lateComponents l now = .ok pc) :
    0 ≤ pc.untrackedInterest.toRat ∧ pc.untrackedInterest.isNormalized ∧
      pc.untrackedInterest.toRat ≤ (276 * l.principalOutstanding.toRat + 10 ^ l.loanScale + 1) * (1 + ε) := by
  have he := Number.nearestError_pos
  obtain ⟨pc0, li, lr, split, net, sf, uf, -, hli, hlr, hsplit, hnet, -, -, rfl⟩ := Loan.lateComponents_parts l now pc h
  obtain ⟨hliN, hli0, hlile⟩ := loanLatePaymentInterest_le l now li hli
  have hlrN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hlr
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hliN hli0 (Or.inl rfl) hs hlr
  have hlrle := STAmount.roundToNumericType_to_nearest_le _ _ _ _ hliN hli0 hs hlr
  obtain ⟨gsp, hsp0, hsple⟩ := computeManagementFee_le _ _ _ _ _ hlrN hlr0 l.broker.managementFeeRate_le hs hint
    hsplit
  have hnetle := (Number.sub_near _ _ _ hlrN gsp.1 hnet).le_max
  have hnet0 := rn_nonneg (operator_sub_rounded_to_nearest _ _ _ hlrN gsp.1 hnet) (by linarith)
  have hmax : max (lr.toRat - split.toRat) 0 ≤ 276 * l.principalOutstanding.toRat + 10 ^ l.loanScale + 1 :=
    max_le (by linarith) (by have : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _; nlinarith [hli0])
  exact ⟨hnet0, operator_sub_isNormalized_to_nearest_sz _ _ _ hlrN gsp.1 hnet,
    le_trans hnetle (mul_le_mul_of_nonneg_right hmax (by linarith))⟩

/-- An overpayment that pays some principal pays less interest than the overpayment. The interest, its
management fee and the overpayment fee all come off the overpayment before the principal. -/
private lemma Loan.overpaymentComponents_interest_lt (l : Loan) (ov : Number) (opc : PaymentComponents)
    (hov : ov.isNormalized) (hov0 : 0 ≤ ov.toRat) (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (h : Loan.overpaymentComponents l ov = .ok opc) (hpd : 0 < opc.principalDelta.toRat) :
    opc.untrackedInterest.isNormalized ∧ opc.untrackedInterest.toRat < ov.toRat := by
  unfold Loan.overpaymentComponents at h
  obtain ⟨of, hof, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨of', hof', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨oi, hoi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pai, hpai, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨paf, hpaf, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pd, hpdv, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  obtain ⟨hofN, hof0, -⟩ := tenthBipsOfValue_le_share _ _ _ hov hov0 hof
  have hof'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hof'
  have hof'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hofN hof0 (Or.inl rfl) hs hof'
  obtain ⟨hoiN, hoi0, -⟩ := tenthBipsOfValue_le_share _ _ _ hov hov0 hoi
  obtain ⟨lr, hlr, hfee, hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  have hlrN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hlr
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hoiN hoi0 (Or.inl rfl) hs hlr
  obtain ⟨gmf, hmf0, -⟩ := computeManagementFee_le _ _ _ _ _ hlrN hlr0 l.broker.managementFeeRate_le hs hint hfee
  have hnetN := operator_sub_isNormalized_to_nearest_sz _ _ _ hlrN gmf.1 hnet
  refine ⟨hnetN, ?_⟩
  -- were the interest at least the overpayment, no principal would be left
  by_contra hge
  push Not at hge
  have hpaiN := operator_sub_isNormalized_to_nearest_sz _ _ _ hov hnetN hpai
  have hpafN := operator_sub_isNormalized_to_nearest_sz _ _ _ hpaiN gmf.1 hpaf
  have h1 := (Number.sub_near _ _ _ hov hnetN hpai).nonpos (by linarith)
  have h2 := (Number.sub_near _ _ _ hpaiN gmf.1 hpaf).nonpos (by linarith)
  have h3 := (Number.sub_near _ _ _ hpafN hof'N hpdv).nonpos (by linarith)
  show False
  linarith

/-- The overpayment tail adds interest below what the loan owes. -/
private lemma UnsettledPayment.applyOverpayment_interest_le (payment p' : UnsettledPayment Vault)
    (amount : Number) (hs : -81 ≤ payment.loan.loanScale ∧ payment.loan.loanScale ≤ 80)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue)
    (hipN : payment.amounts.interestPaid.isNormalized) (htp : payment.totalPaid.isNormalized)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.amounts.interestPaid.toRat ≤
      (max payment.amounts.interestPaid.toRat 0 + payment.loan.totalValueOutstanding.toRat) * (1 + ε) := by
  have he := Number.nearestError_pos
  have hT0 : 0 ≤ payment.loan.totalValueOutstanding.toRat := payment.loan.exact.totalValueOutstanding_nonneg
  have hm := le_max_left payment.amounts.interestPaid.toRat 0
  have hm0 := le_max_right payment.amounts.interestPaid.toRat 0
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | nlinarith
    | skip
  rename_i _ a' ha' hcond _ un hun _ ov hov hovp _ opc hopc hpd _ _ re hre _ am ham _ l' hl'
  have ha'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ ha'
  have hlt : payment.totalPaid.toRat < a'.toRat := by
    have : payment.totalPaid.operator_lt a' = true := by
      revert hcond; cases payment.totalPaid.operator_lt a' <;> simp
    exact (operator_lt_iff _ _ htp ha'N).mp this
  have hunN := operator_sub_isNormalized_to_nearest_sz _ _ _ ha'N htp hun
  have hun0 := rn_nonneg (operator_sub_rounded_to_nearest _ _ _ ha'N htp hun) (by linarith)
  -- the overpayment is at most TotalValueOutstanding
  have hmin : (Number.min un payment.loan.totalValueOutstanding).isNormalized ∧
      0 ≤ (Number.min un payment.loan.totalValueOutstanding).toRat ∧
      (Number.min un payment.loan.totalValueOutstanding).toRat ≤ payment.loan.totalValueOutstanding.toRat := by
    unfold Number.min
    split
    · exact ⟨payment.loan.wf.totalValueOutstanding_norm, hT0, le_rfl⟩
    · rename_i hn
      exact ⟨hunN, hun0, (operator_lt_eq_false_iff _ _ payment.loan.wf.totalValueOutstanding_norm hunN).mp
        (by simpa using hn)⟩
  obtain ⟨hmN, hm0, hmle⟩ := hmin
  have hovN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hov
  have hov0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hmN hm0 (Or.inr (Or.inr rfl)) hs hov
  have hovle := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hmN hm0 hs hov
  -- the tail's interest is below the overpayment
  have hpd' : 0 < opc.principalDelta.toRat := by
    have hpdN := Loan.overpaymentComponents_principalDelta_normalized _ _ _ hovN hopc
    have : opc.principalDelta.operator_gt Number.zero = true := by
      revert hpd; cases opc.principalDelta.operator_gt Number.zero <;> simp
    have := (operator_gt_iff _ _ hpdN Number.zero_isNormalized).mp this
    rwa [Number.toRat_zero] at this
  obtain ⟨hniN, hnilt⟩ := Loan.overpaymentComponents_interest_lt _ _ _ hovN hov0 hs hint hopc hpd'
  obtain ⟨hrei, -⟩ := Loan.tryOverpayment_interestDue_le _ _ _ (by omega) hint hi hre
  have hadd := PaymentAmounts.add_interest _ _ _ ham
  rw [hrei] at hadd
  have hle := (Number.add_near _ _ _ hipN hniN hadd).le_max
  show am.interestPaid.toRat ≤ _
  refine le_trans hle (mul_le_mul_of_nonneg_right (max_le (by linarith) (by linarith)) (by linarith))

/-- The instalment loop keeps the amount paid so far a normalized `Number`. -/
private lemma UnsettledPayment.payInstalments_totalPaid {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), payment.totalPaid.isNormalized →
      UnsettledPayment.payInstalments payment n amount = .ok p' → p'.totalPaid.isNormalized := by
  intro n
  induction n with
  | zero =>
    intro payment p' htp h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact htp
  | succ n ih =>
    intro payment p' htp h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact htp
    · exact htp
    all_goals
      have hpc := ‹Loan.scheduledComponents payment.loan = _›
      obtain ⟨htvN, -, -, -, -, -⟩ := Loan.scheduledComponents_sound _ _ hpc
      obtain ⟨hu, -⟩ := Loan.scheduledComponents_shape _ _ hpc
      have hdue := ‹PaymentComponents.totalDue _ = _›
      unfold PaymentComponents.totalDue at hdue
      obtain ⟨d1, hd1, hdue⟩ := bind_ok_peel _ _ _ hdue
      simp only at hd1 hdue
      rw [hu] at hd1
      have hd1N := operator_add_isNormalized_to_nearest_sz _ _ _ htvN Number.zero_isNormalized hd1
      have hdueN := operator_add_isNormalized_to_nearest_sz _ _ _ hd1N payment.loan.wf.serviceFee_norm hdue
      have htp' := operator_add_isNormalized_to_nearest_sz _ _ _ htp hdueN ‹payment.totalPaid.operator_add _ _ = _›
    · exact htp'
    · exact ih _ p' htp' ‹UnsettledPayment.payInstalments _ n amount = _›

/-- A payment of a reachable loan at a LoanScale of zero or below pays principal and interest of at most
`300·(10^16 + 1)` LoanScale units together. -/
lemma Loan.Reachable.pay_sum_le {loan : Loan} {t : UInt32} (hreach : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v pt amount now).run = .ok (.ok payment)) :
    payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
      300 * ((10 ^ 16 + 1) * 10 ^ loan.loanScale) := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hi := hreach.interestDue_nonneg
  set B := (10 ^ 16 + 1) * (10 : ℚ) ^ loan.loanScale with hB
  have hu : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hu1 : (10 : ℚ) ^ loan.loanScale ≤ B := by rw [hB]; nlinarith
  have h1B : (1 : ℚ) ≤ B := by
    have : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ loan.loanScale := zpow_le_zpow_right₀ (by norm_num) hlo
    rw [hB]; norm_num at this ⊢; nlinarith
  have hT := hreach.totalValue_le
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hiD : loan.toExact.interestDue =
      loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat := rfl
  have hPB : loan.principalOutstanding.toRat ≤ B := by linarith
  -- the principal is at most PrincipalOutstanding
  obtain ⟨-, hpp0, hpe⟩ := Loan.payInstalments_paidOn loan v pt amount now payment ⟨by omega, hls⟩ hpay
  have hpl0 : 0 ≤ payment.loan.principalOutstanding.toRat := payment.loan.exact.principalOutstanding_nonneg
  have hpp : payment.amounts.principalPaid.toRat ≤ B := by linarith
  -- the regular instalments pay at most interestDue as interest
  obtain ⟨hlo', hint', hi'⟩ := Loan.unimpaired_same loan (by omega) hint hi
  have hregular : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      p0.amounts.interestPaid.isNormalized ∧ p0.amounts.interestPaid.toRat ≤ B ∧ p0.totalPaid.isNormalized := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    obtain ⟨g, hv⟩ := UnsettledPayment.payInstalments_interestPaid loan.unimpaired amount maxPaymentsPerTransaction
      { loan := loan.unimpaired, pool := p0.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
        count := 0, scheduledInterest := si } p0 hlo' hint' rfl hi' hi' (Number.OnGrid.zero _)
      (by simp only [PaymentAmounts.zero, Number.toRat_zero, sub_self]) hloop
    have hk := Loan.payInstalments_interestDue loan v .regular amount now p0 (by decide) (by omega) hint hi hp0
    have hiu : loan.unimpaired.toExact.interestDue = loan.toExact.interestDue := rfl
    refine ⟨g.1, ?_, UnsettledPayment.payInstalments_totalPaid amount _ _ p0 Number.zero_isNormalized hloop⟩
    rw [hv, hiu]
    linarith
  suffices hip : payment.amounts.interestPaid.toRat ≤ 285 * B by linarith
  cases pt
  · linarith [(hregular payment hpay).2.1]
  · -- a late instalment: the scheduled deltas plus the late interest
    obtain ⟨pc, hpc, hamt, -⟩ := Loan.latePayInstalments_ok loan v amount now payment hpay
    obtain ⟨pc0, hpc0, e1, e2, e3, -⟩ := Loan.lateComponents_scheduled loan now pc hpc
    obtain ⟨hui0, huiN, huile⟩ := Loan.lateComponents_interest_le loan now pc hs81 hint hpc
    obtain ⟨htvN, hpdN, hmdN, -, hp0', hm0'⟩ := Loan.scheduledComponents_sound loan pc0 hpc0
    have htvle : pc0.totalValueDelta.toRat ≤ loan.totalValueOutstanding.toRat := by
      rcases Loan.scheduledComponents_tracked loan pc0 (by omega) hint hi hpc0 with hf | ⟨-, ht⟩
      · rw [((Loan.scheduledComponents_shape loan pc0 hpc0).2 hf).1]
      · exact ht.totalValue_range.2
    obtain ⟨vap, id, hvap, hid, hipv, -, -⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hamt
    rw [e1, e2] at hvap
    rw [e3] at hid
    have hvapN := operator_sub_isNormalized_to_nearest_sz _ _ _ htvN hpdN hvap
    have hidN := operator_sub_isNormalized_to_nearest_sz _ _ _ hvapN hmdN hid
    have h1 := (Number.sub_near _ _ _ htvN hpdN hvap).le_max
    have h2 := (Number.sub_near _ _ _ hvapN hmdN hid).le_max
    have h3 := (Number.add_near _ _ _ hidN huiN hipv).le_max
    have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
    have hvap' : vap.toRat ≤ B * (1 + ε) := le_trans h1 (by
      gcongr; exact max_le (by linarith) (by linarith))
    have hid' : id.toRat ≤ B * (1 + ε) * (1 + ε) := le_trans h2 (by
      gcongr; exact max_le (by linarith) (by positivity))
    have hui' : pc.untrackedInterest.toRat ≤ (276 * B + B + B) * (1 + ε) := le_trans huile (by gcongr)
    have hE : (1 + ε) ≤ 1 + 1 / 10 ^ 18 := by linarith
    calc payment.amounts.interestPaid.toRat ≤ max (id.toRat + pc.untrackedInterest.toRat) 0 * (1 + ε) := h3
      _ ≤ (B * (1 + ε) * (1 + ε) + (276 * B + B + B) * (1 + ε)) * (1 + ε) := by
          gcongr; exact max_le (by linarith) (by positivity)
      _ ≤ (B * (1 + 1 / 10 ^ 18) * (1 + 1 / 10 ^ 18) + (276 * B + B + B) * (1 + 1 / 10 ^ 18)) *
          (1 + 1 / 10 ^ 18) := by gcongr
      _ ≤ 285 * B := by nlinarith
  · -- an early payoff: the rounded full interest less its fee
    obtain ⟨pc, hpc, -, -⟩ := Loan.fullPayInstalments_ok loan v amount now payment hpay
    obtain ⟨rate, tpo, fi, net, split, -, -, -, -, -, -, -, hrate, htpo, hfi, hsplit, -, -, -, -, -, -, -, -⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    obtain ⟨fi', hfloor, hfee, -⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
    obtain ⟨-, hipv, -⟩ := hreach.full_units v amount now payment rate tpo fi fi' split hpay hrate htpo hfi hfloor hfee
    have hchk := (Loan.payInstalments_ok loan v .full amount now payment hpay).1
    have hnl : now ≤ loan.nextPaymentDueDate := by
      have := hchk.not_late (by decide)
      rw [UInt32.lt_iff_toNat_lt] at this
      rw [UInt32.le_iff_toNat_le]; omega
    have hn : 2 ≤ loan.paymentRemaining.toNat := by
      have h1 := hchk.more_than_one
      rw [UInt32.le_iff_toNat_le] at h1
      simp at h1; omega
    obtain ⟨hfN, hf0, hfle⟩ := hreach.fullInterest_le now rate tpo fi hnl hn hrate htpo hfi
    have hfiN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfloor
    have hfi0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfN hf0 (Or.inr (Or.inr rfl)) hs81 hfloor
    have hfi_le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfN hf0 hs81 hfloor
    obtain ⟨-, hsp0, -⟩ := computeManagementFee_le _ _ _ _ _ hfiN hfi0 loan.broker.managementFeeRate_le hs81 hint hfee
    rw [hipv]
    linarith
  · -- an overpayment: the regular instalments, then the tail's interest below what the loan owes
    obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now payment hpay
    obtain ⟨hipN, hip0, htp⟩ := hregular p0 h0
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
    have hk := Loan.payInstalments_interestDue loan v .regular amount now p0 (by decide) (by omega) hint hi h0
    obtain ⟨hb1, -⟩ := Loan.payInstalments_below loan v .regular amount now p0 h0
    have hls0 : p0.loan.loanScale = loan.loanScale := hst.loanScale
    have hnt0 : p0.loan.broker.numericType = loan.broker.numericType := by rw [hst.broker]; rfl
    have htail := UnsettledPayment.applyOverpayment_interest_le p0 payment amount (by rw [hls0]; exact hs81)
      (by rw [hls0, hnt0]; exact hint) hk hipN htp h1
    have hmax : max p0.amounts.interestPaid.toRat 0 ≤ B := max_le hip0 (by positivity)
    calc payment.amounts.interestPaid.toRat
        ≤ (max p0.amounts.interestPaid.toRat 0 + p0.loan.totalValueOutstanding.toRat) * (1 + ε) := htail
      _ ≤ (B + B) * (1 + 1 / 10 ^ 18) := by gcongr; linarith
      _ ≤ 285 * B := by nlinarith

end XRPL.Model.Lending
