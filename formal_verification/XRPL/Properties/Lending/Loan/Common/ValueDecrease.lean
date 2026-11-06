import XRPL.Properties.Lending.Loan.Common.InterestDue
import XRPL.Properties.Lending.Loan.Common.PayProofs
import XRPL.Properties.Lending.Loan.Common.PayReachable
import XRPL.Properties.Lending.Ledger.Common.BaseGrid

/-! # What a payment takes off the loan

A payment that leaves payments outstanding must change AssetsAvailable, so it credits the vault some principal or
interest, and that credit comes off TotalValueOutstanding, unless a late payment credits only late interest. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment Loan.settlePayment validatePostPayment
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.pay_vault_sums Loan.unimpair_pool UnsettledPayment.applyOverpayment_lowers
  from XRPL.Properties.Lending.Loan.Common.PayBounds
open private Loan.payInstalments_below Loan.lateComponents_scheduled
  from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- Nothing added to an amount the asset stores credits nothing. The amount is a whole number of units at the
exponent `e`. -/
private lemma sumRoundAndSubtract_zero (A : Number) (e : Int) (nt : NumericType) (st : STAmount)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded nt A = false)
    (hgrid : ∃ j : ℕ, A.toRat = j * 10 ^ e) (he : -81 ≤ e ∧ e ≤ 80)
    (h : sumRoundAndSubtract A Number.zero e nt .downward = .ok st) : st.toRat = 0 := by
  have hle := (sumRoundAndSubtract_downward_le A Number.zero e nt st hA hA0 Number.zero_isNormalized
    (by rw [Number.toRat_zero]) ⟨by omega, he.2⟩ h).1
  rw [Number.toRat_zero] at hle
  refine le_antisymm hle ?_
  unfold sumRoundAndSubtract at h
  by_cases hint : nt.isIntegral = true
  · rw [if_pos hint] at h
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ h
    obtain rfl : x = st := Except.ok.inj h
    exact STAmount.ofNumber_nonneg nt _ _ x Number.zero_isNormalized rfl hx
  rw [if_neg hint] at h
  have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  subst hfr
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
  rw [Number.operator_add_zero_right, Except.ok.injEq] at hsum
  subst hsum
  have hErange := postSumExponent_range _ _ _ _ _ (by omega) he.2 hE
  have hEn : numberExponent A e .fractional = .ok E := by
    unfold postSumExponent at hE
    rwa [Number.operator_add_zero_right] at hE
  -- AssetsAvailable is a whole number of `10^E` units, fewer than `10^16`
  have hlt := numberExponent_frac_lt A e E hA (by omega) hEn
  obtain ⟨j, hj, hj16⟩ : ∃ j : ℕ, A.toRat = j * 10 ^ E ∧ j < 10 ^ 16 := by
    have hp : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
    rcases eq_or_lt_of_le hErange.1 with hEe | hEe
    · obtain ⟨j, hj⟩ := hgrid
      rw [← hEe] at hlt ⊢
      refine ⟨j, hj, ?_⟩
      rw [hj, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ e)] at hlt
      have : (j : ℚ) < 10 ^ 16 := by
        have h16 : (10 : ℚ) ^ (16 : ℤ) = 10 ^ 16 := by norm_num
        rw [h16] at hlt
        exact lt_of_mul_lt_mul_right hlt (zpow_pos (by norm_num) _).le
      exact_mod_cast this
    · obtain ⟨-, hge⟩ := numberExponent_frac_lower A e E hA hA0 (by omega) hEn hEe
      rcases (STAmount.isRounded_eq_false_iff _ A hA hA0).mp hArep with h0 | ⟨m, e', hm1, hm2, -, -, hv⟩
      · rw [h0] at hge
        exact absurd hge (not_le.mpr (zpow_pos (by norm_num) _))
      -- the stored exponent is `E`: the amount sits between `10^(E+15)` and `10^(E+16)`
      have hm1' : (10 : ℚ) ^ 15 ≤ m := by exact_mod_cast hm1
      have hm2' : (m : ℚ) < 10 ^ 16 := by exact_mod_cast hm2
      have hp' : (0 : ℚ) < 10 ^ e' := zpow_pos (by norm_num) _
      have hlo : (10 : ℚ) ^ (e' + 15) ≤ A.toRat := by
        rw [hv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm1') hp'.le
      have hhi : A.toRat < (10 : ℚ) ^ (e' + 16) := by
        rw [hv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ e')]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hm2') hp'
      have hee : e' = E := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h1 | h1
        · have : (10 : ℚ) ^ (e' + 16) ≤ 10 ^ (E + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          linarith
        · have : (10 : ℚ) ^ (E + 16) ≤ 10 ^ (e' + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          linarith
      subst hee
      exact ⟨m, hv, hm2⟩
  -- the floor at `E` keeps AssetsAvailable, so the credit is `A - A = 0`
  have hs'v := STAmount.roundToNumericType_representable_grid .fractional A sum' .downward E hA hA0
    (Or.inr (Or.inr rfl)) ⟨by omega, hErange.2.2⟩ (fun h => by cases h) hArep j hj (fun _ => hj16) hsum'
  have hs'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  obtain rfl : sum' = A := Number.isNormalized.toRat_inj hs'n hA hs'v
  have hdn := Number.operator_sub_isNormalized_any sum' sum' d _ hs'n hs'n hd
  have hd0 : d.toRat = 0 := by
    by_cases hm : d.mantissa_ = 0
    · exact Number.toRat_eq_zero_of_mantissa_zero d hm
    obtain ⟨n, hn, hv⟩ := operator_sub_rounded_downward sum' sum' d hs'n hs'n hd hm
    rw [sub_self] at hn
    have h1 := Number.lower_le _ n hn
    have h2 := Number.lower_tight _ n hn Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero])
    rw [Number.toRat_zero] at h2
    rw [hv]
    exact le_antisymm h1 h2
  have hdz : d = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hdn).mp hd0
  subst hdz
  rw [STAmount.ofNumber_fractional_zero, Except.ok.injEq] at h
  subst h
  rw [STAmount.toRat_eq_zero_of_mValue_zero _ rfl]

/-- The pool re-check passes only on a payment that changes AssetsAvailable or pays the loan off. -/
private lemma validatePostPayment_changed (v : Vault) (r0 r : LoanWithAmounts Vault)
    (h : validatePostPayment v r0 = .ok (.ok r)) :
    r = r0 ∧ (r0.pool'.assetsAvailable.operator_ne v.assetsAvailable = true ∨ r0.loan'.paymentRemaining = 0) := by
  simp only [validatePostPayment] at h
  unfold_ter at h
  walk_ok
  rename_i hc _
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Bool.not_eq_true'] at hc
  refine ⟨rfl, ?_⟩
  by_cases hpr : r0.loan'.paymentRemaining = 0
  · exact Or.inr hpr
  · left
    by_contra hne
    exact hpr (by simpa using hc (by simpa using hne))

/-- A settlement that passes changed AssetsAvailable, or paid the loan off. -/
private lemma UnsettledPayment.settle_changed (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (h : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.pool'.assetsAvailable ≠ p.pool.assetsAvailable ∨ r.loan'.paymentRemaining = 0 := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    obtain ⟨rfl, hch⟩ := validatePostPayment_changed _ _ _ ‹validatePostPayment _ _ = _›
    rcases hch with hne | hpr
    · left
      intro heq
      rw [(Number.operator_ne_false_iff_eq' _ _).mpr heq] at hne
      exact absurd hne (by decide)
    · exact Or.inr hpr

/-- A payment that pays no principal and no interest leaves AssetsAvailable as it was, when the asset stores
AssetsAvailable as a whole number of base units. -/
private lemma Loan.pay_zero_credit (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (p : UnsettledPayment Vault)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hgrid : ∃ j : ℕ, v.assetsAvailable.toRat = j * 10 ^ v.baseExponent)
    (hpay : (loan.payInstalments v pt amount now).run = .ok (.ok p))
    (hok : (loan.pay v pt amount now).run = .ok (.ok r))
    (hpp : p.amounts.principalPaid.toRat = 0) (hip : p.amounts.interestPaid.toRat = 0) :
    r.pool'.assetsAvailable = p.pool.assetsAvailable := by
  obtain ⟨p', tp, credit, toPool, aa, hp, hu, htp, hcredit, hto, -, haa, hA', -, hb⟩ :=
    Loan.pay_vault_sums loan v amount now pt r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨hppn, hipn, -⟩ := Loan.payInstalments_norm loan v amount now pt p hpay
  have e1 : p.amounts.principalPaid = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hppn).mp hpp
  have e2 : p.amounts.interestPaid = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hipn).mp hip
  rw [e1, e2, Number.operator_add_zero_right, Except.ok.injEq] at htp
  subst htp
  obtain ⟨hAv, hArep, hnt1, hbe, -⟩ := Loan.unimpair_pool loan v p.pool hu hAA
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds p.pool
  rw [hb, hnt, ← hnt1] at hcredit
  have hA := p.pool.wf.assetsAvailable_norm
  have hA0 : 0 ≤ p.pool.assetsAvailable.toRat := p.pool.exact.assetsAvailable_nonneg
  have hpg : ∃ j : ℕ, p.pool.assetsAvailable.toRat = j * 10 ^ p.pool.baseExponent := by
    obtain ⟨j, hj⟩ := hgrid
    exact ⟨j, by rw [hAv, hj, hbe]⟩
  have hc0 := sumRoundAndSubtract_zero _ _ _ _ hA hA0 hArep hpg ⟨by omega, by omega⟩ hcredit
  obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ _ hA hA0 Number.zero_isNormalized
    (by rw [Number.toRat_zero]) ⟨by omega, by omega⟩ hcredit
  obtain ⟨htv, htnn⟩ := htn toPool hto
  have e3 : toPool = Number.zero := (Number.toRat_eq_zero_iff_eq_zero htnn).mp (by rw [htv, hc0])
  rw [e3, Number.operator_add_zero_right, Except.ok.injEq] at haa
  subst haa
  exact Number.isNormalized.toRat_inj r.pool'.wf.assetsAvailable_norm hA
    (STAmount.roundToNumericType_of_isRounded_false _ _ _ hA hArep hA')

/-- A payment that leaves payments outstanding pays some principal or interest. The vault of a reachable
ledger stores AssetsAvailable exactly, so a zero credit leaves it unchanged and the re-check rejects it. -/
lemma Loan.pay_credit_pos (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan) (hat : l.LoanAt i loan)
    (pt : LoanPaymentType) (amount : Number) (r : LoanWithAmounts Vault) (p : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p))
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r)) (hpr : r.loan'.paymentRemaining ≠ 0) :
    0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat := by
  obtain ⟨h1, h2, -⟩ := Loan.pay_parts_nonneg loan amount pt r l.vault l.now p hpay hok
  by_contra hle
  push Not at hle
  have hsame := Loan.pay_zero_credit loan l.vault pt amount l.now r p (hr.loanAt_scale hat).2
    (hr.storesAvailable hr.holdsAsset.maxValue_le) (hr.assetsAvailable_units hr.holdsAsset) hpay hok
    (by linarith) (by linarith)
  obtain ⟨p', hp', hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  rw [hpay] at hp'
  obtain rfl := Except.ok.inj (Except.ok.inj hp')
  rcases UnsettledPayment.settle_changed p r hs with hne | h0
  · exact hne hsame
  · exact hpr h0

/-- The settlement keeps the paid loan's TotalValueOutstanding and PaymentRemaining. -/
private lemma UnsettledPayment.settle_loan (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (hs : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.loan'.totalValueOutstanding = p.loan.totalValueOutstanding ∧
      r.loan'.paymentRemaining = p.loan.paymentRemaining := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  exact ⟨(congrArg RawLoan.totalValueOutstanding h1 :), (congrArg RawLoan.paymentRemaining h1 :)⟩

/-- A regular payment that leaves payments outstanding takes value off the loan. Its credit is the value it
takes off, less the management fee it takes off. -/
private lemma Loan.regular_value_lt (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (amount : Number) (r : LoanWithAmounts Vault)
    (hok : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r)) (hpr : r.loan'.paymentRemaining ≠ 0) :
    r.loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat := by
  have hrange := hr.loanScale_range hat
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok
  have hpos := Loan.pay_credit_pos l hr i loan hat .regular amount r p hp hok hpr
  obtain ⟨-, -, hpe⟩ := Loan.payInstalments_paidOn loan l.vault .regular amount l.now p hrange hp
  have hint := Loan.regularPayment_interest loan l.vault amount l.now p hrange hp
  obtain ⟨-, -, hm, -, -⟩ := Loan.payInstalments_below loan l.vault .regular amount l.now p hp
  have e1 : loan.toExact.interestDue = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := rfl
  have e2 : p.loan.toExact.interestDue = p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
      p.loan.managementFeeOutstanding.toRat := rfl
  rw [(UnsettledPayment.settle_loan p r hs).1]
  linarith

/-- An overpayment that leaves payments outstanding takes value off the loan. A dropped extra amount leaves
the regular payment, an applied one lowers TotalValueOutstanding again. -/
private lemma Loan.overpayment_value_lt (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (amount : Number) (r : LoanWithAmounts Vault)
    (hok : (loan.pay l.vault .overpayment amount l.now).run = .ok (.ok r)) (hpr : r.loan'.paymentRemaining ≠ 0) :
    r.loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault .overpayment amount l.now r hok
  obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan l.vault amount l.now p hp
  by_cases heq : p = p0
  · subst heq
    have hsame := Loan.overpayment_of_same_instalments loan l.vault amount l.now (fun q hq => by
      rw [h0] at hq
      obtain rfl := Except.ok.inj (Except.ok.inj hq)
      exact hp)
    have hreg : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r) := by
      show (loan.regularPayment l.vault amount l.now).run = _
      rw [← hsame]
      exact hok
    exact Loan.regular_value_lt l hr i loan hat amount r hreg hpr
  · obtain ⟨-, hlt⟩ := UnsettledPayment.applyOverpayment_lowers p0 p amount h1 heq
    obtain ⟨hle, -⟩ := Loan.payInstalments_below loan l.vault .regular amount l.now p0 h0
    rw [(UnsettledPayment.settle_loan p r hs).1]
    linarith

/-- An instalment that isn't the last takes its value delta off TotalValueOutstanding exactly. -/
private lemma Loan.doPayment_value (l l' : Loan) (pc : PaymentComponents) (hf : pc.isFinal = false)
    (hg : Number.OnGrid l.loanScale pc.totalValueDelta) (h0 : 0 ≤ pc.totalValueDelta.toRat)
    (hle : pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat) (h : Loan.doPayment l pc = .ok l') :
    l'.totalValueOutstanding.toRat = l.totalValueOutstanding.toRat - pc.totalValueDelta.toRat := by
  simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
  unfold_ter at h
  walk_ok
  have h1 := (RawLoan.to_lawful_ok ‹_›).1
  have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
  simp only at e1
  rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, e1]
  obtain ⟨gT, -, -, hTb, -, -, -⟩ := Loan.outstanding_grid l
  exact Number.OnGrid.sub_exact gT hg h0 hle hTb (Loan.loanScale_bounds l)
    ‹l.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest = _›

/-- A late payment that leaves payments outstanding takes its instalment's value off the loan. -/
private lemma Loan.late_value_lt (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (amount : Number) (r : LoanWithAmounts Vault)
    (hok : (loan.pay l.vault .late amount l.now).run = .ok (.ok r)) (hpr : r.loan'.paymentRemaining ≠ 0)
    (hlate : ∀ pc, loan.paymentComponents .late l.now = .ok pc → pc.isFinal = false →
      0 < pc.totalValueDelta.toRat) :
    r.loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault .late amount l.now r hok
  obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan l.vault amount l.now p hp
  obtain ⟨htv, hprs⟩ := UnsettledPayment.settle_loan p r hs
  cases hf : pc.isFinal
  · -- the instalment's deltas are tracked, so its value comes off exactly
    have hpos := hlate pc hpc hf
    obtain ⟨pc0, hpc0, e1, -, -, e4⟩ := Loan.lateComponents_scheduled loan l.now pc hpc
    obtain ⟨t, -, hrl⟩ := hr.loanAt_reachable hat
    have hrange := hr.loanScale_range hat
    rcases Loan.scheduledComponents_tracked loan pc0 hrange.1 (fun _ => hrange.2)
      (Loan.Reachable.interestDue_nonneg hrl) hpc0 with h | ⟨-, htr⟩
    · rw [← e4, hf] at h; exact absurd h (by decide)
    have hv := Loan.doPayment_value loan.unimpaired p.loan pc hf (by rw [e1]; exact htr.totalValue_grid)
      (by rw [e1]; exact htr.totalValue_range.1) (by rw [e1]; exact htr.totalValue_range.2) hdo
    rw [htv, hv]
    show loan.totalValueOutstanding.toRat - pc.totalValueDelta.toRat < loan.totalValueOutstanding.toRat
    linarith
  · exact absurd (by rw [hprs]; exact Loan.doPayment_final _ _ _ hf hdo) hpr

/-- Proof body of `payment_decreases`. -/
lemma Loan.payment_decreases_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (paymentType : LoanPaymentType) (amount : Number) (r : LoanWithAmounts Vault)
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hlate : paymentType = .late → ∀ pc, loan.paymentComponents .late l.now = .ok pc → pc.isFinal = false →
      0 < pc.totalValueDelta.toRat) :
    r.loan'.paymentRemaining < loan.paymentRemaining ∧
      r.loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat := by
  refine ⟨Loan.payment_paymentRemaining_decreases loan l.vault amount l.now paymentType r hok, ?_⟩
  by_cases hpr : r.loan'.paymentRemaining = 0
  · -- paid off: nothing is left, and the loan owed at least its principal, which isn't zero
    rw [(r.loan'.valid.paid_zeroed hpr).1, Number.toRat_zero]
    obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault paymentType amount l.now r hok
    obtain ⟨hchecks, -⟩ := Loan.payInstalments_ok loan l.vault paymentType amount l.now p hp
    have hpo : 0 < loan.principalOutstanding.toRat := by
      refine lt_of_le_of_ne loan.exact.principalOutstanding_nonneg (fun h => hchecks.principal ?_)
      exact (Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp h.symm
    obtain ⟨t, -, hrl⟩ := hr.loanAt_reachable hat
    have hin := Loan.Reachable.interest_nonneg_proof loan t hrl
    have hm0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
    have e : loan.toExact.principalOutstanding + loan.toExact.managementFeeOutstanding ≤
        loan.toExact.totalValueOutstanding ↔ loan.principalOutstanding.toRat +
          loan.managementFeeOutstanding.toRat ≤ loan.totalValueOutstanding.toRat := Iff.rfl
    linarith [e.mp hin]
  · cases paymentType
    · exact Loan.regular_value_lt l hr i loan hat amount r hok hpr
    · exact Loan.late_value_lt l hr i loan hat amount r hok hpr (hlate rfl)
    · exact absurd (Loan.fullPayment_closes_proof loan l.vault amount l.now r hok).1 hpr
    · exact Loan.overpayment_value_lt l hr i loan hat amount r hok hpr

end XRPL.Model.Lending
