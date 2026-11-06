import XRPL.Properties.Lending.Loan.Common.Payoff
import XRPL.Properties.Lending.Loan.Common.PayCharge
import XRPL.Properties.Lending.Loan.Common.PayLedger

/-! # A LoanPay transaction that pays off an active loan

A payoff payment, the last regular instalment or a full payment, pays one instalment and reads the amount only in
the check that it covers the instalment's totalDue. Any larger amount pays the loan off the same way, so the largest
amount the vault's asset holds passes the LoanPay preflight and pays the loan off. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.fullComponents Loan.unimpairIfImpaired Loan.payScheduledInstalments
  UnsettledPayment.payInstalments Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps
open private Loan.full_parts from XRPL.Properties.Lending.Loan.Common.PayCharge
open private Number.OnGrid.unitsAt from XRPL.Properties.Lending.Loan.Common.FullPaymentSize
open private computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private PaymentComponents.Norm Loan.fullComponents_norm Loan.scheduledComponents_norm
  from XRPL.Properties.Lending.Loan.Common.PayBounds

/-- A full payment reads the amount only in the check that it covers totalDue. -/
private lemma Loan.fullPayInstalments_amount (loan : Loan) (v : Vault) (now : UInt32) (pc : PaymentComponents)
    (totalDue a b : Number) (hpc : Loan.fullComponents loan now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (ha : a.operator_lt totalDue = false) (hb : b.operator_lt totalDue = false) :
    (loan.payInstalments v .full a now).run = (loan.payInstalments v .full b now).run := by
  simp only [Loan.payInstalments, Loan.payInstalment]
  unfold_ter
  split_ifs
  all_goals try rfl
  rcases hu : Loan.unimpairIfImpaired loan v with e | t | a1
  · rfl
  · rfl
  · have hl := Loan.unimpairIfImpaired_loan loan v a1 (by simp only [ExceptT.run]; exact hu)
    obtain ⟨l1, p1⟩ := a1
    simp only at hl
    subst hl
    have hpc' : Loan.fullComponents loan.unimpaired now = .ok pc := by
      rw [Loan.fullComponents_unimpaired]; exact hpc
    simp only [hpc', hdue, ha, hb, Bool.false_eq_true, ↓reduceIte]

/-- The totalDue of normalized components is normalized. -/
private lemma PaymentComponents.totalDue_isNormalized {pc : PaymentComponents} {td : Number}
    (h1 : pc.totalValueDelta.isNormalized) (h2 : pc.untrackedInterest.isNormalized)
    (h3 : pc.untrackedManagementFee.isNormalized) (h : pc.totalDue = .ok td) : td.isNormalized := by
  unfold PaymentComponents.totalDue at h
  obtain ⟨v1, hv1, hd⟩ := bind_ok_peel _ _ _ h
  exact operator_add_isNormalized_to_nearest_sz _ _ _ (operator_add_isNormalized_to_nearest_sz _ _ _ h1 h2 hv1) h3 hd

/-- A full payment that passes pays the same with any larger normalized amount. -/
lemma Loan.fullPay_amount (loan : Loan) (v : Vault) (now : UInt32) (a b : Number) (p : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault) (hp : (loan.payInstalments v .full a now).run = .ok (.ok p))
    (hok : (loan.pay v .full a now).run = .ok (.ok r)) (hb : b.isNormalized) (hle : p.totalPaid.toRat ≤ b.toRat) :
    (loan.pay v .full b now).run = .ok (.ok r) := by
  obtain ⟨pc, hpc, htd, ha⟩ := Loan.full_parts loan v a now p hp
  obtain ⟨n1, -, -, n4, n5⟩ := Loan.fullComponents_norm loan now pc hpc
  have htdN := PaymentComponents.totalDue_isNormalized n1 n4 n5 htd
  have heq := Loan.fullPayInstalments_amount loan v now pc _ a b hpc htd ha
    ((operator_lt_eq_false_iff b p.totalPaid hb htdN).mpr hle)
  have hx : (loan.payInstalments v .full b now : TerExcept (UnsettledPayment Vault)) =
      loan.payInstalments v .full a now := heq.symm
  rw [Loan.pay_run] at hok ⊢
  rw [hx]
  exact hok

/-- The next scheduled instalment of a loan with one payment left is its last. -/
private lemma Loan.scheduledComponents_one (l : Loan) (pc : PaymentComponents) (hpr : l.paymentRemaining = 1)
    (h : Loan.scheduledComponents l = .ok pc) : pc.isFinal = true := by
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  rw [hpr] at h
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte] at h
  cases h
  rfl

/-- The instalment loop on a loan with one payment left pays the last instalment, whose totalDue the amount covers,
and stops. Any larger amount pays the same. -/
private lemma UnsettledPayment.payInstalments_last (q p : UnsettledPayment Vault) (a b : Number)
    (hpr : q.loan.paymentRemaining = 1) (htp : q.totalPaid = Number.zero)
    (h : UnsettledPayment.payInstalments q maxPaymentsPerTransaction a = .ok p) (hc : p.count ≠ q.count)
    (hb : b.isNormalized) (hle : p.totalPaid.toRat ≤ b.toRat) :
    UnsettledPayment.payInstalments q maxPaymentsPerTransaction b = .ok p := by
  rw [show maxPaymentsPerTransaction = 99 + 1 from rfl, UnsettledPayment.payInstalments] at h ⊢
  have hpr0 : (q.loan.paymentRemaining == 0) = false := by rw [hpr]; decide
  simp only [hpr0, Bool.false_eq_true, ↓reduceIte, htp, Number.operator_add_zero_left] at h ⊢
  cases hsc : Loan.scheduledComponents q.loan with
  | error e => simp [hsc, bind, Except.bind] at h
  | ok pc =>
    have hfin := Loan.scheduledComponents_one q.loan pc hpr hsc
    simp only [hsc, hfin, bind, Except.bind, pure, Except.pure, ↓reduceIte] at h ⊢
    split at h
    · cases h
    rename_i due hdue
    split at h
    · cases h
      exact absurd rfl hc
    have hcopy := h
    have htp' : p.totalPaid = due := by
      split at hcopy
      · cases hcopy
      split at hcopy
      · cases hcopy
      split at hcopy
      · cases hcopy
      cases hcopy
      rfl
    obtain ⟨n1, -, -, n4⟩ := Loan.scheduledComponents_norm q.loan pc hsc
    have hdN := PaymentComponents.totalDue_isNormalized (pc := { pc with
      untrackedManagementFee := q.loan.fees.serviceFee, isFinal := true }) n1
      (by show pc.untrackedInterest.isNormalized; rw [n4]; exact Number.zero_isNormalized)
      q.loan.wf.serviceFee_norm hdue
    have hbd : b.operator_lt due = false := (operator_lt_eq_false_iff b due hb hdN).mpr (htp' ▸ hle)
    rw [if_neg (by rw [hbd]; decide)]
    exact h

/-- The instalment loop on a loan with one payment left charges TotalValueOutstanding + LoanServiceFee. -/
private lemma UnsettledPayment.payInstalments_last_due (q p : UnsettledPayment Vault) (a : Number)
    (hpr : q.loan.paymentRemaining = 1) (htp : q.totalPaid = Number.zero)
    (h : UnsettledPayment.payInstalments q maxPaymentsPerTransaction a = .ok p) (hc : p.count ≠ q.count) :
    q.loan.totalValueOutstanding.operator_add q.loan.fees.serviceFee .to_nearest = .ok p.totalPaid := by
  rw [show maxPaymentsPerTransaction = 99 + 1 from rfl, UnsettledPayment.payInstalments] at h
  have hpr0 : (q.loan.paymentRemaining == 0) = false := by rw [hpr]; decide
  simp only [hpr0, Bool.false_eq_true, ↓reduceIte, htp, Number.operator_add_zero_left] at h
  cases hsc : Loan.scheduledComponents q.loan with
  | error e => simp [hsc, bind, Except.bind] at h
  | ok pc =>
    have hfin := Loan.scheduledComponents_one q.loan pc hpr hsc
    have hpc := Loan.scheduledComponents_final_eq q.loan pc hsc hfin
    simp only [hsc, hfin, bind, Except.bind, pure, Except.pure, ↓reduceIte] at h
    split at h
    · cases h
    rename_i due hdue
    split at h
    · cases h
      exact absurd rfl hc
    have htp' : p.totalPaid = due := by
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      cases h
      rfl
    subst hpc
    unfold PaymentComponents.totalDue at hdue
    simp only [Number.operator_add_zero_right, bind, Except.bind] at hdue
    rw [htp']
    exact hdue

/-- A regular payment of a loan with one payment left charges TotalValueOutstanding + LoanServiceFee. -/
private lemma Loan.regularPay_last_totalPaid (loan : Loan) (v : Vault) (now : UInt32)
    (hpr : loan.paymentRemaining = 1) (a : Number) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments v .regular a now).run = .ok (.ok p)) :
    loan.totalValueOutstanding.operator_add loan.fees.serviceFee .to_nearest = .ok p.totalPaid := by
  obtain ⟨si, -, hloop, hc⟩ := Loan.payScheduled_loop loan v a now p hp
  exact UnsettledPayment.payInstalments_last_due _ p a hpr rfl hloop hc

/-- A regular payment of a loan with one payment left that passes pays the same with any larger normalized amount. -/
lemma Loan.regularPay_last_amount (loan : Loan) (v : Vault) (now : UInt32) (hpr : loan.paymentRemaining = 1)
    (a b : Number) (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (hp : (loan.payInstalments v .regular a now).run = .ok (.ok p))
    (hok : (loan.pay v .regular a now).run = .ok (.ok r)) (hb : b.isNormalized) (hle : p.totalPaid.toRat ≤ b.toRat) :
    (loan.pay v .regular b now).run = .ok (.ok r) := by
  have hpb : (loan.payInstalments v .regular b now).run = .ok (.ok p) := by
    have hp' := hp
    simp only [Loan.payInstalments, Loan.payScheduledInstalments] at hp' ⊢
    unfold_ter at hp' ⊢
    walk_ok
    have hl := Loan.unimpairIfImpaired_loan loan v _
      (by simp only [ExceptT.run]; exact ‹Loan.unimpairIfImpaired loan v = Except.ok (Except.ok _)›)
    have hcount : p.count ≠ 0 := by simpa using ‹¬(p.count == 0) = true›
    rw [UnsettledPayment.payInstalments_last _ p a b (by rw [hl]; exact hpr) rfl ‹_› hcount hb hle,
      if_neg ‹_›, if_neg ‹_›, if_neg ‹_›]
    simp [‹¬(p.count == 0) = true›]
  have hx : (loan.payInstalments v .regular b now : TerExcept (UnsettledPayment Vault)) =
      loan.payInstalments v .regular a now := hpb.trans hp.symm
  rw [Loan.pay_run] at hok ⊢
  rw [hx]
  exact hok

/-- What a full payment charges: at most TotalValueOutstanding + payoff interest + ClosePaymentFee + one unit, while
that stays below `2^63` LoanScale units, and at LoanScale ≤ 0 at most `8` × ClosePaymentFee + `10^20`. -/
private lemma Loan.full_totalPaid_le (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (p : UnsettledPayment Vault) (hreach : loan.Reachable t)
    (hp : (loan.payInstalments v .full amount now).run = .ok (.ok p)) :
    ((∀ fi, loan.payoffInterest now = .ok fi →
      loan.totalValueOutstanding.toRat + fi.toRat + loan.fees.closePaymentFee.toRat + 10 ^ loan.loanScale <
        2 ^ 63 * 10 ^ loan.loanScale) →
      ∃ fi, loan.payoffInterest now = .ok fi ∧ p.totalPaid.toRat ≤
        loan.totalValueOutstanding.toRat + fi.toRat + loan.fees.closePaymentFee.toRat + 10 ^ loan.loanScale) ∧
    (loan.loanScale ≤ 0 → p.totalPaid.toRat ≤ 8 * loan.fees.closePaymentFee.toRat + 10 ^ 20) := by
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hint0 := hreach.loanScale_integral
  have hu0 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hs := Loan.loanScale_bounds loan
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
  obtain ⟨pc, hpc, hdue', -⟩ := Loan.full_parts loan v amount now p hp
  obtain ⟨rate, tpo, fi, net, split, state, cf, ppi, tracked, cfm, uf, ui, hrate, htpo, hfi, hsplit,
    hstate, hcf, hppi, htracked, hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv loan now pc hpc
  obtain ⟨fl, hfloor, hsp, hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  obtain ⟨hfN, hf0, hfB⟩ := hreach.fullInterest_le now rate tpo fi hnl hn hrate htpo hfi
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
  have ht : tN ≤ 10 ^ 16 + 1 := by
    have hT := hreach.totalValue_le
    have : (tN : ℚ) * 10 ^ loan.loanScale ≤ ((10 ^ 16 + 1 : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hTv]; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have hpm : (pN : ℤ) + mN ≤ 10 ^ 16 + 2 := by omega
  -- totalDue adds the value cleared, the interest beyond interestDue and the fees beyond the management fee
  unfold PaymentComponents.totalDue at hdue'
  obtain ⟨vpi, hvpi, hd⟩ := bind_ok_peel _ _ _ hdue'
  dsimp only at hvpi hd
  have hppi' := UnitsAt.add hpv hiv (by constructor <;> omega) hs hppi
  have htr := UnitsAt.add hppi' hmv (by constructor <;> omega) hs htracked
  have hnet' := UnitsAt.sub hav hbv (by constructor <;> omega) hs hnet
  have hui' := UnitsAt.sub hnet' hiv (by constructor <;> omega) hs hui
  have hvpi' := UnitsAt.add htr hui' (by constructor <;> omega) hs hvpi
  have hpoff : loan.payoffInterest now = .ok fi := by
    unfold Loan.payoffInterest
    rw [hrate, ok_bind, htpo, ok_bind, hfi]
  refine ⟨fun hfit => ?_, fun hls0 => ?_⟩
  swap
  · -- each rounding to nearest at most doubles a value
    have he := Number.nearestError_le
    have he0 := Number.nearestError_pos
    have h2 : 1 + Number.nearestError ≤ 2 := by linarith [show (1 : ℚ) / 10 ^ 18 ≤ 1 by norm_num]
    have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hls0
    have hcfmN := operator_add_isNormalized_to_nearest_sz _ _ _ gcf'.1 gfee.1 hcfm
    have hufN := operator_sub_isNormalized_to_nearest_sz _ _ _ hcfmN hmv.norm huf
    have b1 := (Number.add_near _ _ _ gcf'.1 gfee.1 hcfm).abs_le
    have b2 := (Number.sub_near _ _ _ hcfmN hmv.norm huf).abs_le
    have b3 := (Number.add_near _ _ _ hvpi'.norm hufN hd).abs_le
    have hsp0 : 0 ≤ split.toRat := hfee0
    rw [hcfv] at b1
    have e1 : |loan.fees.closePaymentFee.toRat + split.toRat| = loan.fees.closePaymentFee.toRat + split.toRat :=
      abs_of_nonneg (by linarith)
    rw [e1] at b1
    have hM : state.managementFeeDue.toRat ≤ 10 ^ 16 + 2 := by
      rw [hmv.val]
      push_cast
      have : (mN : ℚ) ≤ 10 ^ 16 + 2 := by exact_mod_cast (show (mN : ℤ) ≤ 10 ^ 16 + 2 by omega)
      have := mul_le_mul this hp1 (by positivity) (by positivity)
      linarith
    have hM0 : 0 ≤ state.managementFeeDue.toRat := by rw [hmv.val]; push_cast; positivity
    have hsp : split.toRat ≤ 143 * (10 ^ 16 + 1) := by
      rw [hbv']; have : (b : ℚ) ≤ 143 * (10 ^ 16 + 1) := by exact_mod_cast hab.trans ha
      have := mul_le_mul this hp1 (by positivity) (by positivity)
      linarith
    have hvpi : |vpi.toRat| ≤ 2 * 10 ^ 18 := by
      rw [hvpi'.val, abs_mul, abs_of_pos hu0]
      have hk : |((pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) : ℤ)| ≤ 2 * 10 ^ 18 := by
        rw [abs_le]; constructor <;> omega
      have hk' : |(((pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) : ℤ) : ℚ)| ≤
          2 * 10 ^ 18 := by exact_mod_cast hk
      have := mul_le_mul hk' hp1 (by positivity) (by positivity)
      linarith
    have c1 : |cfm.toRat| ≤ (loan.fees.closePaymentFee.toRat + split.toRat) * 2 :=
      b1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have c2 : |uf.toRat| ≤ (|cfm.toRat| + state.managementFeeDue.toRat) * 2 := by
      have hs' := abs_sub cfm.toRat state.managementFeeDue.toRat
      rw [abs_of_nonneg hM0] at hs'
      exact b2.trans (mul_le_mul hs' h2 (by linarith) (by positivity))
    have c3 : |p.totalPaid.toRat| ≤ (|vpi.toRat| + |uf.toRat|) * 2 :=
      b3.trans (mul_le_mul (abs_add_le vpi.toRat uf.toRat) h2 (by linarith) (by positivity))
    have := le_abs_self p.totalPaid.toRat
    linarith
  -- the payoff fits `2^63` units: TotalValueOutstanding + ⌊fullInterest⌋ + ClosePaymentFee
  have hc : (tN : ℤ) + a + c + 1 < 2 ^ 63 := by
    have h2 := hfit fi hpoff
    rw [hTv, ← hcfv, hcv'] at h2
    have : ((tN + a + c + 1 : ℕ) : ℚ) * 10 ^ loan.loanScale < (2 ^ 63 : ℚ) * 10 ^ loan.loanScale := by
      push_cast
      rw [hav'] at hfi_le
      nlinarith
    have : tN + a + c + 1 < 2 ^ 63 := by exact_mod_cast lt_of_mul_lt_mul_right this hu0.le
    omega
  have hcfm' := UnitsAt.add hcv hbv (by constructor <;> omega) hs hcfm
  have huf' := UnitsAt.sub hcfm' hmv (by constructor <;> omega) hs huf
  have hd' := UnitsAt.add hvpi' huf' (by constructor <;> omega) hs hd
  refine ⟨fi, hpoff, ?_⟩
  rw [hd'.val, hTv, ← hcfv, hcv']
  rw [hav'] at hfi_le
  have hle : (((pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) + ((c + b) - mN) : ℤ) : ℚ) ≤
      (tN : ℚ) + a + c + 1 := by
    have : (pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) + ((c + b) - mN) ≤
        (tN : ℤ) + a + c + 1 := by omega
    exact_mod_cast this
  nlinarith

/-- An active loan on a reachable ledger that is not late is reachable, not impaired, and has room for its payoff,
while the amounts fit the asset. -/
private lemma LendingLedger.Reachable.payoffRoom {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (hpr : loan.paymentRemaining ≠ 0) (hnl : l.now ≤ loan.nextPaymentDueDate)
    (hnp : loan.isPending = false)
    (hroom : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat +
      loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat < 10 ^ 80)
    (hsupply : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
        loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤ l.vault.numericType.maxValue.toNat ∧
      ∀ fi, loan.payoffInterest l.now = .ok fi →
        l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
          fi.toRat + loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤
          l.vault.numericType.maxValue.toNat) :
    ∃ t, loan.Reachable t ∧ loan.isImpaired = false ∧ loan.PayoffRoom l.vault l.now := by
  -- the loan is reachable, and not impaired as it is not late
  obtain ⟨t, ht, hre⟩ := hr.loanAt_reachable hat
  have himp : loan.isImpaired = false := by
    cases h : loan.isImpaired
    · rfl
    · have := Loan.Reachable.impaired_late_proof loan t hre h hpr
      simp only [Loan.isPaymentLate, decide_eq_true_eq] at this
      exact absurd (UInt32.lt_of_lt_of_le this ht) (UInt32.not_lt.mpr hnl)
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hasset := hr.holdsAsset
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  have hpo' : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hpend : e.loan.isPending = false := by
    rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw] at hnp; exact hnp
  have himp' : e.loan.isImpaired = false := by
    rw [show loan.isImpaired = loan.toRawLoan.isImpaired from rfl, hraw] at himp; exact himp
  have hie : loan.toExact.interestDue = e.loan.toExact.interestDue := by
    show loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat =
      e.loan.totalValueOutstanding.toRat - e.loan.principalOutstanding.toRat - e.loan.managementFeeOutstanding.toRat
    rw [show loan.totalValueOutstanding = loan.toRawLoan.totalValueOutstanding from rfl,
      show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl,
      show loan.managementFeeOutstanding = loan.toRawLoan.managementFeeOutstanding from rfl, hraw]
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hbase := Vault.baseExponent_scale_range l.vault
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  obtain ⟨-, -, -, -, hpdt⟩ := hr.loanAt_principal hat
  have hroomP : loan.PayoffRoom l.vault l.now := {
    numericType := hnt
    loanScale := hls
    asset := hasset
    gridA := hr.assetsAvailable_onGrid (by
      intro hint
      rcases hasset with h | h | h
      · rw [h] at hint; cases hint
      · rw [h]; decide
      · rw [h]; decide)
    debt := hr.loanAt_debt_units hat
    principal_debt := hpdt
    count := by
      rw [hlb]
      have hc := hr.loanCountInv.counted _ b hb
      have hpos := LendingLedger.loansOf_pos he
      intro h0
      rw [h0] at hc
      simp at hc
      omega
    deployed := hr.deployed_units
    loss := by
      rw [hpo', hr.lossInv.sum, hr.debtInv.deployed]
      exact LendingLedger.principalSum_add_le_all l (·.isImpaired) he himp'
    reserved := by
      rw [hpo', hr.reservedInv.sum, hr.debtInv.deployed]
      exact LendingLedger.principalSum_add_le_all l (·.isPending) he hpend
    yield := by rw [hie]; exact hr.interest_le_yield he hpend
    yield_lt := by
      have := hr.yield_lt
      have h1 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num) hp1
      linarith [show (10 : ℚ) ^ 16 < 10 ^ 150 by norm_num]
    room := hroom
    supply := hsupply }
  exact ⟨t, hre, himp, hroomP⟩

/-- The largest amount of the asset a LoanPay names here: `10^17` drops of XRP, `2^63 − 1` units of an MPT,
`9999999999999999·10^80` of an IOU. -/
private def payoffAmount (nt : NumericType) : Number :=
  if nt = .native then ⟨false, 1000000000000000000, -1⟩
  else if nt = .int64 then ⟨false, 9223372036854775807, 0⟩
  else ⟨false, 9999999999999999000, 77⟩

/-- An amount the asset holds exactly passes the conversion check of the LoanPay preflight. -/
private lemma STAmount.equalAfterNumberConvert_of_representable (nt : NumericType) (x : Number)
    (hn : x.isNormalized) (h0 : 0 ≤ x.toRat) (hrep : STAmount.Representable nt x.toRat) :
    STAmount.equalAfterNumberConvert nt x = .ok true := by
  have h := (STAmount.isRounded_eq_false_iff nt x hn h0).mpr hrep
  unfold STAmount.isRounded at h
  cases hc : STAmount.equalAfterNumberConvert nt x with
  | error e => rw [hc] at h; cases h
  | ok b => rw [hc] at h; cases b <;> simp_all

/-- The largest amount passes the LoanPay preflight. It is at least `10^95` of an IOU and at least the maximum of
XRP or an MPT, and below `2^63` of those. -/
private lemma payoffAmount_spec (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (pt : LoanPaymentType) :
    (LendingTx.loanPay i pt (payoffAmount l.vault.numericType)).preflight l = .tesSUCCESS ∧
      (payoffAmount l.vault.numericType).isNormalized ∧
      (l.vault.numericType = .fractional → (10 : ℚ) ^ 95 ≤ (payoffAmount l.vault.numericType).toRat) ∧
      (l.vault.numericType.isIntegral = true →
        (l.vault.numericType.maxValue.toNat : ℚ) ≤ (payoffAmount l.vault.numericType).toRat ∧
          (payoffAmount l.vault.numericType).toRat < 2 ^ 63) := by
  have pre : ∀ x : Number, isPositiveInput x = true →
      STAmount.equalAfterNumberConvert l.vault.numericType x = .ok true →
      (LendingTx.loanPay i pt x).preflight l = .tesSUCCESS := fun x h1 h2 => by
    simp only [LendingTx.preflight, h1, h2, Bool.true_and]
    rfl
  rcases hasset with h | h | h
  · have hA : payoffAmount l.vault.numericType = ⟨false, 9999999999999999000, 77⟩ := by
      rw [h]; unfold payoffAmount; rw [if_neg (by decide), if_neg (by decide)]
    have hv : (⟨false, 9999999999999999000, 77⟩ : Number).toRat = 9999999999999999 * 10 ^ (80 : ℤ) := by
      simp [Number.toRat]; norm_num
    rw [hA]
    refine ⟨pre _ (by decide) ?_, by decide, fun _ => by rw [hv]; norm_num, fun hi => by rw [h] at hi; cases hi⟩
    rw [h]
    exact STAmount.equalAfterNumberConvert_of_representable _ _ (by decide) (by rw [hv]; norm_num)
      (Or.inr ⟨9999999999999999, 80, by norm_num, by norm_num, by norm_num, by norm_num, by rw [hv]; push_cast; ring⟩)
  · have hA : payoffAmount l.vault.numericType = ⟨false, 1000000000000000000, -1⟩ := by
      rw [h]; unfold payoffAmount; rw [if_pos rfl]
    have hv : (⟨false, 1000000000000000000, -1⟩ : Number).toRat = 100000000000000000 := by
      simp [Number.toRat]; norm_num
    rw [hA]
    refine ⟨pre _ (by decide) ?_, by decide, fun hf => (by rw [h] at hf; cases hf), fun _ => ?_⟩
    · rw [h]
      exact STAmount.equalAfterNumberConvert_of_representable _ _ (by decide) (by rw [hv]; norm_num)
        (Or.inr ⟨by norm_num, 100000000000000000, by decide, by norm_num, by rw [hv]; norm_num⟩)
    · rw [h, hv]
      rw [show NumericType.native.maxValue.toNat = 100000000000000000 from rfl]
      norm_num
  · have hA : payoffAmount l.vault.numericType = ⟨false, 9223372036854775807, 0⟩ := by
      rw [h]; unfold payoffAmount; rw [if_neg (by decide), if_pos rfl]
    have hv : (⟨false, 9223372036854775807, 0⟩ : Number).toRat = 9223372036854775807 := by
      simp [Number.toRat, Rat.mkRat_eq_div]
    rw [hA]
    refine ⟨pre _ (by decide) ?_, by decide, fun hf => (by rw [h] at hf; cases hf), fun _ => ?_⟩
    · rw [h]
      exact STAmount.equalAfterNumberConvert_of_representable _ _ (by decide) (by rw [hv]; norm_num)
        (Or.inr ⟨by norm_num, 9223372036854775807, by decide, by norm_num, by rw [hv]; norm_num⟩)
    · rw [h, hv]
      rw [show NumericType.int64.maxValue.toNat = 9223372036854775807 from rfl]
      norm_num

/-- Proof body of the one-payment line of `Lending.Reachable.payoff_reachable`. The last regular instalment or the
full payment, of the largest amount the asset holds. -/
lemma LendingLedger.payoff_possible_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (hact : loan.canPay .regular = .tesSUCCESS) (hnl : l.now ≤ loan.nextPaymentDueDate)
    (hroom : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat +
      loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat < 10 ^ 80)
    (hsupply : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
        loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤ l.vault.numericType.maxValue.toNat ∧
      ∀ fi, loan.payoffInterest l.now = .ok fi →
        l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
          fi.toRat + loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤
          l.vault.numericType.maxValue.toNat) :
    ∃ (paymentType : LoanPaymentType) (amount : Number) (l' : LendingLedger) (loan' : Loan),
      (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l'.LoanAt i loan' ∧
        loan'.paymentRemaining = 0 := by
  obtain ⟨hnp, hpr, hpo⟩ := Loan.canPay_active hact
  obtain ⟨t, hre, himp, hroomP⟩ := hr.payoffRoom hat hpr hnl hnp hroom hsupply
  have hasset := hr.holdsAsset
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  have hS0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  have hT := hre.totalValue_le
  rw [hls] at hT
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 := le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  -- an integral loan is at LoanScale 0
  have hint0 : l.vault.numericType.isIntegral = true → loan.loanScale = 0 := fun hint =>
    hre.loanScale_integral (by rw [hnt]; exact hint)
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hnd := hr.live_of_loan he
  -- a payoff of `a` that the largest amount pays the same way is a successful LoanPay of that amount
  have key : ∀ pt (r : LoanWithAmounts Vault), loan.canPay pt = .tesSUCCESS → r.loan'.paymentRemaining = 0 →
      (loan.pay l.vault pt (payoffAmount l.vault.numericType) l.now).run = .ok (.ok r) →
      ∃ (paymentType : LoanPaymentType) (amount : Number) (l' : LendingLedger) (loan' : Loan),
        (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l'.LoanAt i loan' ∧
          loan'.paymentRemaining = 0 := by
    intro pt r hc hr0 hA
    refine ⟨pt, payoffAmount l.vault.numericType, l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool'), r.loan', ?_,
      l.loanAt_commit_ofLoan he hb _ _, hr0⟩
    rw [LendingLedger.apply_loanPay_eq he hb hw (payoffAmount_spec l hasset i pt).1 hnd hc]
    have hx : (loan.pay l.vault pt (payoffAmount l.vault.numericType) l.now : TerExcept (LoanWithAmounts Vault)) =
        ExceptT.mk (.ok (.ok r)) := hA
    rw [hx]
    rfl
  obtain ⟨-, hAN, hAfrac, hAint⟩ := payoffAmount_spec l hasset i .regular
  have hkind : l.vault.numericType = .fractional ∨ l.vault.numericType.isIntegral = true := by
    rcases hasset with h | h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)
  by_cases h1 : loan.paymentRemaining = 1
  · obtain ⟨a, r, hpay, hr0⟩ := Loan.regularPayoff_ok hre l.vault l.now hroomP h1 hpo hnl himp
    obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault .regular a l.now r hpay
    have htp := Loan.regularPay_last_totalPaid loan l.vault l.now h1 a p hp
    have hle : p.totalPaid.toRat ≤ (payoffAmount l.vault.numericType).toRat := by
      rcases hkind with hf | hint
      · have hn := (Number.add_near _ _ _ loan.wf.totalValueOutstanding_norm loan.wf.serviceFee_norm htp).le
          (by linarith)
        have h80 := hroom hf
        have he1 : 1 + Number.nearestError ≤ 2 := by
          linarith [Number.nearestError_le, show (1 : ℚ) / 10 ^ 18 ≤ 1 by norm_num]
        have := mul_le_mul_of_nonneg_left he1 (show 0 ≤ loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat
          by linarith)
        linarith [hAfrac hf, show (2 : ℚ) * (10 ^ 16 + 1 + 10 ^ 80) < 10 ^ 95 by norm_num]
      · have hs0 := hint0 hint
        have hsup := (hsupply hint).1
        have hv := Number.OnGrid.add_toRat (Loan.outstanding_onGrid loan).1 (Loan.Reachable.fees_onGrid hre).1
          (Loan.loanScale_bounds loan) (by
            rw [hs0, zpow_zero, mul_one, abs_of_nonneg (by linarith)]
            linarith [(hAint hint).1, (hAint hint).2]) htp
        rw [hv]
        linarith [(hAint hint).1]
    exact key .regular r hact hr0 (Loan.regularPay_last_amount loan l.vault l.now h1 a _ p r hp hpay hAN hle)
  · have h2 : 2 ≤ loan.paymentRemaining.toNat := by
      have a := UInt32.toNat_inj.not.mpr hpr
      have b := UInt32.toNat_inj.not.mpr h1
      simp at a b
      omega
    obtain ⟨a, r, hpay, hr0⟩ := Loan.fullPayoff_ok hre l.vault l.now hroomP h2 hpo hnl himp
    obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault .full a l.now r hpay
    obtain ⟨hexact, hcrude⟩ := Loan.full_totalPaid_le loan l.vault a l.now t p hre hp
    have hle : p.totalPaid.toRat ≤ (payoffAmount l.vault.numericType).toRat := by
      rcases hkind with hf | hint
      · have h80 := hroom hf
        have := hcrude (by rw [hls]; exact hbase.2)
        linarith [hAfrac hf, show (8 : ℚ) * 10 ^ 80 + 10 ^ 20 < 10 ^ 95 by norm_num]
      · have hs0 := hint0 hint
        obtain ⟨fi, hfi, hle⟩ := hexact fun fi hfi => by
          have := (hsupply hint).2 fi hfi
          rw [hs0, zpow_zero, mul_one]
          linarith [(hAint hint).1, (hAint hint).2]
        have := (hsupply hint).2 fi hfi
        rw [hs0, zpow_zero] at hle
        linarith [(hAint hint).1]
    exact key .full r (by rw [Loan.canPay_eq_regular loan (by decide)]; exact hact) hr0
      (Loan.fullPay_amount loan l.vault l.now a _ p r hp hpay hAN hle)

end XRPL.Model.Lending
