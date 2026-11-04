import XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
import XRPL.Properties.Lending.Loan.Common.PayoffComponents
import XRPL.Properties.Lending.Loan.Common.PayoffPay
import XRPL.Properties.Lending.Loan.Common.PaySize
import XRPL.Properties.Lending.Loan.Common.PaySums
import XRPL.Properties.Lending.Loan.Common.FullPaymentSize

/-! # A payment of exactly its amount due passes its instalments

A late or full payment of exactly the amount due of its instalment pays that instalment: the amounts it moves
and the loan it leaves compute, since every part of the instalment is far below the top of the `Number` range. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired Loan.doPayment
  roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private Loan.lateComponents_parts computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private loanLatePaymentInterest_le Loan.lateComponents_interest_le from XRPL.Properties.Lending.Loan.Common.PaySize
open private Loan.doPayment_late_ne_notLawful Loan.fullComponents_final
  from XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
open private rn_ge rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful

local notation "ε" => Number.nearestError

/-- A fee of a reachable loan is below `10^97`. The loan stores it as an amount its asset holds exactly. -/
lemma Loan.Reachable.fee_below {loan : Loan} {t : UInt32} (hr : loan.Reachable t) (x : Number)
    (hx : x ∈ loan.fees.amountFields) (hxN : x.isNormalized) (hx0 : 0 ≤ x.toRat) : x.Below 97 := by
  have hrep := (STAmount.isRounded_eq_false_iff _ x hxN hx0).mp (hr.fees_representable x hx)
  refine ⟨hxN, ?_⟩
  rw [abs_of_nonneg hx0]
  rcases hrep with h0 | h
  · rw [h0]; positivity
  · cases hnt : loan.broker.numericType with
    | integral mv mo ms msh =>
      rw [hnt] at h
      obtain ⟨-, k, -, hk, hv⟩ := h
      rw [hv]
      have hk' : k < 2 ^ 63 := by omega
      have : (k : ℚ) < 2 ^ 63 := by exact_mod_cast hk'
      linarith [show (2 : ℚ) ^ 63 < 10 ^ 97 by norm_num]
    | fractional =>
      rw [hnt] at h
      obtain ⟨m, e, -, hm, -, he, hv⟩ := h
      rw [hv]
      have hm' : (m : ℚ) < 10 ^ 16 := by exact_mod_cast hm
      have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
      have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
      calc (m : ℚ) * 10 ^ e ≤ 10 ^ 16 * 10 ^ (80 : ℤ) := by
            apply mul_le_mul hm'.le he' hp.le (by norm_num)
        _ < 10 ^ 97 := by norm_num

/-- The service, late and close fees of a reachable loan are at least zero and below `10^97`. -/
lemma Loan.Reachable.fees_below {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.fees.serviceFee.Below 97 ∧ 0 ≤ loan.fees.serviceFee.toRat ∧ loan.fees.latePaymentFee.Below 97 ∧
      0 ≤ loan.fees.latePaymentFee.toRat ∧ loan.fees.closePaymentFee.Below 97 ∧
      0 ≤ loan.fees.closePaymentFee.toRat := by
  have h1 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have h2 : 0 ≤ loan.fees.latePaymentFee.toRat := loan.exact.latePaymentFee_nonneg
  have h3 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  exact ⟨hr.fee_below _ (by simp [LoanFees.amountFields]) loan.wf.serviceFee_norm h1, h1,
    hr.fee_below _ (by simp [LoanFees.amountFields]) loan.wf.latePaymentFee_norm h2, h2,
    hr.fee_below _ (by simp [LoanFees.amountFields]) loan.wf.closePaymentFee_norm h3, h3⟩

/-- The amounts of an instalment whose parts are below `10^180` compute. -/
lemma PaymentComponents.paidAmounts_ok_of_below (pc : PaymentComponents) (h1 : pc.totalValueDelta.Below 180)
    (h2 : pc.principalDelta.Below 180) (h3 : pc.managementFeeDelta.Below 180) (h4 : pc.untrackedInterest.Below 180)
    (h5 : pc.untrackedManagementFee.Below 180) : ∃ a, pc.paidAmounts = .ok a := by
  obtain ⟨d1, hd1⟩ := Number.Below.sub_ok (by norm_num) h1 h2
  have b1 := Number.Below.sub h1 h2 hd1
  obtain ⟨d2, hd2⟩ := Number.Below.sub_ok (by norm_num) b1 (h3.mono (by norm_num))
  have b2 := Number.Below.sub b1 (h3.mono (by norm_num)) hd2
  obtain ⟨d3, hd3⟩ := Number.Below.add_ok (by norm_num) b2 (h4.mono (by norm_num))
  obtain ⟨d4, hd4⟩ := Number.Below.add_ok (by norm_num) h3 h5
  refine ⟨⟨pc.principalDelta, d3, d4⟩, ?_⟩
  unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta
  simp only [hd1, hd2, hd3, hd4, bind, Except.bind, pure, Except.pure]

/-- A re-check of a raw loan either passes or reports a loan that is not lawful. -/
lemma RawLoan.to_lawful_cases (rl : RawLoan) : (∃ l, rl.to_lawful = .ok l) ∨ rl.to_lawful = .error .notLawful := by
  unfold RawLoan.to_lawful
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

/-- An instalment that never fails the loan re-check computes while the loan's amounts and the instalment's
deltas are below `10^180`. -/
lemma Loan.doPayment_ok_of_below (l : Loan) (pc : PaymentComponents) (hne : Loan.doPayment l pc ≠ .error .notLawful)
    (h1 : pc.totalValueDelta.Below 180) (h2 : pc.principalDelta.Below 180) (h3 : pc.managementFeeDelta.Below 180)
    (hT : l.totalValueOutstanding.Below 180) (hP : l.principalOutstanding.Below 180)
    (hM : l.managementFeeOutstanding.Below 180) : ∃ l', Loan.doPayment l pc = .ok l' := by
  cases hf : pc.isFinal
  · obtain ⟨a, ha⟩ := Number.Below.sub_ok (by norm_num) hT h1
    obtain ⟨b, hb⟩ := Number.Below.sub_ok (by norm_num) hP h2
    obtain ⟨c, hc⟩ := Number.Below.sub_ok (by norm_num) hM h3
    have heq : Loan.doPayment l pc = RawLoan.to_lawful { l.toRawLoan with
        totalValueOutstanding := a, principalOutstanding := b, managementFeeOutstanding := c,
        paymentRemaining := l.paymentRemaining - 1, previousPaymentDueDate := l.nextPaymentDueDate,
        nextPaymentDueDate := l.nextPaymentDueDate + l.schedule.paymentInterval } := by
      unfold Loan.doPayment
      simp only [hf, Bool.false_eq_true, ↓reduceIte, ha, hb, hc, bind, Except.bind]
      rfl
    rw [heq] at hne ⊢
    rcases RawLoan.to_lawful_cases _ with h | h
    · exact h
    · exact absurd h hne
  · obtain ⟨l', hl', -⟩ := Loan.doPayment_final_ok l pc hf
    exact ⟨l', hl'⟩

/-- The last scheduled instalment takes the whole loan. A scheduled instalment marked final takes
TotalValueOutstanding, PrincipalOutstanding and ManagementFeeOutstanding, and nothing untracked. -/
lemma Loan.scheduledComponents_final_eq (l : Loan) (pc : PaymentComponents) (h : Loan.scheduledComponents l = .ok pc)
    (hf : pc.isFinal = true) :
    pc = { totalValueDelta := l.totalValueOutstanding, principalDelta := l.principalOutstanding,
           managementFeeDelta := l.managementFeeOutstanding, isFinal := true } := by
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, hrate, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', hpp', h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · exact (Except.ok.inj h).symm
  exfalso
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals (have h' := Except.ok.inj ‹pure _ = Except.ok pc›; rw [← h'] at hf; cases hf)

/-- A payment that passes the LoanPay checks is on an active loan with payments and principal left. -/
lemma Loan.canPay_active {loan : Loan} {pt : LoanPaymentType} (hc : loan.canPay pt = .tesSUCCESS) :
    loan.isPending = false ∧ loan.paymentRemaining ≠ 0 ∧ loan.principalOutstanding ≠ Number.zero := by
  unfold Loan.canPay at hc
  cases hp : loan.isPending
  · rw [hp] at hc
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    split_ifs at hc with h1 h2
    all_goals try cases hc
    rw [Loan.paid_off_iff] at h2
    push Not at h2
    exact ⟨rfl, h2⟩
  · rw [hp] at hc
    simp at hc

/-- The amounts a reachable loan owes at a scale at or below zero: each at least zero and below `10^17`, with
PrincipalOutstanding and ManagementFeeOutstanding together at most TotalValueOutstanding. -/
lemma Loan.Reachable.outstanding_below {loan : Loan} {t : UInt32} (hre : loan.Reachable t)
    (hls : loan.loanScale ≤ 0) :
    loan.totalValueOutstanding.Below 17 ∧ loan.principalOutstanding.Below 17 ∧
      loan.managementFeeOutstanding.Below 17 ∧ 0 ≤ loan.principalOutstanding.toRat ∧
      0 ≤ loan.managementFeeOutstanding.toRat ∧
      loan.principalOutstanding.toRat + loan.managementFeeOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
      loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 := by
  have hT := Loan.Reachable.totalValue_le hre
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hls
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 :=
    le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  have hi : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := hre.interestDue_nonneg
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hb : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
  refine ⟨⟨loan.wf.totalValueOutstanding_norm, ?_⟩, ⟨loan.wf.principalOutstanding_norm, ?_⟩,
    ⟨loan.wf.managementFeeOutstanding_norm, ?_⟩, hP0, hM0, by linarith, hT'⟩
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg hP0]; linarith
  · rw [abs_of_nonneg hM0]; linarith

/-- The scheduled parts of an instalment of a reachable loan: each below `10^17`, the fee part at least zero. -/
private lemma Loan.scheduledComponents_below {loan : Loan} {t : UInt32} (hre : loan.Reachable t)
    (hls : loan.loanScale ≤ 0) (pc : PaymentComponents) (hpc : Loan.scheduledComponents loan = .ok pc) :
    pc.totalValueDelta.Below 17 ∧ pc.principalDelta.Below 17 ∧ pc.managementFeeDelta.Below 17 ∧
      0 ≤ pc.managementFeeDelta.toRat := by
  obtain ⟨hlo, -, hint⟩ := hre.loanScale_facts
  obtain ⟨bT, bP, bM, hP0, hM0, hPM, hT⟩ := hre.outstanding_below hls
  rcases Loan.scheduledComponents_tracked loan pc (by omega) hint hre.interestDue_nonneg hpc with hf | ⟨-, ht⟩
  · rw [Loan.scheduledComponents_final_eq loan pc hpc hf]
    exact ⟨bT, bP, bM, hM0⟩
  · obtain ⟨g1, g2, g3, r1, r2, r3, -, -⟩ := ht
    have hb : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
    refine ⟨⟨g1.1, ?_⟩, ⟨g2.1, ?_⟩, ⟨g3.1, ?_⟩, r3.1⟩
    · rw [abs_of_nonneg r1.1]; linarith [r1.2]
    · rw [abs_of_nonneg r2.1]; linarith [r2.2]
    · rw [abs_of_nonneg r3.1]; linarith [r3.2]

/-- The parts of a late instalment of a reachable loan are below `10^100`, its fee parts at least zero. -/
lemma Loan.lateComponents_below {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (now : UInt32) (pc : PaymentComponents) (hpc : Loan.lateComponents loan now = .ok pc) :
    pc.totalValueDelta.Below 100 ∧ pc.principalDelta.Below 100 ∧ pc.managementFeeDelta.Below 100 ∧
      pc.untrackedInterest.Below 100 ∧ pc.untrackedManagementFee.Below 100 ∧
      0 ≤ pc.managementFeeDelta.toRat ∧ 0 ≤ pc.untrackedManagementFee.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hlo, hhi, hint⟩ := hre.loanScale_facts
  have hs : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hls
  obtain ⟨bT, bP, bM, hP0, hM0, hPM, hT⟩ := hre.outstanding_below hls
  obtain ⟨bS, hS0, bL, hL0, -, -⟩ := hre.fees_below
  obtain ⟨hui0, huiN, huile⟩ := Loan.lateComponents_interest_le loan now pc hs hint hpc
  obtain ⟨pc0, li, lr, split, net, sf, uf, hpc0, hli, hlr, hsplit, hnet, hsf, huf, rfl⟩ :=
    Loan.lateComponents_parts loan now pc hpc
  obtain ⟨b1, b2, b3, hm0⟩ := Loan.scheduledComponents_below hre hls pc0 hpc0
  obtain ⟨hliN, hli0, hlile⟩ := loanLatePaymentInterest_le loan now li hli
  have hlrN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hlr
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hliN hli0 (Or.inl rfl) hs hlr
  have hlrle := STAmount.roundToNumericType_to_nearest_le _ _ _ _ hliN hli0 hs hlr
  obtain ⟨gsp, hsp0, hsple⟩ := computeManagementFee_le _ _ _ _ _ hlrN hlr0 loan.broker.managementFeeRate_le hs hint
    hsplit
  have bsf := Number.Below.add bS bL hsf
  have hsf0 := operator_add_nonneg _ _ _ bS.1 bL.1 hsf (by linarith)
  have bsp : split.Below 98 := ⟨gsp.1, by
    rw [abs_of_nonneg hsp0]
    have : li.toRat ≤ 138 * (10 ^ 16 + 1) := by nlinarith
    linarith [show (2 : ℚ) * (138 * (10 ^ 16 + 1)) + 1 + 1 < 10 ^ 98 by norm_num]⟩
  have buf := Number.Below.add bsf bsp huf
  have huf0 := operator_add_nonneg _ _ _ bsf.1 bsp.1 huf (by linarith)
  refine ⟨b1.mono (by norm_num), b2.mono (by norm_num), b3.mono (by norm_num), ⟨huiN, ?_⟩,
    buf.mono (by norm_num), hm0, huf0⟩
  show |net.toRat| < 10 ^ 100
  have hui : net.toRat ≤ (276 * loan.principalOutstanding.toRat + 10 ^ loan.loanScale + 1) * (1 + ε) := huile
  rw [abs_of_nonneg hui0]
  have h1 : 276 * loan.principalOutstanding.toRat + 10 ^ loan.loanScale + 1 ≤ 276 * (10 ^ 16 + 1) + 2 := by
    linarith
  nlinarith

/-- On a reachable loan that passes the LoanPay checks, the payment's paid-off check and zero due date check pass. -/
private lemma Loan.payChecks_pass {loan : Loan} {t : UInt32} (hre : loan.Reachable t) {pt : LoanPaymentType}
    (hc : loan.canPay pt = .tesSUCCESS) :
    (loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = false ∧
      (loan.nextPaymentDueDate == 0) = false := by
  obtain ⟨-, hr, hpo⟩ := Loan.canPay_active hc
  exact ⟨Loan.not_paid_off loan hr hpo,
    Loan.nextPaymentDueDate_ne_zero loan (Loan.Reachable.nextPaymentDueDate_ne_zero loan t hre hr)⟩

/-- A late payment of at least its amount due pays its instalment on a reachable loan with LoanScale ≤ 0 that passes
the payment checks and is late, when the unimpair of an impaired loan passes. Its fee is at least zero. -/
lemma Loan.latePayInstalments_due {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (v : Vault) (now : UInt32) (hc : loan.canPay .late = .tesSUCCESS) (hlate : loan.isPaymentLate now = true)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (pc : PaymentComponents) (td amount : Number) (hpc : loan.paymentComponents .late now = .ok pc)
    (htd : pc.totalDue = .ok td) (hamt : amount.isNormalized) (hge : td.toRat ≤ amount.toRat) :
    ∃ q, (loan.payInstalments v .late amount now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat := by
  have hpc' : Loan.lateComponents loan now = .ok pc := hpc
  obtain ⟨b1, b2, b3, b4, b5, hm0, huf0⟩ := Loan.lateComponents_below hre hls now pc hpc'
  obtain ⟨a, ha⟩ := pc.paidAmounts_ok_of_below (b1.mono (by norm_num)) (b2.mono (by norm_num))
    (b3.mono (by norm_num)) (b4.mono (by norm_num)) (b5.mono (by norm_num))
  obtain ⟨hchk, hdd⟩ := Loan.payChecks_pass hre hc
  obtain ⟨-, hrem, -⟩ := Loan.canPay_active hc
  obtain ⟨bT, bP, bM, -⟩ := hre.outstanding_below hls
  obtain ⟨hlo, -, hint⟩ := hre.loanScale_facts
  have hshape : loan.PayShape := ⟨by omega, hint, hre.interestDue_nonneg⟩
  obtain ⟨v1, hu⟩ := Loan.unimpairIfImpaired_ok loan v hunimpair
  have hne := Loan.doPayment_late_ne_notLawful loan.unimpaired hshape.unimpaired now pc
    (by rw [Loan.lateComponents_unimpaired]; exact hpc') hrem
  obtain ⟨l', hl'⟩ := Loan.doPayment_ok_of_below loan.unimpaired pc hne (b1.mono (by norm_num))
    (b2.mono (by norm_num)) (b3.mono (by norm_num)) (bT.mono (by norm_num)) (bP.mono (by norm_num))
    (bM.mono (by norm_num))
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  have htdN : td.isNormalized := by
    unfold PaymentComponents.totalDue at htd
    obtain ⟨x, hx, htd⟩ := bind_ok_peel _ _ _ htd
    exact operator_add_isNormalized_to_nearest_sz _ _ _
      (operator_add_isNormalized_to_nearest_sz _ _ _ b1.1 b4.1 hx) b5.1 htd
  refine ⟨⟨l', v1, a, td, 1, i⟩, ?_, ?_⟩
  · simp only [ExceptT.run] at hu
    simp only [Loan.payInstalments, Loan.payInstalment]
    unfold_ter
    simp only [hchk, hdd, hlate, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hu, Loan.lateComponents_unimpaired,
      hpc', htd, (operator_lt_eq_false_iff amount td hamt htdN).mpr hge, Loan.interestDue_unimpaired, hi, ha, hl']
  · obtain ⟨-, -, -, -, -, hfee, -⟩ := PaymentComponents.paidAmounts_ok_inv pc a ha
    exact operator_add_nonneg _ _ _ b3.1 b5.1 hfee (by linarith)

/-- The parts of a full payment's instalment of a reachable loan are below `10^100`, and its two fee parts
add up to at least zero. -/
lemma Loan.fullComponents_below {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (now : UInt32) (hnl : now ≤ loan.nextPaymentDueDate) (hpr : 2 ≤ loan.paymentRemaining.toNat)
    (pc : PaymentComponents) (hpc : Loan.fullComponents loan now = .ok pc) :
    pc.totalValueDelta.Below 100 ∧ pc.principalDelta.Below 100 ∧ pc.managementFeeDelta.Below 100 ∧
      pc.untrackedInterest.Below 100 ∧ pc.untrackedManagementFee.Below 100 ∧
      0 ≤ pc.managementFeeDelta.toRat + pc.untrackedManagementFee.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hlo, hhi, hint⟩ := hre.loanScale_facts
  have hs : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hls
  obtain ⟨bT, bP, bM, hP0, hM0, hPM, hT⟩ := hre.outstanding_below hls
  obtain ⟨-, -, -, -, bC, hC0⟩ := hre.fees_below
  obtain ⟨rate, tpo, fi, net, split, state, cf, ppi, tracked, cfm, uf, ui, hrate, htpo, hfi, hsplit, hstate, hcf,
    hppi, htracked, hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv loan now pc hpc
  obtain ⟨hfiN, hfi0, hfile⟩ := hre.fullInterest_le now rate tpo fi hnl hpr hrate htpo hfi
  obtain ⟨fi', hfi', hsplit', hnet⟩ := roundAndSplitInterest_ok_inv fi _ _ _ _ net split hsplit
  obtain ⟨tv, p, m, -, -, -, htv, hpv, hmv, hiv, -, h1, h2, h3⟩ := Loan.state_units loan state hstate
  have hiD : state.interestDue.toRat = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := by
    rw [hiv.val, ← h1, ← h2, ← h3, htv.val, hpv.val, hmv.val]; push_cast; ring
  have bI : state.interestDue.Below 17 := ⟨hiv.norm, by
    rw [hiD, abs_of_nonneg (by linarith)]
    linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 17 by norm_num]⟩
  have bsP : state.principalOutstanding.Below 17 := by rw [h2]; exact bP
  have bsM : state.managementFeeDue.Below 17 := by rw [h3]; exact bM
  have bppi := Number.Below.add bsP bI hppi
  have btr := Number.Below.add bppi (bsM.mono (by norm_num)) htracked
  have hfi'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfi'
  have hfi'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfiN hfi0 (Or.inr (Or.inr rfl)) hs hfi'
  have hfi'le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfiN hfi0 hs hfi'
  obtain ⟨gsp, hsp0, hsple⟩ := computeManagementFee_le _ _ _ _ _ hfi'N hfi'0 loan.broker.managementFeeRate_le hs hint
    hsplit'
  have hfib : fi.toRat ≤ 143 * (10 ^ 16 + 1) := by
    have : 143 * ((10 ^ 16 + 1) * (10 : ℚ) ^ loan.loanScale) ≤ 143 * (10 ^ 16 + 1) := by
      have := mul_le_of_le_one_right (show (0 : ℚ) ≤ 10 ^ 16 + 1 by norm_num) hp1
      linarith
    linarith
  have b20 : (143 : ℚ) * (10 ^ 16 + 1) < 10 ^ 20 := by norm_num
  have bfi' : fi'.Below 20 := ⟨hfi'N, by rw [abs_of_nonneg hfi'0]; linarith⟩
  have bsp : split.Below 20 := ⟨gsp.1, by rw [abs_of_nonneg hsp0]; linarith⟩
  have bnet := Number.Below.sub bfi' bsp hnet
  have bui := Number.Below.sub bnet (bI.mono (by norm_num)) hui
  have hcfN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf
  have hcf0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ bC.1 hC0 (Or.inl rfl) hs hcf
  have hcfle := STAmount.roundToNumericType_to_nearest_le _ _ _ _ bC.1 hC0 hs hcf
  have bcf : cf.Below 98 := ⟨hcfN, by
    rw [abs_of_nonneg hcf0]
    have := bC.2
    rw [abs_of_nonneg hC0] at this
    linarith [show (2 : ℚ) * 10 ^ 97 + 1 + 1 < 10 ^ 98 by norm_num]⟩
  have bcfm := Number.Below.add bcf (bsp.mono (by norm_num)) hcfm
  have hcfm0 := operator_add_nonneg _ _ _ bcf.1 bsp.1 hcfm (by linarith)
  have buf := Number.Below.sub bcfm (bsM.mono (by norm_num)) huf
  have hufge : -state.managementFeeDue.toRat ≤ uf.toRat := by
    have := rn_ge (operator_sub_rounded_to_nearest _ _ _ bcfm.1 bsM.1 huf) state.managementFeeDue.operator_neg
      (Number.operator_neg_isNormalized _ bsM.1) (by rw [Number.toRat_neg]; linarith)
    rwa [Number.toRat_neg] at this
  refine ⟨btr.mono (by norm_num), bsP.mono (by norm_num), bsM.mono (by norm_num), bui.mono (by norm_num),
    buf.mono (by norm_num), ?_⟩
  show 0 ≤ state.managementFeeDue.toRat + uf.toRat
  linarith

/-- A full payment of at least its amount due pays off a reachable loan with LoanScale ≤ 0 that passes the checks, is
not late and has two or more payments left, when the unimpair of an impaired loan passes. Its fee is at least zero. -/
lemma Loan.fullPayInstalments_due {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (v : Vault) (now : UInt32) (hc : loan.canPay .full = .tesSUCCESS) (hnl : loan.isPaymentLate now = false)
    (hfull : loan.paymentRemaining ≠ 1)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (pc : PaymentComponents) (td amount : Number) (hpc : loan.paymentComponents .full now = .ok pc)
    (htd : pc.totalDue = .ok td) (hamt : amount.isNormalized) (hge : td.toRat ≤ amount.toRat) :
    ∃ q, (loan.payInstalments v .full amount now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat := by
  have hpc' : Loan.fullComponents loan now = .ok pc := hpc
  obtain ⟨hchk, hdd⟩ := Loan.payChecks_pass hre hc
  obtain ⟨-, hrem, -⟩ := Loan.canPay_active hc
  have h1 : ¬ loan.paymentRemaining ≤ 1 := by
    intro h
    have := UInt32.le_iff_toNat_le.mp h
    have h0 : loan.paymentRemaining.toNat ≠ 0 := fun h0 => hrem (UInt32.toNat_inj.mp (by simpa using h0))
    have h1' : loan.paymentRemaining.toNat ≠ 1 := fun h0 => hfull (UInt32.toNat_inj.mp (by simpa using h0))
    simp at this
    omega
  have hpr : 2 ≤ loan.paymentRemaining.toNat := by
    have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp h1)
    simpa using this
  have hnl' : now ≤ loan.nextPaymentDueDate := by
    simpa [Loan.isPaymentLate] using hnl
  obtain ⟨b1, b2, b3, b4, b5, hf0⟩ := Loan.fullComponents_below hre hls now hnl' hpr pc hpc'
  obtain ⟨a, ha⟩ := pc.paidAmounts_ok_of_below (b1.mono (by norm_num)) (b2.mono (by norm_num))
    (b3.mono (by norm_num)) (b4.mono (by norm_num)) (b5.mono (by norm_num))
  obtain ⟨v1, hu⟩ := Loan.unimpairIfImpaired_ok loan v hunimpair
  obtain ⟨l', hl', -⟩ := Loan.doPayment_final_ok loan.unimpaired pc (Loan.fullComponents_final loan now pc hpc')
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  have htdN : td.isNormalized := by
    unfold PaymentComponents.totalDue at htd
    obtain ⟨x, hx, htd⟩ := bind_ok_peel _ _ _ htd
    exact operator_add_isNormalized_to_nearest_sz _ _ _
      (operator_add_isNormalized_to_nearest_sz _ _ _ b1.1 b4.1 hx) b5.1 htd
  refine ⟨⟨l', v1, a, td, 1, i⟩, ?_, ?_⟩
  · simp only [ExceptT.run] at hu
    simp only [Loan.payInstalments, Loan.payInstalment]
    unfold_ter
    simp only [hchk, hdd, hnl, Bool.false_eq_true, ↓reduceIte, h1, hu, Loan.fullComponents_unimpaired, hpc', htd,
      (operator_lt_eq_false_iff amount td hamt htdN).mpr hge, Loan.interestDue_unimpaired, hi, ha, hl']
  · obtain ⟨-, -, -, -, -, hfee, -⟩ := PaymentComponents.paidAmounts_ok_inv pc a ha
    exact operator_add_nonneg _ _ _ b3.1 b5.1 hfee hf0

end XRPL.Model.Lending
