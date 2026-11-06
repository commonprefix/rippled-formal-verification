import XRPL.Properties.Lending.Loan.Common.NextInstalment
import XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
import XRPL.Properties.Lending.Loan.Common.PayMonotone
import XRPL.Properties.Lending.Loan.Common.OverpaymentSkip

/-! # The instalment loop of a regular payment computes

A regular payment pays scheduled instalments one at a time while its amount covers the next one. The running sums
stay far below the top of the `Number` range, so the loop computes whatever the amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments Loan.payScheduledInstalments
  Loan.unimpairIfImpaired UnsettledPayment.applyOverpayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_periodicPayment from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private Loan.doPayment_le from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private rn_ge from XRPL.Properties.Lending.Loan.Common.SetLawful

local notation "ε" => Number.nearestError

/-- What the instalment loop keeps about its loan so that the next scheduled instalment computes: shape, scale, small
amounts and fee, a schedule that computes, payments that fit the 32-bit clock and an asset its amounts fit. -/
structure Loan.LoopRoom (l : Loan) : Prop where
  shape : l.PayShape
  scale : l.loanScale ≤ 0
  value : l.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1
  computes : l.ScheduleComputes
  payments : 2 ≤ l.paymentRemaining.toNat →
    (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1)
  clock : l.paymentRemaining.toNat * l.schedule.paymentInterval.toNat < 2 ^ 32
  asset : l.broker.numericType = .fractional ∨ l.broker.numericType = .native ∨ l.broker.numericType = .int64
  fits : l.broker.numericType.isIntegral = true → 2 ≤ l.paymentRemaining.toNat →
    80 * ((l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat) + 1 ≤ l.broker.numericType.maxValue.toNat
  fee : l.fees.serviceFee.Below 97 ∧ 0 ≤ l.fees.serviceFee.toRat

/-- A scheduled instalment leaves nothing untracked. -/
lemma Loan.scheduledComponents_untracked (l : Loan) (pc : PaymentComponents)
    (h : Loan.scheduledComponents l = .ok pc) :
    pc.untrackedInterest = Number.zero ∧ pc.untrackedManagementFee = Number.zero := by
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    exact ⟨rfl, rfl⟩
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals (have h' := Except.ok.inj ‹pure _ = Except.ok pc›; rw [← h']; exact ⟨rfl, rfl⟩)

/-- On a `LoopRoom` loan the next scheduled instalment computes, with value, principal and fee parts each between
zero and `10^17` in size, and no untracked interest. -/
lemma Loan.LoopRoom.components {l : Loan} (h : l.LoopRoom) (hpr : l.paymentRemaining ≠ 0) :
    ∃ pc, Loan.scheduledComponents l = .ok pc ∧ pc.totalValueDelta.Below 17 ∧ pc.principalDelta.Below 17 ∧
      pc.managementFeeDelta.Below 17 ∧ 0 ≤ pc.totalValueDelta.toRat ∧ 0 ≤ pc.principalDelta.toRat ∧
      0 ≤ pc.managementFeeDelta.toRat ∧ pc.untrackedInterest = Number.zero := by
  have hs := h.shape
  obtain ⟨pc, hpc⟩ := Loan.scheduledComponents_computes l hs.1 h.scale hs.3 h.value h.computes h.payments h.clock
    h.asset h.fits hpr
  have hu := (Loan.scheduledComponents_untracked l pc hpc).1
  have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ l.managementFeeOutstanding.toRat := l.exact.managementFeeOutstanding_nonneg
  have hi : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat -
      l.managementFeeOutstanding.toRat := hs.3
  have hb : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
  have hT := h.value
  refine ⟨pc, hpc, ?_⟩
  rcases Loan.scheduledComponents_tracked l pc hs.1 hs.2 hs.3 hpc with hf | ⟨-, ht⟩
  · rw [Loan.scheduledComponents_final_eq l pc hpc hf]
    exact ⟨⟨l.wf.totalValueOutstanding_norm, by rw [abs_of_nonneg hT0]; linarith⟩,
      ⟨l.wf.principalOutstanding_norm, by rw [abs_of_nonneg hP0]; linarith⟩,
      ⟨l.wf.managementFeeOutstanding_norm, by rw [abs_of_nonneg hM0]; linarith⟩, hT0, hP0, hM0, rfl⟩
  · obtain ⟨g1, g2, g3, r1, r2, r3, -, -⟩ := ht
    exact ⟨⟨g1.1, by rw [abs_of_nonneg r1.1]; linarith [r1.2]⟩, ⟨g2.1, by rw [abs_of_nonneg r2.1]; linarith [r2.2]⟩,
      ⟨g3.1, by rw [abs_of_nonneg r3.1]; linarith [r3.2]⟩, r1.1, r2.1, r3.1, hu⟩

/-- A scheduled instalment that is not the last keeps the loop's room. -/
lemma Loan.LoopRoom.next {l l' : Loan} (h : l.LoopRoom) (pc : PaymentComponents) (fee : Number)
    (hpc : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) (hpr : l.paymentRemaining ≠ 0)
    (hdo : Loan.doPayment l { pc with untrackedManagementFee := fee } = .ok l') : l'.LoopRoom := by
  have hst := Loan.doPayment_sameTerms _ _ _ hdo
  have hpp := Loan.doPayment_periodicPayment _ _ _ hdo
  have hpr' := (Loan.doPayment_notFinal _ _ _ hf hdo).1
  have hprn : l'.paymentRemaining.toNat = l.paymentRemaining.toNat - 1 := by
    rw [hpr', UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le]
      have : l.paymentRemaining.toNat ≠ 0 := fun h0 => hpr (UInt32.toNat_inj.mp (by simpa using h0))
      simp; omega)]
    simp
  have hprle : l'.paymentRemaining.toNat ≤ l.paymentRemaining.toNat := by omega
  have hs := h.shape
  obtain ⟨pc', hpc', b1, b2, b3, h1, h2, h3, -⟩ := h.components hpr
  rw [hpc] at hpc'
  obtain rfl := Except.ok.inj hpc'
  have hle := Loan.doPayment_le l l' _ hpr (fun _ => ⟨b1.1, b2.1, b3.1, h1, h2, h3⟩) hdo
  have hpp0 : 0 ≤ l.periodicPayment.toRat := l.exact.periodicPayment_pos.le
  refine ⟨hs.doPayment pc _ hpc ⟨rfl, rfl, rfl, rfl⟩ hdo, by rw [hst.loanScale]; exact h.scale,
    le_trans hle.1 h.value, Loan.doPayment_computes l l' pc _ h.computes hpr hpc hdo rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h2'
    rw [hprn, hpp]
    have := h.payments (by omega)
    have hc : ((l.paymentRemaining.toNat - 1 : ℕ) : ℚ) ≤ l.paymentRemaining.toNat := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  · rw [hst.schedule]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hprle) h.clock
  · rw [hst.broker]; exact h.asset
  · intro hint h2'
    rw [hst.broker] at hint ⊢
    rw [hprn, hpp]
    have := h.fits hint (by omega)
    have hc : ((l.paymentRemaining.toNat - 1 : ℕ) : ℚ) ≤ l.paymentRemaining.toNat := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  · rw [hst.fees]; exact h.fee

/-- A to-nearest sum with a running total of `c` instalments stays within `c + 1` of them, each instalment
part below `10^99`. -/
private lemma Number.add_count {x y : Number} {c : ℕ} (hx : x.isNormalized) (hy : y.isNormalized)
    (hxl : |x.toRat| ≤ c * (2 * 10 ^ 99)) (hyl : |y.toRat| < 10 ^ 99) (hc : c ≤ 100) :
    ∃ r, x.operator_add y .to_nearest = .ok r ∧ r.isNormalized ∧ |r.toRat| ≤ ((c + 1 : ℕ) : ℚ) * (2 * 10 ^ 99) := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hcq : (c : ℚ) ≤ 100 := by exact_mod_cast hc
  obtain ⟨r, hr⟩ := Number.operator_add_ok_of_abs x y .to_nearest hx hy (by nlinarith) (by nlinarith)
  refine ⟨r, hr, operator_add_isNormalized_to_nearest_sz _ _ _ hx hy hr, ?_⟩
  have h1 := (Number.add_near _ _ _ hx hy hr).abs_le
  have h2 := abs_add_le x.toRat y.toRat
  have h3 : (c * (2 * 10 ^ 99) + 10 ^ 99 : ℚ) * (1 + ε) ≤ ((c + 1 : ℕ) : ℚ) * (2 * 10 ^ 99) := by
    push_cast
    nlinarith
  calc |r.toRat| ≤ |x.toRat + y.toRat| * (1 + ε) := h1
    _ ≤ (c * (2 * 10 ^ 99) + 10 ^ 99) * (1 + ε) := by gcongr; linarith
    _ ≤ _ := h3

/-- Adding an instalment's amounts to the running sums of `c` instalments computes, within `c + 1` of them,
and keeps the fee at least zero. -/
private lemma PaymentAmounts.add_count {a b : PaymentAmounts} {c : ℕ} (ha : a.Norm) (hb : b.Norm) (hc : c ≤ 100)
    (h1 : |a.principalPaid.toRat| ≤ c * (2 * 10 ^ 99)) (h2 : |a.interestPaid.toRat| ≤ c * (2 * 10 ^ 99))
    (h3 : |a.feePaid.toRat| ≤ c * (2 * 10 ^ 99)) (g1 : |b.principalPaid.toRat| < 10 ^ 99)
    (g2 : |b.interestPaid.toRat| < 10 ^ 99) (g3 : |b.feePaid.toRat| < 10 ^ 99) :
    ∃ r, a.add b = .ok r ∧ r.Norm ∧ |r.principalPaid.toRat| ≤ ((c + 1 : ℕ) : ℚ) * (2 * 10 ^ 99) ∧
      |r.interestPaid.toRat| ≤ ((c + 1 : ℕ) : ℚ) * (2 * 10 ^ 99) ∧
      |r.feePaid.toRat| ≤ ((c + 1 : ℕ) : ℚ) * (2 * 10 ^ 99) ∧
      (0 ≤ a.feePaid.toRat → 0 ≤ b.feePaid.toRat → 0 ≤ r.feePaid.toRat) := by
  obtain ⟨p, hp, hpN, hpl⟩ := Number.add_count ha.1 hb.1 h1 g1 hc
  obtain ⟨i, hi, hiN, hil⟩ := Number.add_count ha.2.1 hb.2.1 h2 g2 hc
  obtain ⟨f, hf', hfN, hfl⟩ := Number.add_count ha.2.2 hb.2.2 h3 g3 hc
  refine ⟨⟨p, i, f⟩, ?_, ⟨hpN, hiN, hfN⟩, hpl, hil, hfl, fun h0 h0' =>
    operator_add_nonneg _ _ _ ha.2.2 hb.2.2 hf' (by linarith)⟩
  unfold PaymentAmounts.add
  simp only [hp, hi, hf', bind, Except.bind, pure, Except.pure]

/-- The instalment loop computes on a `LoopRoom` loan, from running sums within the instalments paid so far.
It keeps the fee at least zero and never lowers the total paid. -/
lemma UnsettledPayment.payInstalments_computes {α : Type} (amount : Number) :
    ∀ (n : Nat) (p : UnsettledPayment α), p.loan.LoopRoom → p.count + n ≤ 100 → p.totalPaid.isNormalized →
      |p.totalPaid.toRat| ≤ p.count * (2 * 10 ^ 99) → p.amounts.Norm →
      |p.amounts.principalPaid.toRat| ≤ p.count * (2 * 10 ^ 99) →
      |p.amounts.interestPaid.toRat| ≤ p.count * (2 * 10 ^ 99) →
      |p.amounts.feePaid.toRat| ≤ p.count * (2 * 10 ^ 99) → 0 ≤ p.amounts.feePaid.toRat →
      ∃ p', UnsettledPayment.payInstalments p n amount = .ok p' ∧ 0 ≤ p'.amounts.feePaid.toRat ∧
        p.totalPaid.toRat ≤ p'.totalPaid.toRat ∧ p.count ≤ p'.count ∧ p'.totalPaid.isNormalized := by
  intro n
  induction n with
  | zero =>
    intro p _ _ htN _ _ _ _ _ hF
    exact ⟨p, by rw [UnsettledPayment.payInstalments]; rfl, hF, le_rfl, le_rfl, htN⟩
  | succ n ih =>
    intro p hroom hcnt htN htl hN hpl hil hfl hF
    have hcq : p.count ≤ 100 := by omega
    rw [UnsettledPayment.payInstalments]
    by_cases hpr0 : (p.loan.paymentRemaining == 0) = true
    · simp only [hpr0, ↓reduceIte, pure, Except.pure]
      exact ⟨p, rfl, hF, le_rfl, le_rfl, htN⟩
    have hpr : p.loan.paymentRemaining ≠ 0 := by simpa using hpr0
    obtain ⟨pc, hpc, b1, b2, b3, h1, h2, h3, hu⟩ := hroom.components hpr
    obtain ⟨bS, hS0⟩ := hroom.fee
    have hd1 : pc.totalValueDelta.operator_add pc.untrackedInterest .to_nearest = .ok pc.totalValueDelta := by
      rw [hu]; exact Number.operator_add_zero_right _ _
    obtain ⟨due, hdue⟩ := Number.Below.add_ok (by norm_num) (b1.mono (by norm_num)) bS
    have bdue := Number.Below.add (b1.mono (by norm_num)) bS hdue
    have hdue0 := operator_add_nonneg _ _ _ b1.1 bS.1 hdue (by linarith)
    have hdue' : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).totalDue =
        .ok due := by
      unfold PaymentComponents.totalDue
      simp only [hd1, hdue, bind, Except.bind]
    have hdl : |due.toRat| < 10 ^ 99 := lt_of_lt_of_le bdue.2 (by norm_num)
    obtain ⟨tp', htp', htp'N, htp'l⟩ := Number.add_count htN bdue.1 htl hdl hcq
    have htp'ge : p.totalPaid.toRat ≤ tp'.toRat := by
      have := rn_ge (operator_add_rounded_to_nearest _ _ _ htN bdue.1 htp') p.totalPaid htN (by linarith)
      exact this
    by_cases hlt : amount.operator_lt tp' = true
    · simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, bind, Except.bind, pure,
        Except.pure]
      exact ⟨p, rfl, hF, le_rfl, le_rfl, htN⟩
    obtain ⟨inst, hinst⟩ := PaymentComponents.paidAmounts_ok_of_below
      ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents)
      (b1.mono (by norm_num)) (b2.mono (by norm_num)) (b3.mono (by norm_num))
      (by show pc.untrackedInterest.Below 180; rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩)
      (bS.mono (by norm_num))
    obtain ⟨vap, id, hvap, hid, hip, hfp, hpp⟩ := PaymentComponents.paidAmounts_ok_inv _ inst hinst
    have bvap := Number.Below.sub b1 b2 hvap
    have bid := Number.Below.sub bvap (b3.mono (by norm_num)) hid
    have bip : inst.interestPaid.Below 99 := by
      have := Number.Below.add (bid.mono (by norm_num : 19 ≤ 98)) (show pc.untrackedInterest.Below 98 by
        rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩) hip
      exact this
    have bfp : inst.feePaid.Below 98 := Number.Below.add (b3.mono (by norm_num)) bS hfp
    have hfp0 : 0 ≤ inst.feePaid.toRat := operator_add_nonneg _ _ _ b3.1 bS.1 hfp (by linarith)
    have bpp : inst.principalPaid.Below 17 := by rw [hpp]; exact b2
    have hne := Loan.doPayment_scheduled_ne_notLawful p.loan hroom.shape pc
      ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents) hpc hpr ⟨rfl, rfl, rfl, rfl⟩
    have hT0 : 0 ≤ p.loan.totalValueOutstanding.toRat := p.loan.exact.totalValueOutstanding_nonneg
    have hP0 : 0 ≤ p.loan.principalOutstanding.toRat := p.loan.exact.principalOutstanding_nonneg
    have hM0 : 0 ≤ p.loan.managementFeeOutstanding.toRat := p.loan.exact.managementFeeOutstanding_nonneg
    have hi := hroom.shape.3
    have hTv := hroom.value
    have hb17 : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
    obtain ⟨l', hl'⟩ := Loan.doPayment_ok_of_below p.loan _ hne
      (fun hf => Loan.scheduledComponents_two_le _ _ hpc hpr hf) (b1.mono (by norm_num)) (b2.mono (by norm_num))
      (b3.mono (by norm_num)) ⟨p.loan.wf.totalValueOutstanding_norm, by rw [abs_of_nonneg hT0]; linarith⟩
      ⟨p.loan.wf.principalOutstanding_norm, by
        have : p.loan.principalOutstanding.toRat ≤ p.loan.totalValueOutstanding.toRat := by
          have : 0 ≤ p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
            p.loan.managementFeeOutstanding.toRat := hi
          linarith
        rw [abs_of_nonneg hP0]; linarith⟩
      ⟨p.loan.wf.managementFeeOutstanding_norm, by
        have : p.loan.managementFeeOutstanding.toRat ≤ p.loan.totalValueOutstanding.toRat := by
          have : 0 ≤ p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
            p.loan.managementFeeOutstanding.toRat := hi
          linarith
        rw [abs_of_nonneg hM0]; linarith⟩
    obtain ⟨am', ham', ham'N, hapl, hail, hafl, haf0⟩ := PaymentAmounts.add_count (c := p.count) hN
      ⟨bpp.1, bip.1, bfp.1⟩ hcq hpl hil hfl (lt_of_lt_of_le bpp.2 (by norm_num))
      (lt_of_lt_of_le bip.2 (by norm_num)) (lt_of_lt_of_le bfp.2 (by norm_num))
    have hF' := haf0 hF hfp0
    by_cases hfin : pc.isFinal = true
    · simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, hinst, hl', ham', bind,
        Except.bind, pure, Except.pure]
      simp only [hfin, ↓reduceIte]
      exact ⟨_, rfl, hF', htp'ge, Nat.le_succ _, htp'N⟩
    have hf : pc.isFinal = false := by simpa using hfin
    have hroom' := hroom.next pc _ hpc hf hpr hl'
    obtain ⟨p', hp', hF'', hge, hcge, hp'N⟩ :=
      ih { p with loan := l', amounts := am', totalPaid := tp', count := p.count + 1 }
      hroom' (by simp only; omega) htp'N (by simpa using htp'l) ham'N (by simpa using hapl) (by simpa using hail)
      (by simpa using hafl) hF'
    simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, hinst, hl', ham', bind,
      Except.bind, pure, Except.pure]
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨p', hp', hF'', le_trans htp'ge hge, le_trans (Nat.le_succ _) hcge, hp'N⟩

/-- A loan without the impaired flag keeps the loop's room. -/
lemma Loan.LoopRoom.unimpaired {l : Loan} (h : l.LoopRoom) : l.unimpaired.LoopRoom :=
  ⟨h.shape.unimpaired, h.scale, h.value, ⟨h.computes.1, h.computes.2, h.computes.3⟩, h.payments, h.clock, h.asset,
    h.fits, h.fee⟩

/-- A regular payment of at least its amount due pays its instalments on a `LoopRoom` loan that passes the
checks and is not late, when its unimpair passes. Its fee is at least zero and it pays at least the amount due. -/
lemma Loan.regularPayInstalments_due (loan : Loan) (hroom : loan.LoopRoom) (v : Vault) (now : UInt32)
    (hc : loan.canPay .regular = .tesSUCCESS) (hdd : loan.nextPaymentDueDate ≠ 0)
    (hnl : loan.isPaymentLate now = false)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (pc : PaymentComponents) (td amount : Number) (hpc : loan.paymentComponents .regular now = .ok pc)
    (htd : pc.totalDue = .ok td) (hamt : amount.isNormalized) (hge : td.toRat ≤ amount.toRat) :
    ∃ q, (loan.payInstalments v .regular amount now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat ∧
      td.toRat ≤ q.totalPaid.toRat ∧ q.totalPaid.isNormalized := by
  obtain ⟨-, hrem, hpo⟩ := Loan.canPay_active hc
  have hpc' : (Loan.scheduledComponents loan >>= fun pc0 =>
      pure { pc0 with untrackedManagementFee := loan.fees.serviceFee }) = Except.ok pc := hpc
  obtain ⟨pc0, hpc0, hpce⟩ := bind_ok_peel _ _ _ hpc'
  obtain rfl := (Except.ok.inj hpce).symm
  have hroom' := hroom.unimpaired
  obtain ⟨pc1, hpc1, b1, b2, b3, h1, h2, h3, hu⟩ := hroom'.components hrem
  rw [Loan.scheduledComponents_unimpaired, hpc0] at hpc1
  obtain rfl := Except.ok.inj hpc1
  obtain ⟨bS, hS0⟩ := hroom.fee
  obtain ⟨vap, id, ip, fp, hvap, hid, hip, hfp⟩ : ∃ vap id ip fp,
      pc0.totalValueDelta.operator_sub pc0.principalDelta .to_nearest = .ok vap ∧
      vap.operator_sub pc0.managementFeeDelta .to_nearest = .ok id ∧
      id.operator_add pc0.untrackedInterest .to_nearest = .ok ip ∧
      pc0.managementFeeDelta.operator_add loan.fees.serviceFee .to_nearest = .ok fp := by
    obtain ⟨vap, hvap⟩ := Number.Below.sub_ok (by norm_num) b1 b2
    have bvap := Number.Below.sub b1 b2 hvap
    obtain ⟨id, hid⟩ := Number.Below.sub_ok (by norm_num) bvap (b3.mono (by norm_num))
    have bid := Number.Below.sub bvap (b3.mono (by norm_num)) hid
    obtain ⟨ip, hip⟩ := Number.Below.add_ok (by norm_num) bid (show pc0.untrackedInterest.Below 19 by
      rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩)
    obtain ⟨fp, hfp⟩ := Number.Below.add_ok (by norm_num) (b3.mono (by norm_num)) bS
    exact ⟨vap, id, ip, fp, hvap, hid, hip, hfp⟩
  have bvap := Number.Below.sub b1 b2 hvap
  have bid := Number.Below.sub bvap (b3.mono (by norm_num)) hid
  have bip : ip.Below 20 := Number.Below.add bid (show pc0.untrackedInterest.Below 19 by
      rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩) hip
  have bfp : fp.Below 98 := Number.Below.add (b3.mono (by norm_num)) bS hfp
  have hfp0 : 0 ≤ fp.toRat := operator_add_nonneg _ _ _ b3.1 bS.1 hfp (by linarith)
  set pc := ({ pc0 with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents) with hpcdef
  have hinst : pc.paidAmounts = .ok ⟨pc0.principalDelta, ip, fp⟩ := by
    unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta
    simp only [hpcdef, hvap, hid, hip, hfp, bind, Except.bind, pure, Except.pure]
  have htd' := htd
  have hd1 : pc0.totalValueDelta.operator_add pc0.untrackedInterest .to_nearest = .ok pc0.totalValueDelta := by
    rw [hu]; exact Number.operator_add_zero_right _ _
  obtain ⟨due, hdue⟩ := Number.Below.add_ok (by norm_num) (b1.mono (by norm_num)) bS
  have bdue := Number.Below.add (b1.mono (by norm_num)) bS hdue
  have hdue' : pc.totalDue = .ok due := by
    unfold PaymentComponents.totalDue
    simp only [hpcdef, hd1, hdue, bind, Except.bind]
  rw [hdue'] at htd'
  obtain rfl := Except.ok.inj htd'
  have hshape := hroom.shape
  have hne := Loan.doPayment_scheduled_ne_notLawful loan.unimpaired hroom'.shape pc0 pc
    (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) hrem ⟨rfl, rfl, rfl, rfl⟩
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hi : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := hshape.3
  have hTv := hroom.value
  have hb17 : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
  have bT : loan.unimpaired.totalValueOutstanding.Below 180 :=
    ⟨loan.wf.totalValueOutstanding_norm, by
      show |loan.totalValueOutstanding.toRat| < _
      rw [abs_of_nonneg hT0]; linarith⟩
  have bP : loan.unimpaired.principalOutstanding.Below 180 :=
    ⟨loan.wf.principalOutstanding_norm, by
      show |loan.principalOutstanding.toRat| < _
      rw [abs_of_nonneg hP0]; linarith⟩
  have bM : loan.unimpaired.managementFeeOutstanding.Below 180 :=
    ⟨loan.wf.managementFeeOutstanding_norm, by
      show |loan.managementFeeOutstanding.toRat| < _
      rw [abs_of_nonneg hM0]; linarith⟩
  obtain ⟨l1, hl1⟩ := Loan.doPayment_ok_of_below loan.unimpaired pc hne
    (fun hf => Loan.scheduledComponents_two_le _ pc0 (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) hrem hf)
    (b1.mono (by norm_num))
    (b2.mono (by norm_num)) (b3.mono (by norm_num)) bT bP bM
  obtain ⟨si, hsi⟩ := Loan.interestDue_ok loan
  obtain ⟨v1, hv1⟩ := Loan.unimpairIfImpaired_ok loan v hunimpair
  have hfee : loan.unimpaired.fees.serviceFee = loan.fees.serviceFee := rfl
  have hdueN := bdue.1
  have bdue98 : due.Below 98 := bdue.mono (by norm_num)
  obtain ⟨q, hloop, hqF, hqtp, hqc, hqN⟩ : ∃ q, UnsettledPayment.payInstalments
      (⟨loan.unimpaired, v1, PaymentAmounts.zero, Number.zero, 0, si⟩ : UnsettledPayment Vault)
      maxPaymentsPerTransaction amount = .ok q ∧ 0 ≤ q.amounts.feePaid.toRat ∧ due.toRat ≤ q.totalPaid.toRat ∧
      1 ≤ q.count ∧ q.totalPaid.isNormalized := by
    rw [show maxPaymentsPerTransaction = 99 + 1 from rfl, UnsettledPayment.payInstalments]
    have hpr0 : (loan.unimpaired.paymentRemaining == 0) = false := by simpa using hrem
    simp only [hpr0, Bool.false_eq_true, ↓reduceIte, Loan.scheduledComponents_unimpaired, hpc0, hfee, bind,
      Except.bind]
    rw [show ({ pc0 with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents) = pc from rfl]
    simp only [hdue', Number.operator_add_zero_left, (operator_lt_eq_false_iff amount due hamt hdueN).mpr hge,
      Bool.false_eq_true,
      ↓reduceIte, hinst, hl1, PaymentAmounts.zero_add, pure, Except.pure]
    by_cases hfin : pc0.isFinal = true
    · simp only [hfin, ↓reduceIte]
      exact ⟨_, rfl, hfp0, le_rfl, le_rfl, hdueN⟩
    have hf : pc0.isFinal = false := by simpa using hfin
    have hroom1 := hroom'.next pc0 loan.fees.serviceFee (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0)
      hf hrem hl1
    obtain ⟨q, hq, hqF, hqtp, hqc, hqN⟩ := UnsettledPayment.payInstalments_computes amount 99
      (⟨l1, v1, ⟨pc0.principalDelta, ip, fp⟩, due, 1, si⟩ : UnsettledPayment Vault) hroom1 (by norm_num)
      hdueN (by simp only; push_cast; linarith [bdue98.2, show (10 : ℚ) ^ 98 < 2 * 10 ^ 99 by norm_num])
      ⟨b2.1, bip.1, bfp.1⟩
      (by simp only; push_cast; linarith [b2.2, show (10 : ℚ) ^ 17 < 2 * 10 ^ 99 by norm_num])
      (by simp only; push_cast; linarith [bip.2, show (10 : ℚ) ^ 20 < 2 * 10 ^ 99 by norm_num])
      (by simp only; push_cast; linarith [bfp.2, show (10 : ℚ) ^ 98 < 2 * 10 ^ 99 by norm_num]) hfp0
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨q, hq, hqF, hqtp, hqc, hqN⟩
  have hcount : (q.count == 0) = false := by simp; omega
  refine ⟨q, ?_, hqF, hqtp, hqN⟩
  simp only [ExceptT.run] at hv1
  simp only [Loan.payInstalments, Loan.payScheduledInstalments]
  unfold_ter
  simp only [Loan.not_paid_off loan hrem hpo, Loan.nextPaymentDueDate_ne_zero loan hdd, hnl, Bool.false_eq_true,
    ↓reduceIte, hv1, Loan.interestDue_unimpaired, hsi, hloop, hcount]

/-- An overpayment that passes the LoanPay checks passes them as a regular payment too. -/
lemma Loan.canPay_regular_of_overpayment {loan : Loan} (hc : loan.canPay .overpayment = .tesSUCCESS) :
    loan.canPay .regular = .tesSUCCESS := by
  obtain ⟨hp, hr, hpo⟩ := Loan.canPay_active hc
  unfold Loan.canPay
  simp [hp, Loan.not_paid_off loan hr hpo]

/-- An overpayment of exactly its amount due pays the same instalments as a regular payment and no overpayment
tail, when the loan's asset holds the amount exactly. Its fee is at least zero. -/
lemma Loan.overPayInstalments_due (loan : Loan) (hroom : loan.LoopRoom) (v : Vault) (now : UInt32)
    (hc : loan.canPay .overpayment = .tesSUCCESS) (hdd : loan.nextPaymentDueDate ≠ 0)
    (hnl : loan.isPaymentLate now = false)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (pc : PaymentComponents) (td : Number) (hpc : loan.paymentComponents .overpayment now = .ok pc)
    (htd : pc.totalDue = .ok td) (htdN : td.isNormalized) (htd0 : 0 ≤ td.toRat)
    (hrep : STAmount.isRounded loan.broker.numericType td = false) :
    ∃ q, (loan.payInstalments v .overpayment td now).run = .ok (.ok q) ∧
      (loan.payInstalments v .regular td now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat := by
  obtain ⟨q, hq, hqF, hqtp, hqN⟩ := Loan.regularPayInstalments_due loan hroom v now
    (Loan.canPay_regular_of_overpayment hc) hdd hnl hunimpair pc td td hpc htd htdN le_rfl
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular td now q hq
  have hqb : q.loan.broker = loan.broker := hst.broker
  have hqs : q.loan.loanScale = loan.loanScale := hst.loanScale
  have hskip := UnsettledPayment.applyOverpayment_skips q td htdN htd0 (by rw [hqb]; exact hrep)
    (by rw [hqb]; exact hroom.asset) (by rw [hqs]; exact ⟨hroom.shape.1, hroom.scale⟩) hqN hqtp
  refine ⟨q, ?_, hq, hqF⟩
  have hq' : (Loan.payScheduledInstalments loan v td now).run = .ok (.ok q) := hq
  simp only [Loan.payInstalments]
  unfold_ter
  simp only [ExceptT.run] at hq'
  simp [hq', hskip]

end XRPL.Model.Lending
