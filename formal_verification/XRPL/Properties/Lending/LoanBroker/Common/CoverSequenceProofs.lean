import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy

/-! # Proof bodies for cover operations run one after another

Proofs for the theorems in `LoanBrokerCover.lean`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- **Proof body of `coverDeposit_coverWithdraw_restores`.** -/
lemma LoanBroker.coverDeposit_coverWithdraw_restores_proof (lb : LoanBroker)
    (amount : STAmount) (res res' : LoanBrokerCoverResult)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hwd : res.loanBroker'.coverWithdraw res.amount' = .ok (.ok res'))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hdep hc hexact
  have hcr := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hdep hc).1
  have hdown := LoanBroker.coverWithdraw_debit_request res.loanBroker' res.amount' res' hwd hcr
    ⟨lb.coverAvailable, lb.wf.coverAvailable_norm, by
      show lb.toExact.coverAvailable = _; linarith⟩
  linarith

/-- **Proof body of `coverDeposit_withdrawable`.** -/
lemma LoanBroker.coverDeposit_withdrawable_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (res : LoanBrokerCoverResult) (e : Int)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hcap : lb.toExact.coverAvailable + res.amount'.toRat < 10 ^ 96)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) (hmin : lb.HasMinimumCover e)
    (hcheck : canApplyToBrokerCover res.loanBroker'.numericType res.loanBroker'.coverAvailable
      res.amount' = .ok .tesSUCCESS) :
    res.loanBroker'.canCoverWithdraw pool res.amount' = .ok .tesSUCCESS := by
  -- the deposit only changed `coverAvailable`, by exactly the credited amount
  have hf := LoanBroker.coverDeposit_fixed_fields lb amount res hdep
  have hnt := hf.numericType
  have hdebt := hf.debtTotal
  have hrate := hf.coverRateMinimum
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hdep hc hexact
  have hcr := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hdep hc).1
  have hnr := (LoanBroker.coverDeposit_amount_bounds lb amount res hdep hc hnn).1
  have hc1 : res.loanBroker'.coverAvailable.toRat =
      lb.coverAvailable.toRat + res.amount'.toRat := by
    show res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable + res.amount'.toRat
    linarith
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hcn1 := res.loanBroker'.wf.coverAvailable_norm
  -- the credited amount converts exactly
  obtain ⟨aN, hnum, hav, han⟩ := STAmount.toNumber_exact_canonical res.amount' .to_nearest hcr
  have halt : res.amount'.toRat < 10 ^ 96 :=
    lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt res.amount' hcr)
  -- `coverAvailable` covers the amount
  have hge : res.loanBroker'.coverAvailable.operator_lt aN = false :=
    (operator_lt_eq_false_iff _ _ hcn1 han).mpr (by rw [hav, hc1]; linarith)
  -- the subtraction succeeds and gives back the starting cover exactly
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt res.loanBroker'.coverAvailable aN .to_nearest
    hcn1 han (by rw [hc1]; linarith) (by rw [hc1]; exact hcap) (by rw [hav]; exact hnr)
    (by rw [hav]; exact halt)
  have hc' : c'.toRat = lb.coverAvailable.toRat := by
    rw [Number.roundsToRepresentable_eq c' (res.loanBroker'.coverAvailable.toRat - aN.toRat)
      (operator_sub_rounded_to_nearest _ _ _ hcn1 han hsub) lb.coverAvailable
      lb.wf.coverAvailable_norm (by rw [hav, hc1]; ring), hav, hc1]
    ring
  have hcn' : c'.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ _ hcn1 han hsub
  -- the starting cover was at least the minimum cover, and the debt is unchanged
  have h0 := hmin
  unfold LoanBroker.HasMinimumCover RawLoanBroker.hasMinimumCover at h0
  obtain ⟨m, hm, _⟩ := bind_ok_peel _ _ _ h0
  have hle := (LoanBroker.hasMinimumCover_iff lb e m hm).mp hmin
  have hmin' : ({ res.loanBroker'.toRawLoanBroker with coverAvailable := c' } :
      RawLoanBroker).hasMinimumCover e = .ok true := by
    show (do
        let minimumCover ← minimumBrokerCover res.loanBroker'.numericType
          res.loanBroker'.debtTotal res.loanBroker'.coverRateMinimum e
        return minimumCover.operator_le c') = Except.ok true
    rw [hnt, hdebt, hrate, hm]
    simp only [ok_bind, pure_eq, Except.ok.injEq]
    exact (operator_le_iff m c' (minimumBrokerCover_isNormalized _ _ _ _ _ hm) hcn').mpr
      (by rw [hc']; exact hle)
  exact LoanBroker.canCoverWithdraw_success_proof res.loanBroker' pool res.amount' e aN c' hcheck
    (by rw [hnt]; exact hexp) hnum hge hsub hmin'

/-- **Proof body of `coverDeposit_coverClawback_restores`.** -/
lemma LoanBroker.coverDeposit_coverClawback_restores_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (res res' : LoanBrokerCoverResult)
    (hdebt : lb.debtTotal = Number.zero)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hclaw : res.loanBroker'.coverClawback pool (some res.amount') = .ok (.ok res'))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hat : amount.mNumericType = lb.numericType)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  -- the deposit only changed `coverAvailable`, by exactly the credited amount
  have hf := LoanBroker.coverDeposit_fixed_fields lb amount res hdep
  have hnt := hf.numericType
  have hdebt' : res.loanBroker'.debtTotal = Number.zero := hf.debtTotal.trans hdebt
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hdep hc hexact
  obtain ⟨hcr, hcrt⟩ := LoanBroker.coverDeposit_amount_exactCanonical lb amount res hdep hc
  have hnr := (LoanBroker.coverDeposit_amount_bounds lb amount res hdep hc hnn).1
  have hcov0 : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  -- a deposit credits a nonzero amount
  have hza : res.amount'.isZero = false := by
    simp [STAmount.isZero, LoanBroker.coverDeposit_amount_nonzero lb amount res hdep]
  -- with no debt the minimum cover is zero, so the whole new cover can be clawed
  obtain ⟨claw, hrr, _⟩ := LoanBroker.coverClawback_ok_inv res.loanBroker' pool _ res' hclaw
  obtain ⟨e, m, he, hm⟩ := LoanBroker.roundedCoverClawback_minimum res.loanBroker' pool _ claw hrr
  have hm0' : m.toRat = 0 := by
    have h := hm
    rw [hdebt', minimumBrokerCover_zero_debt, Except.ok.injEq] at h
    rw [← h, Number.toRat_zero]
  -- the clawback takes back exactly the credited amount
  obtain ⟨mag, hmagn, hmagv, hcl⟩ := LoanBroker.coverClawback_request res.loanBroker' pool
    res.amount' res' e m hclaw hcr hza he hm (by rw [hm0']; linarith)
  have hm0 : 0 ≤ mag.toRat := by rw [hmagv]; exact hnr
  -- the credited amount is nonzero and canonical, so the clawed amount is nonzero
  have hnz : res'.amount'.mValue ≠ 0 := STAmount.ofNumber_ne_zero_of_canonical _ mag .to_nearest
    res'.amount' res.amount' hmagn hcr (by rw [hnt, hcrt]; exact hat)
    (LoanBroker.coverDeposit_amount_nonzero lb amount res hdep) hmagv hcl
  have hback : res'.amount'.toRat = res.amount'.toRat :=
    STAmount.ofNumber_to_nearest_eq_of_canonical _ mag res'.amount' res.amount' hmagn hm0 hcr
      (by rw [hnt, hcrt]; exact hat) hmagv hcl
  have hc' : res'.amount'.ExactCanonical :=
    STAmount.ofNumber_exactCanonical _ mag .to_nearest _ hmagn hm0 hcl hnz
  have hdown := LoanBroker.coverClawback_debit_of_canonical res.loanBroker' pool _ res' hclaw hc'
    ⟨lb.coverAvailable, lb.wf.coverAvailable_norm, by
      show lb.toExact.coverAvailable = _; rw [hback]; linarith⟩
  linarith

/-- **Proof body of `coverDeposit_clawable`.** -/
lemma LoanBroker.coverDeposit_clawable_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (claw : STAmount)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hat : amount.mNumericType = lb.numericType)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) (hmin : lb.HasMinimumCover e)
    (hrr : res.loanBroker'.roundedCoverClawback pool (some res.amount') = .ok (.rounded claw))
    (hcheck : canApplyToBrokerCover res.loanBroker'.numericType res.loanBroker'.coverAvailable
      res.amount' = .ok .tesSUCCESS) :
    claw = res.amount' ∧
      res.loanBroker'.canCoverClawback pool (some res.amount') = .ok .tesSUCCESS := by
  -- the deposit only changed `coverAvailable`, by exactly the credited amount
  have hf := LoanBroker.coverDeposit_fixed_fields lb amount res hdep
  have hnt := hf.numericType
  have hdebt := hf.debtTotal
  have hrate := hf.coverRateMinimum
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hdep hc hexact
  obtain ⟨hcr, hcrt⟩ := LoanBroker.coverDeposit_amount_exactCanonical lb amount res hdep hc
  have hnr := (LoanBroker.coverDeposit_amount_bounds lb amount res hdep hc hnn).1
  have hza : res.amount'.isZero = false := by
    simp [STAmount.isZero, LoanBroker.coverDeposit_amount_nonzero lb amount res hdep]
  -- the cover was at least the minimum cover, so the credited amount fits above it
  have h0 := hmin
  unfold LoanBroker.HasMinimumCover RawLoanBroker.hasMinimumCover at h0
  obtain ⟨m, hm, _⟩ := bind_ok_peel _ _ _ h0
  have hle := (LoanBroker.hasMinimumCover_iff lb e m hm).mp hmin
  have hfit : res.amount'.toRat ≤ res.loanBroker'.toExact.coverAvailable - m.toRat := by linarith
  -- the clawed amount is the credited amount
  obtain ⟨mag, hmagn, hmagv, hcl⟩ := LoanBroker.roundedCoverClawback_request res.loanBroker' pool
    res.amount' claw e m hcr hza (by rw [hnt]; exact hexp) (by rw [hnt, hdebt, hrate]; exact hm)
    hfit hrr
  have hat' : res.amount'.mNumericType = res.loanBroker'.numericType := by rw [hnt, hcrt]; exact hat
  have hm0 : 0 ≤ mag.toRat := by rw [hmagv]; exact hnr
  have hnz : claw.mValue ≠ 0 := STAmount.ofNumber_ne_zero_of_canonical _ mag .to_nearest claw
    res.amount' hmagn hcr hat' (LoanBroker.coverDeposit_amount_nonzero lb amount res hdep) hmagv hcl
  have hval : claw.toRat = res.amount'.toRat :=
    STAmount.ofNumber_to_nearest_eq_of_canonical _ mag claw res.amount' hmagn hm0 hcr hat' hmagv
      hcl
  have heq : claw = res.amount' := STAmount.eq_of_exactCanonical claw res.amount'
    (STAmount.ofNumber_exactCanonical _ mag .to_nearest claw hmagn hm0 hcl hnz) hcr
    (by rw [STAmount.ofNumber_mNumericType _ _ _ _ hcl, hat']) hnz hval
  refine ⟨heq, ?_⟩
  unfold LoanBroker.canCoverClawback
  rw [hrr, ok_bind, heq]
  exact hcheck

/-- **Proof body of `coverClawback_split`.** -/
lemma LoanBroker.coverClawback_split_proof (lb : LoanBroker) (pool : α) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (h1 : lb.coverClawback pool (some a) = .ok (.ok r1))
    (h2 : r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2))
    (h3 : lb.coverClawback pool (some c) = .ok (.ok s))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hb0 : 0 ≤ b.toRat) (hc0 : 0 ≤ c.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false) (hzc : c.isZero = false)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : c.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hcan1 : lb.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hcan2 : r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan3 : lb.canCoverClawback pool (some c) = .ok .tesSUCCESS)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  have hn1 := LoanBroker.coverClawback_amount_nonzero lb pool _ r1 hcan1 h1
  have hn2 := LoanBroker.coverClawback_amount_nonzero r1.loanBroker' pool _ r2 hcan2 h2
  have hn3 := LoanBroker.coverClawback_amount_nonzero lb pool _ s hcan3 h3
  have hf := LoanBroker.coverClawback_fixed_fields lb pool _ r1 h1
  have d1 := (LoanBroker.coverClawback_debit_request lb pool a r1 e minimumCover h1 hca hat ha0
    hza hexp hmin (by linarith) hn1 hx1).2
  obtain ⟨w, hwn, hwv⟩ := hx2
  -- after `a` the broker has the same scale and minimum cover, and `b` still fits
  have d2 := (LoanBroker.coverClawback_debit_request r1.loanBroker' pool b r2 e minimumCover h2 hcb
    (by rw [hf.numericType]; exact hbt) hb0 hzb (by rw [hf.numericType]; exact hexp)
    (by rw [hf.numericType, hf.debtTotal, hf.coverRateMinimum]; exact hmin) (by linarith) hn2
    ⟨w, hwn, by rw [hwv]; linarith⟩).2
  have d3 := (LoanBroker.coverClawback_debit_request lb pool c s e minimumCover h3 hcc hct hc0 hzc
    hexp hmin hfit hn3 ⟨w, hwn, hwv⟩).2
  linarith

/-- **Proof body of `coverWithdraw_split`.** -/
lemma LoanBroker.coverWithdraw_split_proof (lb : LoanBroker) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult)
    (h1 : lb.coverWithdraw a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverWithdraw b = .ok (.ok r2))
    (h3 : lb.coverWithdraw c = .ok (.ok s))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  have d1 := LoanBroker.coverWithdraw_debit_request lb a r1 h1 hca hx1
  obtain ⟨w, hwn, hwv⟩ := hx2
  have d2 := LoanBroker.coverWithdraw_debit_request r1.loanBroker' b r2 h2 hcb
    ⟨w, hwn, by rw [hwv]; linarith⟩
  have d3 := LoanBroker.coverWithdraw_debit_request lb c s h3 hcc ⟨w, hwn, hwv⟩
  linarith

/-- **Proof body of `coverDeposit_split`.** -/
lemma LoanBroker.coverDeposit_split_proof (lb : LoanBroker) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult) (e : Int)
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    (h3 : lb.coverDeposit c = .ok (.ok s))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hsum : c.toRat = a.toRat + b.toRat)
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hga : e ≤ a.exponent) (hgb : e ≤ b.exponent) (hgc : e ≤ c.exponent)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  have hr' : numberExponent r1.loanBroker'.coverAvailable r1.loanBroker'.numericType = .ok e := by
    rw [(LoanBroker.coverDeposit_fixed_fields lb a r1 h1).numericType]; exact hr
  -- every amount sits on the cover scale, so each deposit takes it whole
  have ha : r1.amount' = a := STAmount.roundToExponent_ok_eq_self a _ e .downward
    (Or.inr (Or.inr hga)) (LoanBroker.coverDeposit_amount_of_exp lb a r1 e he h1)
  have hb : r2.amount' = b := STAmount.roundToExponent_ok_eq_self b _ e .downward
    (Or.inr (Or.inr hgb)) (LoanBroker.coverDeposit_amount_of_exp r1.loanBroker' b r2 e hr' h2)
  have hc : s.amount' = c := STAmount.roundToExponent_ok_eq_self c _ e .downward
    (Or.inr (Or.inr hgc)) (LoanBroker.coverDeposit_amount_of_exp lb c s e he h3)
  obtain ⟨w1, hw1n, hw1v⟩ := hx1
  obtain ⟨w2, hw2n, hw2v⟩ := hx2
  have d1 := LoanBroker.coverDeposit_credit_proof lb a r1 h1 hca ⟨w1, hw1n, by rw [hw1v, ha]⟩
  rw [ha] at d1
  have d2 := LoanBroker.coverDeposit_credit_proof r1.loanBroker' b r2 h2 hcb
    ⟨w2, hw2n, by rw [hw2v, hb, hsum]; linarith⟩
  have d3 := LoanBroker.coverDeposit_credit_proof lb c s h3 hcc ⟨w2, hw2n, by rw [hw2v, hc]⟩
  rw [hb] at d2
  rw [hc] at d3
  linarith

/-- **Proof body of `coverDeposit_comm`.** -/
lemma LoanBroker.coverDeposit_comm_proof (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int)
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    (h3 : lb.coverDeposit b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverDeposit a = .ok (.ok s2))
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hs : numberExponent s1.loanBroker'.coverAvailable lb.numericType = .ok e) :
    r1.amount' = s2.amount' ∧ r2.amount' = s1.amount' := by
  have hr' : numberExponent r1.loanBroker'.coverAvailable r1.loanBroker'.numericType = .ok e := by
    rw [(LoanBroker.coverDeposit_fixed_fields lb a r1 h1).numericType]; exact hr
  have hs' : numberExponent s1.loanBroker'.coverAvailable s1.loanBroker'.numericType = .ok e := by
    rw [(LoanBroker.coverDeposit_fixed_fields lb b s1 h3).numericType]; exact hs
  have ha1 := LoanBroker.coverDeposit_amount_of_exp lb a r1 e he h1
  have hb1 := LoanBroker.coverDeposit_amount_of_exp lb b s1 e he h3
  have hb2 := LoanBroker.coverDeposit_amount_of_exp r1.loanBroker' b r2 e hr' h2
  have ha2 := LoanBroker.coverDeposit_amount_of_exp s1.loanBroker' a s2 e hs' h4
  rw [ha1, Except.ok.injEq] at ha2
  rw [hb1, Except.ok.injEq] at hb2
  exact ⟨ha2, hb2.symm⟩

/-- **Proof body of `coverDeposit_comm_cover`.** -/
lemma LoanBroker.coverDeposit_comm_cover_proof (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int)
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    (h3 : lb.coverDeposit b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverDeposit a = .ok (.ok s2))
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hs : numberExponent s1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hx1 : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + r1.amount'.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧
      w.toRat = r1.loanBroker'.toExact.coverAvailable + r2.amount'.toRat)
    (hx3 : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + s1.amount'.toRat)
    (hx4 : ∃ w : Number, w.isNormalized ∧
      w.toRat = s1.loanBroker'.toExact.coverAvailable + s2.amount'.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  obtain ⟨hab, hba⟩ := LoanBroker.coverDeposit_comm_proof lb a b r1 r2 s1 s2 e h1 h2 h3 h4 he hr hs
  have d1 := LoanBroker.coverDeposit_credit_proof lb a r1 h1 hca hx1
  have d2 := LoanBroker.coverDeposit_credit_proof r1.loanBroker' b r2 h2 hcb hx2
  have d3 := LoanBroker.coverDeposit_credit_proof lb b s1 h3 hcb hx3
  have d4 := LoanBroker.coverDeposit_credit_proof s1.loanBroker' a s2 h4 hca hx4
  rw [hba] at d2
  rw [← hab] at d4
  linarith

/-- **Proof body of `coverWithdraw_coverDeposit_restores`.** -/
lemma LoanBroker.coverWithdraw_coverDeposit_restores_proof (lb : LoanBroker) (amount : STAmount)
    (res res' : LoanBrokerCoverResult) (e : Int)
    (hwd : lb.coverWithdraw amount = .ok (.ok res))
    (hdep : res.loanBroker'.coverDeposit amount = .ok (.ok res'))
    (hexp : numberExponent res.loanBroker'.coverAvailable res.loanBroker'.numericType = .ok e)
    (hgrid : e ≤ amount.exponent) (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  -- the amount sits on the new cover scale, so the deposit takes it whole
  have hamt := LoanBroker.coverDeposit_amount_of_exp res.loanBroker' amount res' e hexp hdep
  have hsame : res'.amount' = amount :=
    STAmount.roundToExponent_ok_eq_self amount _ e .downward (Or.inr (Or.inr hgrid)) hamt
  have hdown := LoanBroker.coverWithdraw_debit_request lb amount res hwd hc hexact
  have hup := LoanBroker.coverDeposit_credit_proof res.loanBroker' amount res' hdep hc
    ⟨lb.coverAvailable, lb.wf.coverAvailable_norm, by
      rw [hsame]
      show lb.toExact.coverAvailable = _
      linarith⟩
  rw [hsame] at hup
  linarith

/-- **Proof body of `coverClawback_coverDeposit_restores`.** -/
lemma LoanBroker.coverClawback_coverDeposit_restores_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res res' : LoanBrokerCoverResult) (e : Int)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hclaw : lb.coverClawback pool amount = .ok (.ok res))
    (hdep : res.loanBroker'.coverDeposit res.amount' = .ok (.ok res'))
    (hexp : numberExponent res.loanBroker'.coverAvailable res.loanBroker'.numericType = .ok e)
    (hgrid : e ≤ res.amount'.exponent)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  have hc := (LoanBroker.coverClawback_amount_exactCanonical lb pool amount res hcan hclaw hreq).1
  -- the clawed amount sits on the new cover scale, so the deposit takes it whole
  have hamt := LoanBroker.coverDeposit_amount_of_exp res.loanBroker' res.amount' res' e hexp hdep
  have hsame : res'.amount' = res.amount' :=
    STAmount.roundToExponent_ok_eq_self res.amount' _ e .downward (Or.inr (Or.inr hgrid)) hamt
  have hdown := LoanBroker.coverClawback_debit_of_canonical lb pool amount res hclaw hc hexact
  have hup := LoanBroker.coverDeposit_credit_proof res.loanBroker' res.amount' res' hdep
    hc ⟨lb.coverAvailable, lb.wf.coverAvailable_norm, by
      rw [hsame]
      show lb.toExact.coverAvailable = _
      linarith⟩
  rw [hsame] at hup
  linarith

/-- **Proof body of `coverWithdraw_comm`.** -/
lemma LoanBroker.coverWithdraw_comm_proof (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult)
    (h1 : lb.coverWithdraw a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverWithdraw b = .ok (.ok r2))
    (h3 : lb.coverWithdraw b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverWithdraw a = .ok (.ok s2))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hxa : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hxb : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - b.toRat)
    (hxab : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - a.toRat - b.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  have d1 := LoanBroker.coverWithdraw_debit_request lb a r1 h1 hca hxa
  have d3 := LoanBroker.coverWithdraw_debit_request lb b s1 h3 hcb hxb
  obtain ⟨w, hwn, hwv⟩ := hxab
  have d2 := LoanBroker.coverWithdraw_debit_request r1.loanBroker' b r2 h2 hcb
    ⟨w, hwn, by rw [hwv]; linarith⟩
  have d4 := LoanBroker.coverWithdraw_debit_request s1.loanBroker' a s2 h4 hca
    ⟨w, hwn, by rw [hwv]; linarith⟩
  linarith

/-- **Proof body of `coverClawback_comm`.** -/
lemma LoanBroker.coverClawback_comm_proof (lb : LoanBroker) (pool : α) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (h1 : lb.coverClawback pool (some a) = .ok (.ok r1))
    (h2 : r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2))
    (h3 : lb.coverClawback pool (some b) = .ok (.ok s1))
    (h4 : s1.loanBroker'.coverClawback pool (some a) = .ok (.ok s2))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hb0 : 0 ≤ b.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat + b.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hcan1 : lb.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hcan2 : r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan3 : lb.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan4 : s1.loanBroker'.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hxa : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hxb : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - b.toRat)
    (hxab : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - a.toRat - b.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  have hn1 := LoanBroker.coverClawback_amount_nonzero lb pool _ r1 hcan1 h1
  have hn2 := LoanBroker.coverClawback_amount_nonzero r1.loanBroker' pool _ r2 hcan2 h2
  have hn3 := LoanBroker.coverClawback_amount_nonzero lb pool _ s1 hcan3 h3
  have hn4 := LoanBroker.coverClawback_amount_nonzero s1.loanBroker' pool _ s2 hcan4 h4
  have d1 := (LoanBroker.coverClawback_debit_request lb pool a r1 e minimumCover h1 hca hat ha0
    hza hexp hmin (by linarith) hn1 hxa).2
  have d3 := (LoanBroker.coverClawback_debit_request lb pool b s1 e minimumCover h3 hcb hbt hb0
    hzb hexp hmin (by linarith) hn3 hxb).2
  obtain ⟨w, hwn, hwv⟩ := hxab
  -- after the first clawback the broker has the same scale and minimum cover
  have hfr := LoanBroker.coverClawback_fixed_fields lb pool _ r1 h1
  have hfs := LoanBroker.coverClawback_fixed_fields lb pool _ s1 h3
  have d2 := (LoanBroker.coverClawback_debit_request r1.loanBroker' pool b r2 e minimumCover h2 hcb
    (by rw [hfr.numericType]; exact hbt) hb0 hzb (by rw [hfr.numericType]; exact hexp)
    (by rw [hfr.numericType, hfr.debtTotal, hfr.coverRateMinimum]; exact hmin) (by linarith) hn2
    ⟨w, hwn, by rw [hwv]; linarith⟩).2
  have d4 := (LoanBroker.coverClawback_debit_request s1.loanBroker' pool a s2 e minimumCover h4 hca
    (by rw [hfs.numericType]; exact hat) ha0 hza (by rw [hfs.numericType]; exact hexp)
    (by rw [hfs.numericType, hfs.debtTotal, hfs.coverRateMinimum]; exact hmin) (by linarith) hn4
    ⟨w, hwn, by rw [hwv]; linarith⟩).2
  linarith

end XRPL.Model.Lending
