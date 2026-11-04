import XRPL.Properties.Lending.Loan.Common.YieldGrid

/-! # The interest a loan operation books in YieldUnrealized

A new active loan or an accept books the loan's interestDue inside the Open zone, a default releases it, a
payment books the change in it, and the other operations keep both the yield and the loan's interest. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- A new loan's booked interest. An active loan books its exact interest, at least zero and inside the
Open zone with YieldUnrealized, a pending loan books nothing. -/
lemma Loan.create_yieldValue (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ y, v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized ∧
      Number.OnGrid v.baseExponent y ∧ 0 ≤ y.toRat ∧
      y.toRat = (if pending then 0 else r.loan'.toExact.interestDue) ∧
      v.yieldUnrealized.toRat + y.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) := by
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule allowsOverpayment pending r hp hpos
    hst hnt hok
  obtain ⟨-, -, hPO, -, -⟩ := Loan.create_reserved broker v principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hnt har hok
  obtain ⟨props, loanState, _, principal', broker', aa', ad', lu', ar', yu', hchecks, -, hsums, hpool, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨hiN, hi0⟩ := Loan.create_checkedInterest_nonneg broker v principal rates fees schedule allowsOverpayment
    pending r props loanState _ broker' hp hpos hst hok hchecks hl hb
  have hopen := (Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiN hchecks.open_zone).2.1
  have hsb := Loan.loanScale_bounds r.loan'
  rw [hls] at hsb
  obtain ⟨ht, hpg, hm⟩ := Loan.outstanding_onGrid r.loan'
  rw [hls] at ht hpg hm
  -- the interest the checks read is the new loan's interest
  have hPOeq : r.loan'.principalOutstanding = principal :=
    Number.isNormalized.toRat_inj r.loan'.wf.principalOutstanding_norm hp hPO
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hint : r.loan'.interestDue = .ok loanState.interestDue := by
    have hs := hchecks.state
    unfold LoanState.build at hs
    unfold RawLoan.interestDue
    rw [show r.loan'.toRawLoan.totalValueOutstanding = props.totalValueOutstanding from hTV,
      show r.loan'.toRawLoan.principalOutstanding = principal from hPOeq,
      show r.loan'.toRawLoan.managementFeeOutstanding = props.managementFeeOutstanding from hMF]
    obtain ⟨d, hd, hs⟩ := bind_ok_peel _ _ _ hs
    obtain ⟨i, hi, hs⟩ := bind_ok_peel _ _ _ hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst hs
    simp only [bind, Except.bind, hd, hi]
  have hval := Loan.interestDue_toExact r.loan' _ hint
  rw [hTV] at ht
  rw [hMF] at hm
  have hpr : Number.OnGrid v.baseExponent principal := by
    obtain ⟨-, k, hk⟩ := hpg
    exact ⟨hp, k, by rw [← hPO]; exact hk⟩
  have hig : Number.OnGrid v.baseExponent loanState.interestDue := by
    have hs := hchecks.state
    unfold LoanState.build at hs
    obtain ⟨d, hd, hs⟩ := bind_ok_peel _ _ _ hs
    obtain ⟨i, hi, hs⟩ := bind_ok_peel _ _ _ hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst hs
    exact Number.OnGrid.sub (Number.OnGrid.sub ht hpr hsb hd) hm hsb hi
  refine ⟨if pending then Number.zero else loanState.interestDue, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hpool]
    exact hsums.yield
  · split
    · exact Number.OnGrid.zero _
    · exact hig
  · split
    · rw [Number.toRat_zero]
    · exact hi0
  · split
    · rw [Number.toRat_zero]
    · exact hval
  · have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
    split
    · rw [Number.toRat_zero, add_zero]
      have : (0 : ℚ) ≤ loanState.interestDue.toRat := hi0
      linarith
    · exact hopen

/-- An accept that passed its check read the loan's interest inside the Open zone. -/
private lemma Loan.canAccept_open (loan : Loan) (v : Vault) (t : UInt32) (h : loan.canAccept v t = .ok .tesSUCCESS) :
    ∃ i, loan.interestDue = .ok i ∧ v.exceedsOpenLimit i = .ok false := by
  unfold Loan.canAccept at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hc := ‹(_ : Except Error TER) = _›; cases hc; done)
    | skip
  all_goals
    simp only [Bool.not_eq_true] at *
    subst_vars
    exact ⟨_, ‹loan.interestDue = Except.ok _›, ‹AssetPool.exceedsOpenLimit v _ = Except.ok _›⟩

/-- An accept's booked interest. It books the loan's exact interest inside the Open zone with
YieldUnrealized, and keeps the loan's interest. -/
lemma Loan.accept_yieldValue (loan : Loan) (v : Vault) (t : UInt32) (r : LoanWithPool Vault)
    (hc : loan.canAccept v t = .ok .tesSUCCESS) (h : (loan.accept v).run = .ok (.ok r)) :
    ∃ y, v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized ∧
      Number.OnGrid loan.loanScale y ∧ y.toRat = loan.toExact.interestDue ∧
      v.yieldUnrealized.toRat + y.toRat < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) ∧
      r.loan'.toExact.interestDue = loan.toExact.interestDue := by
  obtain ⟨i, hi, ho⟩ := Loan.canAccept_open loan v t hc
  have hiN := (Loan.interestDue_onGrid loan i hi).1
  have hopen := (Vault.exceedsOpenLimit_false_bound v i hiN ho).2.1
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hi' := ‹loan.interestDue = Except.ok _›
  have hpool := ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›
  have hraw := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
  rw [hi] at hi'
  obtain rfl := Except.ok.inj hi'
  refine ⟨i, (Vault.poolAdjust_adjustSums v _ _ hpool).yield, Loan.interestDue_onGrid loan i hi,
    Loan.interestDue_toExact loan i hi, hopen, Loan.toExact_interestDue_congr
      (congrArg RawLoan.totalValueOutstanding hraw :) (congrArg RawLoan.principalOutstanding hraw :)
      (congrArg RawLoan.managementFeeOutstanding hraw :)⟩

/-- Impair keeps the loan's interest. -/
lemma Loan.manageImpair_interest (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : r.loan'.toExact.interestDue = loan.toExact.interestDue := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_interestDue loan v true r ‹_›

/-- Unimpair keeps the loan's interest. -/
lemma Loan.manageUnimpair_interest (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) : r.loan'.toExact.interestDue = loan.toExact.interestDue :=
  Loan.changeImpairment_interestDue loan v false r h

/-- A default's released interest. It takes the loan's exact interest off YieldUnrealized and leaves the
loan with none. -/
lemma Loan.manageDefault_yieldValue (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    ∃ i, v.yieldUnrealized.operator_add i.operator_neg .to_nearest = .ok r.pool'.yieldUnrealized ∧
      Number.OnGrid loan.loanScale i ∧ i.toRat = loan.toExact.interestDue ∧ r.loan'.toExact.interestDue = 0 := by
  obtain ⟨i, _, _, raw, _, hi, -, hadj, hraw, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  refine ⟨i, ?_, Loan.interestDue_onGrid loan i hi, Loan.interestDue_toExact loan i hi, ?_⟩
  · rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hraw, heq]
    exact hs.yield
  · show r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat -
      r.loan'.managementFeeOutstanding.toRat = 0
    rw [show r.loan'.totalValueOutstanding = r.loan'.toRawLoan.totalValueOutstanding from rfl,
      show r.loan'.principalOutstanding = r.loan'.toRawLoan.principalOutstanding from rfl,
      show r.loan'.managementFeeOutstanding = r.loan'.toRawLoan.managementFeeOutstanding from rfl, hloan]
    simp [Loan.defaultedLoan, Number.toRat_zero]

/-- A payment's booked interest. It moves YieldUnrealized by the change in the loan's exact interest. -/
lemma Loan.pay_yieldValue (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r))
    (hi0 : 0 ≤ loan.toExact.interestDue) (hi0' : 0 ≤ r.loan'.toExact.interestDue) :
    ∃ y, v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized ∧
      Number.OnGrid loan.loanScale y ∧ y.toRat = r.loan'.toExact.interestDue - loan.toExact.interestDue := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, yd, _, _, _, raw, _, hsums, hadj, hv', -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpool := Vault.poolAdjust_ok _ _ raw r.pool' hadj hv'
  obtain ⟨i', hi', hyd⟩ := hsums.yield
  have hls : p.loan.loanScale = loan.loanScale := hst.loanScale
  have hsb := Loan.loanScale_bounds loan
  have hg1 := Loan.interestDue_onGrid p.loan i' hi'
  have hg2 := Loan.interestDue_onGrid loan _ hsi
  rw [hls] at hg1
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hrl : r.loan'.toExact.interestDue = p.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)
  have hYU : p.pool.yieldUnrealized = v.yieldUnrealized := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
      obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
      rfl
    · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        exact Vault.poolAdjust_yield_zero v _ _ rfl hadj1
  -- the change in interest is exact: both interests are whole units below `2^63` of them
  obtain ⟨hg1n, a, ha⟩ := hg1
  obtain ⟨hg2n, b, hb⟩ := hg2
  have hab : -2 ^ 63 < a - b ∧ a - b < 2 ^ 63 := by
    obtain ⟨t1, p1, m1, ht1, hp1, hm1, -, -, -, hu1, hge1, -⟩ := Loan.state_units p.loan
      { valueOutstanding := p.loan.totalValueOutstanding, principalOutstanding := p.loan.principalOutstanding,
        interestDue := i', managementFeeDue := p.loan.managementFeeOutstanding } (by
          unfold RawLoan.interestDue at hi'
          unfold Loan.state LoanState.build
          simp only [bind, Except.bind] at hi' ⊢
          split at hi'
          · cases hi'
          · rw [hi']; rfl)
    obtain ⟨t2, p2, m2, ht2, hp2, hm2, -, -, -, hu2, hge2, -⟩ := Loan.state_units loan
      { valueOutstanding := loan.totalValueOutstanding, principalOutstanding := loan.principalOutstanding,
        interestDue := p.scheduledInterest, managementFeeDue := loan.managementFeeOutstanding } (by
          unfold RawLoan.interestDue at hsi
          unfold Loan.state LoanState.build
          simp only [bind, Except.bind] at hsi ⊢
          split at hsi
          · cases hsi
          · rw [hsi]; rfl)
    have hB1 := NumericType.mantissaBound_le p.loan.toExact.numericType
    have hB2 := NumericType.mantissaBound_le loan.toExact.numericType
    have hpos : (0 : ℚ) < (10 : ℚ) ^ loan.loanScale := zpow_pos (by norm_num) _
    have ha0 : 0 ≤ a := by
      have : (0 : ℚ) ≤ (a : ℚ) * 10 ^ loan.loanScale := by
        rw [← ha, Loan.interestDue_toExact p.loan i' hi', ← hrl]; exact hi0'
      exact_mod_cast nonneg_of_mul_nonneg_left this hpos
    have hb0 : 0 ≤ b := by
      have : (0 : ℚ) ≤ (b : ℚ) * 10 ^ loan.loanScale := by
        rw [← hb, Loan.interestDue_toExact loan _ hsi]; exact hi0
      exact_mod_cast nonneg_of_mul_nonneg_left this hpos
    have e1 : a = (t1 : ℤ) - p1 - m1 := by
      have := hu1.val
      rw [show p.loan.loanScale = loan.loanScale from hls] at this
      rw [ha] at this
      exact_mod_cast mul_right_cancel₀ hpos.ne' this
    have e2 : b = (t2 : ℤ) - p2 - m2 := by
      have := hu2.val
      rw [hb] at this
      exact_mod_cast mul_right_cancel₀ hpos.ne' this
    constructor <;> omega
  have hv := Number.operator_sub_toRat_of_grid i' p.scheduledInterest yd a b loan.loanScale hg1n hg2n ha hb hab hsb hyd
  refine ⟨yd, by rw [← hYU]; exact (Vault.poolAdjust_adjustSums _ _ _ hpool).yield,
    Number.OnGrid.sub ⟨hg1n, a, ha⟩ ⟨hg2n, b, hb⟩ hsb hyd, ?_⟩
  rw [hv, hrl, ← Loan.interestDue_toExact p.loan i' hi', ← Loan.interestDue_toExact loan _ hsi, ha, hb]
  push_cast; ring

/-- A delete of an active loan needs a loan with no interest left. -/
lemma Loan.delete_active_interest (loan : Loan) (hc : loan.canDelete = .tesSUCCESS) (hp : loan.isPending = false) :
    loan.toExact.interestDue = 0 := by
  have hpr := Loan.canDelete_active_paid loan hc hp
  obtain ⟨h1, h2, h3⟩ := loan.valid.paid_zeroed hpr
  show loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat = 0
  rw [show loan.totalValueOutstanding = loan.toRawLoan.totalValueOutstanding from rfl, h1,
    show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl, h2,
    show loan.managementFeeOutstanding = loan.toRawLoan.managementFeeOutstanding from rfl, h3, Number.toRat_zero]
  ring

end XRPL.Model.Lending
