import XRPL.Properties.Lending.Loan.Common.FactorComputes
import XRPL.Properties.Lending.Loan.Common.RoundAnySign
import XRPL.Properties.Lending.Loan.Common.DuePayment
import XRPL.Properties.Lending.Loan.Common.PaymentFactor
import XRPL.Properties.Lending.Loan.Common.YieldValue
import XRPL.Properties.Lending.Ledger.Common.RecheckLoan

/-! # The next scheduled instalment computes

The instalment compares the outstanding amounts with the theoretical ones after one payment fewer. Every value
stays far below the top of the `Number` range while the payments fit the 32-bit clock and the amounts fit the asset. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Loan.scheduledComponents from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private loanPrincipalFromPeriodicPayment_normalized
  from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest

local notation "ε" => Number.nearestError

/-- The smaller of two numbers below `10^b` is below `10^b`. -/
private lemma Number.Below.min' {x y : Number} {b : ℕ} (hx : x.Below b) (hy : y.Below b) :
    (Number.min x y).Below b := by
  unfold Number.min; split <;> assumption

/-- The larger of two numbers below `10^b` is below `10^b`. -/
private lemma Number.Below.max' {x y : Number} {b : ℕ} (hx : x.Below b) (hy : y.Below b) :
    (Number.max x y).Below b := by
  unfold Number.max; split <;> assumption

/-- Zero is below every power of ten. -/
private lemma Number.Below.zero' (b : ℕ) : Number.zero.Below b :=
  ⟨Number.zero_isNormalized, by rw [Number.toRat_zero, abs_zero]; positivity⟩

/-- A number floored at zero stays below `10^b`. -/
private lemma Number.Below.floorZero {x : Number} {b : ℕ} (hx : x.Below b) :
    (if x.signum < 0 then Number.zero else x).Below b := by
  split
  · exact Number.Below.zero' b
  · exact hx

/-- The negation of a number below `10^b` is below `10^b`. -/
private lemma Number.Below.neg' {x : Number} {b : ℕ} (hx : x.Below b) : x.operator_neg.Below b :=
  ⟨Number.operator_neg_isNormalized _ hx.1, by rw [Number.toRat_neg, abs_neg]; exact hx.2⟩

/-- The total of deltas below `10^b` computes, below `10^(b + 2)`. -/
private lemma LoanStateDeltas.total_below (d : LoanStateDeltas) {b : ℕ} (hb : b ≤ 180)
    (h1 : d.principal.Below b) (h2 : d.interest.Below b) (h3 : d.managementFee.Below b) :
    ∃ t, d.total = .ok t ∧ t.Below (b + 2) := by
  obtain ⟨u, hu⟩ := Number.Below.add_ok (by omega) h1 h2
  have bu := Number.Below.add h1 h2 hu
  obtain ⟨t, ht⟩ := Number.Below.add_ok (by omega) bu (h3.mono (by omega))
  refine ⟨t, ?_, Number.Below.add bu (h3.mono (by omega)) ht⟩
  unfold LoanStateDeltas.total
  simp only [hu, ht, bind, Except.bind]

/-- Taking part of an excess off a value computes, both below `10^(b + 1)`. -/
private lemma reduceCapped_below (value excess : Number) {b : ℕ} (hb : b ≤ 180) (hv : value.Below b)
    (he : excess.Below b) :
    ∃ v' e', reduceCapped value excess = .ok (v', e') ∧ v'.Below (b + 1) ∧ e'.Below (b + 1) := by
  unfold reduceCapped
  by_cases hg : excess.operator_gt Number.zero = true
  · have hm := Number.Below.min' hv he
    obtain ⟨v', hv'⟩ := Number.Below.sub_ok (by omega) hv hm
    obtain ⟨e', he'⟩ := Number.Below.sub_ok (by omega) he hm
    refine ⟨v', e', ?_, Number.Below.sub hv hm hv', Number.Below.sub he hm he'⟩
    simp only [hg, ↓reduceIte, hv', he', bind, Except.bind, pure, Except.pure]
  · refine ⟨value, excess, ?_, hv.mono (by omega), he.mono (by omega)⟩
    simp only [hg, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]

/-- Taking an excess off deltas below `10^b` computes, below `10^(b + 3)`. -/
private lemma LoanStateDeltas.reduceByExcess_below (d : LoanStateDeltas) (excess : Number) {b : ℕ} (hb : b ≤ 170)
    (h1 : d.principal.Below b) (h2 : d.interest.Below b) (h3 : d.managementFee.Below b) (he : excess.Below b) :
    ∃ d', d.reduceByExcess excess = .ok d' ∧ d'.principal.Below (b + 3) ∧ d'.interest.Below (b + 3) ∧
      d'.managementFee.Below (b + 3) := by
  obtain ⟨i', e1, hr1, bi', be1⟩ := reduceCapped_below d.interest excess (by omega) h2 he
  obtain ⟨m', e2, hr2, bm', be2⟩ := reduceCapped_below d.managementFee e1 (by omega) (h3.mono (by omega)) be1
  obtain ⟨p', e3, hr3, bp', -⟩ := reduceCapped_below d.principal e2 (by omega) (h1.mono (by omega)) be2
  refine ⟨⟨p', i', m'⟩, ?_, bp', bi'.mono (by omega), bm'.mono (by omega)⟩
  unfold LoanStateDeltas.reduceByExcess
  simp only [hr1, hr2, hr3, bind, Except.bind, pure, Except.pure]

/-- The theoretical state with `k` payments left computes, its amounts within a few times the `k` payments. -/
private lemma LoanState.buildTheoretical_below (pp rate : Number) (ir : TenthBips32) (interval k : UInt32)
    (m : TenthBips16) (hrate : loanPeriodicRate ir interval = .ok rate) (hir : ir.toNat ≤ 100000)
    (hiv : 60 ≤ interval.toNat) (hk : k.toNat * interval.toNat < 2 ^ 32) (hk0 : k ≠ 0) (hpp : pp.isNormalized)
    (hpp0 : 0 ≤ pp.toRat) (hB : (k.toNat : ℚ) * pp.toRat ≤ 10 ^ 18) (hm : m.toNat ≤ 10000) :
    ∃ ts, LoanState.buildTheoretical pp rate k m = .ok ts ∧
      ts.principalOutstanding.isNormalized ∧ 0 ≤ ts.principalOutstanding.toRat ∧
      ts.principalOutstanding.toRat ≤ 70 * ((k.toNat : ℚ) * pp.toRat) ∧
      ts.interestDue.isNormalized ∧ |ts.interestDue.toRat| ≤ 80 * ((k.toNat : ℚ) * pp.toRat) ∧
      ts.managementFeeDue.isNormalized ∧ |ts.managementFeeDue.toRat| ≤ 8 * ((k.toNat : ℚ) * pp.toRat) := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hk1 : (1 : ℚ) ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h0 => hk0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hkl : (k.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast k.toNat_lt
  set B := (k.toNat : ℚ) * pp.toRat with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hppB : pp.toRat ≤ B := by nlinarith
  have hcN := Number.ofInt64_isNormalized k.toUInt64.toInt64
  have hcv := Number.ofInt64_count k
  obtain ⟨vo, hvo⟩ := Number.operator_mul_ok_of_abs pp (Number.ofInt64 k.toUInt64.toInt64) .to_nearest hpp hcN
    (by rw [abs_of_nonneg hpp0]; linarith [show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    (by rw [hcv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num])
  have hvoN := Number.operator_mul_isNormalized _ _ _ _ hpp hcN hvo
  have hvol : |vo.toRat| ≤ B * (1 + ε) := by
    have := (Number.mul_near _ _ _ hpp hcN hvo).abs_le
    rwa [hcv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ pp.toRat * k.toNat), mul_comm pp.toRat] at this
  have hrN := loanPeriodicRate_isNormalized _ _ _ hrate
  have hr0 := loanPeriodicRate_nonneg _ _ _ hrate
  obtain ⟨tpo, htpo⟩ := loanPrincipalFromPeriodicPayment_computes pp rate ir interval k hrate hir hiv hk hpp hpp0
    (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 100 by norm_num])
  obtain ⟨htpo0, htpole, -⟩ := loanPrincipalFromPeriodicPayment_le_payments pp rate k tpo hpp hpp0 hrN hr0 htpo
  have htpoN := loanPrincipalFromPeriodicPayment_normalized hpp hrN htpo
  have htpoB : tpo.toRat ≤ 70 * B := by rw [hBdef]; linarith
  have h20 : (70 : ℚ) * 10 ^ 18 + 10 ^ 18 * 2 < 10 ^ 190 := by norm_num
  obtain ⟨ig, hig⟩ := Number.operator_sub_ok_of_abs vo tpo .to_nearest hvoN htpoN
    (by nlinarith) (by rw [abs_of_nonneg htpo0]; nlinarith)
  have higN := operator_sub_isNormalized_to_nearest_sz _ _ _ hvoN htpoN hig
  have higl : |ig.toRat| ≤ 72 * B := by
    have h1 := (Number.sub_near _ _ _ hvoN htpoN hig).abs_le
    have h2 := abs_sub vo.toRat tpo.toRat
    rw [abs_of_nonneg htpo0] at h2
    have h3 : |vo.toRat - tpo.toRat| ≤ 71 * B + B * ε := by nlinarith
    have h4 : (71 + ε) * (1 + ε) ≤ 72 := by nlinarith
    calc |ig.toRat| ≤ |vo.toRat - tpo.toRat| * (1 + ε) := h1
      _ ≤ (71 * B + B * ε) * (1 + ε) := by gcongr
      _ = B * ((71 + ε) * (1 + ε)) := by ring
      _ ≤ B * 72 := mul_le_mul_of_nonneg_left h4 hB0
      _ = 72 * B := by ring
  obtain ⟨mf, hmf, hmfN, hmfl⟩ := tenthBipsOfValue_ok_of_abs ig m.toTenthBips32 higN (by nlinarith)
  have hm' : (m.toTenthBips32.toNat : ℚ) ≤ 10000 := by
    have h' : m.toTenthBips32.toNat = m.toNat := by simp [TenthBips16.toTenthBips32]
    rw [h']; exact_mod_cast hm
  have hmf' : |mf.toRat| ≤ 792 / 100 * B := by
    have h1 : |ig.toRat| * m.toTenthBips32.toNat / 100000 ≤ |ig.toRat| / 10 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [abs_nonneg ig.toRat]
    have h2 : (1 + ε) ^ 2 ≤ 11 / 10 := by nlinarith
    have h3 : |ig.toRat| * m.toTenthBips32.toNat / 100000 * (1 + ε) ^ 2 ≤ |ig.toRat| / 10 * (11 / 10) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  have hmfB : |mf.toRat| ≤ 8 * B := by linarith
  obtain ⟨i, hi⟩ := Number.operator_sub_ok_of_abs ig mf .to_nearest higN hmfN (by nlinarith) (by nlinarith)
  have hiN := operator_sub_isNormalized_to_nearest_sz _ _ _ higN hmfN hi
  have hiB : |i.toRat| ≤ 80 * B := by
    have h1 := (Number.sub_near _ _ _ higN hmfN hi).abs_le
    have h3 : |ig.toRat - mf.toRat| ≤ 7992 / 100 * B := by linarith [abs_sub ig.toRat mf.toRat]
    have h4 : 7992 / 100 * (1 + ε) ≤ 80 := by nlinarith
    calc |i.toRat| ≤ |ig.toRat - mf.toRat| * (1 + ε) := h1
      _ ≤ 7992 / 100 * B * (1 + ε) := by gcongr
      _ = B * (7992 / 100 * (1 + ε)) := by ring
      _ ≤ B * 80 := mul_le_mul_of_nonneg_left h4 hB0
      _ = 80 * B := by ring
  refine ⟨⟨vo, tpo, i, mf⟩, ?_, htpoN, htpo0, htpoB, hiN, hiB, hmfN, hmfB⟩
  have hk0' : (k == 0) = false := by simpa using hk0
  unfold LoanState.buildTheoretical
  simp only [hk0', Bool.false_eq_true, ↓reduceIte, hvo, htpo, hig, hmf, hi, bind, Except.bind, pure, Except.pure]

/-- A number rounds to an IOU, XRP or MPT amount at a scale in `[-81, 0]` when it is below `10^90` for an IOU, or a
unit below the maximum for XRP or an MPT. The result is at most twice its size plus one. -/
private lemma STAmount.roundToNumericType_asset_ok (nt : NumericType) (x : Number) (mode : rounding_mode) (s : Int)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hs : -81 ≤ s ∧ s ≤ 0) (hx : x.isNormalized)
    (hlt : |x.toRat| < 10 ^ 90) (hfit : nt.isIntegral = true → |x.toRat| + 1 ≤ nt.maxValue.toNat) :
    ∃ y, STAmount.roundToNumericType nt x mode (some s) = .ok y ∧ y.isNormalized ∧
      |y.toRat| ≤ 2 * |x.toRat| + 1 := by
  rcases hasset with rfl | h
  · obtain ⟨y, hy, hyN, hyl⟩ := STAmount.roundToNumericType_frac_ok_abs x mode s hx hlt ⟨by omega, by omega⟩
    refine ⟨y, hy, hyN, ?_⟩
    have : (10 : ℚ) ^ s ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hs.2
    linarith
  · have hint : nt.isIntegral = true := by rcases h with rfl | rfl <;> rfl
    exact STAmount.roundToNumericType_integral_ok_abs nt x mode (some s) h hx (hfit hint)

/-- The next scheduled instalment computes on a loan with payments left, LoanScale in `[-81, 0]`, interestDue at
least zero, a schedule that computes, small amounts, payments that fit the 32-bit clock and an asset that fits. -/
lemma Loan.scheduledComponents_computes (l : Loan) (hlo : -81 ≤ l.loanScale) (hls : l.loanScale ≤ 0)
    (hi0 : 0 ≤ l.toExact.interestDue) (hT : l.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1)
    (hsc : l.ScheduleComputes)
    (hpp : 2 ≤ l.paymentRemaining.toNat →
      (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1))
    (hk : l.paymentRemaining.toNat * l.schedule.paymentInterval.toNat < 2 ^ 32)
    (hasset : l.broker.numericType = .fractional ∨ l.broker.numericType = .native ∨
      l.broker.numericType = .int64)
    (hfit : l.broker.numericType.isIntegral = true → 2 ≤ l.paymentRemaining.toNat →
      80 * ((l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat) + 1 ≤ l.broker.numericType.maxValue.toNat)
    (hpr : l.paymentRemaining ≠ 0) :
    ∃ pc, Loan.scheduledComponents l = .ok pc := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨rate, hrate⟩ := hsc.rate
  obtain ⟨pp', hpp'⟩ := hsc.payment hpr
  by_cases hfin : (l.paymentRemaining == 1 || l.totalValueOutstanding.operator_le pp') = true
  · unfold Loan.scheduledComponents
    simp only [hrate, hpp', bind, Except.bind, hfin, ↓reduceIte]
    exact ⟨_, rfl⟩
  unfold Loan.scheduledComponents
  simp only [hrate, hpp', bind, Except.bind, hfin, Bool.false_eq_true, ↓reduceIte]
  -- the instalment is not the last, so two or more payments are left
  have hnf : ¬(l.paymentRemaining == 1 || l.totalValueOutstanding.operator_le pp') = true := hfin
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnf
  obtain ⟨hpr1, hle⟩ := hnf
  have hpr2 : 2 ≤ l.paymentRemaining.toNat := by
    have h0 : l.paymentRemaining.toNat ≠ 0 := fun h0 => hpr (UInt32.toNat_inj.mp (by simpa using h0))
    have h1 : l.paymentRemaining.toNat ≠ 1 := fun h0 => hpr1 (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  have hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, by omega⟩
  have hb17 : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
  obtain ⟨-, -, -, -, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  obtain ⟨i, hi⟩ := Loan.interestDue_ok l
  have hstate := Loan.state_of_interestDue l i hi
  have hiN := RawLoan.interestDue_isNormalized l i hi
  have hiv : i.toRat = l.totalValueOutstanding.toRat - l.principalOutstanding.toRat -
      l.managementFeeOutstanding.toRat := by rw [Loan.interestDue_toExact l i hi]; rfl
  have hi0' : 0 ≤ i.toRat := by rw [hiv]; exact hi0
  have bT : l.totalValueOutstanding.Below 17 :=
    ⟨l.wf.totalValueOutstanding_norm, by rw [abs_of_nonneg hT0]; linarith⟩
  have bP : l.principalOutstanding.Below 17 :=
    ⟨l.wf.principalOutstanding_norm, by rw [abs_of_nonneg hP0]; linarith⟩
  have bM : l.managementFeeOutstanding.Below 17 :=
    ⟨l.wf.managementFeeOutstanding_norm, by rw [abs_of_nonneg hM0]; linarith⟩
  have bI : i.Below 17 := ⟨hiN, by rw [abs_of_nonneg hi0']; linarith⟩
  have hppN := l.wf.periodicPayment_norm
  have hpp0 : 0 < l.periodicPayment.toRat := l.exact.periodicPayment_pos
  have hppr := hpp hpr2
  have hpp'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpp'
  have hpp'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hppN hpp0.le (Or.inr (Or.inl rfl)) hs hpp'
  have hpp'T : pp'.toRat < l.totalValueOutstanding.toRat := by
    rw [← not_le, ← operator_le_iff _ _ l.wf.totalValueOutstanding_norm hpp'N]
    simpa using hle
  have bpp' : pp'.Below 17 := ⟨hpp'N, by rw [abs_of_nonneg hpp'0]; linarith⟩
  have hk0 : l.paymentRemaining - 1 ≠ 0 := by
    intro h0
    have := congrArg UInt32.toNat h0
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at this
    simp at this
    omega
  have hkN : (l.paymentRemaining - 1).toNat = l.paymentRemaining.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp
  have hkq : ((l.paymentRemaining - 1).toNat : ℚ) = l.paymentRemaining.toNat - 1 := by
    rw [hkN]; push_cast [show 1 ≤ l.paymentRemaining.toNat by omega]; ring
  have hBle : ((l.paymentRemaining - 1).toNat : ℚ) * l.periodicPayment.toRat ≤
      (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat := by
    rw [hkq]; nlinarith
  have hir : l.rates.interestRate.toNat ≤ 100000 := by
    have := l.valid.interestRate_cap
    unfold maxLoanRate kTenthBipsPerUnity at this
    exact UInt32.le_iff_toNat_le.mp this
  have hint : 60 ≤ l.schedule.paymentInterval.toNat := UInt32.le_iff_toNat_le.mp l.valid.paymentInterval_min
  have hk' : (l.paymentRemaining - 1).toNat * l.schedule.paymentInterval.toNat < 2 ^ 32 := by
    rw [hkN]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hk
  obtain ⟨ts, hts, htpN, htp0, htpB, htiN, htiB, htmN, htmB⟩ := LoanState.buildTheoretical_below
    l.periodicPayment rate l.rates.interestRate l.schedule.paymentInterval (l.paymentRemaining - 1)
    l.broker.managementFeeRate hrate hir hint hk' hk0 hppN hpp0.le (by linarith) l.broker.managementFeeRate_le
  set B := ((l.paymentRemaining - 1).toNat : ℚ) * l.periodicPayment.toRat with hBdef
  have hB0 : 0 ≤ B := by positivity
  have h90 : 80 * B < 10 ^ 90 := by nlinarith
  have hfitB : l.broker.numericType.isIntegral = true → 80 * B + 1 ≤ l.broker.numericType.maxValue.toNat :=
    fun h => le_trans (by linarith) (hfit h hpr2)
  obtain ⟨tpo', htpo', htpo'N, htpo'l⟩ := STAmount.roundToNumericType_asset_ok _ ts.principalOutstanding .upward
    l.loanScale hasset ⟨hlo, hls⟩ htpN (by rw [abs_of_nonneg htp0]; linarith)
    (fun h => by have := hfitB h; rw [abs_of_nonneg htp0]; linarith)
  obtain ⟨ti', hti', hti'N, hti'l⟩ := STAmount.roundToNumericType_asset_ok _ ts.interestDue .downward
    l.loanScale hasset ⟨hlo, hls⟩ htiN (by linarith) (fun h => by have := hfitB h; linarith)
  obtain ⟨tm', htm', htm'N, htm'l⟩ := STAmount.roundToNumericType_asset_ok _ ts.managementFeeDue .to_nearest
    l.loanScale hasset ⟨hlo, hls⟩ htmN (by linarith) (fun h => by have := hfitB h; linarith)
  have hB19 : 2 * (80 * B) + 1 < 10 ^ 19 := by nlinarith
  have btpo' : tpo'.Below 19 := ⟨htpo'N, by rw [abs_of_nonneg htp0] at htpo'l; linarith⟩
  have bti' : ti'.Below 19 := ⟨hti'N, by linarith⟩
  have btm' : tm'.Below 19 := ⟨htm'N, by linarith⟩
  obtain ⟨dp, hdp⟩ := Number.Below.sub_ok (by norm_num) (bP.mono (by norm_num)) btpo'
  have bdp := Number.Below.sub (bP.mono (by norm_num)) btpo' hdp
  obtain ⟨di, hdi⟩ := Number.Below.sub_ok (by norm_num) (bI.mono (by norm_num)) bti'
  have bdi := Number.Below.sub (bI.mono (by norm_num)) bti' hdi
  obtain ⟨dm, hdm⟩ := Number.Below.sub_ok (by norm_num) (bM.mono (by norm_num)) btm'
  have bdm := Number.Below.sub (bM.mono (by norm_num)) btm' hdm
  have bcp : (Number.min ({ principal := dp, interest := di, managementFee := dm } :
      LoanStateDeltas).nonNegative.principal l.principalOutstanding).Below 20 :=
    Number.Below.min' (Number.Below.floorZero bdp) (bP.mono (by norm_num))
  obtain ⟨room, hroom⟩ := Number.Below.sub_ok (by norm_num) (bpp'.mono (by norm_num)) bcp
  have broom := Number.Below.sub (bpp'.mono (by norm_num)) bcp hroom
  have bci : (Number.min (Number.min ({ principal := dp, interest := di, managementFee := dm } :
      LoanStateDeltas).nonNegative.interest (Number.max Number.zero room)) i).Below 21 :=
    Number.Below.min' (Number.Below.min' (Number.Below.floorZero (bdi.mono (by norm_num)))
      (Number.Below.max' (Number.Below.zero' 21) broom)) (bI.mono (by norm_num))
  obtain ⟨ppi, hppi⟩ := Number.Below.add_ok (by norm_num) (bcp.mono (by norm_num)) bci
  have bppi := Number.Below.add (bcp.mono (by norm_num)) bci hppi
  obtain ⟨rff, hrff⟩ := Number.Below.sub_ok (by norm_num) (bpp'.mono (by norm_num)) bppi
  have brff := Number.Below.sub (bpp'.mono (by norm_num)) bppi hrff
  have bcm : (Number.min (Number.min ({ principal := dp, interest := di, managementFee := dm } :
      LoanStateDeltas).nonNegative.managementFee rff) l.managementFeeOutstanding).Below 23 :=
    Number.Below.min' (Number.Below.min' (Number.Below.floorZero (bdm.mono (by norm_num))) brff)
      (bM.mono (by norm_num))
  simp only [hstate, hts, htpo', hti', htm', hdp, hdi, hdm, hroom, hppi, hrff, pure, Except.pure]
  set D1 : LoanStateDeltas :=
    { principal := Number.min ({ principal := dp, interest := di, managementFee := dm } :
        LoanStateDeltas).nonNegative.principal l.principalOutstanding
      interest := Number.min (Number.min ({ principal := dp, interest := di, managementFee := dm } :
        LoanStateDeltas).nonNegative.interest (Number.max Number.zero room)) i
      managementFee := Number.min (Number.min ({ principal := dp, interest := di, managementFee := dm } :
        LoanStateDeltas).nonNegative.managementFee rff) l.managementFeeOutstanding } with hD1
  obtain ⟨t1, ht1, bt1⟩ := LoanStateDeltas.total_below D1 (b := 23) (by norm_num) (bcp.mono (by norm_num))
    (bci.mono (by norm_num)) bcm
  obtain ⟨ov, hov⟩ := Number.Below.sub_ok (by norm_num) bt1 (bT.mono (by norm_num))
  have bov := Number.Below.sub bt1 (bT.mono (by norm_num)) hov
  rw [ht1]
  simp only [hov]
  have bD1 : D1.principal.Below 26 ∧ D1.interest.Below 26 ∧ D1.managementFee.Below 26 :=
    ⟨bcp.mono (by norm_num), bci.mono (by norm_num), bcm.mono (by norm_num)⟩
  by_cases hovp : ov.operator_gt Number.zero = true
  · obtain ⟨d2, hd2, b1, b2, b3⟩ := LoanStateDeltas.reduceByExcess_below D1 ov (b := 26) (by norm_num) bD1.1 bD1.2.1
      bD1.2.2 bov
    obtain ⟨t2, ht2, bt2⟩ := LoanStateDeltas.total_below d2 (b := 29) (by norm_num) b1 b2 b3
    obtain ⟨sh, hsh⟩ := Number.Below.sub_ok (by norm_num) (bpp'.mono (by norm_num)) bt2
    have bsh := Number.Below.sub (bpp'.mono (by norm_num)) bt2 hsh
    simp only [hovp, ↓reduceIte, hd2, ht2, hsh]
    by_cases hshn : sh.signum < 0
    · obtain ⟨d3, hd3, c1, c2, c3⟩ := LoanStateDeltas.reduceByExcess_below d2 sh.operator_neg (b := 32)
        (by norm_num) (b1.mono (by norm_num)) (b2.mono (by norm_num)) (b3.mono (by norm_num)) (Number.Below.neg' bsh)
      obtain ⟨t3, ht3, -⟩ := LoanStateDeltas.total_below d3 (b := 35) (by norm_num) c1 c2 c3
      simp only [hshn, ↓reduceIte, hd3, ht3]
      exact ⟨_, rfl⟩
    · simp only [hshn, ↓reduceIte]
      exact ⟨_, rfl⟩
  · obtain ⟨sh, hsh⟩ := Number.Below.sub_ok (by norm_num) (bpp'.mono (by norm_num)) bt1
    have bsh := Number.Below.sub (bpp'.mono (by norm_num)) bt1 hsh
    simp only [hovp, Bool.false_eq_true, ↓reduceIte, hsh]
    by_cases hshn : sh.signum < 0
    · obtain ⟨d3, hd3, c1, c2, c3⟩ := LoanStateDeltas.reduceByExcess_below D1 sh.operator_neg (b := 26)
        (by norm_num) bD1.1 bD1.2.1 bD1.2.2 ((Number.Below.neg' bsh).mono (by norm_num))
      obtain ⟨t3, ht3, -⟩ := LoanStateDeltas.total_below d3 (b := 29) (by norm_num) c1 c2 c3
      simp only [hshn, ↓reduceIte, hd3, ht3]
      exact ⟨_, rfl⟩
    · simp only [hshn, ↓reduceIte]
      exact ⟨_, rfl⟩


end XRPL.Model.Lending
