import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Loan.Common.NextPayment
import XRPL.Properties.Lending.Loan.Common.FactorBound

/-! # The instalment loop with the tight payment factor

A loan's rate gives a payment factor of at least `1/(3·n)`, so 4.9 times the payments left is room enough, not the
80 times `Loan.LoopRoom` asks. Every reachable XRP loan then has the room. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments Loan.payScheduledInstalments
  Loan.unimpairIfImpaired UnsettledPayment.applyOverpayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_periodicPayment from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private Loan.doPayment_le from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private rn_ge rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.eq_zero_of_toRat Number.div_zero_error from XRPL.Properties.Lending.Loan.Common.PaymentFactor
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private loanPrincipalFromPeriodicPayment_normalized
  from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private Number.add_count PaymentAmounts.add_count from XRPL.Properties.Lending.Loan.Common.DueLoop
open private Number.Below.min' Number.Below.max' Number.Below.zero' Number.Below.floorZero Number.Below.neg'
  LoanStateDeltas.total_below reduceCapped_below LoanStateDeltas.reduceByExcess_below
  STAmount.roundToNumericType_asset_ok from XRPL.Properties.Lending.Loan.Common.NextInstalment

local notation "ε" => Number.nearestError

/-- The principal a periodic payment implies at a loan's periodic rate is at most `3.1·n` payments. -/
lemma loanPrincipalFromPeriodicPayment_le_third (pp rate : Number) (ir : TenthBips32) (interval pr : UInt32)
    (tpo : Number) (hrate : loanPeriodicRate ir interval = .ok rate) (hint : 60 ≤ interval.toNat)
    (hpp : pp.isNormalized) (hpp0 : 0 ≤ pp.toRat) (h : loanPrincipalFromPeriodicPayment pp rate pr = .ok tpo) :
    tpo.toRat ≤ 31 / 10 * pr.toNat * pp.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrate
  have hN := Number.ofInt64_isNormalized pr.toInt64
  have hNv := Number.ofInt64_count pr
  have hN0 : (0 : ℚ) ≤ pr.toNat := by positivity
  have h1e : 0 < 1 - ε := by linarith
  have h1e3 : (1 - 1 / 10 ^ 18 : ℚ) ^ 3 ≤ (1 - ε) ^ 3 := by gcongr
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    rw [Number.toRat_zero]; positivity
  rename_i hpr
  have hN1 : (1 : ℚ) ≤ pr.toNat := by
    have hpr0 : pr ≠ 0 := by intro h0; apply hpr; simp [h0]
    have : pr.toNat ≠ 0 := fun h0 => hpr0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · -- no interest: `n` payments
    have hle := (Number.mul_near _ _ _ hpp hN h).le (by rw [hNv]; positivity)
    rw [hNv] at hle
    calc tpo.toRat ≤ pp.toRat * pr.toNat * (1 + ε) := hle
      _ ≤ pp.toRat * pr.toNat * (31 / 10) := by gcongr; linarith
      _ = 31 / 10 * pr.toNat * pp.toRat := by ring
  rename_i hz
  have hr : rate.toRat ≠ 0 := fun h' =>
    hz ((Number.operator_eq_iff rate Number.zero hrN Number.zero_isNormalized).mpr
      (by rw [Number.toRat_zero]; exact h'))
  obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
  have hfN := computePaymentFactor_isNormalized rate _ pr f hrN hN hf
  have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) h
  have hfn := computePaymentFactor_ge_third rate pr f hrN (loanPeriodicRate_ge ir interval rate hint hrate hr) hf hfne
  have hNpos : (0 : ℚ) < pr.toNat := by linarith
  have hfpos : 0 < f.toRat := lt_of_lt_of_le (by positivity) hfn
  have hle := (Number.div_near _ _ _ hpp hfN h).le (div_nonneg hpp0 hfpos.le)
  calc tpo.toRat ≤ pp.toRat / f.toRat * (1 + ε) := hle
    _ ≤ pp.toRat / ((1 - ε) ^ 3 / (3 * pr.toNat)) * (1 + ε) := by gcongr
    _ = pp.toRat * pr.toNat * (3 * (1 + ε) / (1 - ε) ^ 3) := by field_simp
    _ ≤ pp.toRat * pr.toNat * (31 / 10) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        nlinarith
    _ = 31 / 10 * pr.toNat * pp.toRat := by ring

/-- The theoretical state with `k` payments left computes, its amounts each within `4.9` times the `k` payments. -/
private lemma LoanState.buildTheoretical_tight (pp rate : Number) (ir : TenthBips32) (interval k : UInt32)
    (m : TenthBips16) (hrate : loanPeriodicRate ir interval = .ok rate) (hir : ir.toNat ≤ 100000)
    (hiv : 60 ≤ interval.toNat) (hk : k.toNat * interval.toNat < 2 ^ 32) (hk0 : k ≠ 0) (hpp : pp.isNormalized)
    (hpp0 : 0 ≤ pp.toRat) (hB : (k.toNat : ℚ) * pp.toRat ≤ 10 ^ 18) (hm : m.toNat ≤ 10000) :
    ∃ ts, LoanState.buildTheoretical pp rate k m = .ok ts ∧
      ts.principalOutstanding.isNormalized ∧ 0 ≤ ts.principalOutstanding.toRat ∧
      ts.principalOutstanding.toRat ≤ 49 / 10 * ((k.toNat : ℚ) * pp.toRat) ∧
      ts.interestDue.isNormalized ∧ |ts.interestDue.toRat| ≤ 49 / 10 * ((k.toNat : ℚ) * pp.toRat) ∧
      ts.managementFeeDue.isNormalized ∧ |ts.managementFeeDue.toRat| ≤ 49 / 10 * ((k.toNat : ℚ) * pp.toRat) := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hk1 : (1 : ℚ) ≤ k.toNat := by
    have : k.toNat ≠ 0 := fun h0 => hk0 (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hkl : (k.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast k.toNat_lt
  set B := (k.toNat : ℚ) * pp.toRat with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hppB : pp.toRat ≤ B := by nlinarith
  have hcN := Number.ofInt64_isNormalized k.toInt64
  have hcv := Number.ofInt64_count k
  obtain ⟨vo, hvo⟩ := Number.operator_mul_ok_of_abs pp (Number.ofInt64 k.toInt64 .to_nearest) .to_nearest hpp hcN
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
  obtain ⟨htpo0, -, -⟩ := loanPrincipalFromPeriodicPayment_le_payments pp rate k tpo hpp hpp0 hrN hr0 htpo
  have htpole := loanPrincipalFromPeriodicPayment_le_third pp rate ir interval k tpo hrate hiv hpp hpp0 htpo
  have htpoN := loanPrincipalFromPeriodicPayment_normalized hpp hrN htpo
  have htpoB : tpo.toRat ≤ 31 / 10 * B := by rw [hBdef]; linarith
  have h20 : (70 : ℚ) * 10 ^ 18 + 10 ^ 18 * 2 < 10 ^ 190 := by norm_num
  obtain ⟨ig, hig⟩ := Number.operator_sub_ok_of_abs vo tpo .to_nearest hvoN htpoN
    (by nlinarith) (by rw [abs_of_nonneg htpo0]; nlinarith)
  have higN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hvoN htpoN hig
  have higl : |ig.toRat| ≤ 42 / 10 * B := by
    have h1 := (Number.sub_near _ _ _ hvoN htpoN hig).abs_le
    have h2 := abs_sub vo.toRat tpo.toRat
    rw [abs_of_nonneg htpo0] at h2
    have h3 : |vo.toRat - tpo.toRat| ≤ 41 / 10 * B + B * ε := by nlinarith
    have h4 : (41 / 10 + ε) * (1 + ε) ≤ 42 / 10 := by nlinarith
    calc |ig.toRat| ≤ |vo.toRat - tpo.toRat| * (1 + ε) := h1
      _ ≤ (41 / 10 * B + B * ε) * (1 + ε) := by gcongr
      _ = B * ((41 / 10 + ε) * (1 + ε)) := by ring
      _ ≤ B * (42 / 10) := mul_le_mul_of_nonneg_left h4 hB0
      _ = 42 / 10 * B := by ring
  obtain ⟨mf, hmf, hmfN, hmfl⟩ := tenthBipsOfValue_ok_of_abs ig m.toTenthBips32 higN (by nlinarith)
  have hm' : (m.toTenthBips32.toNat : ℚ) ≤ 10000 := by
    have h' : m.toTenthBips32.toNat = m.toNat := by simp [TenthBips16.toTenthBips32]
    rw [h']; exact_mod_cast hm
  have hmf' : |mf.toRat| ≤ 462 / 1000 * B := by
    have h1 : |ig.toRat| * m.toTenthBips32.toNat / 100000 ≤ |ig.toRat| / 10 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [abs_nonneg ig.toRat]
    have h2 : (1 + ε) ^ 2 ≤ 11 / 10 := by nlinarith
    have h3 : |ig.toRat| * m.toTenthBips32.toNat / 100000 * (1 + ε) ^ 2 ≤ |ig.toRat| / 10 * (11 / 10) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  have hmfB : |mf.toRat| ≤ 49 / 10 * B := by linarith
  obtain ⟨i, hi⟩ := Number.operator_sub_ok_of_abs ig mf .to_nearest higN hmfN (by nlinarith) (by nlinarith)
  have hiN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ higN hmfN hi
  have hiB : |i.toRat| ≤ 49 / 10 * B := by
    have h1 := (Number.sub_near _ _ _ higN hmfN hi).abs_le
    have h3 : |ig.toRat - mf.toRat| ≤ 4662 / 1000 * B := by linarith [abs_sub ig.toRat mf.toRat]
    have h4 : 4662 / 1000 * (1 + ε) ≤ 49 / 10 := by nlinarith
    calc |i.toRat| ≤ |ig.toRat - mf.toRat| * (1 + ε) := h1
      _ ≤ 4662 / 1000 * B * (1 + ε) := by gcongr
      _ = B * (4662 / 1000 * (1 + ε)) := by ring
      _ ≤ B * (49 / 10) := mul_le_mul_of_nonneg_left h4 hB0
      _ = 49 / 10 * B := by ring
  refine ⟨⟨vo, tpo, i, mf⟩, ?_, htpoN, htpo0, by linarith, hiN, hiB, hmfN, hmfB⟩
  have hk0' : (k == 0) = false := by simpa using hk0
  unfold LoanState.buildTheoretical
  simp only [hk0', Bool.false_eq_true, ↓reduceIte, hvo, htpo, hig, hmf, hi, bind, Except.bind, pure, Except.pure]


/-- The next scheduled instalment computes as in `Loan.scheduledComponents_computes`, with an asset that holds
`4.9` times the payments left in place of `80` times. -/
lemma Loan.scheduledComponents_computes_tight (l : Loan) (hlo : -81 ≤ l.loanScale) (hls : l.loanScale ≤ 0)
    (hi0 : 0 ≤ l.toExact.interestDue) (hT : l.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1)
    (hsc : l.ScheduleComputes)
    (hpp : 2 ≤ l.paymentRemaining.toNat →
      (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1))
    (hk : l.paymentRemaining.toNat * l.schedule.paymentInterval.toNat < 2 ^ 32)
    (hasset : l.broker.numericType = .fractional ∨ l.broker.numericType = .native ∨
      l.broker.numericType = .int64)
    (hfit : l.broker.numericType.isIntegral = true → 2 ≤ l.paymentRemaining.toNat →
      49 / 10 * ((l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat) + 1 ≤
        l.broker.numericType.maxValue.toNat)
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
    rw [← not_le, ← Number.operator_le_iff _ _ l.wf.totalValueOutstanding_norm hpp'N]
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
  obtain ⟨ts, hts, htpN, htp0, htpB, htiN, htiB, htmN, htmB⟩ := LoanState.buildTheoretical_tight
    l.periodicPayment rate l.rates.interestRate l.schedule.paymentInterval (l.paymentRemaining - 1)
    l.broker.managementFeeRate hrate hir hint hk' hk0 hppN hpp0.le (by linarith) l.broker.managementFeeRate_le
  set B := ((l.paymentRemaining - 1).toNat : ℚ) * l.periodicPayment.toRat with hBdef
  have hB0 : 0 ≤ B := by positivity
  have h90 : 80 * B < 10 ^ 90 := by nlinarith
  have hfitB : l.broker.numericType.isIntegral = true → 49 / 10 * B + 1 ≤ l.broker.numericType.maxValue.toNat :=
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
  simp only [UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hpr), hstate, hts, htpo', hti', htm', hdp, hdi,
    hdm, hroom, hppi, hrff, pure, Except.pure]
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



/-- What the instalment loop keeps about its loan, as `Loan.PayRoom` with an asset that holds `4.9` times the
payments left in place of `80` times. -/
structure Loan.PayRoom (l : Loan) : Prop where
  shape : l.PayShape
  scale : l.loanScale ≤ 0
  value : l.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1
  computes : l.ScheduleComputes
  payments : 2 ≤ l.paymentRemaining.toNat →
    (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1)
  clock : l.paymentRemaining.toNat * l.schedule.paymentInterval.toNat < 2 ^ 32
  asset : l.broker.numericType = .fractional ∨ l.broker.numericType = .native ∨ l.broker.numericType = .int64
  fits : l.broker.numericType.isIntegral = true → 2 ≤ l.paymentRemaining.toNat →
    49 / 10 * ((l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat) + 1 ≤ l.broker.numericType.maxValue.toNat
  fee : l.fees.serviceFee.Below 97 ∧ 0 ≤ l.fees.serviceFee.toRat

/-- On a `PayRoom` loan the next scheduled instalment computes, with value, principal and fee parts each between
zero and `10^17` in size, and no untracked interest. -/
lemma Loan.PayRoom.components {l : Loan} (h : l.PayRoom) (hpr : l.paymentRemaining ≠ 0) :
    ∃ pc, Loan.scheduledComponents l = .ok pc ∧ pc.totalValueDelta.Below 17 ∧ pc.principalDelta.Below 17 ∧
      pc.managementFeeDelta.Below 17 ∧ 0 ≤ pc.totalValueDelta.toRat ∧ 0 ≤ pc.principalDelta.toRat ∧
      0 ≤ pc.managementFeeDelta.toRat ∧ pc.untrackedInterest = Number.zero := by
  have hs := h.shape
  obtain ⟨pc, hpc⟩ := Loan.scheduledComponents_computes_tight l hs.1 h.scale hs.3 h.value h.computes h.payments h.clock
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
lemma Loan.PayRoom.next {l l' : Loan} (h : l.PayRoom) (pc : PaymentComponents) (fee : Number)
    (hpc : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) (hpr : l.paymentRemaining ≠ 0)
    (hdo : Loan.doPayment l { pc with untrackedManagementFee := fee } = .ok l') : l'.PayRoom := by
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

/-- The instalment loop computes on a `PayRoom` loan, from running sums within the instalments paid so far.
It keeps the fee at least zero and never lowers the total paid. -/
lemma UnsettledPayment.payInstalments_computes_room {α : Type} (amount : Number) :
    ∀ (n : Nat) (p : UnsettledPayment α), p.loan.PayRoom → p.count + n ≤ 100 → p.totalPaid.isNormalized →
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
    have hdue0 := Number.operator_add_nonneg _ _ _ b1.1 bS.1 hdue (by linarith)
    have hdue' : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).totalDue =
        .ok due := by
      unfold PaymentComponents.totalDue
      simp only [hd1, hdue, bind, Except.bind]
    have hdl : |due.toRat| < 10 ^ 99 := lt_of_lt_of_le bdue.2 (by norm_num)
    obtain ⟨tp', htp', htp'N, htp'l⟩ := Number.add_count htN bdue.1 htl hdl hcq
    have htp'ge : p.totalPaid.toRat ≤ tp'.toRat := by
      have := rn_ge (Number.operator_add_rounded_to_nearest _ _ _ htN bdue.1 htp') p.totalPaid htN (by linarith)
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
    have hfp0 : 0 ≤ inst.feePaid.toRat := Number.operator_add_nonneg _ _ _ b3.1 bS.1 hfp (by linarith)
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
lemma Loan.PayRoom.unimpaired {l : Loan} (h : l.PayRoom) : l.unimpaired.PayRoom :=
  ⟨h.shape.unimpaired, h.scale, h.value, ⟨h.computes.1, h.computes.2, h.computes.3⟩, h.payments, h.clock, h.asset,
    h.fits, h.fee⟩

/-- A regular payment of at least its amount due pays its instalments on a `PayRoom` loan that passes the
checks and is not late, when its unimpair passes. Its fee is at least zero and it pays at least the amount due. -/
lemma Loan.regularPayInstalments_due_room (loan : Loan) (hroom : loan.PayRoom) (v : Vault) (now : UInt32)
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
  have hfp0 : 0 ≤ fp.toRat := Number.operator_add_nonneg _ _ _ b3.1 bS.1 hfp (by linarith)
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
    have hpr0 : (loan.unimpaired.paymentRemaining == 0) = false := by simpa using! hrem
    simp only [hpr0, Bool.false_eq_true, ↓reduceIte, Loan.scheduledComponents_unimpaired, hpc0, hfee, bind,
      Except.bind]
    rw [show ({ pc0 with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents) = pc from rfl]
    simp only [hdue', Number.operator_add_zero_left, (Number.operator_lt_eq_false_iff amount due hamt hdueN).mpr hge,
      Bool.false_eq_true,
      ↓reduceIte, hinst, hl1, PaymentAmounts.zero_add, pure, Except.pure]
    by_cases hfin : pc0.isFinal = true
    · simp only [hfin, ↓reduceIte]
      exact ⟨_, rfl, hfp0, le_rfl, le_rfl, hdueN⟩
    have hf : pc0.isFinal = false := by simpa using hfin
    have hroom1 := hroom'.next pc0 loan.fees.serviceFee (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0)
      hf hrem hl1
    obtain ⟨q, hq, hqF, hqtp, hqc, hqN⟩ := UnsettledPayment.payInstalments_computes_room amount 99
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

/-- An overpayment of exactly its amount due pays the same instalments as a regular payment and no overpayment
tail, when the loan's asset holds the amount exactly. Its fee is at least zero. -/
lemma Loan.overPayInstalments_due_room (loan : Loan) (hroom : loan.PayRoom) (v : Vault) (now : UInt32)
    (hc : loan.canPay .overpayment = .tesSUCCESS) (hdd : loan.nextPaymentDueDate ≠ 0)
    (hnl : loan.isPaymentLate now = false)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (pc : PaymentComponents) (td : Number) (hpc : loan.paymentComponents .overpayment now = .ok pc)
    (htd : pc.totalDue = .ok td) (htdN : td.isNormalized) (htd0 : 0 ≤ td.toRat)
    (hrep : STAmount.isRounded loan.broker.numericType td = false) :
    ∃ q, (loan.payInstalments v .overpayment td now).run = .ok (.ok q) ∧
      (loan.payInstalments v .regular td now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat := by
  obtain ⟨q, hq, hqF, hqtp, hqN⟩ := Loan.regularPayInstalments_due_room loan hroom v now
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
