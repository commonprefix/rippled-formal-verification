import XRPL.Properties.Lending.Loan.Common.DueLoop

/-! # The next payment of a loan computes its instalment

On a `LoopRoom` loan, the payment the date allows computes its first instalment and amount due.
Every value stays far below the top of the `Number` range. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.lateComponents roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private loanLatePaymentInterest_le from XRPL.Properties.Lending.Loan.Common.PaySize
open private STAmount.roundToNumericType_asset_ok from XRPL.Properties.Lending.Loan.Common.NextInstalment

/-- The payment type the date allows for the next instalment: a late payment past NextPaymentDueDate, else a
regular one. -/
def Loan.nextPaymentType (loan : Loan) (now : UInt32) : LoanPaymentType :=
  if loan.isPaymentLate now then .late else .regular

/-- A periodic rate computes for any rate and number of seconds. -/
private lemma loanPeriodicRate_computes (ir : TenthBips32) (interval : UInt32) :
    ∃ rate, loanPeriodicRate ir interval = .ok rate := by
  have heq : loanPeriodicRate ir interval =
      (tenthBipsOfValue (Number.ofInt64 interval.toUInt64.toInt64) ir .to_nearest) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  have hin := Number.ofInt64_isNormalized interval.toUInt64.toInt64
  have hiv := Number.ofInt64_count interval
  have hI : (interval.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast interval.toNat_lt
  obtain ⟨t, ht, htN, htl⟩ := tenthBipsOfValue_ok_of_abs _ ir hin
    (by rw [hiv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 190 by norm_num])
  have hir : (ir.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast ir.toNat_lt
  have he' := Number.nearestError_le
  have he := Number.nearestError_pos
  have htl' : |t.toRat| < 10 ^ 200 := by
    rw [hiv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ interval.toNat)] at htl
    have h2 : (1 + Number.nearestError) ^ 2 ≤ 2 :=
      le_trans (pow_le_pow_left₀ (by positivity) (by linarith : 1 + Number.nearestError ≤ 1 + 1 / 10 ^ 18) 2)
        (by norm_num)
    calc |t.toRat| ≤ interval.toNat * ir.toNat / 100000 * (1 + Number.nearestError) ^ 2 := htl
      _ ≤ 2 ^ 32 * 2 ^ 32 / 100000 * 2 := by gcongr
      _ < 10 ^ 200 := by norm_num
  obtain ⟨hyn, hyv⟩ := TenthBips32.toNumber_facts (31536000 : UInt32)
  have hy : secondsInYear = TenthBips32.toNumber (31536000 : UInt32) := rfl
  have hyv' : ((31536000 : UInt32).toNat : ℚ) = 31536000 := rfl
  obtain ⟨r, hr⟩ := Number.operator_div_ok_of_abs t secondsInYear .to_nearest htN (by rw [hy]; exact hyn) htl'
    (by
      rw [hy, hyv, hyv', abs_of_nonneg (by norm_num)]
      have : (10 : ℚ) ^ (-200 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      linarith)
  exact ⟨r, by rw [heq, ht, ok_bind, hr]⟩

/-- The late interest computes on a lawful loan. -/
private lemma loanLatePaymentInterest_computes (l : Loan) (now : UInt32) :
    ∃ li, loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate =
      .ok li := by
  unfold loanLatePaymentInterest
  by_cases h1 : l.principalOutstanding.operator_eq Number.zero = true
  · simp only [h1, ↓reduceIte, pure, Except.pure]
    exact ⟨_, rfl⟩
  by_cases h2 : (l.rates.lateInterestRate == 0) = true
  · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
    exact ⟨_, rfl⟩
  by_cases h3 : now ≤ l.nextPaymentDueDate
  · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
    exact ⟨_, rfl⟩
  obtain ⟨rate, hrate⟩ := loanPeriodicRate_computes l.rates.lateInterestRate (now - l.nextPaymentDueDate)
  have hrN := loanPeriodicRate_isNormalized _ _ _ hrate
  obtain ⟨hrb, -⟩ := loanPeriodicRate_bounds _ _ _ hrate
  have hr0 := loanPeriodicRate_nonneg _ _ _ hrate
  have he' := Number.nearestError_le
  have he := Number.nearestError_pos
  have hI : ((now - l.nextPaymentDueDate).toNat : ℚ) < 2 ^ 32 := by
    exact_mod_cast (now - l.nextPaymentDueDate).toNat_lt
  have hir : (l.rates.lateInterestRate.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast l.rates.lateInterestRate.toNat_lt
  have hrl : rate.toRat < 10 ^ 30 := by
    have h3' : (1 + Number.nearestError) ^ 3 ≤ 2 :=
      le_trans (pow_le_pow_left₀ (by positivity) (by linarith : 1 + Number.nearestError ≤ 1 + 1 / 10 ^ 18) 3)
        (by norm_num)
    calc rate.toRat ≤ (now - l.nextPaymentDueDate).toNat * l.rates.lateInterestRate.toNat /
          (10 ^ 5 * 31536000) * (1 + Number.nearestError) ^ 3 := hrb
      _ ≤ 2 ^ 32 * 2 ^ 32 / (10 ^ 5 * 31536000) * 2 := by gcongr
      _ < 10 ^ 30 := by norm_num
  have hPO := l.wf.principalOutstanding_norm
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hPl : l.principalOutstanding.toRat < 10 ^ 200 := by
    have := l.grid.principalOutstanding_atExponent
    obtain ⟨p, hp, hpv⟩ := this
    have hB := NumericType.mantissaBound_le l.toExact.numericType
    have hs := l.wf.loanScale_range
    unfold cMaxOffset at hs
    simp only [RawLoan.toExact] at hpv
    rw [hpv]
    have hp' : (p : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hp hB
    have hz : (10 : ℚ) ^ l.loanScale ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hs.2
    calc (p : ℚ) * 10 ^ l.loanScale ≤ 2 ^ 63 * 10 ^ (80 : ℤ) := by
          apply mul_le_mul hp'.le hz (by positivity) (by norm_num)
      _ < 10 ^ 200 := by norm_num
  have hrl' : |rate.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg hr0]; linarith [show (10 : ℚ) ^ 30 < 10 ^ 200 by norm_num]
  obtain ⟨li, hli⟩ := Number.operator_mul_ok_of_abs l.principalOutstanding rate .to_nearest hPO hrN
    (by rw [abs_of_nonneg hP0]; exact hPl) hrl'
  simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, bind, Except.bind, hrate, hli]
  exact ⟨_, rfl⟩

/-- On a `LoopRoom` loan with payments left, the next payment computes its instalment and amount due, while an XRP
loan owes less than 300 million XRP and the late fee is below `10^97`, like any amount of the asset. -/
lemma Loan.LoopRoom.nextPayment_computes {loan : Loan} (h : loan.LoopRoom) (now : UInt32)
    (hpr : loan.paymentRemaining ≠ 0)
    (hxrp : loan.broker.numericType = .native → loan.totalValueOutstanding.toRat < 3 * 10 ^ 14)
    (hlf : loan.fees.latePaymentFee.Below 97) :
    ∃ pc td, loan.paymentComponents (loan.nextPaymentType now) now = .ok pc ∧ pc.totalDue = .ok td := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨pc0, hpc0, b1, b2, b3, h1, h2, h3, hu⟩ := h.components hpr
  obtain ⟨bS, hS0⟩ := h.fee
  have bu : pc0.untrackedInterest.Below 17 := by
    rw [hu]; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero, abs_zero]; positivity⟩
  unfold Loan.nextPaymentType
  cases hl : loan.isPaymentLate now
  · -- a regular payment: the next scheduled instalment with LoanServiceFee
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨d1, hd1⟩ := Number.Below.add_ok (by norm_num) b1 bu
    have bd1 := Number.Below.add b1 bu hd1
    have bd97 : d1.Below 97 := bd1.mono (by norm_num)
    obtain ⟨td, htd⟩ := Number.Below.add_ok (by norm_num) bd97 bS
    refine ⟨{ pc0 with untrackedManagementFee := loan.fees.serviceFee }, td, ?_, ?_⟩
    · show (Loan.scheduledComponents loan >>= fun pc =>
        pure { pc with untrackedManagementFee := loan.fees.serviceFee }) = _
      rw [hpc0, ok_bind]
      rfl
    · unfold PaymentComponents.totalDue
      simp only [hd1, htd, bind, Except.bind]
  · -- a late payment: the instalment with the late interest and the late fees
    simp only [↓reduceIte]
    have hs := h.shape
    have hT := h.value
    have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
    have hi : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
        loan.managementFeeOutstanding.toRat := hs.3
    have hPT : loan.principalOutstanding.toRat ≤ loan.totalValueOutstanding.toRat := by linarith
    have hsc : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := ⟨hs.1, h.scale⟩
    -- the late interest, at most 138 times PrincipalOutstanding
    obtain ⟨li, hli⟩ := loanLatePaymentInterest_computes loan now
    obtain ⟨hliN, hli0, hlile⟩ := loanLatePaymentInterest_le loan now li hli
    have hfitli : loan.broker.numericType.isIntegral = true →
        |li.toRat| + 1 ≤ loan.broker.numericType.maxValue.toNat := by
      intro hint
      rw [abs_of_nonneg hli0]
      rcases h.asset with hn | hn | hn
      · rw [hn] at hint; cases hint
      · have hx := hxrp hn
        rw [hn]
        have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
        rw [this]; nlinarith
      · rw [hn]
        have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
        rw [this]; nlinarith
    obtain ⟨lr, hlr, hlrN, hlrl⟩ := STAmount.roundToNumericType_asset_ok _ li .to_nearest loan.loanScale h.asset hsc
      hliN (by rw [abs_of_nonneg hli0]; nlinarith) hfitli
    have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hliN hli0 (Or.inl rfl) ⟨hsc.1, by omega⟩ hlr
    have hlrb : lr.toRat ≤ 276 * loan.totalValueOutstanding.toRat + 1 := by
      rw [abs_of_nonneg hli0, abs_of_nonneg hlr0] at hlrl; nlinarith
    have hfit : loan.broker.numericType.Fits lr.toRat := by
      rcases h.asset with hn | hn | hn
      · exact Or.inl ⟨hn, by nlinarith⟩
      · refine Or.inr ⟨Or.inl hn, ?_⟩
        have hx := hxrp hn
        rw [hn]
        have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
        rw [this]; nlinarith
      · refine Or.inr ⟨Or.inr hn, ?_⟩
        rw [hn]
        have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
        rw [this]; nlinarith
    obtain ⟨split, hsplit, hspN, hsp0, hsple⟩ := computeManagementFee_ok _ lr loan.broker.managementFeeRate
      loan.loanScale hlrN hlr0 hfit loan.broker.managementFeeRate_le ⟨hsc.1, by omega⟩
    have blr : lr.Below 20 := ⟨hlrN, by rw [abs_of_nonneg hlr0]; nlinarith⟩
    have bsp : split.Below 20 := ⟨hspN, by rw [abs_of_nonneg hsp0]; linarith [blr.2, abs_of_nonneg hlr0]⟩
    obtain ⟨net, hnet⟩ := Number.Below.sub_ok (by norm_num) blr bsp
    have bnet := Number.Below.sub blr bsp hnet
    have hrs : roundAndSplitInterest li loan.broker.managementFeeRate .to_nearest loan.broker.numericType
        loan.loanScale = .ok (net, split) := by
      unfold roundAndSplitInterest
      simp only [hlr, hsplit, hnet, bind, Except.bind, pure, Except.pure]
    obtain ⟨sf, hsf⟩ := Number.Below.add_ok (by norm_num) bS hlf
    have bsf := Number.Below.add bS hlf hsf
    have bsp98 : split.Below 98 := bsp.mono (by norm_num)
    obtain ⟨uf, huf⟩ := Number.Below.add_ok (by norm_num) bsf bsp98
    have buf := Number.Below.add bsf bsp98 huf
    have b121 : pc0.totalValueDelta.Below 21 := b1.mono (by norm_num)
    obtain ⟨d1, hd1⟩ := Number.Below.add_ok (by norm_num) b121 bnet
    have bd1 := Number.Below.add b121 bnet hd1
    have bd99 : d1.Below 99 := bd1.mono (by norm_num)
    obtain ⟨td, htd⟩ := Number.Below.add_ok (by norm_num) bd99 buf
    refine ⟨{ pc0 with untrackedInterest := net, untrackedManagementFee := uf }, td, ?_, ?_⟩
    · show Loan.lateComponents loan now = _
      unfold Loan.lateComponents
      simp only [hpc0, hli, hrs, hsf, huf, bind, Except.bind, pure, Except.pure]
    · unfold PaymentComponents.totalDue
      simp only [hd1, htd, bind, Except.bind]

end XRPL.Model.Lending
