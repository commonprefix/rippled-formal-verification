import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.PaymentTotal
import XRPL.Properties.Lending.Loan.Common.NextPayment
import XRPL.Properties.Lending.Loan.Common.FactorGapLoan
import XRPL.Properties.Lending.Loan.Common.Payoff
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayRoom

/-! # The first instalment of a LoanPay computes

On a reachable ledger every payment type computes its first instalment and amount due, whatever the amount paid.
On XRP a late instalment needs its late interest to be an XRP amount (FV_M4_53). -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents roundAndSplitInterest
  from XRPL.Model.Lending.Loan.LoanPay
open private loanLatePaymentInterest_le loanPeriodicRate_le_cap from XRPL.Properties.Lending.Loan.Common.PaySize
open private loanLatePaymentInterest_computes from XRPL.Properties.Lending.Loan.Common.NextPayment
open private STAmount.roundToNumericType_asset_ok from XRPL.Properties.Lending.Loan.Common.NextInstalment
open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful
open private loanPrincipalFromPeriodicPayment_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest

local notation "ε" => Number.nearestError

/-- A loan stored on a reachable ledger has what the instalment loop needs to compute its next instalment, on an
IOU, XRP or MPT vault and whatever the loan owes. -/
lemma LendingLedger.Reachable.payRoom {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) : loan.PayRoom := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  obtain ⟨hlo, -, hint⟩ := hreach.loanScale_facts
  have hs0 : loan.loanScale ≤ 0 := by rw [hls]; exact hbase.2
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hs0
  have hT := Loan.Reachable.totalValue_le hreach
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 :=
    le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  have hroom := hreach.paymentRoom
  have hasset : loan.broker.numericType = .fractional ∨ loan.broker.numericType = .native ∨
      loan.broker.numericType = .int64 := by rw [hnt]; exact hr.holdsAsset
  obtain ⟨bS, hS0, -, -, -, -⟩ := hreach.fees_below
  obtain ⟨e, b, he, -, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hsched : loan.schedule = e.loan.schedule := (congrArg RawLoan.schedule hraw :)
  obtain ⟨s, hls'⟩ := hr.loansInv
  have hmat := hls'.mature i e he
  have hred : s.redemptionDate.toNat < 2 ^ 32 := s.redemptionDate.toNat_lt
  have hprle := UInt32.le_iff_toNat_le.mp (Loan.Reachable.paymentRemaining_le loan t hreach)
  have hclock : loan.paymentRemaining.toNat * loan.schedule.paymentInterval.toNat < 2 ^ 32 := by
    rw [hsched] at hprle ⊢
    have h1 := Nat.mul_le_mul_right e.loan.schedule.paymentInterval.toNat hprle
    rw [Nat.mul_comm e.loan.schedule.paymentTotal.toNat] at h1
    unfold loanRedemptionBuffer at hmat
    generalize e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat = A at h1 hmat
    generalize loan.paymentRemaining.toNat * e.loan.schedule.paymentInterval.toNat = B at h1 ⊢
    omega
  -- the payments left are worth less than twice TotalValueOutstanding on XRP or an MPT
  have hfits : loan.broker.numericType.isIntegral = true → 2 ≤ loan.paymentRemaining.toNat →
      49 / 10 * ((loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat) + 1 ≤
        loan.broker.numericType.maxValue.toNat := by
    intro hintg h2
    have hrem : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at h2; simp at h2
    obtain ⟨pp', hpp'⟩ := hreach.scheduleComputes.payment hrem
    have hneeds := hreach.needsAllPayments hrem pp' hpp'
    have hppN := loan.wf.periodicPayment_norm
    have hpp0 : 0 < loan.periodicPayment.toRat := loan.exact.periodicPayment_pos
    have hle : loan.periodicPayment.toRat ≤ pp'.toRat :=
      (STAmount.roundToNumericType_int_grid _ hintg _ _ .upward _ hppN hpp0.le (Or.inr (Or.inl rfl)) hpp').2.2.1 rfl
    have hprq : (2 : ℚ) ≤ loan.paymentRemaining.toNat := by exact_mod_cast h2
    have hlt : (loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat <
        2 * loan.totalValueOutstanding.toRat := by nlinarith
    rcases hasset with h | h | h
    · rw [h] at hintg; cases hintg
    · rw [h]
      have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
      rw [this]
      linarith
    · rw [h]
      have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
      rw [this]
      linarith
  exact ⟨⟨by omega, hint, hreach.interestDue_nonneg⟩, hs0, hT', hreach.scheduleComputes,
    fun h2 => le_trans (hroom.periodic h2) (by nlinarith), hclock, hasset, hfits, bS, hS0⟩

/-- The late interest of a loan in exact arithmetic: PrincipalOutstanding × LateInterestRate × the seconds since
NextPaymentDueDate over a year. -/
def Loan.lateInterestExact (loan : Loan) (now : UInt32) : ℚ :=
  loan.principalOutstanding.toRat * (loan.rates.lateInterestRate.toNat / 100000) *
    (((now.toNat - loan.nextPaymentDueDate.toNat : ℕ) : ℚ) / 31536000)

/-- The late interest is at least zero in exact arithmetic. -/
lemma Loan.lateInterestExact_nonneg (loan : Loan) (now : UInt32) : 0 ≤ loan.lateInterestExact now := by
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  unfold Loan.lateInterestExact
  positivity

/-- The late interest the model computes is at most the exact one, times four roundings. -/
lemma Loan.lateInterest_le_exact (l : Loan) (now : UInt32) (li : Number)
    (h : loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate = .ok li) :
    li.toRat ≤ l.lateInterestExact now * (1 + ε) ^ 4 := by
  have he := Number.nearestError_pos
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hE0 := l.lateInterestExact_nonneg now
  have hzero : li = Number.zero → li.toRat ≤ l.lateInterestExact now * (1 + ε) ^ 4 :=
    fun hz => by subst hz; rw [Number.toRat_zero]; positivity
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
  have hle' : l.nextPaymentDueDate ≤ now := UInt32.le_of_lt (UInt32.not_le.mp h3)
  simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, bind, Except.bind] at h
  rw [UInt32.subChecked_of_le hle'] at h
  dsimp only at h
  split at h
  · cases h
  rename_i rate hrate
  obtain ⟨hrN, hr0, -⟩ := loanPeriodicRate_le_cap _ _ rate l.exact.lateInterestRate_cap hrate
  have hrb := (loanPeriodicRate_bounds _ _ rate hrate).1
  have hsub : ((now - l.nextPaymentDueDate).toNat : ℚ) = ((now.toNat - l.nextPaymentDueDate.toNat : ℕ) : ℚ) := by
    rw [UInt32.toNat_sub_of_le _ _ hle']
  rw [hsub] at hrb
  have hle := (Number.mul_near _ _ _ l.wf.principalOutstanding_norm hrN h).le (mul_nonneg hP0 hr0)
  calc li.toRat ≤ l.principalOutstanding.toRat * rate.toRat * (1 + ε) := hle
    _ ≤ l.principalOutstanding.toRat * (((now.toNat - l.nextPaymentDueDate.toNat : ℕ) : ℚ) *
          l.rates.lateInterestRate.toNat / (10 ^ 5 * 31536000) * (1 + ε) ^ 3) * (1 + ε) := by gcongr
    _ = l.lateInterestExact now * (1 + ε) ^ 4 := by unfold Loan.lateInterestExact; ring

/-- A late interest whose exact value is two units below a bound stays one unit below it as the model computes
it, for a bound of at most `10^17`. -/
lemma Loan.lateInterest_fits (l : Loan) (now : UInt32) (li : Number) (B : ℚ) (hB : B ≤ 10 ^ 17)
    (h : loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate = .ok li)
    (hfit : l.lateInterestExact now + 2 ≤ B) : li.toRat + 1 ≤ B := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hE0 := l.lateInterestExact_nonneg now
  have hle := l.lateInterest_le_exact now li h
  have h4 : (1 + ε) ^ 4 ≤ 1 + 2 * (4 : ℕ) * ε := one_add_pow_le_lin ε 4 he.le (by push_cast; linarith)
  push_cast at h4
  have hE : l.lateInterestExact now ≤ 10 ^ 17 := by linarith
  have h5 : l.lateInterestExact now * (1 + ε) ^ 4 ≤ l.lateInterestExact now + 1 := by
    have : l.lateInterestExact now * (1 + ε) ^ 4 ≤ l.lateInterestExact now * (1 + 2 * 4 * ε) :=
      mul_le_mul_of_nonneg_left h4 hE0
    nlinarith
  linarith

/-- On a `PayRoom` loan with payments left a regular payment computes its instalment and amount due. -/
lemma Loan.PayRoom.regularDue_computes {loan : Loan} (h : loan.PayRoom) (now : UInt32)
    (hpr : loan.paymentRemaining ≠ 0) :
    ∃ pc td, loan.paymentComponents .regular now = .ok pc ∧ pc.totalDue = .ok td ∧ td.isNormalized := by
  obtain ⟨pc0, hpc0, b1, b2, b3, h1, h2, h3, hu⟩ := h.components hpr
  obtain ⟨bS, hS0⟩ := h.fee
  have bu : pc0.untrackedInterest.Below 17 := by
    rw [hu]; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero, abs_zero]; positivity⟩
  obtain ⟨d1, hd1⟩ := Number.Below.add_ok (by norm_num) b1 bu
  have bd1 := Number.Below.add b1 bu hd1
  have bd97 : d1.Below 97 := bd1.mono (by norm_num)
  obtain ⟨td, htd⟩ := Number.Below.add_ok (by norm_num) bd97 bS
  refine ⟨{ pc0 with untrackedManagementFee := loan.fees.serviceFee }, td, ?_, ?_, (Number.Below.add bd97 bS htd).1⟩
  · show (Loan.scheduledComponents loan >>= fun pc =>
      pure { pc with untrackedManagementFee := loan.fees.serviceFee }) = _
    rw [hpc0, ok_bind]
    rfl
  · unfold PaymentComponents.totalDue
    simp only [hd1, htd, bind, Except.bind]

/-- On a `PayRoom` loan with payments left a late payment computes its instalment and amount due, when the late
interest of an XRP loan is two drops below the largest XRP amount in exact arithmetic. -/
lemma Loan.PayRoom.lateDue_computes {loan : Loan} (h : loan.PayRoom) (now : UInt32)
    (hpr : loan.paymentRemaining ≠ 0) (hlf : loan.fees.latePaymentFee.Below 97)
    (hxrp : loan.broker.numericType = .native → loan.lateInterestExact now + 2 ≤ 10 ^ 17) :
    ∃ pc td, loan.paymentComponents .late now = .ok pc ∧ pc.totalDue = .ok td ∧ td.isNormalized := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨pc0, hpc0, b1, b2, b3, h1, h2, h3, hu⟩ := h.components hpr
  obtain ⟨bS, hS0⟩ := h.fee
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
  have hmaxN : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
  have hmaxM : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
  have hfitli : loan.broker.numericType.isIntegral = true →
      |li.toRat| + 1 ≤ loan.broker.numericType.maxValue.toNat := by
    intro hint
    rw [abs_of_nonneg hli0]
    rcases h.asset with hn | hn | hn
    · rw [hn] at hint; cases hint
    · rw [hn, hmaxN]
      exact loan.lateInterest_fits now li _ le_rfl hli (hxrp hn)
    · rw [hn, hmaxM]; nlinarith
  obtain ⟨lr, hlr, hlrN, hlrl⟩ := STAmount.roundToNumericType_asset_ok _ li .to_nearest loan.loanScale h.asset hsc
    hliN (by rw [abs_of_nonneg hli0]; nlinarith) hfitli
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hliN hli0 (Or.inl rfl) ⟨hsc.1, by omega⟩ hlr
  have hlrb : lr.toRat ≤ 276 * loan.totalValueOutstanding.toRat + 1 := by
    rw [abs_of_nonneg hli0, abs_of_nonneg hlr0] at hlrl; nlinarith
  have hfit : loan.broker.numericType.Fits lr.toRat := by
    rcases h.asset with hn | hn | hn
    · exact Or.inl ⟨hn, by nlinarith⟩
    · refine Or.inr ⟨Or.inl hn, ?_⟩
      -- the rounded late interest of an XRP loan is a whole number of drops at most the bound of the exact one
      have hint : loan.broker.numericType.isIntegral = true := by rw [hn]; rfl
      have hgrid := (STAmount.roundToNumericType_int_grid _ hint li lr .to_nearest _ hliN hli0 (Or.inl rfl) hlr).1
      have hli1 := loan.lateInterest_fits now li _ le_rfl hli (hxrp hn)
      have hup := hgrid.upper (10 ^ 17 - 1) (by push_cast; simp only [mul_one]; linarith)
      rw [hn, hmaxN]
      push_cast at hup
      simp only [mul_one] at hup
      linarith
    · refine Or.inr ⟨Or.inr hn, ?_⟩
      rw [hn, hmaxM]; nlinarith
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
  refine ⟨{ pc0 with untrackedInterest := net, untrackedManagementFee := uf }, td, ?_, ?_,
    (Number.Below.add bd99 buf htd).1⟩
  · show Loan.lateComponents loan now = _
    unfold Loan.lateComponents
    simp only [hpc0, hli, hrs, hsf, huf, bind, Except.bind, pure, Except.pure]
  · unfold PaymentComponents.totalDue
    simp only [hd1, htd, bind, Except.bind]

/-- For XRP or an MPT the scale does not change the rounding to the asset. -/
private lemma STAmount.roundToNumericType_integral_scale (nt : NumericType) (hint : nt.isIntegral = true)
    (x : Number) (mode : rounding_mode) (s : Int) :
    STAmount.roundToNumericType nt x mode (some s) = STAmount.roundToNumericType nt x mode := by
  unfold STAmount.roundToNumericType
  cases hof : STAmount.ofNumber nt x mode with
  | error e => rfl
  | ok ret =>
    have hri : ret.integral = true := by
      unfold STAmount.integral
      rw [STAmount.ofNumber_mNumericType _ _ _ _ hof]
      exact hint
    simp only [hri, ↓reduceIte]

/-- A full payment that is not late, with two or more payments left, computes its instalment and amount due, while
an IOU ClosePaymentFee is below `10^90`. -/
lemma Loan.Reachable.fullDue_computes {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (hls : loan.loanScale ≤ 0)
    (now : UInt32) (hnl : now ≤ loan.nextPaymentDueDate) (hpr : 2 ≤ loan.paymentRemaining.toNat)
    (hasset : loan.broker.numericType = .fractional ∨ loan.broker.numericType = .native ∨
      loan.broker.numericType = .int64)
    (hcfi : loan.broker.numericType = .fractional → loan.fees.closePaymentFee.toRat < 10 ^ 90) :
    ∃ pc td, loan.paymentComponents .full now = .ok pc ∧ pc.totalDue = .ok td ∧ td.isNormalized := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hlo, hhi, hint⟩ := hre.loanScale_facts
  obtain ⟨bT, bP, bM, hP0, hM0, hPM, hT⟩ := hre.outstanding_below hls
  obtain ⟨-, -, -, -, bC, hF0⟩ := hre.fees_below
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  have hp0 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hls
  have hmaxN : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
  have hmaxM : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
  have hsc := hre.scheduleComputes
  obtain ⟨rate, hrate⟩ := hsc.rate
  obtain ⟨tpo, htpo⟩ := hsc.principal rate hrate
  obtain ⟨hrN, hr0, hr137⟩ := loanPeriodicRate_le_cap _ _ rate (by
    have := loan.valid.interestRate_cap
    unfold maxLoanRate kTenthBipsPerUnity at this
    exact UInt32.le_iff_toNat_le.mp this) hrate
  have hppN := loan.wf.periodicPayment_norm
  have hpp0 : 0 ≤ loan.periodicPayment.toRat := le_of_lt loan.exact.periodicPayment_pos
  obtain ⟨htpo0, htpole, htpor⟩ := loanPrincipalFromPeriodicPayment_le_payments _ _ _ _ hppN hpp0 hrN hr0 htpo
  have htpoN := loanPrincipalFromPeriodicPayment_normalized hppN hrN htpo
  have hroom := hre.paymentRoom
  have hper := hroom.periodic hpr
  have hn2 : (2 : ℚ) ≤ loan.paymentRemaining.toNat := by exact_mod_cast hpr
  set B := (loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat with hB
  have hB16 : B ≤ 2 * (10 ^ 16 + 1) := by nlinarith
  have hppB : 2 * loan.periodicPayment.toRat ≤ B := by nlinarith
  have htpo3 := loanPrincipalFromPeriodicPayment_le_third _ _ loan.rates.interestRate loan.schedule.paymentInterval _
    tpo hrate (UInt32.le_iff_toNat_le.mp loan.valid.paymentInterval_min) hppN hpp0 htpo
  have htpoB : tpo.toRat ≤ 31 / 10 * B := by rw [hB]; linarith
  have htpol : |tpo.toRat| < 10 ^ 150 := by
    rw [abs_of_nonneg htpo0]
    linarith [show (31 / 10 : ℚ) * (2 * (10 ^ 16 + 1)) < 10 ^ 150 by norm_num]
  have hl0 : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hpr; simp at hpr
  have hdue : now.toNat ≤ (if loan.previousPaymentDueDate < loan.schedule.startDate then loan.schedule.startDate
      else loan.previousPaymentDueDate).toNat + loan.schedule.paymentInterval.toNat :=
    le_trans (UInt32.le_iff_toNat_le.mp hnl) (hroom.lastDue hl0)
  have hcr : loan.rates.closeInterestRate.toNat ≤ 100000 := loan.exact.closeInterestRate_cap
  have hfi : ∀ fi, computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval
      loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate = .ok fi →
      fi.isNormalized ∧ 0 ≤ fi.toRat ∧ loan.broker.numericType.Fits fi.toRat := by
    intro fi hfiok
    obtain ⟨hfN, hf0, hfle⟩ := computeFullPaymentInterest_le_principal tpo rate now _ _ _ _ fi htpoN htpo0 hrN hr0 hcr
      hdue hfiok
    -- the payoff interest is at most 4.2 times the payments left
    have h4 : (1 + ε) ^ 4 ≤ 42 / 41 := by
      have := one_add_pow_le_lin ε 4 he.le (by push_cast; linarith)
      push_cast at this; linarith
    have hsum : tpo.toRat * rate.toRat + tpo.toRat ≤ 41 / 10 * B := by linarith
    have h72 : fi.toRat ≤ 42 / 10 * B := by
      calc fi.toRat ≤ (tpo.toRat * rate.toRat + tpo.toRat) * (1 + ε) ^ 4 := hfle
        _ ≤ 41 / 10 * B * (42 / 41) := mul_le_mul hsum h4 (by positivity) (by positivity)
        _ = 42 / 10 * B := by ring
    refine ⟨hfN, hf0, ?_⟩
    rcases hasset with hn | hn | hn
    · exact Or.inl ⟨hn, by linarith [show (42 / 10 : ℚ) * (2 * (10 ^ 16 + 1)) < 10 ^ 90 by norm_num]⟩
    · refine Or.inr ⟨Or.inl hn, ?_⟩
      rw [hn, hmaxN]
      linarith
    · refine Or.inr ⟨Or.inr hn, ?_⟩
      rw [hn, hmaxM]
      linarith
  -- the close fee is an amount of the asset, so it rounds to itself
  have hstcf : STAmount.isRounded loan.broker.numericType loan.fees.closePaymentFee = false :=
    Loan.Reachable.fees_representable hre _ (by simp [LoanFees.amountFields])
  obtain ⟨cf, hcf⟩ : ∃ cf, STAmount.roundToNumericType loan.broker.numericType loan.fees.closePaymentFee
      .to_nearest (some loan.loanScale) = .ok cf := by
    rcases hasset with hn | hn | hn
    · rw [hn]
      exact STAmount.roundToNumericType_frac_ok _ .to_nearest _ loan.wf.closePaymentFee_norm hF0 (hcfi hn)
        ⟨by omega, by omega⟩
    · rw [STAmount.roundToNumericType_integral_scale _ (by rw [hn]; rfl)]
      exact STAmount.roundToNumericType_ok_of_isRounded_false _ _ hstcf
    · rw [STAmount.roundToNumericType_integral_scale _ (by rw [hn]; rfl)]
      exact STAmount.roundToNumericType_ok_of_isRounded_false _ _ hstcf
  have hgcf := (Loan.Reachable.fees_onGrid hre).2.2
  have hcfv := STAmount.roundToNumericType_of_representable _ _ _ _ loan.wf.closePaymentFee_norm hF0
    ⟨by omega, by omega⟩ hre.loanScale_integral hstcf hgcf hcf
  have hcf0 : 0 ≤ cf.toRat := by rw [hcfv]; exact hF0
  have hcfl : |cf.toRat| < 10 ^ 150 := by
    rw [abs_of_nonneg hcf0, hcfv]
    have := bC.2
    rw [abs_of_nonneg hF0] at this
    linarith [show (10 : ℚ) ^ 97 < 10 ^ 150 by norm_num]
  have hb150 : (10 : ℚ) ^ 17 < 10 ^ 150 := by norm_num
  obtain ⟨pc, fi, fi', fee, hfiok, hfi', hfee, hfee0, hfeele, hfi'le, hpc, hfin, hPD, hMD, hTVD, hUI, hUMF, hUMFge,
      hUMFle⟩ := Loan.fullComponents_ok loan now rate tpo cf hrate htpo htpoN htpol hrN
    (by rw [abs_of_nonneg hr0]; linarith [show (137 : ℚ) < 10 ^ 20 by norm_num]) hfi hcf hcfl hcf0
    ⟨by omega, by omega⟩ (lt_trans bT.2 hb150) (lt_trans bP.2 hb150) (lt_trans bM.2 hb150)
  obtain ⟨d1, hd1⟩ := hTVD.add_ok (by norm_num) hUI
  have hd1B := hTVD.add hUI hd1
  obtain ⟨due, hdue'⟩ := hd1B.add_ok (by norm_num) (hUMF.mono (by norm_num))
  refine ⟨pc, due, hpc, ?_, (hd1B.add (hUMF.mono (by norm_num)) hdue').1⟩
  unfold PaymentComponents.totalDue
  rw [hd1, ok_bind, hdue']

/-- A payment that passes the LoanPay checks is rejected with a result code or pays its instalments. An XRP late
interest fits, an IOU ClosePaymentFee is below `10^90`, and an overpayment pays at most the next amount due. -/
lemma Loan.Reachable.pay_rejected_or_instalments {loan : Loan} {t : UInt32} (hre : loan.Reachable t)
    (hroom : loan.PayRoom) (v : Vault) (now : UInt32) (pt : LoanPaymentType) (amount : Number)
    (hc : loan.canPay pt = .tesSUCCESS) (hamt : amount.isNormalized) (hamt0 : 0 ≤ amount.toRat)
    (hrep : STAmount.isRounded loan.broker.numericType amount = false)
    (hover : pt = .overpayment → ∀ pc td, loan.paymentComponents .overpayment now = .ok pc →
      pc.totalDue = .ok td → amount.toRat ≤ td.toRat)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (hlate : loan.broker.numericType = .native → pt = .late → loan.lateInterestExact now + 2 ≤ 10 ^ 17)
    (hcfi : loan.broker.numericType = .fractional → pt = .full → loan.fees.closePaymentFee.toRat < 10 ^ 90) :
    (∃ ter, (loan.pay v pt amount now).run = .ok (.error ter)) ∨
      ∃ q, (loan.payInstalments v pt amount now).run = .ok (.ok q) ∧ 0 ≤ q.amounts.feePaid.toRat := by
  obtain ⟨-, hrem, hpo⟩ := Loan.canPay_active hc
  have hdd := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hre hrem
  have hls := hroom.scale
  cases pt with
  | overpayment =>
    by_cases hl : loan.nextPaymentDueDate < now
    · exact Or.inl ⟨_, Loan.overpayment_late_proof loan v amount now hrem hpo (fun _ => hdd) hl⟩
    have hnl : loan.isPaymentLate now = false := by simp [Loan.isPaymentLate, hl]
    have hchecks : loan.PayChecks .overpayment now :=
      ⟨hrem, hpo, hdd, ⟨nofun, fun h => absurd h hl⟩, nofun⟩
    obtain ⟨pc, td, hpc, htd, htdN⟩ := hroom.regularDue_computes now hrem
    have hpc' : loan.paymentComponents .overpayment now = .ok pc := hpc
    by_cases hlt : amount.operator_lt td = true
    · exact Or.inl ⟨_, Loan.payment_insufficient_proof loan v amount now .overpayment pc td hchecks hunimpair hpc' htd
        hlt⟩
    -- the overpayment pays exactly the amount due, so its tail has nothing left
    have hge := (Number.operator_lt_eq_false_iff amount td hamt htdN).mp (by simpa using hlt)
    obtain rfl : amount = td :=
      Number.isNormalized.toRat_inj hamt htdN (le_antisymm (hover rfl pc td hpc' htd) hge)
    obtain ⟨q, hq, -, hqF⟩ := Loan.overPayInstalments_due_room loan hroom v now hc hdd hnl hunimpair pc amount hpc'
      htd hamt hamt0 hrep
    exact Or.inr ⟨q, hq, hqF⟩
  | regular =>
    by_cases hl : loan.nextPaymentDueDate < now
    · exact Or.inl ⟨_, Loan.regularPayment_late_proof loan v amount now hrem hpo (fun _ => hdd) hl⟩
    have hnl : loan.isPaymentLate now = false := by simp [Loan.isPaymentLate, hl]
    have hchecks : loan.PayChecks .regular now :=
      ⟨hrem, hpo, hdd, ⟨nofun, fun h => absurd h hl⟩, nofun⟩
    obtain ⟨pc, td, hpc, htd, htdN⟩ := hroom.regularDue_computes now hrem
    by_cases hlt : amount.operator_lt td = true
    · exact Or.inl ⟨_, Loan.payment_insufficient_proof loan v amount now .regular pc td hchecks hunimpair hpc htd hlt⟩
    have hge := (Number.operator_lt_eq_false_iff amount td hamt htdN).mp (by simpa using hlt)
    obtain ⟨q, hq, hqF, -, -⟩ := Loan.regularPayInstalments_due_room loan hroom v now hc hdd hnl hunimpair pc td amount
      hpc htd hamt hge
    exact Or.inr ⟨q, hq, hqF⟩
  | late =>
    by_cases hl : loan.nextPaymentDueDate < now
    · have hlb : loan.isPaymentLate now = true := by simp [Loan.isPaymentLate, hl]
      have hchecks : loan.PayChecks .late now :=
        ⟨hrem, hpo, hdd, ⟨fun _ => hl, fun _ => rfl⟩, nofun⟩
      obtain ⟨-, -, bL, -, -, -⟩ := hre.fees_below
      obtain ⟨pc, td, hpc, htd, htdN⟩ := hroom.lateDue_computes now hrem bL (fun hn => hlate hn rfl)
      by_cases hlt : amount.operator_lt td = true
      · exact Or.inl ⟨_, Loan.payment_insufficient_proof loan v amount now .late pc td hchecks hunimpair hpc htd hlt⟩
      have hge := (Number.operator_lt_eq_false_iff amount td hamt htdN).mp (by simpa using hlt)
      exact Or.inr (Loan.latePayInstalments_due hre hls v now hc hlb hunimpair pc td amount hpc htd hamt hge)
    · exact Or.inl ⟨_, Loan.latePayment_too_soon_proof loan v amount now hrem hpo (fun _ => hdd)
        (UInt32.not_lt.mp hl)⟩
  | full =>
    by_cases hl : loan.nextPaymentDueDate < now
    · exact Or.inl ⟨_, Loan.fullPayment_late_proof loan v amount now hrem hpo (fun _ => hdd) hl⟩
    have hle : now ≤ loan.nextPaymentDueDate := UInt32.not_lt.mp hl
    by_cases h1 : loan.paymentRemaining = 1
    · exact Or.inl ⟨_, Loan.fullPayment_last_proof loan v amount now hpo (fun _ => hdd) h1 hle⟩
    have hnl : loan.isPaymentLate now = false := by simp [Loan.isPaymentLate, hl]
    have hchecks : loan.PayChecks .full now :=
      ⟨hrem, hpo, hdd, ⟨nofun, fun h => absurd h hl⟩, fun _ => h1⟩
    have hpr2 : 2 ≤ loan.paymentRemaining.toNat := by
      have h0 : loan.paymentRemaining.toNat ≠ 0 := fun h0 => hrem (UInt32.toNat_inj.mp (by simpa using h0))
      have h1' : loan.paymentRemaining.toNat ≠ 1 := fun h0 => h1 (UInt32.toNat_inj.mp (by simpa using h0))
      omega
    obtain ⟨pc, td, hpc, htd, htdN⟩ := hre.fullDue_computes hls now hle hpr2 hroom.asset (fun hn => hcfi hn rfl)
    by_cases hlt : amount.operator_lt td = true
    · exact Or.inl ⟨_, Loan.payment_insufficient_proof loan v amount now .full pc td hchecks hunimpair hpc htd hlt⟩
    have hge := (Number.operator_lt_eq_false_iff amount td hamt htdN).mp (by simpa using hlt)
    exact Or.inr (Loan.fullPayInstalments_due hre hls v now hc hnl h1 hunimpair pc td amount hpc htd hamt hge)

end XRPL.Model.Lending
