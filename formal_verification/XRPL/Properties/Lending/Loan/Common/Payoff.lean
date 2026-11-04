import XRPL.Properties.Lending.Loan.Common.PayoffSettle
import XRPL.Properties.Lending.Loan.Common.PaySize
import XRPL.Properties.Lending.Loan.Common.PaymentFactor
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
import XRPL.Properties.Lending.Loan.Common.PaidAmounts
import XRPL.Properties.Lending.Loan.Common.Impaired
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.VaultSteps

/-! # An active loan that is not late can be paid off

With one payment left the last regular instalment clears the loan, with two or more the full payment does. On a
reachable ledger both instalments compute and settle, given that the amounts fit the asset. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.fullComponents from XRPL.Model.Lending.Loan.LoanPay
open private loanPeriodicRate_le_cap from XRPL.Properties.Lending.Loan.Common.PaySize
open private loanPrincipalFromPeriodicPayment_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
open private LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal

/-- The interest an early payoff at `now` charges: what accrued since the last payment plus the prepayment
penalty, both on the theoretical principal. -/
def Loan.payoffInterest (loan : Loan) (now : UInt32) : Except Error Number := do
  let rate ← loan.periodicRate
  let tpo ← loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining
  computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
    loan.schedule.startDate loan.rates.closeInterestRate

/-- What a payoff of the loan on the vault needs: the loan's asset and scale are the vault's, the broker's debt
and the vault's balances hold the loan, and every amount the payoff moves fits the asset. -/
structure Loan.PayoffRoom (loan : Loan) (v : Vault) (now : UInt32) : Prop where
  numericType : loan.broker.numericType = v.numericType
  loanScale : loan.loanScale = v.baseExponent
  asset : Vault.HoldsAsset v
  gridA : Number.OnGrid v.baseExponent v.assetsAvailable
  debt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent
  principal_debt : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat
  count : loan.broker.loanCount ≠ 0
  deployed : ∃ d : ℕ, d ≤ 10 ^ 16 ∧ v.assetsDeployed.toRat = (d : ℚ) * 10 ^ v.baseExponent
  loss : v.lossUnrealized.toRat + loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat
  reserved : v.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat
  yield : loan.toExact.interestDue ≤ v.yieldUnrealized.toRat
  yield_lt : v.yieldUnrealized.toRat < 10 ^ 150
  room : v.numericType = .fractional → v.assetsAvailable.toRat + loan.broker.coverAvailable.toRat +
    loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat < 10 ^ 80
  supply : v.numericType.isIntegral = true →
    v.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat +
      loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤ v.numericType.maxValue.toNat ∧
    ∀ fi, loan.payoffInterest now = .ok fi →
      v.assetsAvailable.toRat + loan.broker.coverAvailable.toRat + loan.totalValueOutstanding.toRat + fi.toRat +
        loan.fees.serviceFee.toRat + loan.fees.closePaymentFee.toRat + 1 ≤ v.numericType.maxValue.toNat

/-- An integral asset of a vault that holds it is XRP or an MPT, with a maximum of at most `2^63`. -/
private lemma Vault.HoldsAsset.integral {v : Vault} (h : Vault.HoldsAsset v) (hint : v.numericType.isIntegral = true) :
    (v.numericType = .native ∨ v.numericType = .int64) ∧ (v.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by
  rcases h with h | h | h
  · rw [h] at hint; cases hint
  · refine ⟨Or.inl h, ?_⟩
    rw [h]
    have : NumericType.native.maxValue.toNat ≤ 2 ^ 63 := by decide
    exact_mod_cast this
  · refine ⟨Or.inr h, ?_⟩
    rw [h]
    have : NumericType.int64.maxValue.toNat ≤ 2 ^ 63 := by decide
    exact_mod_cast this

/-- The vault's asset is an IOU or else XRP or an MPT. -/
private lemma Vault.HoldsAsset.cases {v : Vault} (h : Vault.HoldsAsset v) :
    v.numericType = .fractional ∨ v.numericType.isIntegral = true := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h]; rfl)
  · exact Or.inr (by rw [h]; rfl)

/-- AssetsAvailable, CoverAvailable and the two fees of a payoff room are each below `10^80`. -/
private lemma Loan.PayoffRoom.small {loan : Loan} {v : Vault} {now : UInt32} (h : loan.PayoffRoom v now) :
    v.assetsAvailable.toRat < 10 ^ 80 ∧ loan.broker.coverAvailable.toRat < 10 ^ 80 ∧
      loan.fees.serviceFee.toRat < 10 ^ 80 ∧ loan.fees.closePaymentFee.toRat < 10 ^ 80 := by
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  have hS0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  rcases h.asset.cases with hf | hint
  · have := h.room hf
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · have h1 := (h.supply hint).1
    have h2 := (h.asset.integral hint).2
    have h3 : (2 : ℚ) ^ 63 < 10 ^ 80 := by norm_num
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- On a reachable loan the computed interestDue is a whole number of LoanScale units, at least zero. -/
private lemma Loan.Reachable.interestDue_units {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (i : Number)
    (hi : loan.interestDue = .ok i) :
    Number.OnGrid loan.loanScale i ∧ 0 ≤ i.toRat ∧
      i.toRat = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
        loan.managementFeeOutstanding.toRat := by
  have hst := Loan.state_of_interestDue loan i hi
  obtain ⟨tv, pr, mf, -, -, -, ht, hp, hm, hi', -, -, -, -⟩ := Loan.state_units loan _ hst
  have hv : i.toRat = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := by
    rw [hi'.val, ht.val, hp.val, hm.val]; push_cast; ring
  have h0 : 0 ≤ i.toRat := by
    rw [hv]; exact hre.interestDue_nonneg
  exact ⟨⟨hi'.norm, _, hi'.val⟩, h0, hv⟩

/-- The last scheduled instalment clears the loan. -/
private lemma Loan.scheduledComponents_last (loan : Loan) (hpr : loan.paymentRemaining = 1) (rate pp' : Number)
    (hrate : loan.periodicRate = .ok rate)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp') :
    Loan.scheduledComponents loan = .ok ⟨loan.totalValueOutstanding, loan.principalOutstanding,
      loan.managementFeeOutstanding, Number.zero, Number.zero, true⟩ := by
  unfold Loan.scheduledComponents
  rw [hrate, ok_bind, hpp, ok_bind]
  simp [hpr]

/-- A regular payment of the last instalment's total due pays off a reachable loan with one payment left that
is not impaired and not late. -/
lemma Loan.regularPayoff_ok {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (v : Vault) (now : UInt32)
    (h : loan.PayoffRoom v now) (hpr : loan.paymentRemaining = 1) (hpo : loan.principalOutstanding ≠ Number.zero)
    (hnl : now ≤ loan.nextPaymentDueDate) (himp : loan.isImpaired = false) :
    ∃ amount r, (loan.pay v .regular amount now).run = .ok (.ok r) ∧ r.loan'.paymentRemaining = 0 := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  have hsc := hre.scheduleComputes
  obtain ⟨rate, hrate⟩ := hsc.rate
  obtain ⟨pp', hpp⟩ := hsc.payment (by rw [hpr]; decide)
  have hpc := Loan.scheduledComponents_last loan hpr rate pp' hrate hpp
  have hdd := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hre (by rw [hpr]; decide)
  obtain ⟨hA, hC, hS, hF⟩ := h.small
  have hbase := Vault.baseExponent_scale_range v
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hT := Loan.Reachable.totalValue_le hre
  rw [h.loanScale] at hT
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 := le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  have hP0' : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hS0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hTN := loan.wf.totalValueOutstanding_norm
  have hSN := loan.wf.serviceFee_norm
  have hMN := loan.wf.managementFeeOutstanding_norm
  obtain ⟨due, hdue'⟩ := Number.operator_add_ok_of_abs loan.totalValueOutstanding loan.fees.serviceFee .to_nearest
    hTN hSN (by rw [abs_of_nonneg hT0]; linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hS0]; linarith [show (10 : ℚ) ^ 80 < 10 ^ 200 by norm_num])
  have hdueN := operator_add_isNormalized_to_nearest_sz _ _ _ hTN hSN hdue'
  have hdue : (⟨loan.totalValueOutstanding, loan.principalOutstanding, loan.managementFeeOutstanding, Number.zero,
      loan.fees.serviceFee, true⟩ : PaymentComponents).totalDue = .ok due := by
    unfold PaymentComponents.totalDue
    rw [Number.operator_add_zero_right, ok_bind, hdue']
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  obtain ⟨hgi, hi0, hiv⟩ := Loan.Reachable.interestDue_units hre i hi
  obtain ⟨fp, hfp⟩ := Number.operator_add_ok_of_abs loan.managementFeeOutstanding loan.fees.serviceFee .to_nearest
    hMN hSN (by rw [abs_of_nonneg hM0]; linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hS0]; linarith [show (10 : ℚ) ^ 80 < 10 ^ 200 by norm_num])
  have hfpN := operator_add_isNormalized_to_nearest_sz _ _ _ hMN hSN hfp
  have hfp0 := operator_add_nonneg _ _ _ hMN hSN hfp (by linarith)
  have ha : (⟨loan.totalValueOutstanding, loan.principalOutstanding, loan.managementFeeOutstanding, Number.zero,
      loan.fees.serviceFee, true⟩ : PaymentComponents).paidAmounts = .ok ⟨loan.principalOutstanding, i, fp⟩ := by
    have hi' : (loan.totalValueOutstanding.operator_sub loan.principalOutstanding .to_nearest >>=
        fun x => x.operator_sub loan.managementFeeOutstanding .to_nearest) = .ok i := hi
    obtain ⟨x, hx, hix⟩ := bind_ok_peel _ _ _ hi'
    unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta
    simp only []
    rw [hx, ok_bind, hix, ok_bind, Number.operator_add_zero_right, ok_bind, hfp]
    rfl
  obtain ⟨l', hpay, hl'⟩ := Loan.regularPayInstalments_payoff loan v now _ due hpr hpo hdd hnl himp hpc rfl hdue
    hdueN _ ha i hi
  have hst := (Loan.payInstalments_ok loan v .regular due now _ hpay).2.2.1
  have hb' : l'.broker = loan.broker := hst.broker
  have hst0 := Loan.state_of_interestDue loan i hi
  obtain ⟨tv, pr, mf, -, -, -, ht, hpu, hm, -, -, -, -, -⟩ := Loan.state_units loan _ hst0
  have hgP : Number.OnGrid v.baseExponent loan.principalOutstanding := ⟨hpu.norm, pr, by rw [hpu.val, h.loanScale]⟩
  have hgi' : Number.OnGrid v.baseExponent i := by rw [← h.loanScale]; exact hgi
  have hP0 : 0 < loan.principalOutstanding.toRat := by
    rcases lt_or_eq_of_le hP0' with h1 | h1
    · exact h1
    · exact absurd ((Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp h1.symm) hpo
  have hT62 : (10 ^ 16 + 1 : ℚ) * 10 ^ v.baseExponent < 2 ^ 62 * 10 ^ v.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hp10
  have hgS : Number.OnGrid v.baseExponent loan.fees.serviceFee := by
    rw [← h.loanScale]; exact (Loan.Reachable.fees_onGrid hre).1
  have hcredit : v.numericType.CreditFits v.assetsAvailable.toRat (loan.principalOutstanding.toRat + i.toRat) := by
    rcases h.asset.cases with hf | hint
    · exact Or.inl ⟨hf, by linarith [show (10 : ℚ) ^ 80 + 10 ^ 17 < 10 ^ 89 by norm_num]⟩
    · have h1 := (h.supply hint).1
      have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
      have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
      have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
      exact Or.inr ⟨(h.asset.integral hint).1, by linarith⟩
  have hAAfit : v.numericType.isIntegral = true → v.assetsAvailable.toRat + loan.principalOutstanding.toRat +
      i.toRat + 1 ≤ v.numericType.maxValue.toNat := by
    intro hint
    have h1 := (h.supply hint).1
    have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
    have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
    linarith
  have hfee : v.numericType.CreditFits loan.broker.coverAvailable.toRat fp.toRat := by
    rcases h.asset.cases with hf | hint
    · have := (Number.add_near _ _ _ hMN hSN hfp).le (by linarith)
      refine Or.inl ⟨hf, ?_⟩
      have h2 : fp.toRat ≤ (loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat) * 2 :=
        le_trans this (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      linarith [show (10 : ℚ) ^ 80 + (10 ^ 17 + 10 ^ 80) * 2 < 10 ^ 89 by norm_num]
    · have h1 := (h.supply hint).1
      have hb0 : v.baseExponent = 0 := by
        unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos hint]
      have hgM : Number.OnGrid v.baseExponent loan.managementFeeOutstanding := ⟨hm.norm, mf, by
        rw [hm.val, h.loanScale]⟩
      have hmax := (h.asset.integral hint).2
      have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
      have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
      have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
      have hfpv := Number.OnGrid.add_exact hgM hgS hM0 hS0 (by rw [hb0]; norm_num; linarith)
        ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩ hfp
      refine Or.inr ⟨(h.asset.integral hint).1, ?_⟩
      rw [hfpv]
      linarith
  have h150 : (10 : ℚ) ^ 17 < 10 ^ 150 := by norm_num
  have h80 : (10 : ℚ) ^ 80 < 10 ^ 150 := by norm_num
  obtain ⟨r, hr, hr0⟩ := Loan.payoff_pay_ok loan v .regular due now
    ⟨l', v, ⟨loan.principalOutstanding, i, fp⟩, due, 1, i⟩ hpay hl' (by rw [hb', h.numericType]) h.asset h.gridA
    hgP hgi' hP0 hi0 (by simp only; linarith) hfpN hfp0 hgi.1 (by rw [hiv]; exact h.yield)
    (by rw [abs_of_nonneg hi0]; linarith) (by rw [hb']; exact h.debt) (by rw [hb']; exact h.principal_debt)
    (by rw [hb']; exact h.count) h.deployed h.loss h.reserved hcredit hAAfit (by rw [hb']; exact hfee)
    (by rw [hb']; linarith) h.yield_lt
  exact ⟨due, r, hr, hr0⟩

/-- A full payment of the payoff's total due pays off a reachable loan with two or more payments left that is
not impaired and not late. -/
lemma Loan.fullPayoff_ok {loan : Loan} {t : UInt32} (hre : loan.Reachable t) (v : Vault) (now : UInt32)
    (h : loan.PayoffRoom v now) (hpr : 2 ≤ loan.paymentRemaining.toNat)
    (hpo : loan.principalOutstanding ≠ Number.zero)
    (hnl : now ≤ loan.nextPaymentDueDate) (himp : loan.isImpaired = false) :
    ∃ amount r, (loan.pay v .full amount now).run = .ok (.ok r) ∧ r.loan'.paymentRemaining = 0 := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  have hpr0 : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hpr; simp at hpr
  have hdd := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hre hpr0
  obtain ⟨hA, hC, hS, hF⟩ := h.small
  have hbase := Vault.baseExponent_scale_range v
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hT := Loan.Reachable.totalValue_le hre
  rw [h.loanScale] at hT
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 := le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  have hT0 : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg
  have hP0' : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hF0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hS0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  obtain ⟨hgi, hi0, hiv⟩ := Loan.Reachable.interestDue_units hre i hi
  have hsc := hre.scheduleComputes
  obtain ⟨rate, hrate⟩ := hsc.rate
  obtain ⟨tpo, htpo⟩ := hsc.principal rate hrate
  obtain ⟨hrN, hr0, hr137⟩ := loanPeriodicRate_le_cap _ _ rate (by
    have := loan.valid.interestRate_cap
    unfold maxLoanRate kTenthBipsPerUnity at this
    exact UInt32.le_iff_toNat_le.mp this) hrate
  have hppN := loan.wf.periodicPayment_norm
  have hpp0 : 0 ≤ loan.periodicPayment.toRat := le_of_lt loan.exact.periodicPayment_pos
  obtain ⟨htpo0, htpole, -⟩ := loanPrincipalFromPeriodicPayment_le_payments _ _ _ _ hppN hpp0 hrN hr0 htpo
  have htpoN := loanPrincipalFromPeriodicPayment_normalized hppN hrN htpo
  have hroom := hre.paymentRoom.periodic hpr
  rw [h.loanScale] at hroom
  have htpol : |tpo.toRat| < 10 ^ 150 := by
    rw [abs_of_nonneg htpo0]
    have h1 : (loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1) := by
      have := mul_le_of_le_one_right (by norm_num : (0 : ℚ) ≤ 10 ^ 16 + 1) hp1
      linarith
    nlinarith [show (140 : ℚ) * (10 ^ 16 + 1) < 10 ^ 150 by norm_num]
  have hfi : ∀ fi, computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval
      loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate = .ok fi →
      fi.isNormalized ∧ 0 ≤ fi.toRat ∧ loan.broker.numericType.Fits fi.toRat := by
    intro fi hfiok
    obtain ⟨hfiN, hfi0, hfile⟩ := Loan.Reachable.fullInterest_le hre now rate tpo fi hnl hpr hrate htpo hfiok
    refine ⟨hfiN, hfi0, ?_⟩
    rw [h.numericType]
    rcases h.asset.cases with hf | hint
    · refine Or.inl ⟨hf, ?_⟩
      rw [h.loanScale] at hfile
      have := mul_le_of_le_one_right (by norm_num : (0 : ℚ) ≤ 143 * (10 ^ 16 + 1)) hp1
      linarith [show (143 : ℚ) * (10 ^ 16 + 1) < 10 ^ 90 by norm_num]
    · have hpi : loan.payoffInterest now = .ok fi := by
        unfold Loan.payoffInterest
        rw [hrate, ok_bind, htpo, ok_bind, hfiok]
      have h2 := (h.supply hint).2 fi hpi
      exact Or.inr ⟨(h.asset.integral hint).1, by linarith⟩
  have hcfFits : loan.broker.numericType.Fits loan.fees.closePaymentFee.toRat := by
    rw [h.numericType]
    rcases h.asset.cases with hf | hint
    · exact Or.inl ⟨hf, by linarith [show (10 : ℚ) ^ 80 < 10 ^ 90 by norm_num]⟩
    · have h1 := (h.supply hint).1
      exact Or.inr ⟨(h.asset.integral hint).1, by linarith⟩
  have hls := h.loanScale
  obtain ⟨cf, hcf⟩ := STAmount.roundToNumericType_ok_of_fits _ loan.fees.closePaymentFee .to_nearest loan.loanScale
    loan.wf.closePaymentFee_norm hF0 hcfFits ⟨by omega, by omega⟩
  have hgcf := (Loan.Reachable.fees_onGrid hre).2.2
  have hstcf : STAmount.isRounded loan.broker.numericType loan.fees.closePaymentFee = false :=
    Loan.Reachable.fees_representable hre _ (by simp [LoanFees.amountFields])
  have hint0 : loan.broker.numericType.isIntegral = true → loan.loanScale = 0 := by
    intro hint
    rw [h.numericType] at hint
    rw [hls]
    unfold Vault.baseExponent NumericType.baseExponent
    rw [if_pos hint]
  have hcfv := STAmount.roundToNumericType_of_representable _ _ _ _ loan.wf.closePaymentFee_norm hF0
    ⟨by omega, by omega⟩ hint0 hstcf hgcf hcf
  have hcf0 : 0 ≤ cf.toRat := by rw [hcfv]; exact hF0
  have hcfl : |cf.toRat| < 10 ^ 150 := by
    rw [abs_of_nonneg hcf0, hcfv]; linarith [show (10 : ℚ) ^ 80 < 10 ^ 150 by norm_num]
  have hMT : loan.managementFeeOutstanding.toRat ≤ loan.totalValueOutstanding.toRat := by linarith
  have hb150 : (10 : ℚ) ^ 16 + 1 < 10 ^ 150 := by norm_num
  obtain ⟨pc, fi, fi', fee, hfiok, hfi', hfee, hfee0, hfeele, hfi'le, hpc, hfin, hPD, hMD, hTVD, hUI, hUMF, hUMFge,
      hUMFle⟩ := Loan.fullComponents_ok loan now rate tpo cf hrate htpo htpoN htpol hrN
    (by rw [abs_of_nonneg hr0]; linarith [show (137 : ℚ) < 10 ^ 20 by norm_num]) hfi hcf hcfl hcf0
    ⟨by omega, by omega⟩ (by rw [abs_of_nonneg hT0]; linarith) (by rw [abs_of_nonneg hP0']; linarith)
    (by rw [abs_of_nonneg hM0]; linarith)
  obtain ⟨hfiN, hfi0, hfile⟩ := Loan.Reachable.fullInterest_le hre now rate tpo fi hnl hpr hrate htpo hfiok
  rw [hls] at hfile
  have hfi16 : fi.toRat ≤ 143 * (10 ^ 16 + 1) := by
    have h1 : (10 ^ 16 + 1 : ℚ) * 10 ^ v.baseExponent ≤ 10 ^ 16 + 1 := mul_le_of_le_one_right (by norm_num) hp1
    linarith
  obtain ⟨d1, hd1⟩ := hTVD.add_ok (by norm_num) hUI
  have hd1B := hTVD.add hUI hd1
  obtain ⟨due, hdue'⟩ := hd1B.add_ok (by norm_num) (hUMF.mono (by norm_num))
  have hdueB := hd1B.add (hUMF.mono (by norm_num)) hdue'
  have hdue : pc.totalDue = .ok due := by
    unfold PaymentComponents.totalDue
    rw [hd1, ok_bind, hdue']
  have h160 : (10 : ℚ) ^ 16 + 1 < 10 ^ 160 := by norm_num
  have hPB : loan.principalOutstanding.Below 160 := by
    refine ⟨loan.wf.principalOutstanding_norm, ?_⟩
    rw [abs_of_nonneg hP0']
    linarith
  have hMB : loan.managementFeeOutstanding.Below 160 := by
    refine ⟨loan.wf.managementFeeOutstanding_norm, ?_⟩
    rw [abs_of_nonneg hM0]
    linarith
  have hPDB : pc.principalDelta.Below 160 := by rw [hPD]; exact hPB
  have hMDB : pc.managementFeeDelta.Below 161 := by rw [hMD]; exact hMB.mono (by norm_num)
  obtain ⟨vap, hvap⟩ := hTVD.sub_ok (by norm_num) hPDB
  have hvapB := hTVD.sub hPDB hvap
  obtain ⟨idl, hidl⟩ := hvapB.sub_ok (by norm_num) hMDB
  have hidlB := hvapB.sub hMDB hidl
  obtain ⟨ip, hip⟩ := hidlB.add_ok (by norm_num) (hUI.mono (by norm_num))
  obtain ⟨fp, hfp⟩ := (hMB.mono (by norm_num : 160 ≤ 160)).add_ok (by norm_num) hUMF
  have hfpN := operator_add_isNormalized_to_nearest_sz _ _ _ hMB.1 hUMF.1 hfp
  have hfp0 := operator_add_nonneg _ _ _ hMB.1 hUMF.1 hfp (by linarith)
  have ha : pc.paidAmounts = .ok ⟨loan.principalOutstanding, ip, fp⟩ := by
    unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta
    rw [hvap, ok_bind, hidl, ok_bind, hip, ok_bind, hMD, hfp, ok_bind, hPD]
    rfl
  obtain ⟨l', hpay, hl'⟩ := Loan.fullPayInstalments_payoff loan v now pc due hpr hpo hdd hnl himp hpc hfin hdue
    hdueB.1 _ ha i hi
  obtain ⟨-, hIPv, hFPv⟩ := Loan.Reachable.full_units hre v due now _ rate tpo fi fi' fee hpay hrate htpo hfiok hfi'
    hfee
  simp only at hIPv hFPv
  obtain ⟨hgPP, hgIP⟩ := Loan.payInstalments_onGrid loan v .full due now _ ⟨by omega, by omega⟩ hpay
  simp only at hgPP hgIP
  rw [hls] at hgPP hgIP
  have hst := (Loan.payInstalments_ok loan v .full due now _ hpay).2.2.1
  have hb' : l'.broker = loan.broker := hst.broker
  have hP0 : 0 < loan.principalOutstanding.toRat := by
    rcases lt_or_eq_of_le hP0' with h1 | h1
    · exact h1
    · exact absurd ((Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp h1.symm) hpo
  have hIP0 : 0 ≤ ip.toRat := by rw [hIPv]; linarith
  have hIPle : ip.toRat ≤ fi.toRat := by rw [hIPv]; linarith
  have hT62 : loan.principalOutstanding.toRat + ip.toRat < 2 ^ 62 * 10 ^ v.baseExponent := by
    have h1 : loan.principalOutstanding.toRat + ip.toRat ≤ 144 * (10 ^ 16 + 1) * 10 ^ v.baseExponent := by
      rw [hIPv]
      nlinarith
    have h2 : (144 * (10 ^ 16 + 1) : ℚ) * 10 ^ v.baseExponent < 2 ^ 62 * 10 ^ v.baseExponent :=
      mul_lt_mul_of_pos_right (by norm_num) hp10
    linarith
  have hcredit : v.numericType.CreditFits v.assetsAvailable.toRat (loan.principalOutstanding.toRat + ip.toRat) := by
    rcases h.asset.cases with hf | hint
    · have h89 : (10 : ℚ) ^ 80 + (10 ^ 16 + 1) + 143 * (10 ^ 16 + 1) < 10 ^ 89 := by norm_num
      exact Or.inl ⟨hf, by linarith⟩
    · have hpi : loan.payoffInterest now = .ok fi := by
        unfold Loan.payoffInterest
        rw [hrate, ok_bind, htpo, ok_bind, hfiok]
      have h2 := (h.supply hint).2 fi hpi
      exact Or.inr ⟨(h.asset.integral hint).1, by linarith⟩
  have hAAfit : v.numericType.isIntegral = true → v.assetsAvailable.toRat + loan.principalOutstanding.toRat +
      ip.toRat + 1 ≤ v.numericType.maxValue.toNat := by
    intro hint
    have hpi : loan.payoffInterest now = .ok fi := by
      unfold Loan.payoffInterest
      rw [hrate, ok_bind, htpo, ok_bind, hfiok]
    have h2 := (h.supply hint).2 fi hpi
    linarith
  have hfeeF : v.numericType.CreditFits loan.broker.coverAvailable.toRat fp.toRat := by
    rcases h.asset.cases with hf | hint
    · have h1 := (Number.add_near _ _ _ hMB.1 hUMF.1 hfp).le (by linarith)
      have h2 : (1 + Number.nearestError) ^ 2 ≤ 2 := by nlinarith
      have h3 : pc.untrackedManagementFee.toRat ≤ (cf.toRat + fee.toRat) * 2 :=
        le_trans hUMFle (mul_le_mul_of_nonneg_left h2 (by linarith))
      have h4 : fp.toRat ≤ (loan.managementFeeOutstanding.toRat + pc.untrackedManagementFee.toRat) * 2 :=
        le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      refine Or.inl ⟨hf, ?_⟩
      rw [hcfv] at h3
      linarith [show (10 : ℚ) ^ 80 + ((10 ^ 16 + 1) + (10 ^ 80 + 143 * (10 ^ 16 + 1)) * 2) * 2 < 10 ^ 89 by norm_num]
    · have hpi : loan.payoffInterest now = .ok fi := by
        unfold Loan.payoffInterest
        rw [hrate, ok_bind, htpo, ok_bind, hfiok]
      have h2 := (h.supply hint).2 fi hpi
      have hmax := (h.asset.integral hint).2
      have hb0 : loan.loanScale = 0 := hint0 (by rw [h.numericType]; exact hint)
      have hgcf' : Number.OnGrid loan.loanScale cf := by
        obtain ⟨-, k, hk⟩ := hgcf
        exact ⟨STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf, k, by rw [hcfv, hk]⟩
      have hfpv := hFPv cf hcf hgcf' hcf0 (by rw [hb0, zpow_zero, mul_one, hcfv]; linarith)
      refine Or.inr ⟨(h.asset.integral hint).1, ?_⟩
      rw [hfpv, hcfv]
      linarith
  have h150 : (10 : ℚ) ^ 17 < 10 ^ 150 := by norm_num
  have h80 : (10 : ℚ) ^ 80 < 10 ^ 150 := by norm_num
  obtain ⟨r, hr, hr0⟩ := Loan.payoff_pay_ok loan v .full due now
    ⟨l', v, ⟨loan.principalOutstanding, ip, fp⟩, due, 1, i⟩ hpay hl' (by rw [hb', h.numericType]) h.asset
    h.gridA hgPP hgIP hP0 hIP0 hT62 hfpN hfp0 hgi.1 (by rw [hiv]; exact h.yield) (by rw [abs_of_nonneg hi0]; linarith)
    (by rw [hb']; exact h.debt) (by rw [hb']; exact h.principal_debt) (by rw [hb']; exact h.count) h.deployed h.loss
    h.reserved hcredit hAAfit (by rw [hb']; exact hfeeF) (by rw [hb']; linarith) h.yield_lt
  exact ⟨due, r, hr, hr0⟩

end XRPL.Model.Lending
