import XRPL.Properties.Lending.Ledger.Common.PayReplay
import XRPL.Properties.Lending.Ledger.Common.IsolationDefs

/-! # A payment whose instalments pass settles

On a reachable ledger whose vault is not coarsened, the settlement of a payment succeeds once its instalments
passed, no part of it is negative, it credits the vault or pays the loan off, and the cover, the credit and the fee
fit the asset. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.unimpairIfImpaired from XRPL.Model.Lending.Loan.LoanPay
open private LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private UnsettledPayment.PaidOn from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private LendingLedger.Reachable.unimpair_pool UnsettledPayment.fee_of_fits
  from XRPL.Properties.Lending.Ledger.Common.PayReplay

/-- A payment whose instalments passed succeeds on a reachable vault that is not coarsened, when no part is
negative, the vault gets principal or interest or the loan is paid off, and the cover, credit and fee fit the asset. -/
lemma LendingLedger.Reachable.pay_of_instalments {l : LendingLedger} (hr : l.Reachable)
    (hnd : l.vaultDeleted = false) {i : Nat} {e : LoanEntry} {b : LoanBroker} {loan : Loan}
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    (pt : LoanPaymentType) (amount : Number) (hc : loan.canPay pt = .tesSUCCESS)
    (hpre : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS)
    (q : UnsettledPayment Vault) (hq : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok q))
    (hqi : 0 ≤ q.loan.toExact.interestDue)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hI0 : 0 ≤ q.amounts.interestPaid.toRat) (hF0 : 0 ≤ q.amounts.feePaid.toRat)
    (hmove : 0 < q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat ∨ q.loan.paymentRemaining = 0)
    (hca : b.coverAvailable.toRat < 10 ^ 96) (hfit : l.CreditFits i pt amount) (hfee : l.FeeFits i pt amount) :
    ∃ l', (l.apply (.loanPay i pt amount)).run = .ok (.ok l') := by
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  obtain ⟨hchk, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now q hq
  obtain ⟨hAv, hADe, hARe, hYUe, hntv, hbev, hArep, hLUroom⟩ := LendingLedger.Reachable.unimpair_pool hr hat hu
  have hqb : q.loan.broker = b := by rw [hst.broker]; exact hlb
  have hntb : b.numericType = l.vault.numericType := hr.scaleInv.brokers _ b hb
  obtain ⟨hls, -⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  have hrange : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := by rw [hls]; omega
  have hsq : loan.loanScale = q.pool.baseExponent := by rw [hls, hbev]
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg

  obtain ⟨gP, gI⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now q hrange hq
  rw [hsq] at gP gI
  obtain ⟨hpN, hiN, hfN⟩ := Loan.payInstalments_norm loan l.vault amount l.now pt q hq
  obtain ⟨-, hP0, hpps⟩ : UnsettledPayment.PaidOn q loan.loanScale loan.principalOutstanding.toRat :=
    Loan.payInstalments_paidOn loan l.vault pt amount l.now q hrange hq
  have hparts : (q.amounts.principalPaid.signum < 0 || q.amounts.interestPaid.signum < 0 ||
      q.amounts.feePaid.signum < 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
    exact ⟨⟨(Number.signum_nonneg_iff_toRat hpN).mpr hP0, (Number.signum_nonneg_iff_toRat hiN).mpr hI0⟩,
      (Number.signum_nonneg_iff_toRat hfN).mpr hF0⟩
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  have hsum := Loan.Reachable.pay_sum_le hreach hrange.2 l.vault pt amount l.now q hq
  rw [hls] at hsum
  have hPI : q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat < 2 ^ 62 * 10 ^ q.pool.baseExponent := by
    rw [hbev]
    have : (300 : ℚ) * (10 ^ 16 + 1) < 2 ^ 62 := by norm_num
    nlinarith
  have hqPO0 : 0 ≤ q.loan.principalOutstanding.toRat := q.loan.exact.principalOutstanding_nonneg
  have hppPO : q.amounts.principalPaid.toRat ≤ loan.principalOutstanding.toRat := by linarith
  obtain ⟨-, -, -, hPOAD, hPODT⟩ := hr.loanAt_principal hat
  have hpoe : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hnp : loan.isPending = false := by
    unfold Loan.canPay at hc
    cases h : loan.isPending
    · rfl
    · rw [h] at hc; simp at hc
  have hnpe : e.loan.isPending = false := by
    rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw] at hnp; exact hnp
  have hPOpos : 0 < loan.principalOutstanding.toRat := by
    have h0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    rcases eq_or_lt_of_le h0 with h | h
    · exact absurd ((Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp h.symm)
        hchk.principal
    · exact h

  obtain ⟨i', hi'⟩ := Loan.interestDue_ok q.loan
  have hi'N := RawLoan.interestDue_isNormalized q.loan i' hi'
  have hsiN := RawLoan.interestDue_isNormalized loan q.scheduledInterest hsi
  have hqls : q.loan.loanScale = loan.loanScale := by rw [hst.loanScale]; rfl
  have gi' : Number.OnGrid loan.loanScale i' := hqls ▸ Loan.interestDue_onGrid q.loan i' hi'
  have gsi : Number.OnGrid loan.loanScale q.scheduledInterest := Loan.interestDue_onGrid loan _ hsi
  have hi'0 : 0 ≤ i'.toRat := by rw [Loan.interestDue_toExact q.loan i' hi']; exact hqi
  have hsiYU : q.scheduledInterest.toRat ≤ l.vault.yieldUnrealized.toRat := by
    rw [Loan.interestDue_toExact loan _ hsi]
    have hex : loan.toExact.interestDue = e.loan.toExact.interestDue := by
      show loan.toRawLoan.totalValueOutstanding.toRat - loan.toRawLoan.principalOutstanding.toRat -
        loan.toRawLoan.managementFeeOutstanding.toRat = _
      rw [hraw]; rfl
    rw [hex]; exact hr.interest_le_yield he hnpe
  have hsi0 : 0 ≤ q.scheduledInterest.toRat := by
    rw [Loan.interestDue_toExact loan _ hsi]; exact Loan.Reachable.interestDue_nonneg hreach
  have hYUb := hr.yield_lt
  have hs81 : minExponent + 18 ≤ loan.loanScale ∧ loan.loanScale ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hpL : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hpL1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hrange.2
  -- interestDue after the payment is at most TotalValueOutstanding, which only falls
  have hi'le : i'.toRat ≤ (10 ^ 16 + 1) * 10 ^ loan.loanScale := by
    have hTL := Loan.Reachable.totalValue_le hreach
    have hbelow := (Loan.payInstalments_below loan l.vault pt amount l.now q hq).1
    have hP' : 0 ≤ q.loan.principalOutstanding.toRat := q.loan.exact.principalOutstanding_nonneg
    have hM' : 0 ≤ q.loan.managementFeeOutstanding.toRat := q.loan.exact.managementFeeOutstanding_nonneg
    rw [Loan.interestDue_toExact q.loan i' hi']
    show q.loan.totalValueOutstanding.toRat - q.loan.principalOutstanding.toRat -
      q.loan.managementFeeOutstanding.toRat ≤ _
    linarith
  have hsile : q.scheduledInterest.toRat < 10 ^ 16 * 10 ^ loan.loanScale := by rw [hls]; linarith
  have hb63 : |i'.toRat - q.scheduledInterest.toRat| < 2 ^ 63 * 10 ^ loan.loanScale := by
    rw [abs_lt]; constructor <;> nlinarith
  obtain ⟨yd, hyd⟩ := Number.operator_sub_ok_of_abs i' q.scheduledInterest .to_nearest hi'N hsiN
    (by rw [abs_of_nonneg hi'0]; nlinarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hsi0]; nlinarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
  have hydN := operator_sub_isNormalized_to_nearest_sz _ _ _ hi'N hsiN hyd
  have hydv : yd.toRat = i'.toRat - q.scheduledInterest.toRat := Number.OnGrid.sub_toRat gi' gsi hs81 hb63 hyd
  have hyd0 : 0 ≤ q.pool.yieldUnrealized.toRat + yd.toRat := by rw [hYUe, hydv]; linarith
  have hydl : |yd.toRat| < 10 ^ 150 := by
    rw [hydv, abs_lt]; constructor <;> nlinarith [show (10 : ℚ) ^ 17 < 10 ^ 150 by norm_num]
  have hYU : q.pool.yieldUnrealized.toRat < 10 ^ 150 := by
    rw [hYUe]
    have : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num) hp1
    linarith [show (10 : ℚ) ^ 16 < 10 ^ 150 by norm_num]

  have hnt : q.loan.broker.numericType = q.pool.numericType := by rw [hqb, hntb, hntv]
  have hasset : Vault.HoldsAsset q.pool := by unfold Vault.HoldsAsset; rw [hntv]; exact hr.holdsAsset
  have hAg : ∃ a : ℕ, q.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
    exact ⟨a, by rw [hAv, hbev, ha]⟩
  have hA16 : q.pool.assetsAvailable.toRat < 10 ^ 16 * 10 ^ q.pool.baseExponent := by
    rw [hAv, hbev]; linarith
  have hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧
      q.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨t, ht, htv⟩ := hr.loanAt_debt_units hat
    exact ⟨t, ht, by rw [hqb, ← hlb, htv, hbev]⟩
  have hPDT : q.amounts.principalPaid.toRat ≤ q.loan.broker.debtTotal.toRat := by
    rw [hqb, ← hlb]; linarith
  have hcount : q.loan.broker.loanCount ≠ 0 := by
    rw [hqb]
    have hc' := hr.loanCountInv.counted _ b hb
    have hpos := LendingLedger.loansOf_pos he
    intro h0
    rw [h0] at hc'
    simp at hc'
    omega
  have hdep : ∃ d : ℕ, d < 10 ^ 16 ∧ q.pool.assetsDeployed.toRat = (d : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨d, -, hdv⟩ := hr.deployed_units
    refine ⟨d, ?_, by rw [hADe, hdv, hbev]⟩
    have : (d : ℚ) * 10 ^ l.vault.baseExponent < 10 ^ 16 * 10 ^ l.vault.baseExponent := by rw [← hdv]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  have hADpos : 0 < q.pool.assetsDeployed.toRat := by rw [hADe]; linarith
  have hLU : q.pool.lossUnrealized.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    linarith
  have hAR : q.pool.assetsReserved.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    have hres : l.vault.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
      rw [hpoe, hr.reservedInv.sum, hr.debtInv.deployed]
      exact LendingLedger.principalSum_add_le_all l (·.isPending) he hnpe
    rw [hARe, hADe]; linarith
  have hAAfit : q.pool.numericType.isIntegral = true → q.pool.assetsAvailable.toRat +
      q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤ q.pool.numericType.maxValue.toNat := by
    intro hint
    rw [hntv] at hint ⊢
    rw [hAv]
    exact hfit loan q hat hq hint

  obtain ⟨toBroker, cover', hfeeF, hcovN, hcov0⟩ := UnsettledPayment.fee_of_fits q hasset hnt hdebt hfN hF0
    (by have := hfee loan q hat hq; rw [hntv, hqb, ← hlb]; exact this)
    (by rw [hqb]; linarith [show (10 : ℚ) ^ 96 < 10 ^ 150 by norm_num])

  obtain ⟨r, hok⟩ := Loan.pay_ok_of_room loan l.vault pt amount l.now q hq hnt hasset hArep hAg hA16 gP gI hP0
    hI0 hPI hparts yd ⟨i', hi', hyd⟩ hydN hyd0 hydl hYU toBroker cover' hfeeF hcovN hcov0 hdebt hPDT hcount hdep
    hADpos hLU hAR hAAfit (hmove.symm.imp id id)
  refine ⟨l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool'), ?_⟩
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  simp only [ExceptT.run] at hok
  rw [hc, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hok]
  rfl

end XRPL.Model.Lending
