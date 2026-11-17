import XRPL.Properties.Lending.Ledger.Common.PaymentSettles
import XRPL.Properties.Lending.Loan.Common.DuePayment

/-! # The settlement of a LoanPay never ends in an arithmetic error

Once its instalments passed, a payment settles with the vault and the broker. On a reachable ledger every sum of
the settlement computes while the credit and the fee fit the asset. The payment then ends in a result code, unless
one of its three lawfulness re-checks fails. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private LendingLedger.Reachable.unimpair_pool UnsettledPayment.fee_of_fits
  from XRPL.Properties.Lending.Ledger.Common.PayReplay
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private UnsettledPayment.PaidOn from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private near_lt_pow from XRPL.Properties.Lending.Loan.Common.PayoffSettle

local notation "ε" => Number.nearestError

/-- An amount the asset holds exactly is below `10^97`. -/
private lemma STAmount.representable_lt (nt : NumericType) (x : Number) (hxN : x.isNormalized) (hx0 : 0 ≤ x.toRat)
    (h : STAmount.isRounded nt x = false) : x.toRat < 10 ^ 97 := by
  have hrep := (STAmount.isRounded_eq_false_iff _ x hxN hx0).mp h
  rcases hrep with h0 | h
  · rw [h0]; positivity
  · cases hnt : nt with
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

/-- AssetsTotal of a lawful vault computes: AssetsAvailable and AssetsDeployed are amounts of the asset. -/
private lemma Vault.assetsTotal_computes (v : Vault) : ∃ t, v.assetsTotal = .ok t := by
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hA := STAmount.representable_lt _ _ v.wf.assetsAvailable_norm hA0 v.valid.assetsAvailable_representable
  have hD := STAmount.representable_lt _ _ v.wf.assetsDeployed_norm hD0 v.valid.assetsDeployed_representable
  exact Number.operator_add_ok_of_abs _ _ .downward v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm
    (by rw [abs_of_nonneg hA0]; linarith [show (10 : ℚ) ^ 97 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hD0]; linarith [show (10 : ℚ) ^ 97 < 10 ^ 200 by norm_num])

/-- A vault re-check fails only as not lawful. -/
private lemma RawVault.to_lawful_error_eq {rv : RawVault} {e : Error} (h : rv.to_lawful = .error e) :
    e = .notLawful := by
  unfold RawVault.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- A broker re-check fails only as not lawful. -/
private lemma RawLoanBroker.to_lawful_error_eq {rb : RawLoanBroker} {e : Error} (h : rb.to_lawful = .error e) :
    e = .notLawful := by
  unfold RawLoanBroker.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- A loan re-check fails only as not lawful. -/
private lemma RawLoan.to_lawful_error_eq {rl : RawLoan} {e : Error} (h : rl.to_lawful = .error e) :
    e = .notLawful := by
  unfold RawLoan.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- Once the settlement's sums and the vault update computed, the settlement ends in a result code or one of its
three re-checks fails. -/
private lemma UnsettledPayment.SettleSums.error_notLawful {payment : UnsettledPayment Vault}
    {toPool yieldDelta toBroker cover' debtTotal' : Number}
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hadj : ∃ r, (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok r) (e : Error)
    (h : (Loan.settlePayment payment.loan payment.pool payment.amounts payment.scheduledInterest).run = .error e) :
    e = .notLawful := by
  obtain ⟨r, hadj⟩ := hadj
  rcases r with ter | raw
  · rw [hsums.rejected ter hadj] at h
    cases h
  have hadj' := hadj
  simp only [ExceptT.run] at hadj'
  rcases hv : raw.to_lawful with ev | v'
  · rw [hsums.run_eq, Vault.pool_adjustBalances] at h
    unfold_ter at h
    simp only [hadj', hv] at h
    obtain rfl : ev = e := by injection h
    exact RawVault.to_lawful_error_eq hv
  rcases hb : ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
      : RawLoanBroker).to_lawful with eb | broker'
  · rw [hsums.run_eq, Vault.pool_adjustBalances] at h
    unfold_ter at h
    simp only [hadj', hv, hb] at h
    obtain rfl : eb = e := by injection h
    exact RawLoanBroker.to_lawful_error_eq hb
  rcases hl : ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful with el | loan'
  · rw [hsums.run_eq, Vault.pool_adjustBalances] at h
    unfold_ter at h
    simp only [hadj', hv, hb, hl] at h
    obtain rfl : el = e := by injection h
    exact RawLoan.to_lawful_error_eq hl
  obtain ⟨at', hat⟩ := Vault.assetsTotal_computes v'
  rw [hsums.settled raw v' broker' loan' at' hadj hv hb hl hat] at h
  split at h <;> cases h

set_option maxHeartbeats 800000 in
-- one proof derives every sum of the settlement from the reachable ledger
/-- A payment whose instalments passed ends in a result code or fails a lawfulness re-check, while the new vault
total and the fee fit the asset, the cover is below `10^96` and an IOU vault holds less than `10^88`. -/
lemma LendingLedger.Reachable.pay_settle_error {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (pt : LoanPaymentType) (amount : Number) (q : UnsettledPayment Vault)
    (hq : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok q)) (hF0 : 0 ≤ q.amounts.feePaid.toRat)
    (hca : loan.broker.coverAvailable.toRat < 10 ^ 96) (hfit : l.CreditFits i pt amount)
    (hfee : l.FeeFits i pt amount)
    (hAA : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat < 10 ^ 88) (e : Error)
    (herr : (loan.pay l.vault pt amount l.now).run = .error e) : e = .notLawful := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hchk, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now q hq
  obtain ⟨hAv, hADe, hARe, hYUe, hntv, hbev, hArep, hLUroom⟩ := LendingLedger.Reachable.unimpair_pool hr hat hu
  have hqb : q.loan.broker = loan.broker := hst.broker
  obtain ⟨hls, hntl⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  have hrange : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := by rw [hls]; omega
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hs : minExponent + 18 ≤ q.pool.baseExponent ∧ q.pool.baseExponent ≤ maxExponent - 1 := by
    rw [hbev]; unfold minExponent maxExponent; omega
  obtain ⟨hpN, hiN, hfN⟩ := Loan.payInstalments_norm loan l.vault amount l.now pt q hq
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨bT, bP, bM, hP0l, hM0l, hPMl, hTl⟩ := hreach.outstanding_below hrange.2
  have hT0l : 0 ≤ loan.totalValueOutstanding.toRat := loan.exact.totalValueOutstanding_nonneg

  -- a negative part rejects the payment
  by_cases hneg : q.amounts.principalPaid.signum < 0 ∨ q.amounts.interestPaid.signum < 0 ∨
      q.amounts.feePaid.signum < 0
  · rw [Loan.payment_negative_part_proof loan l.vault amount l.now pt q hq hneg] at herr
    cases herr
  have hnn : 0 ≤ q.amounts.principalPaid.signum ∧ 0 ≤ q.amounts.interestPaid.signum := by
    constructor <;> (by_contra hc; exact hneg (by simp only [not_le] at hc; tauto))
  have hP0 : 0 ≤ q.amounts.principalPaid.toRat := (Number.signum_nonneg_iff_toRat hpN).mp hnn.1
  have hI0 : 0 ≤ q.amounts.interestPaid.toRat := (Number.signum_nonneg_iff_toRat hiN).mp hnn.2
  have hparts : (q.amounts.principalPaid.signum < 0 || q.amounts.interestPaid.signum < 0 ||
      q.amounts.feePaid.signum < 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
    exact ⟨⟨hnn.1, hnn.2⟩, (Number.signum_nonneg_iff_toRat hfN).mpr hF0⟩
  have hsum := Loan.Reachable.pay_sum_le hreach hrange.2 l.vault pt amount l.now q hq
  rw [hls] at hsum
  have hsum' : q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat ≤ 300 * (10 ^ 16 + 1) := by
    have : (10 ^ 16 + 1 : ℚ) * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 + 1 := mul_le_of_le_one_right (by norm_num) hp1
    linarith

  -- YieldUnrealized follows interestDue
  obtain ⟨i', hi'⟩ := Loan.interestDue_ok q.loan
  have hi'N := RawLoan.interestDue_isNormalized q.loan i' hi'
  have hsiN := RawLoan.interestDue_isNormalized loan q.scheduledInterest hsi
  obtain ⟨hbT, hbP, hbM, -, -⟩ := Loan.payInstalments_below loan l.vault pt amount l.now q hq
  have hqT0 : 0 ≤ q.loan.totalValueOutstanding.toRat := q.loan.exact.totalValueOutstanding_nonneg
  have hqP0 : 0 ≤ q.loan.principalOutstanding.toRat := q.loan.exact.principalOutstanding_nonneg
  have hqM0 : 0 ≤ q.loan.managementFeeOutstanding.toRat := q.loan.exact.managementFeeOutstanding_nonneg
  have hi'l : |i'.toRat| < 10 ^ 20 := by
    rw [Loan.interestDue_toExact q.loan i' hi']
    show |q.loan.totalValueOutstanding.toRat - q.loan.principalOutstanding.toRat -
      q.loan.managementFeeOutstanding.toRat| < _
    rw [abs_lt]; constructor <;> linarith
  have hsil : |q.scheduledInterest.toRat| < 10 ^ 20 := by
    rw [Loan.interestDue_toExact loan _ hsi]
    show |loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat| < _
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨yd, hyd⟩ := Number.operator_sub_ok_of_abs i' q.scheduledInterest .to_nearest hi'N hsiN
    (by linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
  have hydN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hi'N hsiN hyd
  have hydl : |yd.toRat| < 10 ^ 22 := by
    have h1 := (Number.sub_near _ _ _ hi'N hsiN hyd).abs_le
    have h2 := abs_sub i'.toRat q.scheduledInterest.toRat
    have h3 : |i'.toRat - q.scheduledInterest.toRat| * (1 + ε) ≤ 2 * 10 ^ 20 * 2 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith

  -- the credit to the vault
  have hnt : q.loan.broker.numericType = q.pool.numericType := by rw [hqb, hntl, hntv]
  have hasset : Vault.HoldsAsset q.pool := by unfold Vault.HoldsAsset; rw [hntv]; exact hr.holdsAsset
  obtain ⟨gP, gI⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now q hrange hq
  have hsq : loan.loanScale = q.pool.baseExponent := by rw [hls, hbev]
  rw [hsq] at gP gI
  have hpq : (0 : ℚ) < 10 ^ q.pool.baseExponent := by rw [hbev]; exact hp10
  have hPI : q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat < 2 ^ 63 * 10 ^ q.pool.baseExponent := by
    have h1 := Loan.Reachable.pay_sum_le hreach hrange.2 l.vault pt amount l.now q hq
    rw [hsq] at h1
    have : (300 : ℚ) * (10 ^ 16 + 1) < 2 ^ 63 := by norm_num
    nlinarith
  obtain ⟨tp, htp⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hpN hiN
    (by rw [abs_of_nonneg hP0]; linarith [show (300 : ℚ) * (10 ^ 16 + 1) < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hI0]; linarith [show (300 : ℚ) * (10 ^ 16 + 1) < 10 ^ 200 by norm_num])
  have htpv : tp.toRat = q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat :=
    Number.OnGrid.add_exact gP gI hP0 hI0 hPI hs htp
  have htpN := Number.operator_add_isNormalized_to_nearest_sz _ _ _ hpN hiN htp
  have hAAN := q.pool.wf.assetsAvailable_norm
  have hAA0 : 0 ≤ q.pool.assetsAvailable.toRat := q.pool.exact.assetsAvailable_nonneg
  have hint0 : q.pool.numericType.isIntegral = true → q.pool.baseExponent = 0 := by
    intro h; unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos h]
  have hATfit : q.pool.numericType.isIntegral = true → q.pool.assetsAvailable.toRat +
      q.pool.assetsDeployed.toRat + q.amounts.interestPaid.toRat + 1 ≤ q.pool.numericType.maxValue.toNat := by
    intro hint
    rw [hntv] at hint ⊢
    rw [hAv, hADe]
    exact hfit loan q hat hq hint
  -- the principal paid is part of AssetsDeployed, so the cash after the credit is within the total
  obtain ⟨-, -, hpps⟩ : UnsettledPayment.PaidOn q loan.loanScale loan.principalOutstanding.toRat :=
    Loan.payInstalments_paidOn loan l.vault pt amount l.now q hrange hq
  have hLU0 : 0 ≤ q.pool.lossUnrealized.toRat := q.pool.exact.lossUnrealized_nonneg
  have hPAD : q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by linarith
  have hAAfit : q.pool.numericType.isIntegral = true → q.pool.assetsAvailable.toRat +
      q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤ q.pool.numericType.maxValue.toNat :=
    fun hint => by linarith [hATfit hint]
  have hAA88 : q.pool.numericType = .fractional → q.pool.assetsAvailable.toRat < 10 ^ 88 := by
    intro h
    rw [hAv]
    exact hAA (by rw [← hntv]; exact h)
  have hcredit : q.pool.numericType.CreditFits q.pool.assetsAvailable.toRat tp.toRat := by
    rcases hasset with h | h | h
    · exact Or.inl ⟨h, by
        rw [htpv]
        linarith [hAA88 h, show (10 : ℚ) ^ 88 + 300 * (10 ^ 16 + 1) < 10 ^ 89 by norm_num]⟩
    · refine Or.inr ⟨Or.inl h, ?_⟩
      have := hAAfit (by rw [h]; rfl)
      rw [htpv]; linarith
    · refine Or.inr ⟨Or.inr h, ?_⟩
      have := hAAfit (by rw [h]; rfl)
      rw [htpv]; linarith
  obtain ⟨st, toPool, hst', htoPool, htoN, htole, hAAm⟩ := sumRoundAndSubtract_credit_ok q.pool.assetsAvailable tp
    q.pool.baseExponent q.pool.numericType hAAN htpN hAA0 (by rw [htpv]; linarith) ⟨by omega, by omega⟩ hcredit
  rw [htpv] at htole

  -- the fee and the debt
  have hdebt : ∃ d : ℕ, d ≤ 10 ^ 16 ∧
      q.loan.broker.debtTotal.toRat = (d : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨d, hd, hdv⟩ := hr.loanAt_debt_units hat
    exact ⟨d, hd, by rw [hqb, hdv, hbev]⟩
  obtain ⟨toBroker, cover', hfeeF, hcovN, hcov0⟩ := UnsettledPayment.fee_of_fits q hasset hnt hdebt hfN hF0
    (by have := hfee loan q hat hq; rw [hntv, hqb]; exact this)
    (by rw [hqb]; linarith [show (10 : ℚ) ^ 96 < 10 ^ 150 by norm_num])
  obtain ⟨d, hd16, hdv⟩ := hdebt
  have hdtN := q.loan.broker.wf.debtTotal_norm
  have hdt0 : 0 ≤ q.loan.broker.debtTotal.toRat := q.loan.broker.exact.debtTotal_nonneg
  have hdt16 : q.loan.broker.debtTotal.toRat ≤ 10 ^ 16 := by
    rw [hdv]
    have h1 : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16
    have h2 : (10 : ℚ) ^ q.pool.baseExponent ≤ 1 := by rw [hbev]; exact hp1
    nlinarith
  obtain ⟨dt', hdt'⟩ := Number.operator_sub_ok_of_abs _ _ .to_nearest hdtN hpN
    (by rw [abs_of_nonneg hdt0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hP0]; linarith [show (300 : ℚ) * (10 ^ 16 + 1) < 10 ^ 200 by norm_num])
  have hsums : q.SettleSums toPool yd toBroker cover' dt' :=
    ⟨hparts, ⟨i', hi', hyd⟩, ⟨tp, st, htp, by rw [hnt]; exact hst', htoPool⟩, hfeeF, hdt'⟩

  -- the vault update computes
  have hgA : Number.OnGrid q.pool.baseExponent q.pool.assetsAvailable := by
    obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
    exact ⟨hAAN, a, by rw [hAv, hbev, ha]; norm_cast⟩
  have hgm : Number.OnGrid q.pool.baseExponent toPool :=
    sumRoundAndSubtract_onGrid _ _ _ _ _ st toPool hgA (by rw [hbev]; exact hbase) hint0 hst' htoPool
  have hAAl : q.pool.assetsAvailable.toRat < 10 ^ 97 :=
    STAmount.representable_lt _ _ hAAN hAA0 hArep
  have htol : |toPool.toRat| < 10 ^ 98 := by
    rw [abs_lt]; constructor <;> linarith [show (300 : ℚ) * (10 ^ 16 + 1) < 10 ^ 98 by norm_num]
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hAAN htoN
    (by rw [abs_of_nonneg hAA0]; linarith [show (10 : ℚ) ^ 97 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 98 < 10 ^ 200 by norm_num])
  have haaN := Number.operator_add_isNormalized_to_nearest_sz _ _ _ hAAN htoN haa
  have haa0 := Number.operator_add_nonneg _ _ _ hAAN htoN haa hAAm
  obtain ⟨aa', haa'⟩ : ∃ aa', STAmount.roundToNumericType q.pool.numericType aa .to_nearest = .ok aa' := by
    rcases hasset with h | h | h
    · rw [h]
      have hle := (Number.add_near _ _ _ hAAN htoN haa).le hAAm
      have h89 : q.pool.assetsAvailable.toRat + toPool.toRat < 10 ^ 89 := by
        linarith [hAA88 h, show (10 : ℚ) ^ 88 + 300 * (10 ^ 16 + 1) < 10 ^ 89 by norm_num]
      exact STAmount.roundToNumericType_frac_none_ok aa haaN haa0 (lt_of_le_of_lt hle (near_lt_pow _ h89))
    all_goals
      have hint : q.pool.numericType.isIntegral = true := by rw [h]; rfl
      have hfitI := hAAfit hint
      have hm : (q.pool.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by
        have : q.pool.numericType.maxValue.toNat ≤ 2 ^ 63 := by rw [h]; decide
        exact_mod_cast this
      have haav : aa.toRat = q.pool.assetsAvailable.toRat + toPool.toRat := by
        refine Number.OnGrid.add_toRat hgA hgm hs ?_ haa
        rw [hint0 hint, zpow_zero, mul_one, abs_of_nonneg hAAm]
        linarith
      refine STAmount.roundToNumericType_integral_ok _ aa .to_nearest none (by simp [h]) haaN haa0 ?_
      rw [haav]
      linarith
  obtain ⟨dp, hdp16, hdpv⟩ := hr.deployed_units
  have hAD0 : 0 ≤ q.pool.assetsDeployed.toRat := q.pool.exact.assetsDeployed_nonneg
  have hADl : q.pool.assetsDeployed.toRat ≤ 10 ^ 16 := by
    rw [hADe, hdpv]
    have h1 : (dp : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hdp16
    nlinarith
  obtain ⟨ad', had'⟩ := Number.operator_add_ok_of_abs q.pool.assetsDeployed q.amounts.principalPaid.operator_neg
    .to_nearest q.pool.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpN)
    (by rw [abs_of_nonneg hAD0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [Number.toRat_neg, abs_neg, abs_of_nonneg hP0]
        linarith [show (300 : ℚ) * (10 ^ 16 + 1) < 10 ^ 200 by norm_num])
  have hYU0 : 0 ≤ q.pool.yieldUnrealized.toRat := q.pool.exact.yieldUnrealized_nonneg
  have hYUl : q.pool.yieldUnrealized.toRat < 10 ^ 16 := by
    rw [hYUe]
    have h1 := hr.yield_lt
    have h2 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num) hp1
    linarith
  obtain ⟨yu', hyu'⟩ := Number.operator_add_ok_of_abs q.pool.yieldUnrealized yd .to_nearest
    q.pool.wf.yieldUnrealized_norm hydN
    (by rw [abs_of_nonneg hYU0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 22 < 10 ^ 200 by norm_num])
  have hadjS : Vault.AdjustSums q.pool (q.change toPool yd) aa' ad' q.pool.lossUnrealized q.pool.assetsReserved
      yu' :=
    ⟨⟨aa, haa, haa'⟩, had', Number.operator_add_zero_right _ _, Number.operator_add_zero_right _ _, hyu'⟩
  have hadj : ∃ r, (q.pool.adjustBalances (q.change toPool yd)).run = .ok r := by
    by_cases hbad : aa'.signum < 0 ∨ ad'.signum < 0 ∨ q.pool.lossUnrealized.signum < 0 ∨ yu'.signum < 0 ∨
        q.pool.assetsReserved.signum < 0
    · exact ⟨_, Vault.adjustBalances_bad_ledger _ _ _ _ _ _ _ hadjS hbad⟩
    have hnn' : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ q.pool.lossUnrealized.signum ∧ 0 ≤ yu'.signum ∧
        0 ≤ q.pool.assetsReserved.signum := by
      simp only [not_or, not_lt] at hbad
      exact hbad
    cases hgt : q.pool.lossUnrealized.operator_gt ad'
    · -- the new total is an amount of the asset, which C++ `syncAssetsTotal` stores
      have had'N := Number.operator_add_isNormalized_to_nearest_sz _ _ _ q.pool.wf.assetsDeployed_norm
        (Number.operator_neg_isNormalized _ hpN) had'
      have had'0 : 0 ≤ ad'.toRat := (Number.signum_nonneg_iff_toRat had'N).mp hnn'.2.1
      have hgD : Number.OnGrid q.pool.baseExponent q.pool.assetsDeployed :=
        ⟨q.pool.wf.assetsDeployed_norm, dp, by rw [hADe, hdpv, hbev]; norm_cast⟩
      have had'v : ad'.toRat = q.pool.assetsDeployed.toRat - q.amounts.principalPaid.toRat := by
        rw [Number.OnGrid.add_toRat hgD gP.neg hs ?_ had', Number.toRat_neg]
        · ring
        rw [Number.toRat_neg, abs_of_nonneg (by linarith)]
        have h1 : (dp : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hdp16
        have h2 : q.pool.assetsDeployed.toRat ≤ 10 ^ 16 * 10 ^ q.pool.baseExponent := by
          rw [hADe, hdpv, hbev]; exact mul_le_mul_of_nonneg_right h1 hp10.le
        have h3 : (10 : ℚ) ^ 16 * 10 ^ q.pool.baseExponent < 2 ^ 63 * 10 ^ q.pool.baseExponent :=
          mul_lt_mul_of_pos_right (by norm_num) hpq
        linarith
      have hst : XRPL.Model.SingleAssetVault.TotalStores q.pool.numericType aa' ad' := by
        refine XRPL.Model.SingleAssetVault.TotalStores.of_rounded_cash _ hasset aa aa' ad' haaN haa0 haa' had'N had'0
          (fun hint => ?_) (fun _ => by rw [had'v]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 80 by norm_num])
        have hfitI := hATfit hint
        have hm : (q.pool.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by
          have : q.pool.numericType.maxValue.toNat ≤ 2 ^ 63 := by rcases hasset with h | h | h <;> rw [h] <;> decide
          exact_mod_cast this
        have haav : aa.toRat = q.pool.assetsAvailable.toRat + toPool.toRat := by
          refine Number.OnGrid.add_toRat hgA hgm hs ?_ haa
          rw [hint0 hint, zpow_zero, mul_one, abs_of_nonneg hAAm]
          linarith
        rw [haav, had'v]
        linarith
      exact ⟨_, Vault.adjustBalances_ok _ _ _ _ _ _ _ hadjS hnn' hgt hst⟩
    · exact ⟨_, Vault.adjustBalances_limit_exceeded _ _ _ _ _ _ _ hadjS hnn' hgt⟩
  rw [Loan.pay_settle loan l.vault pt amount l.now q hq] at herr
  exact hsums.error_notLawful hadj e herr

end XRPL.Model.Lending
