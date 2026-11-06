import XRPL.Properties.Lending.Ledger.Common.PayReplay
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceDefs

/-! # A loan transaction replayed on a twin of the loan

A LoanDelete, LoanManage or LoanPay that succeeded on a stored loan succeeds as well on another reachable ledger
that stores a twin of the loan under another number: the same loan but for the copy of its broker. The second
ledger has the same close time and asset, a vault that exists and is not coarsened, and a broker of the same
management fee rate. The vault and broker balances may differ. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private LendingLedger.Reachable.available_principal_fits Loan.canManage_default_facts
  LendingLedger.unimpair_total from XRPL.Properties.Lending.Ledger.Common.LoanReplay
open private Loan.canManage_withBroker LendingLedger.principalSum_add_le_all
  from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private UnsettledPayment.settle_moved LendingLedger.Reachable.unimpair_pool UnsettledPayment.fee_of_fits
  Loan.Twin.canPay from XRPL.Properties.Lending.Ledger.Common.PayReplay
open private UnsettledPayment.PaidOn from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private sumRoundAndSubtract_zero from XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-- The management checks read the loan only, never its broker. -/
private lemma Loan.canManage_of_raw {loan loan' : Loan} {b : LoanBroker}
    (hraw : loan'.toRawLoan = { loan.toRawLoan with broker := b }) (action : LoanManageAction) (now : UInt32) :
    loan'.canManage action now = loan.canManage action now := by
  unfold Loan.canManage
  rw [hraw]

/-- A LoanDelete replays on a twin of the loan while the vault is not coarsened. -/
lemma LendingLedger.delete_replay_twin {l L lb : LendingLedger} (hR : L.Reachable) {j j' : Nat} {e e' : LoanEntry}
    (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hdel : L.vaultDeleted = false) (hb : (l.apply (.loanDelete j)).run = .ok (.ok lb))
    (htotal : L.NotCoarsened) :
    ∃ L', (L.apply (.loanDelete j')).run = .ok (.ok L') := by
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, -, hw, hc, -, -⟩ := LendingLedger.applyLoan_delete_inv l u j hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hrawl := Loan.withBroker_eq hw
  have hp : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hrawl :)
  have hp' : e'.loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
  have hpr : loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hrawl :)
  have hpr' : e'.loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
  cases hpend : e.loan.isPending
  · -- a closed loan: the check passed, so no payment is left
    have hrem : e.loan.paymentRemaining = 0 := by
      unfold Loan.canDelete at hc
      rw [hp, hpend, hpr] at hc
      by_contra h0
      have : e.loan.paymentRemaining > 0 := by
        rw [GT.gt, UInt32.lt_iff_toNat_lt]
        have := UInt32.toNat_inj.not.mpr h0
        simp at this ⊢
        omega
      simp [this] at hc
    exact LendingLedger.closed_loan_deletable L hR hdel j' e' he' (by rw [hpr', hrem]) (by rw [hp', hpend])
  · exact LendingLedger.pending_resolvable_proof L hR hR.holdsAsset.maxValue_le hdel j' e' he' (by rw [hp', hpend])
      (LendingLedger.Reachable.available_principal_fits hR he' htotal)

/-- A LoanManage replays on a twin of the loan while the vault is not coarsened. A default also needs a cover the
broker holds. -/
lemma LendingLedger.manage_replay_twin {l L lb : LendingLedger} (hR : L.Reachable) {j j' : Nat} {e e' : LoanEntry}
    (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hdel : L.vaultDeleted = false) (action : LoanManageAction)
    (hb : (l.apply (.loanManage j action)).run = .ok (.ok lb)) (htotal : L.NotCoarsened)
    (hca : ∀ b, L.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) :
    ∃ L', (L.apply (.loanManage j' action)).run = .ok (.ok L') := by
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, -, hw, hc, hok, -⟩ := LendingLedger.applyLoan_manage_inv l u j action hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hc' : e'.loan.canManage action L.now = .ok .tesSUCCESS := by
    rw [hnow, Loan.canManage_of_raw hraw, ← Loan.canManage_withBroker hw]; exact hc
  have hrawl := Loan.withBroker_eq hw
  cases action with
  | impair =>
    have hlate : e'.loan.nextPaymentDueDate < L.now := by
      have hnd' : e'.loan.nextPaymentDueDate = e.loan.nextPaymentDueDate :=
        (congrArg RawLoan.nextPaymentDueDate hraw :)
      rw [hnow, hnd']
      by_contra hl
      have hnd : loan.nextPaymentDueDate = e.loan.nextPaymentDueDate :=
        (congrArg RawLoan.nextPaymentDueDate hrawl :)
      have hlf : loan.isPaymentLate l.now = false := by
        unfold Loan.isPaymentLate; rw [hnd]; exact decide_eq_false hl
      simp only [Loan.manage, Loan.manageImpair, hlf] at hok
      unfold_ter at hok
      simp at hok
    exact LendingLedger.impair_total_proof L hR hdel hR.holdsAsset.maxValue_le j' e' he' hc' hlate
  | unimpair => exact LendingLedger.unimpair_total L hR hdel j' e' he' hc'
  | default =>
    obtain ⟨hp, hd, hrem, hlate⟩ := Loan.canManage_default_facts e'.loan L.now hc'
    exact LendingLedger.default_possible_proof L hR hdel hR.holdsAsset j' e' he' hp hd hrem hlate htotal
      (hR.assetsAvailable_units hR.holdsAsset) hR.yield_lt (hR.interest_le_yield he' hp) hca

/-- A LoanPay replays on a twin of the loan while the vault is not coarsened, the credit fits the asset, and the
fee fits beside the cover. -/
lemma LendingLedger.pay_replay_twin {l L lb : LendingLedger} (hr : l.Reachable) (hR : L.Reachable) {j j' : Nat}
    {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hdel : L.vaultDeleted = false) (hnt : L.vault.numericType = l.vault.numericType)
    (hbroker : ∀ b, l.broker? e.brokerIndex = some b →
      ∃ b', L.broker? e'.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate)
    (pt : LoanPaymentType) (amount : Number) (hb : (l.apply (.loanPay j pt amount)).run = .ok (.ok lb))
    (htotal : L.NotCoarsened) (hca : ∀ b, L.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hvfit : L.CreditFits j' pt amount) (hfee : L.FeeFits j' pt amount) :
    ∃ L', (L.apply (.loanPay j' pt amount)).run = .ok (.ok L') := by
  have hpre := (LendingLedger.apply_checked hb).1
  obtain ⟨u, hu, hlbu⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, hb0, hw, hc, hok, hueq⟩ := LendingLedger.applyLoan_pay_inv l u j pt amount hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0

  obtain ⟨b', hbL, hm⟩ := hbroker b hb0
  have hntb : b.numericType = l.vault.numericType := hr.scaleInv.brokers _ b hb0
  have hntb' : b'.numericType = L.vault.numericType := hR.scaleInv.brokers _ b' hbL
  obtain ⟨loanL, hwL⟩ := Loan.withBroker_ok e'.loan b' (by rw [hntb', hR.scaleInv.loanBroker j' e' he'])
  have hatL : L.LoanAt j' loanL := ⟨e', b', he', hbL, hwL⟩
  have hrawl := Loan.withBroker_eq hw
  have hrawL := Loan.withBroker_eq hwL
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hrawl]
  have hlbL : loanL.broker = b' := by rw [show loanL.broker = loanL.toRawLoan.broker from rfl, hrawL]
  have htw : Loan.Twin loan loanL :=
    ⟨by rw [hrawL, hraw, hrawl], by rw [hlbL, hlb, hntb', hnt, hntb], by rw [hlbL, hlb, hm]⟩
  have hcL : loanL.canPay pt = .tesSUCCESS := by rw [Loan.Twin.canPay htw]; exact hc

  obtain ⟨p, hpay, hsettle⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  obtain ⟨toPool, yd, toBroker, cover', dt', raw, broker', hsums, hadj, hv, hbr', hl', -, -⟩ :=
    UnsettledPayment.settle_ok p r hsettle
  have hmoved := UnsettledPayment.settle_moved p r hsettle

  obtain ⟨v1, hu1⟩ := Loan.unimpairIfImpaired_ok loanL L.vault (fun himp => hR.manageUnimpair_ok hatL himp)
  obtain ⟨q, hq, htwq, hqa, hqt, hqc, hqp, hqs⟩ := Loan.payInstalments_twin htw l.vault L.vault v1 pt amount l.now
    p (by simpa using hu1) hpay
  rw [← hnow] at hq
  obtain ⟨hchkL, huL, hstL, hsiL, -⟩ := Loan.payInstalments_ok loanL L.vault pt amount L.now q hq
  obtain ⟨hAv, hADe, hARe, hYUe, hntv, hbev, hArep, hLUroom⟩ := LendingLedger.Reachable.unimpair_pool hR hatL huL
  have hqb : q.loan.broker = b' := by rw [hstL.broker]; exact hlbL
  obtain ⟨hls, -⟩ := hR.loanAt_scale hatL
  have hbase := Vault.baseExponent_scale_range L.vault
  have hrange : -81 ≤ loanL.loanScale ∧ loanL.loanScale ≤ 0 := by rw [hls]; omega
  have hsq : loanL.loanScale = q.pool.baseExponent := by rw [hls, hbev]
  have hp10 : (0 : ℚ) < 10 ^ L.vault.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ L.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hAA0 : 0 ≤ L.vault.assetsAvailable.toRat := L.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ L.vault.assetsDeployed.toRat := L.vault.exact.assetsDeployed_nonneg

  obtain ⟨gP, gI⟩ := Loan.payInstalments_onGrid loanL L.vault pt amount L.now q hrange hq
  rw [hsq] at gP gI
  obtain ⟨hpN, hiN, hfN⟩ := Loan.payInstalments_norm loanL L.vault amount L.now pt q hq
  have hparts : (q.amounts.principalPaid.signum < 0 || q.amounts.interestPaid.signum < 0 ||
      q.amounts.feePaid.signum < 0) = false := by rw [hqa]; exact hsums.parts
  have hparts' := hparts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hparts'
  obtain ⟨⟨hpS, hiS⟩, hfS⟩ := hparts'
  have hP0 := Number.toRat_nonneg_of_not_signum_neg _ hpN hpS
  have hI0 := Number.toRat_nonneg_of_not_signum_neg _ hiN hiS
  have hF0 := Number.toRat_nonneg_of_not_signum_neg _ hfN hfS
  obtain ⟨t, -, hreachL⟩ := hR.loanAt_reachable hatL
  have hsum := Loan.Reachable.pay_sum_le hreachL hrange.2 L.vault pt amount L.now q hq
  rw [hls] at hsum
  have hPI : q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat < 2 ^ 62 * 10 ^ q.pool.baseExponent := by
    rw [hbev]
    have : (300 : ℚ) * (10 ^ 16 + 1) < 2 ^ 62 := by norm_num
    nlinarith
  obtain ⟨-, hpp0, hpps⟩ : UnsettledPayment.PaidOn q loanL.loanScale loanL.principalOutstanding.toRat :=
    Loan.payInstalments_paidOn loanL L.vault pt amount L.now q hrange hq
  have hqPO0 : 0 ≤ q.loan.principalOutstanding.toRat := q.loan.exact.principalOutstanding_nonneg
  have hppPO : q.amounts.principalPaid.toRat ≤ loanL.principalOutstanding.toRat := by linarith
  obtain ⟨-, -, -, hPOAD, hPODT⟩ := hR.loanAt_principal hatL

  have hpoL : loanL.principalOutstanding = e'.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hrawL :)
  have hnpL : loanL.isPending = false := by
    unfold Loan.canPay at hcL
    cases h : loanL.isPending
    · rfl
    · rw [h] at hcL; simp at hcL
  have hnpe : e'.loan.isPending = false := by
    rw [show loanL.isPending = loanL.toRawLoan.isPending from rfl, hrawL] at hnpL; exact hnpL
  have hPOpos : 0 < loanL.principalOutstanding.toRat := by
    have h0 : 0 ≤ loanL.principalOutstanding.toRat := loanL.exact.principalOutstanding_nonneg
    rcases eq_or_lt_of_le h0 with h | h
    · exact absurd ((Number.toRat_eq_zero_iff_eq_zero loanL.wf.principalOutstanding_norm).mp h.symm)
        hchkL.principal
    · exact h

  obtain ⟨i', hi', hyd'⟩ := hsums.yield
  have hiN := RawLoan.interestDue_isNormalized p.loan i' hi'
  have hsiN := RawLoan.interestDue_isNormalized loanL q.scheduledInterest hsiL
  rw [← hqs] at hyd'
  have hydN := operator_sub_isNormalized_to_nearest_sz _ _ _ hiN hsiN hyd'
  have hpls : p.loan.loanScale = loanL.loanScale := by
    rw [← (congrArg RawLoan.loanScale htwq.raw :), hstL.loanScale]; rfl
  have gi' : Number.OnGrid loanL.loanScale i' := hpls ▸ Loan.interestDue_onGrid p.loan i' hi'
  have gsi : Number.OnGrid loanL.loanScale q.scheduledInterest := Loan.interestDue_onGrid loanL _ hsiL
  -- the interest after the payment is at least zero: the paid loan is stored in a reachable ledger
  have hi'0 : 0 ≤ i'.toRat := by
    have hrb : lb.Reachable := hr.apply hb
    have hlbj : lb.loan? j = some { e with loan := r.loan' } := by
      rw [hlbu, LendingLedger.loan?_commitLoan, hueq]
      simp [LoanEffect.ofLoan, LendingLedger.loan?_lt he]
    obtain ⟨s, hls'⟩ := hrb.loansInv
    obtain ⟨t', -, hre⟩ := hls'.reachable j _ hlbj
    have := Loan.Reachable.interestDue_nonneg hre
    have hr' := (RawLoan.to_lawful_ok hl').1
    rw [Loan.interestDue_toExact p.loan i' hi']
    have hex : r.loan'.toExact.interestDue = p.loan.toExact.interestDue := by
      show r.loan'.toRawLoan.totalValueOutstanding.toRat - r.loan'.toRawLoan.principalOutstanding.toRat -
        r.loan'.toRawLoan.managementFeeOutstanding.toRat = _
      rw [hr']; rfl
    rw [← hex]; exact this
  have hsiYU : q.scheduledInterest.toRat ≤ L.vault.yieldUnrealized.toRat := by
    rw [Loan.interestDue_toExact loanL _ hsiL]
    have hex : loanL.toExact.interestDue = e'.loan.toExact.interestDue := by
      show loanL.toRawLoan.totalValueOutstanding.toRat - loanL.toRawLoan.principalOutstanding.toRat -
        loanL.toRawLoan.managementFeeOutstanding.toRat = _
      rw [hrawL]; rfl
    rw [hex]; exact hR.interest_le_yield he' hnpe
  have hsi0 : 0 ≤ q.scheduledInterest.toRat := by
    rw [Loan.interestDue_toExact loanL _ hsiL]; exact Loan.Reachable.interestDue_nonneg hreachL
  have hYUb := hR.yield_lt
  have hs81 : minExponent + 18 ≤ loanL.loanScale ∧ loanL.loanScale ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hpL : (0 : ℚ) < 10 ^ loanL.loanScale := zpow_pos (by norm_num) _
  have hpL1 : (10 : ℚ) ^ loanL.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hrange.2
  -- interestDue after the payment is at most TotalValueOutstanding, which only falls
  have hi'le : i'.toRat ≤ (10 ^ 16 + 1) * 10 ^ loanL.loanScale := by
    have hTL := Loan.Reachable.totalValue_le hreachL
    have hbelow := (Loan.payInstalments_below loanL L.vault pt amount L.now q hq).1
    have hqT : q.loan.totalValueOutstanding.toRat = p.loan.totalValueOutstanding.toRat :=
      congrArg (fun x => x.toRat) (congrArg RawLoan.totalValueOutstanding htwq.raw :)
    have hP' : 0 ≤ p.loan.principalOutstanding.toRat := p.loan.exact.principalOutstanding_nonneg
    have hM' : 0 ≤ p.loan.managementFeeOutstanding.toRat := p.loan.exact.managementFeeOutstanding_nonneg
    rw [Loan.interestDue_toExact p.loan i' hi']
    show p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
      p.loan.managementFeeOutstanding.toRat ≤ _
    rw [hls] at hTL ⊢
    linarith
  have hsile : q.scheduledInterest.toRat < 10 ^ 16 * 10 ^ loanL.loanScale := by rw [hls]; linarith
  have hydv : yd.toRat = i'.toRat - q.scheduledInterest.toRat :=
    Number.OnGrid.sub_toRat gi' gsi hs81 (by rw [abs_lt]; constructor <;> nlinarith) hyd'
  have hyd0 : 0 ≤ q.pool.yieldUnrealized.toRat + yd.toRat := by rw [hYUe, hydv]; linarith
  have hydl : |yd.toRat| < 10 ^ 150 := by
    rw [hydv, abs_lt]; constructor <;> nlinarith [show (10 : ℚ) ^ 17 < 10 ^ 150 by norm_num]
  have hYU : q.pool.yieldUnrealized.toRat < 10 ^ 150 := by
    rw [hYUe]
    have : (10 : ℚ) ^ 16 * 10 ^ L.vault.baseExponent ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num) hp1
    linarith [show (10 : ℚ) ^ 16 < 10 ^ 150 by norm_num]

  have hntq : q.loan.broker.numericType = q.pool.numericType := by rw [hqb, hntb', hntv]
  have hasset : Vault.HoldsAsset q.pool := by unfold Vault.HoldsAsset; rw [hntv]; exact hR.holdsAsset
  have hAg : ∃ a : ℕ, q.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨a, ha⟩ := hR.assetsAvailable_units hR.holdsAsset
    exact ⟨a, by rw [hAv, hbev, ha]⟩
  have hA16 : q.pool.assetsAvailable.toRat < 10 ^ 16 * 10 ^ q.pool.baseExponent := by
    rw [hAv, hbev]; unfold LendingLedger.NotCoarsened at htotal; linarith
  have hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧
      q.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨t, ht, htv⟩ := hR.loanAt_debt_units hatL
    exact ⟨t, ht, by rw [hqb, ← hlbL, htv, hbev]⟩
  have hPDT : q.amounts.principalPaid.toRat ≤ q.loan.broker.debtTotal.toRat := by
    rw [hqb, ← hlbL]; linarith
  have hcount : q.loan.broker.loanCount ≠ 0 := by
    rw [hqb]
    have hc' := hR.loanCountInv.counted _ b' hbL
    have hpos := LendingLedger.loansOf_pos he'
    intro h0
    rw [h0] at hc'
    simp at hc'
    omega
  have hdep : ∃ d : ℕ, d < 10 ^ 16 ∧ q.pool.assetsDeployed.toRat = (d : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨d, -, hdv⟩ := hR.deployed_units
    refine ⟨d, ?_, by rw [hADe, hdv, hbev]⟩
    have : (d : ℚ) * 10 ^ L.vault.baseExponent < 10 ^ 16 * 10 ^ L.vault.baseExponent := by
      rw [← hdv]; unfold LendingLedger.NotCoarsened at htotal; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  have hADpos : 0 < q.pool.assetsDeployed.toRat := by rw [hADe]; linarith
  have hLU : q.pool.lossUnrealized.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    linarith
  have hAR : q.pool.assetsReserved.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    have hres : L.vault.assetsReserved.toRat + loanL.principalOutstanding.toRat ≤ L.vault.assetsDeployed.toRat := by
      rw [hpoL, hR.reservedInv.sum, hR.debtInv.deployed]
      exact LendingLedger.principalSum_add_le_all L (·.isPending) he' hnpe
    rw [hARe, hADe]; linarith
  have hAAfit : q.pool.numericType.isIntegral = true → q.pool.assetsAvailable.toRat +
      q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤ q.pool.numericType.maxValue.toNat := by
    intro hint
    rw [hntv] at hint ⊢
    rw [hAv]
    exact hvfit loanL q hatL hq hint

  have hat : l.LoanAt j loan := ⟨e, b, he, hb0, hw⟩
  obtain ⟨-, hul, hstl, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hpay
  obtain ⟨hAvl, -, -, -, hntvl, hbevl, hArepl, -⟩ := LendingLedger.Reachable.unimpair_pool hr hat hul
  have hpb : p.loan.broker = b := by rw [hstl.broker]; exact hlb

  obtain ⟨toBroker', cover'', hfeeF, hcovN, hcov0⟩ := UnsettledPayment.fee_of_fits q hasset hntq hdebt hfN hF0
    (by have := hfee loanL q hatL hq; rw [hntv, hqb, ← hlbL]; exact this)
    (by rw [hqb]; linarith [hca b' hbL, show (10 : ℚ) ^ 96 < 10 ^ 150 by norm_num])

  have hmove : q.loan.paymentRemaining = 0 ∨ 0 < q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat := by
    have hqpr : q.loan.paymentRemaining = p.loan.paymentRemaining :=
      (congrArg RawLoan.paymentRemaining htwq.raw :)
    rcases hmoved with hne | h0
    · right
      by_contra hle
      push Not at hle
      have hp0 : p.amounts.principalPaid.toRat = 0 := by rw [← hqa]; linarith
      have hi0 : p.amounts.interestPaid.toRat = 0 := by rw [← hqa]; linarith
      apply hne
      obtain ⟨tp, cr, htp, hcr, hto⟩ := hsums.toPool
      have hpNp := (Loan.payInstalments_norm loan l.vault amount l.now pt p hpay).1
      have hiNp := (Loan.payInstalments_norm loan l.vault amount l.now pt p hpay).2.1
      have htpv := Number.operator_add_exact_of_fits hpNp hiNp htp
        ⟨Number.zero, Number.zero_isNormalized, by rw [hp0, hi0, Number.toRat_zero]; ring⟩
      have htpN := operator_add_isNormalized_to_nearest_sz _ _ _ hpNp hiNp htp
      have htpz : tp = Number.zero := (Number.toRat_eq_zero_iff_eq_zero htpN).mp (by rw [htpv, hp0, hi0]; ring)
      rw [htpz, hpb, hntb, ← hntvl] at hcr
      have hbl := Vault.baseExponent_scale_range p.pool
      obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
      have hcr0 := sumRoundAndSubtract_zero p.pool.assetsAvailable p.pool.baseExponent p.pool.numericType cr
        p.pool.wf.assetsAvailable_norm p.pool.exact.assetsAvailable_nonneg hArepl
        ⟨a, by rw [hAvl, hbevl, ha]⟩ ⟨by omega, by omega⟩ hcr
      obtain ⟨-, hcrx⟩ := sumRoundAndSubtract_downward_le _ _ _ _ cr p.pool.wf.assetsAvailable_norm
        p.pool.exact.assetsAvailable_nonneg Number.zero_isNormalized (by rw [Number.toRat_zero])
        ⟨by omega, by omega⟩ hcr
      obtain ⟨htov, htoN⟩ := hcrx toPool hto
      have htoz : toPool = Number.zero := (Number.toRat_eq_zero_iff_eq_zero htoN).mp (by rw [htov, hcr0])
      obtain ⟨aa', ad', lu', ar', yu', hs, -, -, hraw'⟩ := Vault.adjustBalances_ok_parts p.pool _ raw hadj
      obtain ⟨aa, haa, hround⟩ := hs.cash
      simp only [UnsettledPayment.change, htoz, Number.operator_add_zero_right, Except.ok.injEq] at haa
      subst haa
      have hv1 := STAmount.roundToNumericType_of_isRounded_false _ _ _ p.pool.wf.assetsAvailable_norm hArepl hround
      have hrv := (RawVault.to_lawful_ok hv).1
      have hra : r.pool'.assetsAvailable = aa' := by
        rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl, hrv, hraw']
      rw [hra]
      exact Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround)
        p.pool.wf.assetsAvailable_norm hv1
    · exact Or.inl (by rw [hqpr]; exact h0)

  obtain ⟨r', hok'⟩ := Loan.pay_ok_of_room loanL L.vault pt amount L.now q hq hntq hasset hArep hAg hA16 gP gI hP0
    hI0 hPI hparts yd ⟨i', by rw [htwq.interestDue]; exact hi', hyd'⟩ hydN hyd0 hydl hYU toBroker' cover'' hfeeF
    hcovN hcov0 hdebt hPDT hcount hdep hADpos hLU hAR hAAfit hmove
  have hpreL : (LendingTx.loanPay j' pt amount).preflight L = .tesSUCCESS := by
    have h1 : (LendingTx.loanPay j' pt amount).preflight L = (LendingTx.loanPay j pt amount).preflight l := by
      simp only [LendingTx.preflight, hnt]
    rw [h1]
    exact (TER.isTesSuccess_iff _).mp hpre
  refine ⟨L.commitLoan (LoanEffect.ofLoan j' e' r'.loan' r'.pool'), ?_⟩
  rw [LendingLedger.apply_of_preflight hpreL]
  simp only [LendingLedger.applyChecked, hdel, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he', hbL, hwL]
  unfold_ter
  simp only [ExceptT.run] at hok'
  rw [hcL, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hok']
  rfl

/-- A LoanDelete, LoanManage or LoanPay that succeeded on stored loan `j` succeeds on a twin of the loan stored at
`j'` on another reachable ledger, while the vault is not coarsened and the balances the model does not track fit. -/
lemma LendingLedger.loanTx_replay_twin_at {l L lb : LendingLedger} (hr : l.Reachable) (hR : L.Reachable)
    {j j' : Nat} {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hdel : L.vaultDeleted = false)
    (hnt : L.vault.numericType = l.vault.numericType)
    (hbroker : ∀ b, l.broker? e.brokerIndex = some b →
      ∃ b', L.broker? e'.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate)
    (tx : LendingTx) (htx : tx.loanIndex? = some j) (hacc : ∀ k, tx ≠ .loanAccept k)
    (hb : (l.apply tx).run = .ok (.ok lb))
    (htotal : L.NotCoarsened)
    (hca : ∀ b, L.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hfits : ∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) :
    ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L') := by
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx
  · exact absurd rfl (hacc _)
  · subst htx; exact LendingLedger.delete_replay_twin hR he he' hraw hdel hb htotal
  · subst htx; exact LendingLedger.manage_replay_twin hR he he' hraw hnow hdel _ hb htotal hca
  · subst htx
    exact LendingLedger.pay_replay_twin hr hR he he' hraw hnow hdel hnt hbroker _ _ hb htotal hca
      (hfits _ _ rfl).1 (hfits _ _ rfl).2

/-- The replay of a transaction on stored loan `j` on a twin of the loan on the same broker number. -/
lemma LendingLedger.loanTx_replay_twin {l L lb : LendingLedger} (hr : l.Reachable) (hR : L.Reachable)
    {j j' : Nat} {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hbi : e'.brokerIndex = e.brokerIndex)
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hdel : L.vaultDeleted = false)
    (hnt : L.vault.numericType = l.vault.numericType)
    (hbroker : ∀ b, l.broker? e.brokerIndex = some b →
      ∃ b', L.broker? e.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate)
    (tx : LendingTx) (htx : tx.loanIndex? = some j) (hacc : ∀ k, tx ≠ .loanAccept k)
    (hb : (l.apply tx).run = .ok (.ok lb))
    (htotal : L.NotCoarsened)
    (hca : ∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hfits : ∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) :
    ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L') :=
  LendingLedger.loanTx_replay_twin_at hr hR he he' hraw hnow hdel hnt (by rw [hbi]; exact hbroker) tx htx hacc hb
    htotal (by rw [hbi]; exact hca) hfits

end XRPL.Model.Lending
