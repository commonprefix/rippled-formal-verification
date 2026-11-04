import XRPL.Properties.Lending.Ledger.Common.LoanReplay
import XRPL.Properties.Lending.Loan.Common.PaySize
import XRPL.Properties.Lending.Ledger.Common.RecheckLoan
import XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-! # A LoanPay replayed on another reachable ledger

The payment computes the same instalments on the loan the second ledger stores, since the loan reads its broker
only through the asset and the management fee rate. While the vault is not coarsened the credit lands at the base
scale, so the settlement moves AssetsAvailable on the second ledger whenever it did on the first. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment validatePostPayment Loan.unimpairIfImpaired from XRPL.Model.Lending.Loan.LoanPay
open private LendingLedger.Reachable.loan_withBroker LendingLedger.principalSum_add_le_all
  from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private UnsettledPayment.PaidOn from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private sumRoundAndSubtract_zero from XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-- A settlement that passed moved AssetsAvailable or paid the loan off. -/
private lemma UnsettledPayment.settle_moved (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (h : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.pool'.assetsAvailable ≠ p.pool.assetsAvailable ∨ p.loan.paymentRemaining = 0 := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    rename_i hval
    simp only [validatePostPayment] at hval
    unfold_ter at hval
    walk_ok
    have hlaw := ‹RawLoan.to_lawful _ = Except.ok _›
    have hpr := congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok hlaw).1
    have hc := ‹¬((!_) && _) = true›
    simp only [Vault.pool_amounts] at hc
    by_cases h0 : p.loan.paymentRemaining = 0
    · exact Or.inr h0
    left
    intro heq
    apply hc
    simp only at heq hpr ⊢
    rw [Bool.and_eq_true]
    refine ⟨by rw [heq, (Number.operator_ne_false_iff_eq' _ _).mpr rfl]; rfl, ?_⟩
    show (_ != _) = true
    rw [show RawLoan.paymentRemaining _ = _ from hpr]
    simpa using h0

/-- The vault after the unimpair before a payment: AssetsAvailable keeps its value, the other balances but
LossUnrealized are as they were, and LossUnrealized has room next to the loan's principal. -/
private lemma LendingLedger.Reachable.unimpair_pool {L : LendingLedger} (hR : L.Reachable) {j : Nat} {loan : Loan}
    (hat : L.LoanAt j loan) {v1 : Vault}
    (hu : (Loan.unimpairIfImpaired loan L.vault).run = .ok (.ok { loan' := loan.unimpaired, pool' := v1 })) :
    v1.assetsAvailable.toRat = L.vault.assetsAvailable.toRat ∧ v1.assetsDeployed = L.vault.assetsDeployed ∧
      v1.assetsReserved = L.vault.assetsReserved ∧ v1.yieldUnrealized = L.vault.yieldUnrealized ∧
      v1.numericType = L.vault.numericType ∧ v1.baseExponent = L.vault.baseExponent ∧
      STAmount.isRounded v1.numericType v1.assetsAvailable = false ∧
      v1.lossUnrealized.toRat + loan.principalOutstanding.toRat ≤ v1.assetsDeployed.toRat := by
  obtain ⟨e, he, -, hraw⟩ := hat.stored
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hst := hR.availableStored
  have himpe : e.loan.isImpaired = loan.isImpaired := by
    rw [show loan.isImpaired = loan.toRawLoan.isImpaired from rfl, hraw]
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan L.vault himp] at hu
    obtain rfl : L.vault = v1 := by injection hu with hu; injection hu with hu; injection hu
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hst, ?_⟩
    rw [hpo, hR.lossInv.sum, hR.debtInv.deployed]
    exact LendingLedger.principalSum_add_le_all L (·.isImpaired) he
      (by show e.loan.isImpaired = false; rw [himpe, himp])
  · rw [Loan.unimpairIfImpaired_impaired loan L.vault himp] at hu
    split at hu
    · cases hu
    · cases hu
    rename_i v1' hadj
    obtain rfl : v1' = v1 := by injection hu with hu; injection hu with hu; injection hu
    obtain ⟨hs, hnt, hsc⟩ := Vault.poolAdjust_sums L.vault v1' _ hadj
    obtain ⟨aa, haa, hround⟩ := hs.cash
    rw [Number.operator_add_zero_right, Except.ok.injEq] at haa
    subst haa
    have hAv := STAmount.roundToNumericType_of_isRounded_false _ _ _ L.vault.wf.assetsAvailable_norm hst hround
    have hd := hs.deployed
    rw [Number.operator_add_zero_right, Except.ok.injEq] at hd
    have hres := hs.reserved
    rw [Number.operator_add_zero_right, Except.ok.injEq] at hres
    have hy := hs.yield
    rw [Number.operator_add_zero_right, Except.ok.injEq] at hy
    have hPN := loan.wf.principalOutstanding_norm
    have hnegN := Number.operator_neg_isNormalized _ hPN
    obtain ⟨w, hw, hwv⟩ := hR.unimpair_fits hat
    have hlv := Number.operator_add_exact_of_fits L.vault.wf.lossUnrealized_norm hnegN hs.loss
      ⟨w, hw, by rw [hwv, Number.toRat_neg]; ring⟩
    rw [Number.toRat_neg] at hlv
    have hLUAD : L.vault.lossUnrealized.toRat ≤ L.vault.assetsDeployed.toRat := L.vault.exact.lossUnrealized_le
    have hbe : v1'.baseExponent = L.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt, hsc]
    refine ⟨hAv, hd.symm, hres.symm, hy.symm, hnt, hbe, ?_, ?_⟩
    · have hA0 : 0 ≤ L.vault.assetsAvailable.toRat := L.vault.exact.assetsAvailable_nonneg
      rw [STAmount.isRounded_eq_false_iff _ _ v1'.wf.assetsAvailable_norm (by rw [hAv]; exact hA0), hAv, hnt]
      exact (STAmount.isRounded_eq_false_iff _ _ L.vault.wf.assetsAvailable_norm hA0).mp hst
    · rw [hlv, ← hd]; linarith

/-- The fee's settlement computes when the fee fits beside the cover: the owner takes it, or the cover takes it
floored onto the cover's grid and stays at least zero. -/
private lemma UnsettledPayment.fee_of_fits (p : UnsettledPayment Vault) (hasset : Vault.HoldsAsset p.pool)
    (hnt : p.loan.broker.numericType = p.pool.numericType)
    (hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ p.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ p.pool.baseExponent)
    (hfN : p.amounts.feePaid.isNormalized) (hF0 : 0 ≤ p.amounts.feePaid.toRat)
    (hfee : p.pool.numericType.CreditFits p.loan.broker.coverAvailable.toRat p.amounts.feePaid.toRat)
    (hCA : p.loan.broker.coverAvailable.toRat < 10 ^ 150) :
    ∃ toBroker cover',
      ((p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok true ∧ toBroker = p.amounts.feePaid ∧
          cover' = p.loan.broker.coverAvailable) ∨
        (p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok false ∧
          ∃ feeToCover, sumRoundAndSubtract p.loan.broker.coverAvailable p.amounts.feePaid
              p.pool.baseExponent p.loan.broker.numericType .downward = .ok feeToCover ∧
            feeToCover.toNumber .to_nearest = .ok toBroker ∧
            p.loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok cover')) ∧
      cover'.isNormalized ∧ 0 ≤ cover'.toRat := by
  have hbase := Vault.baseExponent_scale_range p.pool
  have hp10 : (0 : ℚ) < 10 ^ p.pool.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨t, ht16, htv⟩ := hdebt
  have hdtN := p.loan.broker.wf.debtTotal_norm
  have hdt0 : 0 ≤ p.loan.broker.debtTotal.toRat := p.loan.broker.exact.debtTotal_nonneg
  have hdtle : p.loan.broker.debtTotal.toRat ≤ 10 ^ 16 * 10 ^ p.pool.baseExponent := by
    rw [htv]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht16) hp10.le
  have hdtgrid : p.loan.broker.debtTotal.mantissa_ ≠ 0 → (10 : ℚ) ^ p.pool.baseExponent ≤
      p.loan.broker.debtTotal.toRat := by
    intro h0
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact h0 (by
        have : p.loan.broker.debtTotal.toRat = 0 := by rw [htv]; simp
        have := (Number.toRat_eq_zero_iff_eq_zero hdtN).mp this
        rw [this]; rfl)
    rw [htv]
    have : (1 : ℚ) ≤ t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht0
    nlinarith
  have hrate : p.loan.broker.coverRateMinimum.toNat ≤ 100000 := by
    have := p.loan.broker.valid.coverRateMinimum_cap
    unfold maxCoverRate at this
    exact UInt32.le_iff_toNat_le.mp this
  obtain ⟨mc, hmc⟩ := RawLoanBroker.hasMinimumCover_ok p.loan.broker.toRawLoanBroker p.pool.baseExponent
    (by show p.loan.broker.numericType = _ ∨ _; rw [hnt]; exact hasset) hdtN hdt0 hdtgrid hdtle
    ⟨by omega, hbase.2⟩ hrate
  have hCAN := p.loan.broker.wf.coverAvailable_norm
  have hCA0 : 0 ≤ p.loan.broker.coverAvailable.toRat := p.loan.broker.exact.coverAvailable_nonneg
  cases mc
  · obtain ⟨stc, tb, hstc, htb, htbN, htble, hcb0⟩ := sumRoundAndSubtract_credit_ok p.loan.broker.coverAvailable
      p.amounts.feePaid p.pool.baseExponent p.pool.numericType hCAN hfN hCA0 hF0 ⟨by omega, by omega⟩ hfee
    have hfl : p.amounts.feePaid.toRat < 10 ^ 150 := by
      rcases hfee with ⟨-, h⟩ | ⟨hn, h⟩
      · linarith [show (10 : ℚ) ^ 89 < 10 ^ 150 by norm_num]
      · have hm : p.pool.numericType.maxValue.toNat ≤ 2 ^ 63 := by rcases hn with h' | h' <;> rw [h'] <;> decide
        have : (p.pool.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
        linarith [show (2 : ℚ) ^ 63 < 10 ^ 150 by norm_num]
    have htbl : |tb.toRat| < 10 ^ 151 := by
      rw [abs_lt]; constructor <;> nlinarith [show (10 : ℚ) ^ 150 < 10 ^ 151 by norm_num]
    obtain ⟨cv, hcv⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hCAN htbN
      (by rw [abs_of_nonneg hCA0]; linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
      (by linarith [show (10 : ℚ) ^ 151 < 10 ^ 200 by norm_num])
    exact ⟨tb, cv, Or.inr ⟨hmc, stc, by rw [hnt]; exact hstc, htb, hcv⟩,
      operator_add_isNormalized_to_nearest_sz _ _ _ hCAN htbN hcv, operator_add_nonneg _ _ _ hCAN htbN hcv hcb0⟩
  · exact ⟨p.amounts.feePaid, p.loan.broker.coverAvailable, Or.inl ⟨hmc, rfl, rfl⟩, hCAN, hCA0⟩

/-- Twins pass the same payment checks. -/
private lemma Loan.Twin.canPay {l l' : Loan} (h : Loan.Twin l l') (pt : LoanPaymentType) :
    l'.canPay pt = l.canPay pt := by
  have hraw := h.raw
  unfold Loan.canPay
  rw [show l'.isPending = l.isPending from (congrArg RawLoan.isPending hraw :),
    show l'.allowsOverpayment = l.allowsOverpayment from (congrArg RawLoan.allowsOverpayment hraw :),
    show l'.paymentRemaining = l.paymentRemaining from (congrArg RawLoan.paymentRemaining hraw :),
    show l'.principalOutstanding = l.principalOutstanding from (congrArg RawLoan.principalOutstanding hraw :)]

/-- A LoanPay replays on a reachable ledger that keeps what it reads, while its vault is not coarsened, the
credit fits the asset, and the fee settles as on the first ledger or fits beside the cover. -/
lemma LendingLedger.pay_replay {l L lb : LendingLedger} (hr : l.Reachable) (hR : L.Reachable) {j : Nat}
    {e : LoanEntry} (hk : l.KeepsLoan L j e) (he : l.loan? j = some e) (pt : LoanPaymentType) (amount : Number)
    (hb : (l.apply (.loanPay j pt amount)).run = .ok (.ok lb))
    (htotal : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent)
    (hca : ∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hvfit : ∀ loan p, L.LoanAt j loan → (loan.payInstalments L.vault pt amount L.now).run = .ok (.ok p) →
      L.vault.numericType.isIntegral = true → L.vault.assetsAvailable.toRat + p.amounts.principalPaid.toRat +
        p.amounts.interestPaid.toRat + 1 ≤ L.vault.numericType.maxValue.toNat)
    (hfee : (∀ b, l.broker? e.brokerIndex = some b → L.broker? e.brokerIndex = some b) ∨
      ∀ loan p, L.LoanAt j loan → (loan.payInstalments L.vault pt amount L.now).run = .ok (.ok p) →
        L.vault.numericType.CreditFits loan.broker.coverAvailable.toRat p.amounts.feePaid.toRat) :
    ∃ L', (L.apply (.loanPay j pt amount)).run = .ok (.ok L') := by
  have hndL : L.vaultDeleted = false := by rw [hk.deleted]; exact LendingLedger.apply_loan_live rfl hb
  have hpre := (LendingLedger.apply_checked hb).1
  obtain ⟨u, hu, hlbu⟩ := LendingLedger.apply_loan rfl hb
  obtain ⟨e0, b, loan, r, he0, hb0, hw, hc, hok, hueq⟩ := LendingLedger.applyLoan_pay_inv l u j pt amount hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  have hset := hk.settings
  have hbe : L.vault.baseExponent = l.vault.baseExponent := hset.baseExponent_eq

  obtain ⟨b', hbL, hm⟩ := hk.broker b hb0
  have hntb : b.numericType = l.vault.numericType := hr.scaleInv.brokers _ b hb0
  have hntb' : b'.numericType = L.vault.numericType := hR.scaleInv.brokers _ b' hbL
  have hnte : e.loan.broker.numericType = l.vault.numericType := hr.scaleInv.loanBroker j e he
  obtain ⟨loanL, hwL⟩ := Loan.withBroker_ok e.loan b' (by rw [hntb', hset.numericType, hnte])
  have hatL : L.LoanAt j loanL := ⟨e, b', hk.loan, hbL, hwL⟩
  have hraw := Loan.withBroker_eq hw
  have hrawL := Loan.withBroker_eq hwL
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  have hlbL : loanL.broker = b' := by rw [show loanL.broker = loanL.toRawLoan.broker from rfl, hrawL]
  have htw : Loan.Twin loan loanL :=
    ⟨by rw [hrawL, hraw], by rw [hlbL, hlb, hntb', hset.numericType, hntb], by rw [hlbL, hlb, hm]⟩
  have hcL : loanL.canPay pt = .tesSUCCESS := by rw [htw.canPay]; exact hc

  obtain ⟨p, hpay, hsettle⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  obtain ⟨toPool, yd, toBroker, cover', dt', raw, broker', hsums, hadj, hv, hbr', hl', -, -⟩ :=
    UnsettledPayment.settle_ok p r hsettle
  have hmoved := UnsettledPayment.settle_moved p r hsettle

  obtain ⟨v1, hu1⟩ := Loan.unimpairIfImpaired_ok loanL L.vault (fun himp => hR.manageUnimpair_ok hatL himp)
  obtain ⟨q, hq, htwq, hqa, hqt, hqc, hqp, hqs⟩ := Loan.payInstalments_twin htw l.vault L.vault v1 pt amount l.now
    p (by simpa using hu1) hpay
  rw [← hk.now] at hq
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

  have hrawLe := hrawL
  have hpoL : loanL.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hrawL :)
  have hnpL : loanL.isPending = false := by
    unfold Loan.canPay at hcL
    cases h : loanL.isPending
    · rfl
    · rw [h] at hcL; simp at hcL
  have hnpe : e.loan.isPending = false := by
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
    have hex : loanL.toExact.interestDue = e.loan.toExact.interestDue := by
      show loanL.toRawLoan.totalValueOutstanding.toRat - loanL.toRawLoan.principalOutstanding.toRat -
        loanL.toRawLoan.managementFeeOutstanding.toRat = _
      rw [hrawL]; rfl
    rw [hex]; exact hR.interest_le_yield hk.loan hnpe
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

  have hnt : q.loan.broker.numericType = q.pool.numericType := by rw [hqb, hntb', hntv]
  have hasset : Vault.HoldsAsset q.pool := by unfold Vault.HoldsAsset; rw [hntv]; exact hR.holdsAsset
  have hAg : ∃ a : ℕ, q.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨a, ha⟩ := hR.assetsAvailable_units hR.holdsAsset
    exact ⟨a, by rw [hAv, hbev, ha]⟩
  have hA16 : q.pool.assetsAvailable.toRat < 10 ^ 16 * 10 ^ q.pool.baseExponent := by
    rw [hAv, hbev]; linarith
  have hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧
      q.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨t, ht, htv⟩ := hR.loanAt_debt_units hatL
    exact ⟨t, ht, by rw [hqb, ← hlbL, htv, hbev]⟩
  have hPDT : q.amounts.principalPaid.toRat ≤ q.loan.broker.debtTotal.toRat := by
    rw [hqb, ← hlbL]; linarith
  have hcount : q.loan.broker.loanCount ≠ 0 := by
    rw [hqb]
    have hc' := hR.loanCountInv.counted _ b' hbL
    have hpos := LendingLedger.loansOf_pos hk.loan
    intro h0
    rw [h0] at hc'
    simp at hc'
    omega
  have hdep : ∃ d : ℕ, d < 10 ^ 16 ∧ q.pool.assetsDeployed.toRat = (d : ℚ) * 10 ^ q.pool.baseExponent := by
    obtain ⟨d, -, hdv⟩ := hR.deployed_units
    refine ⟨d, ?_, by rw [hADe, hdv, hbev]⟩
    have : (d : ℚ) * 10 ^ L.vault.baseExponent < 10 ^ 16 * 10 ^ L.vault.baseExponent := by rw [← hdv]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  have hADpos : 0 < q.pool.assetsDeployed.toRat := by rw [hADe]; linarith
  have hLU : q.pool.lossUnrealized.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    linarith
  have hAR : q.pool.assetsReserved.toRat + q.amounts.principalPaid.toRat ≤ q.pool.assetsDeployed.toRat := by
    have hres : L.vault.assetsReserved.toRat + loanL.principalOutstanding.toRat ≤ L.vault.assetsDeployed.toRat := by
      rw [hpoL, hR.reservedInv.sum, hR.debtInv.deployed]
      exact LendingLedger.principalSum_add_le_all L (·.isPending) hk.loan hnpe
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

  have hfeeS : ∃ toBroker cover',
      ((q.loan.broker.hasMinimumCover q.pool.baseExponent = .ok true ∧ toBroker = q.amounts.feePaid ∧
          cover' = q.loan.broker.coverAvailable) ∨
        (q.loan.broker.hasMinimumCover q.pool.baseExponent = .ok false ∧
          ∃ feeToCover, sumRoundAndSubtract q.loan.broker.coverAvailable q.amounts.feePaid
              q.pool.baseExponent q.loan.broker.numericType .downward = .ok feeToCover ∧
            feeToCover.toNumber .to_nearest = .ok toBroker ∧
            q.loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok cover')) ∧
      cover'.isNormalized ∧ 0 ≤ cover'.toRat := by
    rcases hfee with hsame | hfits
    · have hbb := hsame b hb0
      rw [hbL] at hbb
      obtain rfl := Option.some.inj hbb
      have hqp' : q.loan.broker = p.loan.broker := by rw [hqb, hpb]
      have hqbe : q.pool.baseExponent = p.pool.baseExponent := by rw [hbev, hbevl, hbe]
      have hbr := (RawLoanBroker.to_lawful_ok hbr').1
      have hcv : broker'.coverAvailable = cover' := by
        rw [show broker'.coverAvailable = broker'.toRawLoanBroker.coverAvailable from rfl, hbr]
      refine ⟨toBroker, cover', ?_, by rw [← hcv]; exact broker'.wf.coverAvailable_norm,
        by rw [← hcv]; exact broker'.exact.coverAvailable_nonneg⟩
      rw [hqp', hqbe, hqa]
      exact hsums.fee
    · refine UnsettledPayment.fee_of_fits q hasset hnt hdebt hfN hF0 ?_ ?_
      · have := hfits loanL q hatL hq
        rw [hntv, hqb, ← hlbL]; exact this
      · rw [hqb]; linarith [hca b' hbL, show (10 : ℚ) ^ 96 < 10 ^ 150 by norm_num]
  obtain ⟨toBroker', cover'', hfeeF, hcovN, hcov0⟩ := hfeeS

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
      obtain ⟨aa', ad', lu', ar', yu', hs, -, -, hraw⟩ := Vault.adjustBalances_ok_parts p.pool _ raw hadj
      obtain ⟨aa, haa, hround⟩ := hs.cash
      simp only [UnsettledPayment.change, htoz, Number.operator_add_zero_right, Except.ok.injEq] at haa
      subst haa
      have hv1 := STAmount.roundToNumericType_of_isRounded_false _ _ _ p.pool.wf.assetsAvailable_norm hArepl hround
      have hrv := (RawVault.to_lawful_ok hv).1
      have hra : r.pool'.assetsAvailable = aa' := by
        rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl, hrv, hraw]
      rw [hra]
      exact Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround)
        p.pool.wf.assetsAvailable_norm hv1
    · exact Or.inl (by rw [hqpr]; exact h0)

  obtain ⟨r', hok'⟩ := Loan.pay_ok_of_room loanL L.vault pt amount L.now q hq hnt hasset hArep hAg hA16 gP gI hP0
    hI0 hPI hparts yd ⟨i', by rw [htwq.interestDue]; exact hi', hyd'⟩ hydN hyd0 hydl hYU toBroker' cover'' hfeeF
    hcovN hcov0 hdebt hPDT hcount hdep hADpos hLU hAR hAAfit hmove
  have hpreL : (LendingTx.loanPay j pt amount).preflight L = .tesSUCCESS := by
    have h1 : (LendingTx.loanPay j pt amount).preflight L = (LendingTx.loanPay j pt amount).preflight l := by
      simp only [LendingTx.preflight, hset.numericType]
    rw [h1]
    exact (TER.isTesSuccess_iff _).mp hpre
  refine ⟨L.commitLoan (LoanEffect.ofLoan j e r'.loan' r'.pool'), ?_⟩
  rw [LendingLedger.apply_of_preflight hpreL]
  simp only [LendingLedger.applyChecked, hndL, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, hk.loan, hbL, hwL]
  unfold_ter
  simp only [ExceptT.run] at hok'
  rw [hcL, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hok']
  rfl

end XRPL.Model.Lending
