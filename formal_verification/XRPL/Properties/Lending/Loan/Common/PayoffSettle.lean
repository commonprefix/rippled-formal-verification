import XRPL.Properties.Lending.Loan.Common.PayoffPay
import XRPL.Properties.Lending.Ledger.Common.VaultGrid
import XRPL.Properties.Lending.Ledger.Common.RecheckPool

/-! # The settlement of a payoff succeeds

A payoff leaves nothing owed, so it never trips the no-credit check. Its credits compute within range, the vault
gives up the principal and the interest it booked, and the vault, the broker and the loan pass their re-checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private LoanBroker.settle_lawful Loan.withBroker_lawful from XRPL.Properties.Lending.Loan.Common.RecheckPayLoan

/-- A nonnegative number below `10^90` rounds to an IOU amount at its own precision. -/
lemma STAmount.roundToNumericType_frac_none_ok (x : Number) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hlt : x.toRat < 10 ^ 90) : ∃ y, STAmount.roundToNumericType .fractional x .to_nearest = .ok y := by
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr x .to_nearest hx
    (by rw [abs_of_nonneg h0]; exact hlt)
  obtain ⟨y, hy, -, -⟩ := hretf.toNumber_ok .to_nearest
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  exact hy

/-- A paid-off loan owes no interest. -/
private lemma Loan.interestDue_paid_zero (l : Loan) (h : l.paymentRemaining = 0) : l.interestDue = .ok Number.zero := by
  obtain ⟨hT, hP, hM⟩ := l.valid.paid_zeroed h
  have hz : Number.zero.operator_sub Number.zero .to_nearest = .ok Number.zero := by
    unfold Number.operator_sub
    rw [Number.operator_neg_of_mantissa_zero _ rfl]
    exact Number.operator_add_zero_right _ _
  show (l.totalValueOutstanding.operator_sub l.principalOutstanding .to_nearest >>=
    fun x => x.operator_sub l.managementFeeOutstanding .to_nearest) = _
  rw [hT, hP, hM, hz, ok_bind, hz]

/-- A value below `10^89` stays below `10^90` after one rounding to nearest. -/
private lemma near_lt_pow (x : ℚ) (h : x < 10 ^ 89) : x * (1 + Number.nearestError) < 10 ^ 90 := by
  have hε' := Number.nearestError_le
  have h1 : 1 + Number.nearestError ≤ 2 := by
    have : (1 : ℚ) / 10 ^ 18 ≤ 1 := by norm_num
    linarith
  calc x * (1 + Number.nearestError) ≤ 10 ^ 89 * 2 := mul_le_mul h.le h1 (by linarith [Number.nearestError_pos])
        (by norm_num)
    _ < 10 ^ 90 := by norm_num

/-- A number rounded to an IOU, XRP or MPT amount at its own precision has an exponent far from the top. -/
private lemma STAmount.roundToNumericType_none_exp (nt : NumericType) (x y : Number)
    (hnt : nt = .fractional ∨ nt = .native ∨ nt = .int64)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.exponent_ + 22 ≤ maxExponent := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; cases hok
  | ok ret =>
    rw [hof] at hok
    simp only at hok
    rcases hnt with rfl | rfl | rfl
    · obtain ⟨n, hn, -, hne⟩ := (STAmount.ofNumber_fractional_fczr x .to_nearest ret hof).toNumber_ok .to_nearest
      rw [hn] at hok
      obtain rfl := Except.ok.inj hok
      exact hne
    all_goals
      obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical _ x .to_nearest ret rfl hof
      obtain ⟨n, hn, hnv, hnN, -⟩ := STAmount.toNumber_integral_exact ret .to_nearest hc (by rw [hrnt]; decide)
      rw [hn] at hok
      obtain rfl := Except.ok.inj hok
      have hm : ret.mValue.toNat ≤ 2 ^ 63 := le_trans hc.in_range (by rw [hrnt]; decide)
      have hl : |n.toRat| < 10 ^ 200 := by
        rw [hnv, STAmount.abs_toRat, hc.offset_zero, zpow_zero, mul_one]
        have : (ret.mValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
        linarith [show (2 : ℚ) ^ 63 < 10 ^ 200 by norm_num]
      have := Number.exponent_le_of_abs_lt_big n hnN hl
      unfold maxExponent
      omega

/-- The sums of a payoff's settlement compute. The vault's credit is at most the principal and interest paid,
the fee reaches the owner or the cover, and DebtTotal gives up the principal exactly. -/
lemma UnsettledPayment.payoff_settle_sums (p : UnsettledPayment Vault) (hpaid : p.loan.paymentRemaining = 0)
    (hnt : p.loan.broker.numericType = p.pool.numericType) (hasset : Vault.HoldsAsset p.pool)
    (hgA : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable)
    (hgP : Number.OnGrid p.pool.baseExponent p.amounts.principalPaid)
    (hgI : Number.OnGrid p.pool.baseExponent p.amounts.interestPaid)
    (hP0 : 0 < p.amounts.principalPaid.toRat) (hI0 : 0 ≤ p.amounts.interestPaid.toRat)
    (hPI : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 2 ^ 62 * 10 ^ p.pool.baseExponent)
    (hfN : p.amounts.feePaid.isNormalized) (hF0 : 0 ≤ p.amounts.feePaid.toRat)
    (hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ p.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ p.pool.baseExponent)
    (hPDT : p.amounts.principalPaid.toRat ≤ p.loan.broker.debtTotal.toRat)
    (hcredit : p.pool.numericType.CreditFits p.pool.assetsAvailable.toRat
      (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat))
    (hfee : p.pool.numericType.CreditFits p.loan.broker.coverAvailable.toRat p.amounts.feePaid.toRat)
    (hCA : p.loan.broker.coverAvailable.toRat < 10 ^ 150) :
    ∃ toPool toBroker cover' dt', p.SettleSums toPool p.scheduledInterest.operator_neg toBroker cover' dt' ∧
      toPool.isNormalized ∧ Number.OnGrid p.pool.baseExponent toPool ∧
      toPool.toRat ≤ p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∧
      0 ≤ p.pool.assetsAvailable.toRat + toPool.toRat ∧ cover'.isNormalized ∧ 0 ≤ cover'.toRat ∧
      dt'.isNormalized ∧ dt'.toRat = p.loan.broker.debtTotal.toRat - p.amounts.principalPaid.toRat := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  have hbase := Vault.baseExponent_scale_range p.pool
  have hs : minExponent + 18 ≤ p.pool.baseExponent ∧ p.pool.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ p.pool.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ p.pool.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hint0 : p.pool.numericType.isIntegral = true → p.pool.baseExponent = 0 := by
    intro h; unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos h]
  have hAA0 : 0 ≤ p.pool.assetsAvailable.toRat := p.pool.exact.assetsAvailable_nonneg
  have hAAN := p.pool.wf.assetsAvailable_norm
  obtain ⟨t, ht16, htv⟩ := hdebt
  have hPI' : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 10 ^ 20 := by
    have : (2 : ℚ) ^ 62 * 10 ^ p.pool.baseExponent ≤ 2 ^ 62 := mul_le_of_le_one_right (by norm_num) hp1
    linarith [show (2 : ℚ) ^ 62 < 10 ^ 20 by norm_num]
  obtain ⟨tp, htp⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hgP.1 hgI.1
    (by rw [abs_of_nonneg hP0.le]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hI0]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
  have htpv : tp.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
    Number.OnGrid.add_exact hgP hgI hP0.le hI0 (by nlinarith) hs htp
  have htpN := operator_add_isNormalized_to_nearest_sz _ _ _ hgP.1 hgI.1 htp
  obtain ⟨st, toPool, hst, htoPool, htoN, htole, hAAm⟩ := sumRoundAndSubtract_credit_ok p.pool.assetsAvailable tp
    p.pool.baseExponent p.pool.numericType hAAN htpN hAA0 (by rw [htpv]; linarith) ⟨by omega, by omega⟩
    (by rw [htpv]; exact hcredit)
  rw [htpv] at htole
  have hgm : Number.OnGrid p.pool.baseExponent toPool :=
    sumRoundAndSubtract_onGrid _ _ _ _ _ st toPool hgA hbase hint0 hst htoPool
  -- the minimum cover check
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
  -- the fee: to the owner, or to the cover
  have hCAN := p.loan.broker.wf.coverAvailable_norm
  have hCA0 : 0 ≤ p.loan.broker.coverAvailable.toRat := p.loan.broker.exact.coverAvailable_nonneg
  obtain ⟨toBroker, cover', hfeeS, hcovN, hcov0, hcovl⟩ : ∃ toBroker cover',
      ((p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok true ∧ toBroker = p.amounts.feePaid ∧
          cover' = p.loan.broker.coverAvailable) ∨
        (p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok false ∧
          ∃ feeToCover, sumRoundAndSubtract p.loan.broker.coverAvailable p.amounts.feePaid
              p.pool.baseExponent p.loan.broker.numericType .downward = .ok feeToCover ∧
            feeToCover.toNumber .to_nearest = .ok toBroker ∧
            p.loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok cover')) ∧
      cover'.isNormalized ∧ 0 ≤ cover'.toRat ∧ cover'.toRat < 10 ^ 160 := by
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
      have hcvN := operator_add_isNormalized_to_nearest_sz _ _ _ hCAN htbN hcv
      have hcv0 := operator_add_nonneg _ _ _ hCAN htbN hcv hcb0
      have hcvl : cv.toRat < 10 ^ 160 := by
        have := (Number.add_near _ _ _ hCAN htbN hcv).le hcb0
        have h1 : p.loan.broker.coverAvailable.toRat + tb.toRat ≤ 2 * 10 ^ 150 := by linarith
        nlinarith [show (2 : ℚ) * 10 ^ 150 * 2 < 10 ^ 160 by norm_num]
      exact ⟨tb, cv, Or.inr ⟨hmc, stc, by rw [hnt]; exact hstc, htb, hcv⟩, hcvN, hcv0, hcvl⟩
    · exact ⟨p.amounts.feePaid, p.loan.broker.coverAvailable, Or.inl ⟨hmc, rfl, rfl⟩, hCAN, hCA0,
        by linarith [show (10 : ℚ) ^ 150 < 10 ^ 160 by norm_num]⟩
  have hid := Loan.interestDue_paid_zero p.loan hpaid
  have hyd : Number.zero.operator_sub p.scheduledInterest .to_nearest = .ok p.scheduledInterest.operator_neg := by
    unfold Number.operator_sub; exact Number.operator_add_zero_left _ _
  have hgDT : Number.OnGrid p.pool.baseExponent p.loan.broker.debtTotal := ⟨hdtN, t, by rw [htv]; norm_cast⟩
  have hdt16 : p.loan.broker.debtTotal.toRat ≤ 10 ^ 16 := by
    refine le_trans hdtle ?_
    have := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℚ) ≤ 10 ^ 16)
    simpa using this
  obtain ⟨dt', hdt'⟩ := Number.operator_sub_ok_of_abs _ _ .to_nearest hdtN hgP.1
    (by rw [abs_of_nonneg hdt0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hP0.le]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
  have hsums : p.SettleSums toPool p.scheduledInterest.operator_neg toBroker cover' dt' := by
    refine ⟨?_, ⟨Number.zero, hid, hyd⟩, ⟨tp, st, htp, by rw [hnt]; exact hst, htoPool⟩, hfeeS, hdt'⟩
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
    exact ⟨⟨Number.signum_nonneg_of_toRat _ hgP.1 hP0.le, Number.signum_nonneg_of_toRat _ hgI.1 hI0⟩,
      Number.signum_nonneg_of_toRat _ hfN hF0⟩
  have hdt'N := operator_sub_isNormalized_to_nearest_sz _ _ _ hdtN hgP.1 hdt'
  have hdt63 : p.loan.broker.debtTotal.toRat < 2 ^ 63 * 10 ^ p.pool.baseExponent := by
    have : (10 : ℚ) ^ 16 * 10 ^ p.pool.baseExponent < 2 ^ 63 * 10 ^ p.pool.baseExponent :=
      mul_lt_mul_of_pos_right (by norm_num) hp10
    linarith
  have hdt'v := Number.OnGrid.sub_exact hgDT hgP hP0.le hPDT hdt63 hs hdt'
  exact ⟨toPool, toBroker, cover', dt', hsums, htoN, hgm, htole, hAAm, hcovN, hcov0, hdt'N, hdt'v⟩

/-- The vault update of a payoff succeeds and leaves a lawful vault. AssetsAvailable takes the credit,
AssetsDeployed gives up the principal and YieldUnrealized the interest the loan had booked. -/
lemma Vault.payoff_adjust (v : Vault) (hasset : Vault.HoldsAsset v) (toPool pp si : Number)
    (hgA : Number.OnGrid v.baseExponent v.assetsAvailable) (hAAl : v.assetsAvailable.toRat < 10 ^ 89)
    (htoN : toPool.isNormalized) (hgm : Number.OnGrid v.baseExponent toPool)
    (hAAm : 0 ≤ v.assetsAvailable.toRat + toPool.toRat) (htol : toPool.toRat < 10 ^ 20)
    (hfit : (v.numericType = .fractional ∧ v.assetsAvailable.toRat + toPool.toRat < 10 ^ 89) ∨
      (v.numericType.isIntegral = true ∧
        v.assetsAvailable.toRat + toPool.toRat + 1 ≤ v.numericType.maxValue.toNat))
    (hgP : Number.OnGrid v.baseExponent pp) (hP0 : 0 < pp.toRat)
    (hdep : ∃ d : ℕ, d ≤ 10 ^ 16 ∧ v.assetsDeployed.toRat = (d : ℚ) * 10 ^ v.baseExponent)
    (hLU : v.lossUnrealized.toRat + pp.toRat ≤ v.assetsDeployed.toRat)
    (hAR : v.assetsReserved.toRat + pp.toRat ≤ v.assetsDeployed.toRat)
    (hsiN : si.isNormalized) (hsiYU : si.toRat ≤ v.yieldUnrealized.toRat) (hsil : |si.toRat| < 10 ^ 150)
    (hYU : v.yieldUnrealized.toRat < 10 ^ 150) :
    ∃ raw v' at', (v.adjustBalances ⟨toPool, pp.operator_neg, si.operator_neg, Number.zero, Number.zero⟩).run =
      .ok (.ok raw) ∧ raw.to_lawful = .ok v' ∧ v'.assetsTotal = .ok at' := by
  have hbase := Vault.baseExponent_scale_range v
  have hs : minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hint0 : v.numericType.isIntegral = true → v.baseExponent = 0 := by
    intro h; unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos h]
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAN := v.wf.assetsAvailable_norm
  obtain ⟨d, hd16, hdv⟩ := hdep
  -- AssetsAvailable takes the credit
  have htol' : |toPool.toRat| < 10 ^ 150 := by
    rw [abs_lt]
    constructor <;> linarith [show (10 : ℚ) ^ 89 < 10 ^ 150 by norm_num, show (10 : ℚ) ^ 20 < 10 ^ 150 by norm_num]
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hAAN htoN
    (by rw [abs_of_nonneg hAA0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
  have haaN := operator_add_isNormalized_to_nearest_sz _ _ _ hAAN htoN haa
  have haa0 := operator_add_nonneg _ _ _ hAAN htoN haa hAAm
  obtain ⟨aa', haa'⟩ : ∃ aa', STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa' := by
    rcases hfit with ⟨h, h1⟩ | ⟨hint, h1⟩
    · rw [h]
      have := (Number.add_near _ _ _ hAAN htoN haa).le hAAm
      exact STAmount.roundToNumericType_frac_none_ok aa haaN haa0 (lt_of_le_of_lt this (near_lt_pow _ h1))
    · have hb0 := hint0 hint
      have hm : v.numericType.maxValue.toNat ≤ 2 ^ 63 := by
        rcases hasset with h | h | h <;> rw [h] <;> decide
      have hm' : (v.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
      have haav : aa.toRat = v.assetsAvailable.toRat + toPool.toRat := by
        refine Number.OnGrid.add_toRat hgA hgm hs ?_ haa
        rw [hb0, zpow_zero, mul_one, abs_of_nonneg hAAm]
        linarith
      have hnt : v.numericType = .native ∨ v.numericType = .int64 := by
        rcases hasset with h | h | h
        · rw [h] at hint; cases hint
        · exact Or.inl h
        · exact Or.inr h
      refine STAmount.roundToNumericType_integral_ok _ aa .to_nearest none hnt haaN haa0 ?_
      rw [haav]
      exact h1
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa'
  have haa'0 := STAmount.roundToNumericType_nonneg _ _ _ haaN haa0 haa'
  -- AssetsDeployed gives up the principal
  obtain ⟨-, k, hk⟩ := id hgP
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : (k : ℚ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    rw [hk] at hP0
    nlinarith
  have hLU0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  have hAR0 : 0 ≤ v.assetsReserved.toRat := v.exact.assetsReserved_nonneg
  have hkd : k ≤ d := by
    have h1 : (k : ℚ) * 10 ^ v.baseExponent ≤ (d : ℚ) * 10 ^ v.baseExponent := by
      rw [← hk, ← hdv]; linarith
    have := le_of_mul_le_mul_right h1 hp10
    exact_mod_cast this
  have hgD : Number.OnGrid v.baseExponent v.assetsDeployed := ⟨v.wf.assetsDeployed_norm, d, by rw [hdv]; norm_cast⟩
  have hAD16 : v.assetsDeployed.toRat ≤ 10 ^ 16 := by
    rw [hdv]
    have : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16
    have h2 : (d : ℚ) * 10 ^ v.baseExponent ≤ (d : ℚ) * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
    linarith
  obtain ⟨ad', had'⟩ := Number.operator_add_ok_of_abs v.assetsDeployed pp.operator_neg .to_nearest
    v.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hgP.1)
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [Number.toRat_neg, abs_neg, abs_of_nonneg hP0.le]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
  have had'N := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsDeployed_norm
    (Number.operator_neg_isNormalized _ hgP.1) had'
  have had'v : ad'.toRat = v.assetsDeployed.toRat - pp.toRat := by
    have h63 : |v.assetsDeployed.toRat + pp.operator_neg.toRat| < 2 ^ 63 * 10 ^ v.baseExponent := by
      rw [Number.toRat_neg, ← sub_eq_add_neg, abs_of_nonneg (by linarith), hdv]
      have : (d : ℚ) < 2 ^ 63 := by
        have : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16
        linarith [show (10 : ℚ) ^ 16 < 2 ^ 63 by norm_num]
      nlinarith
    have := Number.OnGrid.add_toRat hgD hgP.neg hs h63 had'
    rw [this, Number.toRat_neg]; ring
  have had'u : ad'.toRat = ((d - k.toNat : ℕ) : ℚ) * 10 ^ v.baseExponent := by
    rw [had'v, hdv, hk]
    have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hkd' : k.toNat ≤ d := by omega
    push_cast [Nat.cast_sub hkd']
    rw [show ((k.toNat : ℕ) : ℚ) = (k : ℚ) by exact_mod_cast hkn]
    ring
  -- YieldUnrealized gives up the interest
  have hYU0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  obtain ⟨yu', hyu'⟩ := Number.operator_add_ok_of_abs v.yieldUnrealized si.operator_neg .to_nearest
    v.wf.yieldUnrealized_norm (Number.operator_neg_isNormalized _ hsiN)
    (by rw [abs_of_nonneg hYU0]; linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
    (by rw [Number.toRat_neg, abs_neg]; linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
  have hyu'N := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.yieldUnrealized_norm
    (Number.operator_neg_isNormalized _ hsiN) hyu'
  have hyu'0 := operator_add_nonneg _ _ _ v.wf.yieldUnrealized_norm (Number.operator_neg_isNormalized _ hsiN) hyu'
    (by rw [Number.toRat_neg]; linarith)
  -- the update passes its checks, and the vault it writes is lawful
  have hsums : Vault.AdjustSums v ⟨toPool, pp.operator_neg, si.operator_neg, Number.zero, Number.zero⟩ aa' ad'
      v.lossUnrealized v.assetsReserved yu' :=
    ⟨⟨aa, haa, haa'⟩, had', Number.operator_add_zero_right _ _, Number.operator_add_zero_right _ _, hyu'⟩
  have hlule : v.lossUnrealized.toRat ≤ ad'.toRat := by rw [had'v]; linarith
  have harle : v.assetsReserved.toRat ≤ ad'.toRat := by rw [had'v]; linarith
  have hle : v.lossUnrealized.operator_gt ad' = false := by
    unfold Number.operator_gt
    exact (operator_lt_eq_false_iff _ _ had'N v.wf.lossUnrealized_norm).mpr hlule
  have had'0 : 0 ≤ ad'.toRat := le_trans hLU0 hlule
  have hadj := Vault.adjustBalances_ok v _ _ _ _ _ _ hsums
    ⟨Number.signum_nonneg_of_toRat _ haa'N haa'0, Number.signum_nonneg_of_toRat _ had'N had'0,
      Number.signum_nonneg_of_toRat _ v.wf.lossUnrealized_norm hLU0, Number.signum_nonneg_of_toRat _ hyu'N hyu'0,
      Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm hAR0⟩ hle
  obtain ⟨v', hv', hv'r⟩ := Vault.balances_lawful v aa' ad' v.assetsReserved v.lossUnrealized yu'
    ⟨haa'N, had'N, v.wf.assetsReserved_norm, v.wf.lossUnrealized_norm, hyu'N⟩
    ⟨haa'0, had'0, hAR0, hLU0, hyu'0⟩ hlule harle
    (hasset.isRounded_units ad' (d - k.toNat) had'N (by omega) had'u)
    (Vault.adjustBalances_cash_valid v _ _ hasset.maxValue_le hgm hadj haa'0).1
    (Vault.adjustBalances_cash_valid v _ _ hasset.maxValue_le hgm hadj haa'0).2 (by
      intro h0
      obtain ⟨-, hd0⟩ := v.valid.empty_shares h0
      exfalso
      have : v.assetsDeployed.toRat = 0 := by rw [hd0]; exact Number.toRat_zero
      linarith)
  have hat : ∃ at', v'.assetsTotal = .ok at' := by
    have hvt : v'.assetsTotal = aa'.operator_add ad' .downward := by
      show RawVault.assetsTotal v'.toRawVault = _
      rw [hv'r]
      rfl
    rw [hvt]
    have h1 := STAmount.roundToNumericType_none_exp v.numericType aa aa' hasset haa'
    have h2 := Number.exponent_le_of_abs_lt_big ad' had'N (by
      rw [abs_of_nonneg had'0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    exact Number.operator_add_ok_of_exp _ _ _ haa'N had'N h1 (by unfold maxExponent; omega)
  obtain ⟨at', hat'⟩ := hat
  exact ⟨_, v', at', hadj, hv', hat'⟩

/-- A payoff whose instalments passed settles, and the payment succeeds with a paid-off loan, when the broker and
the vault still carry the loan and the credits fit the asset. -/
lemma Loan.payoff_pay_ok (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hpay : (loan.payInstalments v pt amount now).run = .ok (.ok p))
    (hpaid : p.loan.paymentRemaining = 0)
    (hnt : p.loan.broker.numericType = p.pool.numericType) (hasset : Vault.HoldsAsset p.pool)
    (hgA : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable)
    (hgP : Number.OnGrid p.pool.baseExponent p.amounts.principalPaid)
    (hgI : Number.OnGrid p.pool.baseExponent p.amounts.interestPaid)
    (hP0 : 0 < p.amounts.principalPaid.toRat) (hI0 : 0 ≤ p.amounts.interestPaid.toRat)
    (hPI : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 2 ^ 62 * 10 ^ p.pool.baseExponent)
    (hfN : p.amounts.feePaid.isNormalized) (hF0 : 0 ≤ p.amounts.feePaid.toRat)
    (hsiN : p.scheduledInterest.isNormalized) (hsiYU : p.scheduledInterest.toRat ≤ p.pool.yieldUnrealized.toRat)
    (hsil : |p.scheduledInterest.toRat| < 10 ^ 150)
    (hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ p.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ p.pool.baseExponent)
    (hPDT : p.amounts.principalPaid.toRat ≤ p.loan.broker.debtTotal.toRat) (hcount : p.loan.broker.loanCount ≠ 0)
    (hdep : ∃ d : ℕ, d ≤ 10 ^ 16 ∧ p.pool.assetsDeployed.toRat = (d : ℚ) * 10 ^ p.pool.baseExponent)
    (hLU : p.pool.lossUnrealized.toRat + p.amounts.principalPaid.toRat ≤ p.pool.assetsDeployed.toRat)
    (hAR : p.pool.assetsReserved.toRat + p.amounts.principalPaid.toRat ≤ p.pool.assetsDeployed.toRat)
    (hcredit : p.pool.numericType.CreditFits p.pool.assetsAvailable.toRat
      (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat))
    (hAAfit : p.pool.numericType.isIntegral = true → p.pool.assetsAvailable.toRat + p.amounts.principalPaid.toRat +
      p.amounts.interestPaid.toRat + 1 ≤ p.pool.numericType.maxValue.toNat)
    (hfee : p.pool.numericType.CreditFits p.loan.broker.coverAvailable.toRat p.amounts.feePaid.toRat)
    (hCA : p.loan.broker.coverAvailable.toRat < 10 ^ 150) (hYU : p.pool.yieldUnrealized.toRat < 10 ^ 150) :
    ∃ r, (loan.pay v pt amount now).run = .ok (.ok r) ∧ r.loan'.paymentRemaining = 0 := by
  obtain ⟨toPool, toBroker, cover', dt', hsums, htoN, hgm, htole, hAAm, hcovN, hcov0, -, -⟩ :=
    UnsettledPayment.payoff_settle_sums p hpaid hnt hasset hgA hgP hgI hP0 hI0 hPI hfN hF0 hdebt hPDT hcredit
      hfee hCA
  have hbase := Vault.baseExponent_scale_range p.pool
  have hp1 : (10 : ℚ) ^ p.pool.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hPI' : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 10 ^ 20 := by
    have : (2 : ℚ) ^ 62 * 10 ^ p.pool.baseExponent ≤ 2 ^ 62 := mul_le_of_le_one_right (by norm_num) hp1
    linarith [show (2 : ℚ) ^ 62 < 10 ^ 20 by norm_num]
  have hAAl : p.pool.assetsAvailable.toRat < 10 ^ 89 := by
    rcases hcredit with ⟨-, h⟩ | ⟨hn, -⟩
    · linarith
    · have hint : p.pool.numericType.isIntegral = true := by rcases hn with h' | h' <;> rw [h'] <;> rfl
      have h := hAAfit hint
      have hm : p.pool.numericType.maxValue.toNat ≤ 2 ^ 63 := by rcases hn with h' | h' <;> rw [h'] <;> decide
      have : (p.pool.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
      linarith [show (2 : ℚ) ^ 63 < 10 ^ 89 by norm_num]
  have hfit : (p.pool.numericType = .fractional ∧ p.pool.assetsAvailable.toRat + toPool.toRat < 10 ^ 89) ∨
      (p.pool.numericType.isIntegral = true ∧
        p.pool.assetsAvailable.toRat + toPool.toRat + 1 ≤ p.pool.numericType.maxValue.toNat) := by
    rcases hcredit with ⟨h, h1⟩ | ⟨hn, -⟩
    · exact Or.inl ⟨h, by linarith⟩
    · have hint : p.pool.numericType.isIntegral = true := by rcases hn with h' | h' <;> rw [h'] <;> rfl
      exact Or.inr ⟨hint, by linarith [hAAfit hint]⟩
  obtain ⟨raw, v', at', hadj, hv', hat⟩ := Vault.payoff_adjust p.pool hasset toPool p.amounts.principalPaid
    p.scheduledInterest hgA hAAl htoN hgm hAAm (by linarith) hfit hgP hP0 hdep hLU hAR hsiN hsiYU hsil hYU
  obtain ⟨broker', hb'⟩ := LoanBroker.settle_lawful p.loan.broker p.amounts.principalPaid dt' cover' hgP.1
    hP0.le hPDT hcount hsums.debt hcovN hcov0
  have hbnt : broker'.numericType = p.loan.broker.numericType :=
    (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok hb').1 :)
  obtain ⟨loan', hl'⟩ := Loan.withBroker_lawful p.loan broker' hbnt
  have hpr' : loan'.paymentRemaining = 0 := by
    rw [show loan'.paymentRemaining = loan'.toRawLoan.paymentRemaining from rfl, (RawLoan.to_lawful_ok hl').1]
    exact hpaid
  exact ⟨_, Loan.payment_success_proof loan v amount now pt p toPool _ toBroker cover' dt' raw v' broker' loan' at'
    hpay hsums hadj hv' hb' hl' hat (Or.inr hpaid), hpr'⟩

end XRPL.Model.Lending
