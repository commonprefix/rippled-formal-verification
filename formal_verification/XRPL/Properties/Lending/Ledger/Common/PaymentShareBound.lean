import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # What a payment writes to AssetsAvailable and AssetsDeployed

The vault floors its credit for a payment at the scale of AssetsAvailable', so AssetsAvailable' falls short of
AssetsAvailable plus the payment by less than one unit of that scale. The principal leaves AssetsDeployed in full. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.unimpairIfImpaired_balances from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private Vault.total_of_raw from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private Loan.unimpairIfImpaired Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay

/-- What a payment writes to AssetsAvailable and AssetsDeployed. AssetsDeployed loses the principal exactly, and
AssetsAvailable' falls short of AssetsAvailable plus the payment by less than one unit of its scale. -/
lemma LendingLedger.pay_credit_floor (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (pt : LoanPaymentType) (amount : Number) (payment : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault)
    (hpay : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r))
    (hpaid : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hfit : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.pool'.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - payment.amounts.principalPaid.toRat ∧
      0 ≤ payment.amounts.interestPaid.toRat ∧
      ∀ e, numberExponent r.pool'.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
        l.vault.assetsAvailable.toRat +
          (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) -
            r.pool'.assetsAvailable.toRat < 10 ^ e := by
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, -, -⟩ := LendingLedger.base_grid_proof l hr hmax
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  obtain ⟨hblo, hbhi, hbint⟩ := l.vault.baseExponent_bounds
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid l.vault
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg

  obtain ⟨p, hp', hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  rw [hpay] at hp'
  have hpe : p = payment := (Except.ok.inj (Except.ok.inj hp')).symm
  subst hpe
  obtain ⟨-, hu', hst, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hpay
  obtain ⟨hpAA, hpAD, hpnt, hpbe⟩ := Loan.unimpairIfImpaired_balances loan l.vault p.pool loan.unimpaired
    (hr.storesAvailable hmax) hu'
  obtain ⟨toPool, yd, toBroker, cover', debt', raw, broker', hsums, hadj, hlaw, -, -, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  have hraw := (RawVault.to_lawful_ok hlaw).1
  have hAA' : r.pool'.assetsAvailable = raw.assetsAvailable := congrArg RawVault.assetsAvailable hraw
  have hAD' : r.pool'.assetsDeployed = raw.assetsDeployed := congrArg RawVault.assetsDeployed hraw
  rw [hAA', hAD']
  obtain ⟨hPg, hIg⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now p (by rw [hls]; omega) hpay
  rw [hls] at hPg hIg
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hparts
  obtain ⟨⟨hP0s, hI0s⟩, -⟩ := hparts
  have hP0 := Number.toRat_nonneg_of_not_signum_neg _ hPg.1 hP0s
  have hI0 := Number.toRat_nonneg_of_not_signum_neg _ hIg.1 hI0s
  obtain ⟨tot, credit, htot, hcred, hto⟩ := hsums.toPool
  rw [hpb, hnt, hpbe] at hcred
  obtain ⟨hsa, -⟩ := Vault.adjustBalances_ok_inv p.pool _ raw hadj
  obtain ⟨aa, haa, hround⟩ := hsa.cash
  have hdep := hsa.deployed
  have hpAAg : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable := by
    obtain ⟨k, hk⟩ := hAAg.2
    exact ⟨p.pool.wf.assetsAvailable_norm, k, by rw [hpAA, hk, hpbe]⟩
  have hpADg : Number.OnGrid p.pool.baseExponent p.pool.assetsDeployed := by
    obtain ⟨k, hk⟩ := hADg.2
    exact ⟨p.pool.wf.assetsDeployed_norm, k, by rw [hpAD, hk, hpbe]⟩
  rw [hpbe] at hpAAg hpADg
  -- the principal never exceeds AssetsDeployed, so taking it off is exact
  have hPAD : p.amounts.principalPaid.toRat ≤ l.vault.assetsDeployed.toRat := by
    by_contra hgt
    push Not at hgt
    obtain ⟨kD, hkD⟩ := hADg.2
    obtain ⟨kP, hkP⟩ := hPg.2
    have hlt : kD < kP := by
      have : (kD : ℚ) * 10 ^ l.vault.baseExponent < (kP : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [← hkD, ← hkP]; exact hgt
      exact_mod_cast lt_of_mul_lt_mul_right this hp.le
    obtain ⟨w, hw', hwv⟩ := Number.exists_normalized_int_mul_pow (-1) l.vault.baseExponent (by norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hR := operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsDeployed_norm
      (Number.operator_neg_isNormalized _ hPg.1) hdep
    have := Number.roundsToRepresentable_le _ _ hR w hw' (by
      rw [hwv, Number.toRat_neg, hpAD, hkD, hkP]
      have : ((kD - kP : ℤ) : ℚ) ≤ -1 := by exact_mod_cast (by omega : kD - kP ≤ -1)
      push_cast at this ⊢
      nlinarith)
    rw [hwv] at this
    push_cast at this
    have hrAD0 : 0 ≤ raw.assetsDeployed.toRat := by
      have := r.pool'.exact.assetsDeployed_nonneg
      rwa [show r.pool'.toExact.assetsDeployed = r.pool'.toRawVault.assetsDeployed.toRat from rfl, hraw] at this
    linarith
  have hT : 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ≤ 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    mul_le_mul_of_nonneg_right (by norm_num) hp.le
  have hADle : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := hr.lossInv.deployed
  have hPdeploy : raw.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - p.amounts.principalPaid.toRat := by
    have := Number.add_exact_of_grid hpADg hPg.neg (by rw [Number.toRat_neg, hpAD]; nlinarith)
      (by rw [Number.toRat_neg, hpAD]; linarith) hsr hdep
    rw [this, Number.toRat_neg, hpAD]; ring
  refine ⟨hPdeploy, hI0, fun e he => ?_⟩
  have hPI : tot.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
    Number.add_exact_of_grid hPg hIg (by nlinarith) (by linarith) hsr htot
  have htotn := operator_add_isNormalized_to_nearest_sz _ _ _ hPg.1 hIg.1 htot
  have htot0 : 0 ≤ tot.toRat := by rw [hPI]; linarith
  obtain ⟨kA, hkA⟩ := hpAAg.2
  obtain ⟨kP, hkP⟩ := hPg.2
  obtain ⟨kI, hkI⟩ := hIg.2
  have hKv : ((kA + (kP + kI) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent = l.vault.assetsAvailable.toRat +
      (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) := by
    rw [← hpAA, hkA, hkP, hkI]; push_cast; ring
  have hK : kA + (kP + kI) < 2 ^ 63 := by
    have : ((kA + (kP + kI) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [hKv]; push_cast; exact hfit
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have hK0 : 0 ≤ kA + (kP + kI) := by
    have : (0 : ℚ) ≤ ((kA + (kP + kI) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [hKv]; linarith
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (kA + (kP + kI)) l.vault.baseExponent ⟨by omega, hK⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hwsum : w.toRat = p.pool.assetsAvailable.toRat + tot.toRat := by
    rw [hwv, hPI, hkA, hkP, hkI]; push_cast; ring
  rw [hpnt] at hround
  rw [← hpAA, ← hPI]
  cases hint : l.vault.numericType.isIntegral
  · -- an IOU vault: the credit floors the sum at the scale of AssetsAvailable'
    have hfr := NumericType.eq_fractional_of_not_integral hint
    rw [hfr] at hcred hround he
    have hArep : STAmount.isRounded .fractional p.pool.assetsAvailable = false := by
      have hst := hr.storesAvailable hmax
      rw [hfr] at hst
      rw [STAmount.isRounded_eq_false_iff _ _ p.pool.wf.assetsAvailable_norm (by rw [hpAA]; exact hAA0), hpAA]
      exact (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm hAA0).mp hst
    have hkA0 : 0 ≤ kA := by
      have : (0 : ℚ) ≤ (kA : ℚ) * 10 ^ l.vault.baseExponent := by rw [← hkA, hpAA]; exact hAA0
      exact_mod_cast nonneg_of_mul_nonneg_left this hp
    obtain ⟨-, hfl⟩ := sumRoundAndSubtract_credit_floor p.pool.assetsAvailable tot l.vault.baseExponent credit toPool aa
      raw.assetsAvailable p.pool.wf.assetsAvailable_norm (by rw [hpAA]; exact hAA0) hArep
      ⟨kA.toNat, by rw [hkA]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hkA0).symm⟩ htotn htot0
      (by rw [hPI]; exact hpaid) ⟨hblo, hbhi⟩ ⟨w, hw, hwsum⟩ hcred hto haa hround
    exact hfl e he
  · -- an XRP or MPT vault: the credit is the whole sum, so nothing is lost
    have hb0 : l.vault.baseExponent = 0 := hbint hint
    unfold sumRoundAndSubtract at hcred
    rw [if_pos hint] at hcred
    obtain ⟨x, hx, hcred⟩ := bind_ok_peel _ _ _ hcred
    obtain rfl : x = credit := Except.ok.inj hcred
    have htneg := Number.negative_false_of_nonneg tot htotn htot0
    obtain ⟨iv, hiv, hxv⟩ := STAmount.ofNumber_integral_toRat _ tot _ x hint htneg hx
    obtain ⟨hfl1, hfl2⟩ := Number.to_rep_downward_floor tot iv htotn htneg hiv
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ x hint hx
    have hsmall : x.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, hsnv, -⟩ := STAmount.toNumber_integral_small_exact x .to_nearest hic hsmall
    rw [hsn, Except.ok.injEq] at hto
    subst hto
    have hcrn : sn.isNormalized := STAmount.toNumber_isNormalized x _ sn hsn
    rw [hb0, zpow_zero, mul_one] at hkP hkI hkA
    have htk : tot.toRat = ((kP + kI : ℤ) : ℚ) := by rw [hPI, hkP, hkI]; push_cast; ring
    have hcr : sn.toRat = tot.toRat := by
      rw [hsnv, hxv]
      rw [htk] at hfl1 hfl2 ⊢
      have h1 : iv.toInt ≤ kP + kI := by exact_mod_cast hfl1
      have h2 : kP + kI < iv.toInt + 1 := by exact_mod_cast hfl2
      have : iv.toInt = kP + kI := by omega
      rw [this]
    have haav := Number.operator_add_exact_of_fits p.pool.wf.assetsAvailable_norm hcrn haa
      ⟨w, hw, by rw [hwsum, hcr]⟩
    have haan := operator_add_isNormalized_to_nearest_sz _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa
    have haa0 : 0 ≤ aa.toRat := by rw [haav, hcr]; rw [hpAA]; linarith
    have hden : aa.toRat.den = 1 := by
      rw [haav, hcr, htk, hkA]
      rw [show (kA : ℚ) + ((kP + kI : ℤ) : ℚ) = ((kA + (kP + kI) : ℤ) : ℚ) by push_cast; ring]
      exact Rat.den_intCast _
    have hrep := STAmount.isRounded_eq_false_of_integral_round _ aa _ hint haan haa0 hden hround
    rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep hround, haav, hcr]
    simp only [sub_self]
    exact zpow_pos (by norm_num) _

end XRPL.Model.Lending
