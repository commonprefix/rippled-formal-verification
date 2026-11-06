import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Loan.Common.PayBounds
import XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
import XRPL.Properties.Lending.Loan.Common.CreatedSize

/-! # A payment on a reachable ledger passes its re-checks

LoanPay builds the loan again after each instalment, re-checks the broker and the vault after settling, and
re-checks the vault and the loan in the unimpair before it pays. On a reachable ledger none of these re-checks
fails: the loan keeps its interest at least zero, its principal is within DebtTotal and AssetsDeployed, and the
vault keeps AssetsDeployed a whole number of base units below `10^16` of them. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments
  Loan.doPayment Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private UnsettledPayment.PaidOn from XRPL.Properties.Lending.Loan.Common.PayPrincipal
open private LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private STAmount.roundToNumericType_frac_canon from XRPL.Properties.Lending.Loan.Common.PayBounds
open private Loan.payInstalments_below from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- The unimpair before a payment keeps the vault's AssetsDeployed, AssetsReserved, SharesTotal, asset and
scale. -/
private lemma Loan.unimpairIfImpaired_pool (loan : Loan) (v v1 : Vault) (l1 : Loan)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := l1, pool' := v1 })) :
    v1.assetsDeployed = v.assetsDeployed ∧ v1.assetsReserved = v.assetsReserved ∧ v1.sharesTotal = v.sharesTotal ∧
      v1.numericType = v.numericType ∧ v1.scale = v.scale := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h
    obtain rfl : v = v1 := by injection h with h; injection h with h; injection h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    split at h
    · cases h
    · cases h
    · rename_i v2 hadj
      obtain rfl : v2 = v1 := by injection h with h; injection h with h; injection h
      obtain ⟨raw, hraw, hv'⟩ := Vault.poolAdjust_ok_inv v _ v2 hadj
      obtain ⟨-, heq⟩ := Vault.adjustBalances_ok_inv v _ raw hraw
      have h1 := (RawVault.to_lawful_ok hv').1
      refine ⟨Vault.poolAdjust_deployed_zero v v2 _ rfl hadj, Vault.poolAdjust_reserved_zero v v2 _ rfl hadj,
        ?_, ?_, ?_⟩
      · show v2.toRawVault.sharesTotal = _; rw [h1, heq]
      · show v2.toRawVault.numericType = _; rw [h1, heq]
      · show v2.toRawVault.scale = _; rw [h1, heq]

/-- An IOU amount the asset stores, or zero, is below `10^96`. -/
private lemma STAmount.FracCanonZero.lt_pow {a : STAmount} (h : a.FracCanonZero) : a.toRat < 10 ^ 96 := by
  rw [STAmount.toRat_signed]
  rcases h.2 with hc | hz
  · have hm : (a.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
    have he : (10 : ℚ) ^ a.mOffset ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hc.exp_hi
    have hp : (0 : ℚ) < 10 ^ a.mOffset := zpow_pos (by norm_num) _
    have h80 : (10 : ℚ) ^ (80 : ℤ) = 10 ^ 80 := by norm_num
    rw [h80] at he
    have h0 : 0 ≤ (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := by positivity
    have hb : (a.mValue.toNat : ℚ) * 10 ^ a.mOffset < 10 ^ 16 * 10 ^ 80 :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hm hp) (mul_le_mul_of_nonneg_left he (by norm_num))
    split
    · nlinarith
    · nlinarith
  · rw [hz]; simp

/-- A fee that joins a cover below its minimum leaves the cover at least zero. The minimum is an amount the asset
stores, so the credit floored onto the grid of the new cover never takes the cover below zero. -/
lemma LoanBroker.feeCover_nonneg (b : LoanBroker) (e : Int) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80) (fee : Number)
    (st : STAmount) (toBroker : Number) (hfn : fee.isNormalized) (hf0 : 0 ≤ fee.toRat)
    (hmin : b.hasMinimumCover e = .ok false)
    (hsr : sumRoundAndSubtract b.coverAvailable fee e b.numericType .downward = .ok st)
    (htb : st.toNumber .to_nearest = .ok toBroker) :
    0 ≤ b.coverAvailable.toRat + toBroker.toRat := by
  refine sumRoundAndSubtract_downward_cover_nonneg _ _ _ _ _ _ b.wf.coverAvailable_norm b.exact.coverAvailable_nonneg
    ?_ hfn hf0 he hsr htb
  intro hfr
  unfold RawLoanBroker.hasMinimumCover minimumBrokerCover at hmin
  obtain ⟨mc, hmc, hmin⟩ := bind_ok_peel _ _ _ hmin
  obtain ⟨x, -, hx⟩ := bind_ok_peel _ _ _ hmc
  rw [hfr] at hx
  obtain ⟨a, ha, hav⟩ := STAmount.roundToNumericType_frac_canon _ _ _ _ hx
  have hle : mc.operator_le b.coverAvailable = false := by
    simpa [pure, Except.pure] using hmin
  have hmcn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hx
  have hlt : b.coverAvailable.toRat < mc.toRat := by
    by_contra hc
    push Not at hc
    rw [(operator_le_iff _ _ hmcn b.wf.coverAvailable_norm).mpr hc] at hle
    cases hle
  have := STAmount.FracCanonZero.lt_pow ha
  rw [hav] at this
  linarith

/-- A payment on an active loan a reachable ledger stores never fails a re-check. -/
lemma LendingLedger.Reachable.pay_ne_notLawful_at {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (hnp : loan.isPending = false) (pt : LoanPaymentType) (amount : Number) :
    (loan.pay l.vault pt amount l.now).run ≠ .error .notLawful := by
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  -- the loan is reachable, so its interest is at least zero
  obtain ⟨s, hli⟩ := hr.loansInv
  obtain ⟨t, -, hre⟩ := hli.reachable i e he
  have hre' := hre.withBroker (hr.scaleInv.broker_asset he hb) hw
  have hshape : loan.PayShape := ⟨by rw [hls]; omega, fun _ => by rw [hls]; exact hbase.2,
    Loan.Reachable.interestDue_nonneg hre'⟩
  have hsc : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := ⟨hshape.1, by rw [hls]; exact hbase.2⟩
  -- a reachable loan owes at most what its LoanSet allowed
  have hTV : loan.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ loan.loanScale := by
    obtain ⟨start, t₀, hc, hrf⟩ := hre'
    rw [(Loan.ReachableFrom.keepsTerms hrf).loanScale]
    exact le_trans (Loan.ReachableFrom.outstanding_monotone_proof hrf).totalValueOutstanding
      (Loan.Created.totalValue_le hc)
  apply Loan.pay_ne_notLawful_of
  · refine Loan.payInstalments_ne_notLawful loan l.vault pt amount l.now hshape
      (Loan.unimpairIfImpaired_ne_notLawful loan l.vault hr.availableStored) ?_
    rintro rfl p0 hp0
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now p0 hp0
    have hi0 := Loan.payInstalments_interestDue loan l.vault .regular amount l.now p0 (by decide) hshape.1 hshape.2
      hshape.3 hp0
    refine UnsettledPayment.applyOverpayment_ne_notLawful p0 amount
      ⟨by rw [hst.loanScale]; exact hshape.1, by rw [hst.loanScale, hst.broker]; exact hshape.2, hi0⟩ ?_
    -- an XRP or MPT loan counts whole units and its instalments only lowered what it owes
    intro hpi
    have hpb : p0.loan.broker = loan.broker := hst.broker
    have hpl : p0.loan.loanScale = loan.loanScale := hst.loanScale
    rw [hpb, hnt] at hpi
    obtain ⟨hTp, -⟩ := Loan.payInstalments_below loan l.vault .regular amount l.now p0 hp0
    refine ⟨by rw [hpb, hnt]; exact hr.holdsAsset.maxValue_le hpi,
      by rw [hpl, hls]; exact Vault.baseExponent_integral _ hpi, ?_⟩
    rw [hpl]
    exact le_trans hTp hTV
  · intro p hp
    obtain ⟨hchecks, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hp
    obtain ⟨gpp, hpp0, hpps⟩ := Loan.payInstalments_paidOn loan l.vault pt amount l.now p hsc hp
    have hpb : p.loan.broker = loan.broker := hst.broker
    obtain ⟨-, -, -, hpoAD, hpoDT⟩ := hr.loanAt_principal hat
    have hP0 : 0 ≤ p.loan.principalOutstanding.toRat := p.loan.exact.principalOutstanding_nonneg
    have hppPO : p.amounts.principalPaid.toRat ≤ loan.principalOutstanding.toRat := by linarith
    obtain ⟨hpAD, hpAR, hpS, hpnt, hpsc⟩ := Loan.unimpairIfImpaired_pool loan l.vault p.pool _ hu
    have hpbe : p.pool.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hpnt, hpsc]
    refine Loan.settle_ne_notLawful p ⟨gpp.1, hpp0, by rw [hpb]; linarith⟩
      (RawLoan.interestDue_isNormalized loan _ hsi) ?_ ?_ ?_ (by rw [hpb, hnt, hpnt])
      (by rw [hpnt]; exact hr.holdsAsset.maxValue_le)
    · -- the broker counts the loan
      rw [hpb, hlb]
      have hc := hr.loanCountInv.counted _ b hb
      have hpos := LendingLedger.loansOf_pos he
      intro h0
      rw [h0] at hc
      simp at hc
      omega
    · -- a fee that joins the cover leaves it at least zero
      intro st toBroker hfs hmin hsr htb
      have hfn := (Loan.payInstalments_norm loan l.vault amount l.now pt p hp).2.2
      have hf0 := (Number.signum_nonneg_iff_toRat hfn).mp hfs
      rw [hpb, hpbe] at hmin hsr
      rw [hpb]
      exact loan.broker.feeCover_nonneg _ ⟨by omega, by omega⟩ _ _ _ hfn hf0 hmin hsr htb
    · -- the vault update keeps AssetsDeployed stored and above AssetsReserved, on a vault with shares
      intro toPool yd raw hadj
      obtain ⟨aa', ad', lu', ar', yu', hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts p.pool _ raw hadj
      have hex := l.vault.exact
      obtain ⟨d, hd16, hdv⟩ := hr.deployed_units
      have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
        (congrArg RawLoan.principalOutstanding hraw :)
      have hpend : e.loan.isPending = false := by
        rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw] at hnp; exact hnp
      have hres : l.vault.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
        rw [hpo, hr.reservedInv.sum, hr.debtInv.deployed]
        exact LendingLedger.principalSum_add_le_all l (·.isPending) he hpend
      have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := hex.assetsReserved_nonneg
      have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
      have gAD : Number.OnGrid l.vault.baseExponent p.pool.assetsDeployed :=
        ⟨by rw [hpAD]; exact l.vault.wf.assetsDeployed_norm, d, by rw [hpAD, hdv]; push_cast; ring⟩
      have gneg : Number.OnGrid l.vault.baseExponent p.amounts.principalPaid.operator_neg := by
        rw [← hls]; exact gpp.neg
      have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
        unfold minExponent maxExponent; omega
      have hAD16 : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 * 10 ^ l.vault.baseExponent := by
        rw [hdv]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd16) hp10.le
      have hlt63 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
        mul_lt_mul_of_pos_right (by norm_num) hp10
      have vad := Number.add_exact_of_grid gAD gneg (by rw [hpAD, Number.toRat_neg]; linarith)
        (by rw [hpAD, Number.toRat_neg]; linarith) hsb hs.deployed
      rw [hpAD, Number.toRat_neg] at vad
      have hpp_le : p.amounts.principalPaid.toRat ≤ l.vault.assetsDeployed.toRat := by linarith
      refine ⟨?_, ?_, fun h0 => ?_⟩
      · -- the asset stores the new AssetsDeployed
        rw [hpnt]
        rcases eq_or_lt_of_le hpp0 with hz | hpos
        · rw [vad, ← hz, neg_zero, add_zero]; exact hex.assetsDeployed_representable
        · have gad' := Number.OnGrid.add gAD gneg hsb hs.deployed
          obtain ⟨k, hk⟩ := gad'.2
          have hk0 : 0 ≤ k := by
            have : (0 : ℚ) ≤ k * 10 ^ l.vault.baseExponent := by rw [← hk, vad]; linarith
            exact_mod_cast nonneg_of_mul_nonneg_left this hp10
          have hk16 : k < 10 ^ 16 := by
            have : (k : ℚ) * 10 ^ l.vault.baseExponent < 10 ^ 16 * 10 ^ l.vault.baseExponent := by
              rw [← hk, vad]; linarith
            have := lt_of_mul_lt_mul_right this hp10.le
            exact_mod_cast this
          have hnr := hr.holdsAsset.isRounded_units ad' k.toNat gad'.1 (by omega)
            (by rw [hk]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hk0).symm)
          exact (STAmount.isRounded_eq_false_iff _ _ gad'.1 (by rw [vad]; linarith)).mp hnr
      · -- AssetsReserved stays within it
        rw [Number.eq_of_add_zero hs.reserved, hpAR, vad]
        linarith
      · -- a vault without shares has nothing deployed, so no loan to pay
        exfalso
        rw [hpS] at h0
        have hs0 : l.vault.toExact.sharesTotal = 0 := by
          show l.vault.sharesTotal.toRat.num.toNat = 0
          rw [h0, Number.toRat_zero]; rfl
        have hAD0 := (hex.empty_shares hs0).2
        have hP0' : loan.principalOutstanding.toRat = 0 := by
          have := loan.exact.principalOutstanding_nonneg
          have h' : loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := hpoAD
          change l.vault.assetsDeployed.toRat = 0 at hAD0
          linarith
        exact hchecks.principal ((Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp hP0')

/-- A LoanPay on a reachable ledger never fails its lawfulness re-check. -/
lemma LendingLedger.pay_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat) (pt : LoanPaymentType)
    (amount : Number) :
    (l.apply (.loanPay i pt amount)).run ≠ .error .notLawful := by
  refine LendingLedger.apply_ne_notLawful_of_loan rfl fun _ _ => ?_
  intro h
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok'
  · -- the stored loan takes the ledger's broker
    rename_i hwb
    obtain ⟨loan', hl'⟩ := Loan.withBroker_ok _ _ (hr.scaleInv.broker_asset ‹l.loan? i = _› ‹l.broker? _ = _›)
    rw [hl'] at hwb
    cases hwb
  · rename_i e he _ b hb _ _ loan hw _ hc _ hpay
    have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
    have hnp : loan.isPending = false := by
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
      have hc' := (TER.isTesSuccess_iff _).mp hc
      unfold Loan.canPay at hc'
      cases hpend : loan.isPending
      · rfl
      · rw [hpend, if_pos rfl] at hc'; cases hc'
    exact LendingLedger.Reachable.pay_ne_notLawful_at hr hat hnp pt amount
      (by simp only [ExceptT.run]; exact hpay)

end XRPL.Model.Lending
