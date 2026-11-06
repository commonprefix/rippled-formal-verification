import XRPL.Properties.Lending.Loan.Common.FactorBound
import XRPL.Properties.Lending.Loan.Common.PayBounds
import XRPL.Properties.Lending.Loan.Common.ValueDecrease
import XRPL.Properties.Lending.Loan.Common.PaymentRoom
import XRPL.Properties.Lending.Loan.Common.FullPaymentSize
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterest

/-! # What the extra amount of an overpayment lowers

The re-amortization charges a new PeriodicPayment on the theoretical principal less at least one LoanScale unit,
more than the rounding errors on a reachable loan, so the new PeriodicPayment is strictly lower. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.overpaymentComponents Loan.tryOverpayment UnsettledPayment.applyOverpayment
  UnsettledPayment.payInstalments Loan.doPayment Loan.settlePayment Loan.payScheduledInstalments
  roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.eq_zero_of_toRat Number.div_zero_error from XRPL.Properties.Lending.Loan.Common.PaymentFactor
open private UnsettledPayment.applyOverpayment_lowers from XRPL.Properties.Lending.Loan.Common.PayBounds
open private LoanState.buildTheoretical_normalized from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest

local notation "ε" => Number.nearestError

/-- A theoretical state over payments left reads its principal from the periodic payment. -/
private lemma LoanState.buildTheoretical_principal_eq (pp rate : Number) (n : UInt32) (m : TenthBips16)
    (th : LoanState) (hn : n ≠ 0) (h : LoanState.buildTheoretical pp rate n m = .ok th) :
    loanPrincipalFromPeriodicPayment pp rate n = .ok th.principalOutstanding := by
  unfold LoanState.buildTheoretical at h
  split at h
  · rename_i h0; exact absurd (by simpa using h0) hn
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tpo, htpo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  exact htpo

/-- The properties of a re-amortization charge the periodic payment of their principal. -/
private lemma computeLoanPropertiesFromPeriodicRate_pp (p rate : Number) (n : UInt32) (m : TenthBips16)
    (nt : NumericType) (s : Int) (props : LoanProperties)
    (h : computeLoanPropertiesFromPeriodicRate p rate n m nt s = .ok props) :
    loanPeriodicPayment p rate n = .ok props.periodicPayment := by
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact hpp

/-- A payment charged on a principal `δ ≥ D` below the theoretical one is lower, while `n` payments total at most
`2·(10^16 + 1)·D` and the factor is at least `(1 − ε)^3 / (3·n)`. Each of the three roundings loses at most `ε`. -/
private lemma periodic_lt_of_factor (pp f tpo x pp' δ D n : ℚ) (hf : 0 < f) (hn : 0 < n)
    (htpo : tpo ≤ pp / f * (1 + ε)) (hx : x ≤ (tpo - δ) * (1 + ε)) (hpp' : pp' ≤ x * f * (1 + ε))
    (hδ : D ≤ δ) (hD : 0 < D) (hroom : n * pp ≤ 2 * ((10 ^ 16 + 1) * D)) (hfn : (1 - ε) ^ 3 / (3 * n) ≤ f) :
    pp' < pp := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hf1 : 0 ≤ f * (1 + ε) := by positivity
  have hf2 : 0 ≤ (1 + ε) ^ 2 * f := by positivity
  have key1 : pp' ≤ pp * (1 + ε) ^ 3 - δ * f * (1 + ε) ^ 2 := by
    calc pp' ≤ x * f * (1 + ε) := hpp'
      _ = x * (f * (1 + ε)) := by ring
      _ ≤ (tpo - δ) * (1 + ε) * (f * (1 + ε)) := mul_le_mul_of_nonneg_right hx hf1
      _ = (1 + ε) ^ 2 * f * tpo - δ * f * (1 + ε) ^ 2 := by ring
      _ ≤ (1 + ε) ^ 2 * f * (pp / f * (1 + ε)) - δ * f * (1 + ε) ^ 2 := by
          have := mul_le_mul_of_nonneg_left htpo hf2
          linarith
      _ = pp * (1 + ε) ^ 3 - δ * f * (1 + ε) ^ 2 := by field_simp
  -- the three roundings cost at most `4·ε` of PeriodicPayment, less than `δ·f`
  have hcube : (1 + ε) ^ 3 - 1 ≤ 4 * ε := by
    have e : (1 + ε) ^ 3 - 1 = ε * (3 + 3 * ε + ε ^ 2) := by ring
    have hs : 3 * ε + ε ^ 2 ≤ 1 := by nlinarith
    rw [e]
    nlinarith
  have key2 : n * (pp * ((1 + ε) ^ 3 - 1)) < n * (δ * f * (1 + ε) ^ 2) := by
    have h1 : n * (pp * ((1 + ε) ^ 3 - 1)) ≤ 2 * ((10 ^ 16 + 1) * D) * (4 * ε) := by
      calc n * (pp * ((1 + ε) ^ 3 - 1)) = (n * pp) * ((1 + ε) ^ 3 - 1) := by ring
        _ ≤ 2 * ((10 ^ 16 + 1) * D) * (4 * ε) := by
            apply mul_le_mul hroom hcube (by nlinarith) (by positivity)
    have h2 : D * ((1 - ε) ^ 3 / 3) ≤ n * (δ * f * (1 + ε) ^ 2) := by
      have hnf : (1 - ε) ^ 3 / 3 ≤ n * f := by
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < 3 * n)] at hfn
        linarith
      have h1e : 1 ≤ (1 + ε) ^ 2 := one_le_pow₀ (by linarith)
      calc D * ((1 - ε) ^ 3 / 3) ≤ δ * (n * f) := mul_le_mul hδ hnf (by
            have : 0 < 1 - ε := by linarith
            positivity) (by linarith)
        _ = δ * (n * f) * 1 := by ring
        _ ≤ δ * (n * f) * (1 + ε) ^ 2 := mul_le_mul_of_nonneg_left h1e (by nlinarith)
        _ = n * (δ * f * (1 + ε) ^ 2) := by ring
    have h3 : 2 * ((10 ^ 16 + 1) * D) * (4 * ε) < D * ((1 - ε) ^ 3 / 3) := by
      have hl : (1 - 1 / 10 ^ 18 : ℚ) ^ 3 ≤ (1 - ε) ^ 3 := by gcongr
      have : 2 * ((10 ^ 16 + 1) : ℚ) * (4 * ε) < (1 - ε) ^ 3 / 3 := by
        calc 2 * ((10 ^ 16 + 1) : ℚ) * (4 * ε) ≤ 2 * (10 ^ 16 + 1) * (4 * (1 / 10 ^ 18)) := by gcongr
          _ < (1 - 1 / 10 ^ 18) ^ 3 / 3 := by norm_num
          _ ≤ (1 - ε) ^ 3 / 3 := by gcongr
      nlinarith
    linarith
  have key3 := lt_of_mul_lt_mul_left key2 hn.le
  nlinarith

/-- A re-amortization charges a lower PeriodicPayment, while the payments left times PeriodicPayment are at
most `2·(10^16 + 1)` LoanScale units and the extra amount pays at least one unit of principal. -/
private lemma Loan.reamortized_periodic_lt (l : Loan) (opc : PaymentComponents) {rate v18 : Number}
    {th : LoanState} {props : LoanProperties} (hn : l.paymentRemaining ≠ 0)
    (hroom : (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * ((10 ^ 16 + 1) * 10 ^ l.loanScale))
    (hδN : opc.principalDelta.isNormalized) (hδ : (10 : ℚ) ^ l.loanScale ≤ opc.principalDelta.toRat)
    (hrate : l.periodicRate = .ok rate)
    (hth : LoanState.buildTheoretical l.periodicPayment rate l.paymentRemaining l.broker.managementFeeRate = .ok th)
    (h18 : th.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok v18)
    (hprops : computeLoanPropertiesFromPeriodicRate (v18.max Number.zero) rate l.paymentRemaining
      l.broker.managementFeeRate l.broker.numericType l.loanScale = .ok props)
    (hsig : 0 < props.periodicPayment.signum) :
    props.periodicPayment.toRat < l.periodicPayment.toRat := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hrateN := loanPeriodicRate_isNormalized _ _ _ hrate
  have hppN := l.wf.periodicPayment_norm
  have hpp : 0 < l.periodicPayment.toRat := by
    have := (operator_lt_iff _ _ Number.zero_isNormalized hppN).mp l.valid.periodicPayment_pos
    rwa [Number.toRat_zero] at this
  have hN := Number.ofInt64_isNormalized l.paymentRemaining.toInt64
  have hNv := Number.ofInt64_count l.paymentRemaining
  have hn0 : (0 : ℚ) < l.paymentRemaining.toNat := by
    have : l.paymentRemaining.toNat ≠ 0 := fun h0 => hn (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.pos_of_ne_zero this
  have hD : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  have htpo := LoanState.buildTheoretical_principal_eq _ _ _ _ _ hn hth
  have hpp' := computeLoanPropertiesFromPeriodicRate_pp _ _ _ _ _ _ _ hprops
  have hthN := (LoanState.buildTheoretical_normalized hppN hrateN hth).2.1
  have hv18N := operator_sub_isNormalized_to_nearest_sz _ _ _ hthN hδN h18
  have hmaxN : (v18.max Number.zero).isNormalized := by
    unfold Number.max; split
    · exact Number.zero_isNormalized
    · exact hv18N
  have hpp0 := (Number.signum_pos_iff_toRat
    (loanPeriodicPayment_isNormalized _ _ _ _ hmaxN hrateN hpp')).mp hsig
  -- the reduced principal is the theoretical principal less `δ`, above zero
  unfold loanPeriodicPayment at hpp'
  dsimp only at hpp'
  split at hpp'
  · simp only [pure, Except.pure, Except.ok.injEq] at hpp'
    rw [← hpp', Number.toRat_zero] at hpp0
    exact absurd hpp0 (lt_irrefl 0)
  rename_i hz
  have hrp : (v18.max Number.zero).operator_eq Number.zero = false := by
    revert hz; cases (v18.max Number.zero).operator_eq Number.zero <;> simp
  have hzz : Number.zero.operator_eq Number.zero = true :=
    (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
  obtain ⟨hmax, hx0⟩ : v18.max Number.zero = v18 ∧ 0 < v18.toRat := by
    unfold Number.max at hrp ⊢
    split at hrp
    · rw [hzz] at hrp; cases hrp
    · rename_i hlt
      refine ⟨by rw [if_neg hlt], ?_⟩
      have h0 := (operator_lt_eq_false_iff _ _ hv18N Number.zero_isNormalized).mp (by simpa using hlt)
      have hne : v18.toRat ≠ 0 := fun h0' => by
        rw [(operator_eq_iff _ _ hv18N Number.zero_isNormalized).mpr (by rw [h0', Number.toRat_zero])] at hrp
        cases hrp
      rw [Number.toRat_zero] at h0
      exact lt_of_le_of_ne h0 (Ne.symm hne)
  rw [hmax] at hpp'
  have hx := Number.sub_near _ _ _ hthN hδN h18
  have htd : 0 ≤ th.principalOutstanding.toRat - opc.principalDelta.toRat := by
    by_contra hc
    push Not at hc
    have := hx.nonpos hc.le
    linarith
  have hxle := hx.le htd
  obtain ⟨_, -, hpp'⟩ := bind_ok_peel _ _ _ hpp'
  unfold loanPrincipalFromPeriodicPayment at htpo
  dsimp only at htpo
  split at htpo
  · rename_i h0; exact absurd (by simpa using h0) hn
  obtain ⟨_, -, htpo⟩ := bind_ok_peel _ _ _ htpo
  have h1e : 0 < 1 - ε := by linarith
  split at htpo
  · -- no interest: `n` payments of principal
    rename_i hrz
    rw [if_pos hrz] at hpp'
    have htle := (Number.mul_near _ _ _ hppN hN htpo).le (by rw [hNv]; positivity)
    rw [hNv] at htle
    have hple := (Number.div_near _ _ _ hv18N hN hpp').le (by rw [hNv]; positivity)
    rw [hNv] at hple
    refine periodic_lt_of_factor _ (1 / l.paymentRemaining.toNat) _ _ _ _ _ _ (by positivity) hn0 ?_ hxle ?_ hδ hD
      hroom ?_
    · rw [div_div_eq_mul_div, div_one]; exact htle
    · calc props.periodicPayment.toRat ≤ v18.toRat / l.paymentRemaining.toNat * (1 + ε) := hple
        _ = v18.toRat * (1 / l.paymentRemaining.toNat) * (1 + ε) := by ring
    · rw [div_le_div_iff₀ (by positivity) hn0]
      have : (1 - ε) ^ 3 ≤ 1 := pow_le_one₀ h1e.le (by linarith)
      nlinarith
  · -- the payment factor of the periodic rate, at least `1/(3·n)`
    rename_i hrz
    rw [if_neg hrz] at hpp'
    obtain ⟨f, hf, htpo⟩ := bind_ok_peel _ _ _ htpo
    obtain ⟨f', hf', hpp'⟩ := bind_ok_peel _ _ _ hpp'
    rw [hf, Except.ok.injEq] at hf'
    subst hf'
    have hfN := computePaymentFactor_isNormalized _ _ _ _ hrateN hN hf
    have hfne : f.toRat ≠ 0 := fun h0 => Number.div_zero_error (Number.eq_zero_of_toRat hfN h0) htpo
    have hrne : rate.toRat ≠ 0 := fun h0 =>
      hrz ((operator_eq_iff _ _ hrateN Number.zero_isNormalized).mpr (by rw [h0, Number.toRat_zero]))
    have hint : 60 ≤ l.schedule.paymentInterval.toNat := UInt32.le_iff_toNat_le.mp l.valid.paymentInterval_min
    have hlow := loanPeriodicRate_ge _ _ _ hint hrate hrne
    have hfn := computePaymentFactor_ge_third rate _ f hrateN hlow hf hfne
    have hf0 : 0 < f.toRat := lt_of_lt_of_le (div_pos (pow_pos h1e 3) (by positivity)) hfn
    have htle := (Number.div_near _ _ _ hppN hfN htpo).le (div_nonneg hpp.le hf0.le)
    have hple := (Number.mul_near _ _ _ hv18N hfN hpp').le (by positivity)
    exact periodic_lt_of_factor _ _ _ _ _ _ _ _ hf0 hn0 htle hxle hple hδ hD hroom hfn

/-- A re-amortization that passes lowers PeriodicPayment, while the payments left times PeriodicPayment are
at most `2·(10^16 + 1)` LoanScale units and the extra amount pays at least one unit of principal. -/
private lemma Loan.tryOverpayment_periodic_lt (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) (hn : l.paymentRemaining ≠ 0)
    (hroom : (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * ((10 ^ 16 + 1) * 10 ^ l.loanScale))
    (hδN : opc.principalDelta.isNormalized) (hδ : (10 : ℚ) ^ l.loanScale ≤ opc.principalDelta.toRat) :
    re.periodicPayment.toRat < l.periodicPayment.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  have hpos : ∀ a b c : Int, ¬(decide (a ≤ 0) || decide (b ≤ 0) || decide (c < 0)) = true → 0 < a := by
    intro a b c h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at h
    exact h.1.1
  have hprops := ‹computeLoanPropertiesFromPeriodicRate _ _ _ _ _ _ = Except.ok _›
  exact Loan.reamortized_periodic_lt l opc hn hroom hδN hδ ‹_› ‹_› ‹_› hprops (hpos _ _ _ ‹_›)

/-- A management fee rounds at the loan scale. -/
private lemma computeManagementFee_grid (nt : NumericType) (x : Number) (rate : TenthBips16) (s : Int)
    (fee : Number) (hs : -81 ≤ s ∧ s ≤ 80) (hint : nt.isIntegral = true → s ≤ 0)
    (h : computeManagementFee nt x rate s = .ok fee) : Number.OnGrid s fee := by
  unfold computeManagementFee at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint h

/-- The principal an overpayment pays is a whole number of LoanScale units. The overpayment, its interest,
the management fee and the overpayment fee are all rounded at LoanScale. -/
private lemma Loan.overpaymentComponents_principal_grid (l : Loan) (ov : Number) (opc : PaymentComponents)
    (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hov : Number.OnGrid l.loanScale ov) (h : Loan.overpaymentComponents l ov = .ok opc) :
    Number.OnGrid l.loanScale opc.principalDelta := by
  have hsb := Loan.loanScale_bounds l
  unfold Loan.overpaymentComponents at h
  obtain ⟨of, hof, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨of', hof', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨oi, hoi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pai, hpai, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨paf, hpaf, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pd, hpdv, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  have g1 := STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint hof'
  obtain ⟨i', h1, h2, h3⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  have g2 := STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint h1
  have g3 := computeManagementFee_grid _ _ _ _ _ hs hint h2
  have g4 := Number.OnGrid.sub g2 g3 hsb h3
  exact Number.OnGrid.sub (Number.OnGrid.sub (Number.OnGrid.sub hov g4 hsb hpai) g3 hsb hpaf) g1 hsb hpdv

/-- The extra amount of an overpayment that isn't dropped lowers PeriodicPayment, while the payments left
times PeriodicPayment are at most `2·(10^16 + 1)` LoanScale units. -/
private lemma UnsettledPayment.applyOverpayment_periodic_lt (p p' : UnsettledPayment Vault) (amount : Number)
    (hs : -81 ≤ p.loan.loanScale ∧ p.loan.loanScale ≤ 80)
    (hint : p.loan.broker.numericType.isIntegral = true → p.loan.loanScale ≤ 0)
    (hroom : (p.loan.paymentRemaining.toNat : ℚ) * p.loan.periodicPayment.toRat ≤
      2 * ((10 ^ 16 + 1) * 10 ^ p.loan.loanScale))
    (h : UnsettledPayment.applyOverpayment p amount = .ok p') (hne : p' ≠ p) :
    p'.loan.periodicPayment.toRat < p.loan.periodicPayment.toRat := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first | exact absurd rfl hne | skip
  rename_i _ a' ha' hcond _ un hun _ ov hov hovp _ opc hopc hpd _ _ re hre _ am ham _ l' hl'
  have hpr : p.loan.paymentRemaining ≠ 0 := by
    intro h0
    simp [h0] at hcond
  -- the extra amount pays at least one LoanScale unit of principal
  have hovg := STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint hov
  have hδg := Loan.overpaymentComponents_principal_grid _ _ _ hs hint hovg hopc
  have hδ0 : 0 < opc.principalDelta.toRat := by
    have hgt : opc.principalDelta.operator_gt Number.zero = true := by
      revert hpd; cases opc.principalDelta.operator_gt Number.zero <;> simp
    have := (operator_gt_iff _ _ hδg.1 Number.zero_isNormalized).mp hgt
    rwa [Number.toRat_zero] at this
  have hδ : (10 : ℚ) ^ p.loan.loanScale ≤ opc.principalDelta.toRat := by
    obtain ⟨-, k, hk⟩ := hδg
    have hD : (0 : ℚ) < 10 ^ p.loan.loanScale := zpow_pos (by norm_num) _
    have hk0 : (0 : ℚ) < k := by
      by_contra hc
      push Not at hc
      rw [hk] at hδ0
      nlinarith
    have hk1 : (1 : ℚ) ≤ k := by
      have : 0 < k := Int.cast_pos.mp hk0
      exact_mod_cast this
    rw [hk]
    nlinarith
  have hlt := Loan.tryOverpayment_periodic_lt _ _ _ hre hpr hroom hδg.1 hδ
  have e : l'.periodicPayment = re.periodicPayment :=
    (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok hl').1 :)
  show l'.periodicPayment.toRat < _
  rw [e]
  exact hlt

/-- An instalment keeps PeriodicPayment. -/
private lemma Loan.doPayment_periodicPayment (l l' : Loan) (pc : PaymentComponents) (h : Loan.doPayment l pc = .ok l') :
    l'.periodicPayment = l.periodicPayment := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l1, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok hl).1 :)
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, hc1, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc1
    obtain ⟨_, hc2, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨-, rfl⟩ := UInt32.addChecked_eq_ok.mp hc2
    exact (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok h).1 :)

/-- The instalment loop keeps PeriodicPayment. -/
private lemma UnsettledPayment.payInstalments_periodicPayment {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      p'.loan.periodicPayment = payment.loan.periodicPayment := by
  intro n
  induction n with
  | zero =>
    intro payment p' h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    rfl
  | succ n ih =>
    intro payment p' h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · rfl
    · rfl
    all_goals
      have hstep := Loan.doPayment_periodicPayment _ _ _ ‹Loan.doPayment _ _ = _›
    · exact hstep
    · exact (ih _ p' ‹UnsettledPayment.payInstalments _ n amount = _›).trans hstep

/-- The extra amount of an overpayment that is not dropped lowers PrincipalOutstanding, TotalValueOutstanding and
PeriodicPayment of a reachable loan, against the loan its scheduled instalments leave. -/
lemma Loan.overpayment_reduces_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (r : LoanWithAmounts Vault) (hreach : loan.Reachable t) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v .regular amount now).run = .ok (.ok payment))
    (hok : (loan.overpayment v amount now).run = .ok (.ok r))
    (happlied : (loan.overpayment v amount now).run ≠ (loan.regularPayment v amount now).run) :
    r.loan'.principalOutstanding.toRat < payment.loan.principalOutstanding.toRat ∧
      r.loan'.totalValueOutstanding.toRat < payment.loan.totalValueOutstanding.toRat ∧
      r.loan'.periodicPayment.toRat < payment.loan.periodicPayment.toRat := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v .overpayment amount now r hok
  obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
  rw [hpay] at h0
  obtain rfl : payment = p0 := Except.ok.inj (Except.ok.inj h0)
  -- an extra amount that is dropped leaves the regular payment
  have hne : p ≠ payment := by
    rintro rfl
    exact happlied (Loan.overpayment_of_same_instalments loan v amount now (fun q hq => by
      rw [hpay] at hq
      obtain rfl := Except.ok.inj (Except.ok.inj hq)
      exact hp))
  obtain ⟨hpo, htv⟩ := UnsettledPayment.applyOverpayment_lowers payment p amount h1 hne
  -- the scheduled instalments keep LoanScale and PeriodicPayment and take at least one payment
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  obtain ⟨si, -, hloop, hc0⟩ := Loan.payScheduled_loop loan v amount now payment hpay
  have hcnt := (UnsettledPayment.payInstalments_count _ _ _ _ hloop).2.1
  have hpp := UnsettledPayment.payInstalments_periodicPayment amount _ _ _ hloop
  simp only at hcnt hpp
  have hls : payment.loan.loanScale = loan.loanScale := hst.loanScale
  have hbr : payment.loan.broker = loan.broker := hst.broker
  have hcnt' : payment.loan.paymentRemaining.toNat + 1 ≤ loan.paymentRemaining.toNat := by
    have : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
    rw [this] at hcnt
    omega
  obtain ⟨hlo, hhi, hint⟩ := Loan.Reachable.loanScale_facts hreach
  have hroom : (payment.loan.paymentRemaining.toNat : ℚ) * payment.loan.periodicPayment.toRat ≤
      2 * ((10 ^ 16 + 1) * 10 ^ payment.loan.loanScale) := by
    have hpp0 : 0 < payment.loan.periodicPayment.toRat := by
      have := (operator_lt_iff _ _ Number.zero_isNormalized payment.loan.wf.periodicPayment_norm).mp
        payment.loan.valid.periodicPayment_pos
      rwa [Number.toRat_zero] at this
    rw [hls]
    by_cases h2 : 2 ≤ loan.paymentRemaining.toNat
    · have hr := (Loan.Reachable.paymentRoom hreach).periodic h2
      have hpe : payment.loan.periodicPayment = loan.periodicPayment := hpp
      rw [hpe] at hpp0 ⊢
      have hle : (payment.loan.paymentRemaining.toNat : ℚ) ≤ loan.paymentRemaining.toNat := by
        exact_mod_cast (by omega : payment.loan.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat)
      nlinarith
    · have h0' : payment.loan.paymentRemaining.toNat = 0 := by omega
      rw [h0']
      push_cast
      rw [zero_mul]
      positivity
  have hppl := UnsettledPayment.applyOverpayment_periodic_lt payment p amount
    ⟨by rw [hls]; omega, by rw [hls]; exact hhi⟩ (by rw [hls, hbr]; exact hint) hroom h1 hne
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hl := (RawLoan.to_lawful_ok hloan).1
  have e1 : r.loan'.principalOutstanding = p.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hl :)
  have e2 : r.loan'.totalValueOutstanding = p.loan.totalValueOutstanding :=
    (congrArg RawLoan.totalValueOutstanding hl :)
  have e3 : r.loan'.periodicPayment = p.loan.periodicPayment := (congrArg RawLoan.periodicPayment hl :)
  rw [e1, e2, e3]
  exact ⟨hpo, htv, hppl⟩

end XRPL.Model.Lending
