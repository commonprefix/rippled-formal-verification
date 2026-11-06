import XRPL.Properties.Lending.Loan.Common.FullInterest
import XRPL.Properties.Lending.Loan.Common.PaymentRoom
import XRPL.Properties.Lending.Loan.Common.PaySums
import XRPL.Properties.Lending.Loan.Common.PayValues

/-! # What a full payment of a reachable loan pays

A reachable loan owes at most `10^16 + 1` LoanScale units, so the interest of an early payoff is at most
`143·(10^16 + 1)` units. Every sum the payoff computes is exact while its fees stay below `2^63` units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.fullComponents roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private STAmount.ofNumber_frac_of_representable from XRPL.Properties.Lending.Loan.Common.SetValue

local notation "ε" => Number.nearestError

/-- The interest a full payment of a reachable loan charges is at most `143·(10^16 + 1)` LoanScale units.
The payoff is not late, so it accrues at most one period, and two or more payments are left. -/
lemma Loan.Reachable.fullInterest_le {loan : Loan} {t : UInt32} (hr : loan.Reachable t) (now : UInt32)
    (rate tpo fullInterest : Number) (hnl : now ≤ loan.nextPaymentDueDate) (hn : 2 ≤ loan.paymentRemaining.toNat)
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest) :
    fullInterest.isNormalized ∧ 0 ≤ fullInterest.toRat ∧
      fullInterest.toRat ≤ 143 * ((10 ^ 16 + 1) * 10 ^ loan.loanScale) := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hroom := hr.paymentRoom
  set B := (10 ^ 16 + 1) * (10 : ℚ) ^ loan.loanScale with hB
  have hB0 : 0 ≤ B := by positivity
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrate
  have hr0 := loanPeriodicRate_nonneg _ _ rate hrate
  have hpp0 : 0 < loan.periodicPayment.toRat := loan.exact.periodicPayment_pos
  obtain ⟨htpo0, htpo1, htpo2⟩ := loanPrincipalFromPeriodicPayment_le_payments _ _ _ _ loan.wf.periodicPayment_norm
    hpp0.le hrN hr0 htpo
  have hroomP := hroom.periodic hn
  have hn2 : (2 : ℚ) ≤ loan.paymentRemaining.toNat := by exact_mod_cast hn
  -- the theoretical principal is at most `140·B`, its interest per period at most `2·B`
  have hA : tpo.toRat ≤ 140 * B := by nlinarith
  have hPB : loan.periodicPayment.toRat ≤ B := by nlinarith
  have hC : tpo.toRat * rate.toRat ≤ 2 * B := by linarith
  have hcr : loan.rates.closeInterestRate.toNat ≤ 100000 := loan.exact.closeInterestRate_cap
  have hl0 : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn
  have hdue : now.toNat ≤ (if loan.previousPaymentDueDate < loan.schedule.startDate then loan.schedule.startDate
      else loan.previousPaymentDueDate).toNat + loan.schedule.paymentInterval.toNat :=
    le_trans (UInt32.le_iff_toNat_le.mp hnl) (hroom.lastDue hl0)
  have htpoN : tpo.isNormalized := by
    unfold loanPrincipalFromPeriodicPayment at htpo
    dsimp only at htpo
    split at htpo
    · simp only [pure, Except.pure, Except.ok.injEq] at htpo; subst htpo; exact Number.zero_isNormalized
    · obtain ⟨_, -, htpo⟩ := bind_ok_peel _ _ _ htpo
      split at htpo
      · exact Number.operator_mul_isNormalized _ _ _ _ loan.wf.periodicPayment_norm (Number.ofInt64_isNormalized _)
          htpo
      · obtain ⟨f, hf, htpo⟩ := bind_ok_peel _ _ _ htpo
        exact Number.operator_div_isNormalized _ _ _ _ loan.wf.periodicPayment_norm
          (computePaymentFactor_isNormalized rate _ _ f hrN (Number.ofInt64_isNormalized _) hf) htpo
  obtain ⟨hfN, hf0, hfle⟩ := computeFullPaymentInterest_le_principal tpo rate now _ _ _ _ fullInterest htpoN htpo0 hrN
    hr0 hcr hdue hfi
  refine ⟨hfN, hf0, le_trans hfle ?_⟩
  have h4 : (1 + ε) ^ 4 ≤ 143 / 142 := by
    have := one_add_pow_le_lin ε 4 he.le (by push_cast; linarith)
    push_cast at this; linarith
  have hsum : tpo.toRat * rate.toRat + tpo.toRat ≤ 2 * B + 140 * B := by linarith
  calc (tpo.toRat * rate.toRat + tpo.toRat) * (1 + ε) ^ 4 ≤ (2 * B + 140 * B) * (143 / 142) :=
        mul_le_mul hsum h4 (by positivity) (by positivity)
    _ = 143 * B := by ring

/-- A reachable loan has LoanScale between `-10` and `80`, and `0` or below for an integral asset. -/
lemma Loan.Reachable.loanScale_facts {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    -10 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 ∧ (loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr').2.2.2.2.2.2.1
  have hnt := hr'.numericType
  have hhi : loan.loanScale ≤ 80 := by
    have := loan.wf.loanScale_range.2; unfold cMaxOffset at this; exact this
  refine ⟨by rw [hls]; exact Loan.Created.loanScale_ge hc, hhi, fun hi => ?_⟩
  rw [hls]
  exact Loan.Created.loanScale_integral hc (by rw [← hnt]; exact hi)

/-- A reachable integral loan has LoanScale `0`. -/
lemma Loan.Reachable.loanScale_integral {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.broker.numericType.isIntegral = true → loan.loanScale = 0 := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr').2.2.2.2.2.2.1
  rw [hls, hr'.numericType]
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := hc
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hrange := r.loan'.grid.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨-, -, hint⟩ := Loan.create_loanScale_range broker v principal rates fees _ props _ _ hchecks hrange.2
  intro hi
  rw [hLS]
  exact hint (by rw [← hNT]; exact hi)

/-- A value on a grid at least zero is a whole number of units, as `UnitsAt`. -/
private lemma Number.OnGrid.unitsAt {s : Int} {x : Number} (h : Number.OnGrid s x) (h0 : 0 ≤ x.toRat) :
    ∃ k : ℕ, UnitsAt x s k ∧ x.toRat = (k : ℚ) * 10 ^ s := by
  obtain ⟨k, hk⟩ := h.units h0
  exact ⟨k, ⟨h.1, by exact_mod_cast hk⟩, hk⟩

/-- Rounding down at a scale never raises a value at least zero. -/
lemma STAmount.roundToNumericType_downward_le_of_nonneg (nt : NumericType) (x T : Number) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType nt x .downward (some s) = .ok T) : T.toRat ≤ x.toRat := by
  cases hnt : nt with
  | fractional =>
    rw [hnt] at hok
    exact STAmount.roundToNumericType_frac_downward_le x T s hx h0 hs hok
  | integral mv mo ms msh =>
    rw [hnt] at hok
    exact (STAmount.roundToNumericType_int_grid _ rfl x T .downward _ hx h0 (Or.inr (Or.inr rfl)) hok).2.2.2 rfl

/-- The values a full payoff of a reachable loan settles. principalPaid is PrincipalOutstanding, interestPaid
the rounded interest less its fee, feePaid the rounded ClosePaymentFee plus that fee while below `2^63` units. -/
lemma Loan.Reachable.full_units {loan : Loan} {t : UInt32} (hreach : loan.Reachable t) (v : Vault)
    (amount : Number) (now : UInt32) (payment : UnsettledPayment Vault)
    (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments v .full amount now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee) :
    payment.amounts.principalPaid = loan.principalOutstanding ∧
      payment.amounts.interestPaid.toRat = fullInterest'.toRat - managementFee.toRat ∧
      (∀ cf : Number, STAmount.roundToNumericType loan.broker.numericType loan.fees.closePaymentFee .to_nearest
          (some loan.loanScale) = .ok cf → Number.OnGrid loan.loanScale cf → 0 ≤ cf.toRat →
          cf.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale →
        payment.amounts.feePaid.toRat = cf.toRat + managementFee.toRat) := by
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hu0 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  -- the checks: the payoff is not late and the loan has two or more payments left
  have hchk := (Loan.payInstalments_ok loan v .full amount now payment hpay).1
  have hnl : now ≤ loan.nextPaymentDueDate := by
    have := hchk.not_late (by decide)
    rw [UInt32.lt_iff_toNat_lt] at this
    rw [UInt32.le_iff_toNat_le]; omega
  have hn : 2 ≤ loan.paymentRemaining.toNat := by
    have h1 := hchk.more_than_one
    rw [UInt32.le_iff_toNat_le] at h1
    simp at h1; omega
  obtain ⟨hfN, hf0, hfle⟩ := hreach.fullInterest_le now rate tpo fullInterest hnl hn hrate htpo hfi
  -- the rounded interest `a` and its fee `b ≤ a`, in LoanScale units
  have hfiN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfloor
  have hfi0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfN hf0 (Or.inr (Or.inr rfl)) hs81 hfloor
  have hfi_le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfN hf0 hs81 hfloor
  obtain ⟨a, hav, hav'⟩ := (STAmount.roundToNumericType_onGrid _ _ _ _ _ hs81 hint hfloor).unitsAt hfi0
  obtain ⟨gfee, hfee0, hfee_le⟩ := computeManagementFee_le _ _ _ _ _ hfiN hfi0 loan.broker.managementFeeRate_le
    hs81 hint hfee
  obtain ⟨b, hbv, hbv'⟩ := gfee.unitsAt hfee0
  have hab : b ≤ a := by
    have : (b : ℚ) * 10 ^ loan.loanScale ≤ (a : ℚ) * 10 ^ loan.loanScale := by rw [← hbv', ← hav']; exact hfee_le
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have ha : a ≤ 143 * (10 ^ 16 + 1) := by
    have : (a : ℚ) * 10 ^ loan.loanScale ≤ ((143 * (10 ^ 16 + 1) : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hav']; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  obtain ⟨pc, hpc, hamt, -⟩ := Loan.fullPayInstalments_ok loan v amount now payment hpay
  obtain ⟨rate', tpo', fi', net, split, state, cf, ppi, tracked, cfm, uf, ui, hrate', htpo', hfi', hsplit,
    hstate, hcf, hppi, htracked, hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv loan now pc hpc
  rw [hrate] at hrate'; obtain rfl := Except.ok.inj hrate'
  rw [htpo] at htpo'; obtain rfl := Except.ok.inj htpo'
  rw [hfi] at hfi'; obtain rfl := Except.ok.inj hfi'
  obtain ⟨i', hfloor', hfee', hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  rw [hfloor] at hfloor'; obtain rfl := Except.ok.inj hfloor'
  rw [hfee] at hfee'; obtain rfl := Except.ok.inj hfee'
  obtain ⟨t, p, m, -, -, -, htv, hpv, hmv, hiv, hge, h1, hpo, -⟩ := Loan.state_units loan state hstate
  obtain ⟨vap, id, hvap, hid, hip, hfp, hpp⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hamt
  have ht : t ≤ 10 ^ 16 + 1 := by
    have hT := hreach.totalValue_le
    have hval := htv.val
    rw [h1] at hval
    push_cast at hval
    have : (t : ℚ) * 10 ^ loan.loanScale ≤ ((10 ^ 16 + 1 : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hval]; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have hs := Loan.loanScale_bounds loan
  simp only at hvap hid hip hfp hpp
  have hppi' := UnitsAt.add hpv hiv (by constructor <;> omega) hs hppi
  have htr := UnitsAt.add hppi' hmv (by constructor <;> omega) hs htracked
  have hvap' := UnitsAt.sub htr hpv (by constructor <;> omega) hs hvap
  have hid' := UnitsAt.sub hvap' hmv (by constructor <;> omega) hs hid
  have hnet' := UnitsAt.sub hav hbv (by constructor <;> omega) hs hnet
  have hui' := UnitsAt.sub hnet' hiv (by constructor <;> omega) hs hui
  have hip' := UnitsAt.add hid' hui' (by constructor <;> omega) hs hip
  refine ⟨by rw [hpp, hpo], ?_, fun cf' hcf' gcf hcf0 hsum => ?_⟩
  · have : (((p : ℤ) + (t - p - m) + m - p - m) + ((a - b) - (t - p - m)) : ℤ) = (a : ℤ) - b := by ring
    rw [this] at hip'
    rw [hip'.val, hav', hbv']; push_cast; ring
  · rw [hcf] at hcf'; obtain rfl := Except.ok.inj hcf'
    obtain ⟨c, hcv, hcv'⟩ := gcf.unitsAt hcf0
    have hcb : c + b < 2 ^ 63 := by
      have : ((c + b : ℕ) : ℚ) * 10 ^ loan.loanScale < ((2 ^ 63 : ℕ) : ℚ) * 10 ^ loan.loanScale := by
        push_cast; rw [add_mul, ← hcv', ← hbv']; linarith
      exact_mod_cast lt_of_mul_lt_mul_right this hu0.le
    have hcfm' := UnitsAt.add hcv hbv (by constructor <;> omega) hs hcfm
    have huf' := UnitsAt.sub hcfm' hmv (by constructor <;> omega) hs huf
    have hfp' := UnitsAt.add hmv huf' (by constructor <;> omega) hs hfp
    have : ((m : ℤ) + ((c + b) - m) : ℤ) = (c : ℤ) + b := by ring
    rw [this] at hfp'
    rw [hfp'.val, hcv', hbv']; push_cast; ring

/-- Rounding an amount the asset holds exactly, on the scale's grid, gives it back. An IOU amount of `10^16` grid
units or more already has an exponent at or above the scale, so rounding keeps it. -/
lemma STAmount.roundToNumericType_of_representable (nt : NumericType) (x T : Number) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80) (hint : nt.isIntegral = true → s = 0)
    (hst : STAmount.isRounded nt x = false) (hg : Number.OnGrid s x)
    (hok : STAmount.roundToNumericType nt x .to_nearest (some s) = .ok T) : T.toRat = x.toRat := by
  have hu : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  obtain ⟨j, -, hj⟩ := hg.unitsAt h0
  by_cases hj16 : nt = .fractional → j < 10 ^ 16
  · exact STAmount.roundToNumericType_representable_grid nt x T .to_nearest s hx h0 (Or.inl rfl) hs hint hst j hj
      hj16 hok
  push Not at hj16
  obtain ⟨hnt, hj16⟩ := hj16
  subst hnt
  have hz : x.toRat ≠ 0 := by
    intro h; rw [h] at hj
    have : (j : ℚ) = 0 := by
      rcases mul_eq_zero.mp hj.symm with h' | h'
      · exact h'
      · exact absurd h' hu.ne'
    have : j = 0 := by exact_mod_cast this
    omega
  obtain ⟨m, e, hmlo, hmhi, helo, -, hv⟩ :=
    ((STAmount.isRounded_eq_false_iff .fractional x hx h0).mp hst).resolve_left hz
  cases hof : STAmount.ofNumber .fractional x .to_nearest with
  | error err =>
    unfold STAmount.roundToNumericType at hok; rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    obtain ⟨hst0, hc, hstx, hste⟩ :=
      STAmount.ofNumber_frac_of_representable x .to_nearest st m e hx h0 (Or.inl rfl) ⟨hmlo, hmhi⟩ helo hv hof
    have hse : s ≤ e := by
      by_contra hlt
      push Not at hlt
      have h1 : (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ s := by
        calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := by
              gcongr; exact_mod_cast hmhi
          _ ≤ 10 ^ 16 * 10 ^ s :=
              mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hlt.le) (by positivity)
      have h2 : (10 : ℚ) ^ 16 * 10 ^ s ≤ (j : ℚ) * 10 ^ s := by
        gcongr; exact_mod_cast hj16
      rw [← hv, hj] at h1
      linarith
    unfold STAmount.roundToNumericType at hok
    rw [hof] at hok
    simp only at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hfr : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
    rw [if_neg (by rw [hfr]; decide)] at hok
    have hre : STAmount.roundToExponent st s .to_nearest = .ok st := by
      unfold STAmount.roundToExponent
      rw [if_neg (by rw [hfr]; decide), if_neg (by unfold STAmount.isZero; simpa using hst0),
        if_pos (by rw [hste]; exact hse)]
    rw [hre] at hok
    simp only at hok
    rw [(STAmount.toNumber_exact_of st T (Or.inl hc) hok).1, hstx]

/-- A reachable loan stores each fee as an amount its asset holds exactly. -/
lemma Loan.Reachable.fees_representable {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    ∀ x ∈ loan.fees.amountFields, STAmount.isRounded loan.broker.numericType x = false := by
  obtain ⟨s0, t0, hc, hr0⟩ := hr
  have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr0
  rw [hft.2.1, hr0.numericType]
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, hcan, hok, rfl⟩ := hc
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, -, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hF : r.loan'.fees = fees := by show r.loan'.toRawLoan.fees = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  intro x hx
  rw [hF] at hx
  rw [hNT]
  exact Loan.canCreate_exact broker v principal fees _ _ twoStep hcan x (List.mem_cons_of_mem _ hx)

/-- Proof body of the vault part of `Lending.fullPayment_payoff`, for every reachable loan. -/
lemma Loan.fullPayment_vault_reachable_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (hreach : loan.Reachable t) (payment : UnsettledPayment Vault)
    (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments v .full amount now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee) :
    payment.amounts.principalPaid = loan.principalOutstanding ∧
      payment.amounts.interestPaid.toRat = fullInterest'.toRat - managementFee.toRat :=
  let h := hreach.full_units v amount now payment rate tpo fullInterest fullInterest' managementFee hpay hrate htpo hfi
    hfloor hfee
  ⟨h.1, h.2.1⟩

/-- Proof body of `fullPayment_broker`, for every reachable loan whose fee sum stays below `2^63` units. -/
lemma Loan.fullPayment_broker_reachable_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (hreach : loan.Reachable t) (payment : UnsettledPayment Vault)
    (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments v .full amount now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee)
    (hsum : loan.fees.closePaymentFee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale) :
    payment.amounts.feePaid.toRat = loan.fees.closePaymentFee.toRat + managementFee.toRat := by
  obtain ⟨-, -, hfp⟩ := hreach.full_units v amount now payment rate tpo fullInterest fullInterest' managementFee hpay
    hrate htpo hfi hfloor hfee
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hint0 := hreach.loanScale_integral
  obtain ⟨-, -, gcf⟩ := Loan.Reachable.fees_onGrid hreach
  have hcf0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hrep := hreach.fees_representable loan.fees.closePaymentFee (by simp [LoanFees.amountFields])
  obtain ⟨pc, hpc, -, -⟩ := Loan.fullPayInstalments_ok loan v amount now payment hpay
  obtain ⟨_, _, _, _, _, _, cf, _, _, _, _, _, -, -, -, -, -, hcf, -, -, -, -, -, -⟩ :=
    Loan.fullComponents_ok_inv loan now pc hpc
  have hcfv := STAmount.roundToNumericType_of_representable _ _ _ _ loan.wf.closePaymentFee_norm hcf0 hs81 hint0 hrep
    gcf hcf
  have gcf' : Number.OnGrid loan.loanScale cf :=
    ⟨STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf, by obtain ⟨-, k, hk⟩ := gcf; exact ⟨k, by rw [hcfv, hk]⟩⟩
  rw [← hcfv]
  exact hfp cf hcf gcf' (by rw [hcfv]; exact hcf0) (by rw [hcfv]; exact hsum)

end XRPL.Model.Lending
