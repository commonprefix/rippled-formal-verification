import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
import XRPL.Properties.Lending.Ledger.Common.RecheckPool

/-! # LoanSet passes its lawfulness re-check

Once every LoanSet check passed, the vault sits on the base grid below the Open limit, so no re-check fails. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private canFundLoan checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet
open private Loan.createChecks_of_steps from XRPL.Properties.Lending.Loan.Common.SetLawful
open private atExponent_of_int open_bound_lt from XRPL.Properties.Lending.Loan.Common.OrderCreates
open private Vault.assetsTotal_ge_available from XRPL.Properties.Lending.Loan.Common.SetScale
open private loanPeriodicRate_zero loanPeriodicPayment_zero_rate from XRPL.Properties.Lending.Loan.Common.SetValue

lemma computeLoanProperties_ne_notLawful (principal : Number) (ir : TenthBips32) (interval pr : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) :
    computeLoanProperties principal ir interval pr mgmt nt minScale ≠ .error .notLawful := by
  unfold computeLoanProperties
  simp only [bind, Except.bind]
  split_ne_notLawful [loanPeriodicRate_ne_notLawful, computeLoanPropertiesFromPeriodicRate_ne_notLawful]

private lemma checkPrecisionFields_ne_notLawful (principal : Number) (fees : LoanFees)
    (f : Number → Except Error Bool)
    (hf : ∀ x, f x ≠ .error .notLawful) : checkPrecisionFields principal fees f ≠ .error .notLawful := by
  intro h
  unfold checkPrecisionFields LoanFees.amountFields at h
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals exact hf _ ‹_›

lemma isRounded_ne_notLawful (value : Number) (scale : Int) (nt : NumericType) :
    isRounded value scale nt ≠ .error .notLawful := by
  unfold isRounded
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.roundToNumericType_ne_notLawful]

lemma LoanProperties.checkGuards_ne_notLawful (props : LoanProperties) (principal : Number) (ir : TenthBips32)
    (n : UInt32) (nt : NumericType) : props.checkGuards principal ir n nt ≠ .error .notLawful := by
  intro h
  unfold LoanProperties.checkGuards LoanProperties.amortizationGuards at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [Number.operator_sub_ne_notLawful, STAmount.roundToNumericType_ne_notLawful,
    Number.operator_div_ne_notLawful, Number.to_rep_ne_notLawful]

lemma LoanBroker.checkLimits_ne_notLawful (b : LoanBroker) (d : Number) (e : Int) :
    b.checkLimits d e ≠ .error .notLawful := by
  intro h
  unfold LoanBroker.checkLimits at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [RawLoanBroker.hasMinimumCover_ne_notLawful]

/-- The vault exponent a LoanSet reads is a Number sum and an exponent read. -/
private lemma Vault.exponent_ne_notLawful (v : Vault) (nt : NumericType) :
    AssetPool.exponent v nt ≠ .error .notLawful := by
  unfold AssetPool.exponent
  simp only [bind, Except.bind, Vault.pool_assetsTotal]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, numberExponent_ne_notLawful]

/-- The LoanSet checks never raise `notLawful`. -/
lemma Loan.canCreate_ne_notLawful (broker : LoanBroker) (v : Vault) (principal : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (now : UInt32) (twoStep : Bool) :
    Loan.canCreate broker v principal fees schedule now twoStep ≠ .error .notLawful := by
  have hfund : canFundLoan v schedule now broker.numericType ≠ .error .notLawful := by
    intro h
    unfold canFundLoan at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    walk_ok
    all_goals simp_all [Vault.exponent_ne_notLawful]
  have hprec := checkPrecisionFields_ne_notLawful principal fees
    (fun value => pure !(STAmount.isRounded broker.numericType value)) (fun _ => by simp [pure, Except.pure])
  have hsched : schedule.checkTimeAvailability ≠ .error .notLawful := by
    rw [LoanSchedule.checkTimeAvailability_eq]; split <;> exact nofun
  intro h
  unfold Loan.canCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all

/-- A create whose checks passed carries a nonnegative interest. It needs the principal below `10^16` base
units on an IOU, and below `10^17` units for a zero-rate loan on an integral asset. -/
private lemma Loan.create_checks_interest (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number) (hpre : Loan.CreatePreflight broker principal rates fees schedule)
    (hfrac : broker.numericType = .fractional → principal.toRat < 10 ^ 16 * 10 ^ v.baseExponent)
    (hint : broker.numericType.isIntegral = true → rates.interestRate = 0 → principal.toRat < 10 ^ 17)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal') :
    loanState.interestDue.isNormalized ∧ 0 ≤ loanState.interestDue.toRat := by
  have hp := hpre.principal_norm
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨hlsmin, hls0⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2
  obtain ⟨ti', hsub, hgt0, hle0, -, hmf0, htv0, hpp0⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrt
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hp hrN hpp
  have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toInt64
  have hNv := Number.ofInt64_count schedule.paymentTotal
  have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
  have htvN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have hmfN : props.managementFeeOutstanding.isNormalized := by
    have heq : computeManagementFee broker.numericType ti broker.managementFeeRate props.loanScale =
        (tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest) >>=
          (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some props.loanScale)) := rfl
    rw [heq] at hmfo
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ hmfo
    exact STAmount.roundToNumericType_isNormalized _ _ _ _ _ h
  have hpp0' : 0 < props.periodicPayment.toRat := (Number.signum_pos_iff_toRat hppN).mp hpp0
  have htv0' : 0 < props.totalValueOutstanding.toRat := (Number.signum_pos_iff_toRat htvN).mp htv0
  have hmode : valueMode rate = .to_nearest ∨ valueMode rate = .upward ∨ valueMode rate = .downward :=
    (valueMode_cases rate).elim Or.inl (fun h => Or.inr (Or.inl h))
  have hamt0 : 0 ≤ amount.toRat := by
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamt h0
      have := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero, hNv]; positivity)
      rwa [Number.toRat_zero] at this
  have hls80 : props.loanScale ≤ 80 := by
    rw [hls]
    refine max_le (le_trans hbase.2 (by norm_num)) ?_
    cases hnt' : broker.numericType with
    | integral mv mo ms msh =>
      rw [hnt'] at hst'
      have := (STAmount.ofNumber_integral_canonical _ _ _ amountSt rfl hst').1.offset_zero
      show amountSt.mOffset ≤ 80; omega
    | fractional =>
      rw [hnt'] at hst'
      by_cases hz : amountSt.mValue = 0
      · -- a zero amount would leave a zero total value
        rw [hnt'] at htvo
        rw [STAmount.roundToNumericType_frac_of_zero _ _ _ _ _ hst' hz htvo] at htv0'
        exact absurd htv0' (lt_irrefl _)
      · exact (STAmount.ofNumber_frac_stage amount _ amountSt hamtN hamt0 hmode hst' hz).1.exp_hi
  have hlo : -10 ≤ props.loanScale := le_trans hbase.1 hlsmin
  have hs : minExponent + 18 ≤ props.loanScale ∧ props.loanScale ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hpos.le hst
    ⟨by omega, hls80⟩ hls0 (hchecks.exact principal List.mem_cons_self)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0] at hj; simp at hj; linarith
    · exact h0
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h1 := hchecks.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)
  have hj16 : broker.numericType = .fractional → j < 10 ^ 16 := by
    intro hfr
    have h1 : (j : ℚ) * 10 ^ props.loanScale < (10 ^ 16 : ℕ) * 10 ^ props.loanScale := by
      calc (j : ℚ) * 10 ^ props.loanScale = principal.toRat := hj.symm
        _ < 10 ^ 16 * 10 ^ v.baseExponent := hfrac hfr
        _ ≤ (10 ^ 16 : ℕ) * 10 ^ props.loanScale := by
            push_cast
            exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hlsmin) (by positivity)
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
  obtain ⟨aT, haTv, haT⟩ : ∃ aT : ℕ, props.totalValueOutstanding.toRat = (aT : ℚ) * 10 ^ props.loanScale ∧
      aT < broker.numericType.mantissaBound := by
    cases hnt' : broker.numericType with
    | fractional =>
      rw [hnt'] at htvo hst'
      have hexp : ∀ st, STAmount.ofNumber .fractional amount (valueMode rate) = .ok st → st.mValue ≠ 0 →
          st.exponent ≤ props.loanScale := fun st hst2 _ => by
        rw [hst', Except.ok.injEq] at hst2
        rw [← hst2, hls]; exact le_max_right _ _
      obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_frac_grid amount _ _ props.loanScale hamtN hamt0
        hmode ⟨by omega, hls80⟩ hexp htvo
      have hle := STAmount.roundToNumericType_frac_le amount _ _ props.loanScale hamtN hamt0 hmode
        ⟨by omega, hls80⟩ hexp htvo
      refine ⟨k, hk, ?_⟩
      rw [hk] at hle
      have : k ≤ 10 ^ 16 - 1 := by exact_mod_cast le_of_mul_le_mul_right hle hp10
      show k < 10 ^ 16
      omega
    | integral mv mo ms msh =>
      rw [hnt'] at htvo
      have hls00 := hls0 (by rw [hnt']; rfl)
      obtain ⟨-, ⟨k, hk⟩, -, -⟩ :=
        STAmount.roundToNumericType_int_grid _ rfl amount _ _ _ hamtN hamt0 hmode htvo
      have hlt := STAmount.roundToNumericType_int_lt_bound _ rfl amount _ _ _ hamtN hamt0 htvo
      refine ⟨k, by rw [hk, hls00, zpow_zero, mul_one], ?_⟩
      rw [hk] at hlt
      exact_mod_cast hlt
  have haT63 : aT < 2 ^ 63 := lt_of_lt_of_le haT (NumericType.mantissaBound_le _)
  have hja : j ≤ aT := by
    by_cases hir : rates.interestRate = 0
    · have hprops := hchecks.properties_ok
      rw [hir] at hprops
      have h1 := (computeLoanProperties_zero_rate_value principal _ _ _ _ _ props hp ⟨hbase.1, hbase.2⟩
        hpre.fits.paymentTotal_pos j hj1 hj (fun hi => by
          have h17 := hint hi hir
          rw [hj, hls0 hi, zpow_zero, mul_one] at h17
          exact_mod_cast h17) hprops).1
      rw [haTv, hj] at h1
      exact le_of_eq (by exact_mod_cast (mul_right_cancel₀ hp10.ne' h1).symm)
    · have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti' htvN hp hsub
      have hR := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
      by_contra hc'
      push Not at hc'
      have h1 : props.totalValueOutstanding.toRat - principal.toRat ≤ 0 := by
        rw [haTv, hj]
        have : (aT : ℚ) ≤ j := by exact_mod_cast hc'.le
        nlinarith
      have := Number.roundsToRepresentable_nonpos ti' _ hR h1
      have := (Number.signum_pos_iff_toRat htiN).mp (hgt0 hir)
      linarith
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest props.loanScale hp
      hpos.le (Or.inl rfl) ⟨by omega, hls80⟩ hls0 hst j hj hj16 hpo
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ props.loanScale := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j props.loanScale htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hs hti]
    push_cast [Nat.cast_sub hja]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := by
    intro hf
    rw [hf] at haT
    exact lt_of_le_of_lt (Nat.sub_le _ _) haT
  obtain ⟨-, hmf_hi, -, ⟨mm, hmm⟩⟩ := computeManagementFee_bounds broker.numericType ti _ (aT - j)
    broker.managementFeeRate props.loanScale (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) htiv
    (by omega) hR10 ⟨hlo, hls80⟩ hls0 hfr hmfo
  have hmmK : mm ≤ aT - j := by
    have hC : ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 ≤ aT - j := by
      have : (aT - j) * broker.managementFeeRate.toNat ≤ (aT - j) * 10000 := Nat.mul_le_mul_left _ hR10
      omega
    have h1 : (mm : ℚ) * 10 ^ props.loanScale ≤
        ((((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) : ℚ) * 10 ^ props.loanScale := by
      rw [← hmm]; exact hmf_hi
    have h2 : mm ≤ ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 := by
      exact_mod_cast le_of_mul_le_mul_right h1 hp10
    omega
  have hiv := LoanState.build_interestDue_grid _ _ _ props.loanScale aT j mm loanState htvN hp hmfN haTv hj hmm
    haT63 hja (by omega) hs hchecks.state
  refine ⟨hiv.1, ?_⟩
  rw [hiv.2, haTv, hj, hmm]
  have h2 : ((j + mm : ℕ) : ℚ) ≤ (aT : ℚ) := by exact_mod_cast (by omega)
  push_cast at h2
  nlinarith

/-- A create never fails its re-checks when its checks pass only on a vault and broker on the base grid. -/
lemma Loan.create_ne_notLawful (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hasset : Vault.HoldsAsset v)
    (hcount : broker.loanCount + 1 ≠ 0)
    (hgrid : ∀ props loanState debtTotal', Loan.CreateChecks broker v principal rates fees schedule props loanState
      debtTotal' → Loan.CreateGrid broker v) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run ≠ .error .notLawful := by
  intro h
  have h0 := h
  simp only [Loan.create] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp_all [computeLoanProperties_ne_notLawful, LoanProperties.checkGuards_ne_notLawful,
    LoanState.build_ne_notLawful, LoanBroker.checkLimits_ne_notLawful, Number.operator_add_ne_notLawful,
    STAmount.roundToNumericType_ne_notLawful, UInt32.addChecked_ne_notLawful]; done)
  all_goals try (exact checkPrecisionFields_ne_notLawful _ _ _ (fun x => isRounded_ne_notLawful _ _ _) ‹_›)
  all_goals try (exact Vault.exceedsOpenLimit_ne_notLawful _ _ ‹_›)
  -- a re-check is reached only once every check passed, and then the create succeeds
  all_goals
    have hchecks := Loan.createChecks_of_steps broker v principal rates fees schedule _ _ _ _ _ _ _ ‹_› ‹_›
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    obtain ⟨loan, v', _, hrun⟩ := Loan.create_success_lawful broker v principal rates fees schedule
      allowsOverpayment pending _ _ _ hpre hasset (hgrid _ _ _ hchecks) hcount hchecks
    rw [hrun] at h0
    exact absurd h0 (by simp)

/-- On a reachable ledger a create whose checks passed reads its vault and broker on the base grid. Its interest
is not negative, so the passed Open-limit check keeps AssetsTotal and YieldUnrealized below `10^16` base units. -/
lemma LendingLedger.Reachable.createGrid_of_checks {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {broker : LoanBroker} (hb : l.broker? j = some broker) {principal : Number} {rates : LoanRates}
    {fees : LoanFees} {schedule : LoanSchedule} {props : LoanProperties} {loanState : LoanState}
    {debtTotal' : Number}
    (hchecks : Loan.CreateChecks broker l.vault principal rates fees schedule props loanState debtTotal')
    (hiN : loanState.interestDue.isNormalized) (hi0 : 0 ≤ loanState.interestDue.toRat) :
    Loan.CreateGrid broker l.vault := by
  have hex := l.vault.exact
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := hex.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := hex.assetsDeployed_nonneg
  have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := hex.assetsReserved_nonneg
  have hARD : l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := hex.assetsReserved_le
  have hYU0 : 0 ≤ l.vault.yieldUnrealized.toRat := hex.yieldUnrealized_nonneg
  -- the passed Open-limit check bounds the total and the yield
  have hbase := Vault.baseExponent_scale_range l.vault
  have hlt := open_bound_lt l.vault.baseExponent
  obtain ⟨atot, hat⟩ := Vault.assetsTotal_of_exceedsOpenLimit l.vault _ _ hchecks.open_zone
  obtain ⟨-, hyopen, hatopen⟩ := Vault.exceedsOpenLimit_false_bound l.vault loanState.interestDue hiN
    hchecks.open_zone
  have hatlt := hatopen atot hat
  have hroom : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 16 + 5) (l.vault.baseExponent - 1)
      (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
    have hwle : w.toRat ≤ l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
      rw [hwv]; push_cast at hlt ⊢; linarith
    have hle := Vault.assetsTotal_ge_of_le l.vault atot hat w hw hwle
    rw [hwv] at hle
    push_cast at hle hatlt
    linarith
  have hyield : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by linarith
  have hdt := hr.debtInv.debt j broker hb
  have hdtle : broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hdt, hr.debtInv.deployed]; exact l.brokerPrincipal_le j
  have hdt0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  obtain ⟨na, hna⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  rw [← hr.debtInv.deployed] at hnd
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨ny, hny⟩ := hr.yieldGridInv.grid.nat hYU0
  obtain ⟨nt, hnt⟩ := hr.scaleInv.brokerPrincipal_grid j
  exact ⟨atExponent_of_int _ na _ (by rw [hna]; push_cast; ring) hAA0 (by linarith),
    atExponent_of_int _ nd _ (by rw [hnd]; push_cast; ring) hAD0 (by linarith),
    atExponent_of_int _ nr _ (by rw [hnr]; push_cast; ring) hAR0 (by linarith),
    atExponent_of_int _ ny _ (by rw [hny]; push_cast; ring) hYU0 hyield,
    atExponent_of_int _ nt _ (by rw [hdt, hnt]; push_cast; ring) hdt0 (by linarith)⟩

/-- The vault check of a LoanSet that passed read the vault total at the base exponent. -/
private lemma canFundLoan_exponent (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (h : canFundLoan v schedule t nt = .ok .tesSUCCESS) : AssetPool.exponent v nt = .ok v.baseExponent := by
  unfold canFundLoan at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals
    rw [‹AssetPool.exponent v nt = _›]
    have hne := ‹¬ (_ != AssetPool.baseExponent v) = true›
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    rw [hne]; rfl

/-- A vault check that returned a passing code read the vault total at the base exponent. -/
private lemma canFundLoan_exponent' (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (vt : TER) (h : canFundLoan v schedule t nt = .ok vt) (hvt : ¬(!vt.isTesSuccess) = true) :
    AssetPool.exponent v nt = .ok v.baseExponent := by
  have hvt' : vt.isTesSuccess = true := by simpa using hvt
  rw [(TER.isTesSuccess_iff _).mp hvt'] at h
  exact canFundLoan_exponent v schedule t nt h

/-- A LoanSet that passed its checks read the vault total at the base exponent. -/
lemma Loan.canCreate_exponent (broker : LoanBroker) (v : Vault) (principal : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (now : UInt32) (twoStep : Bool)
    (h : Loan.canCreate broker v principal fees schedule now twoStep = .ok .tesSUCCESS) :
    ∃ atot, v.assetsTotal = .ok atot ∧
      numberExponent atot v.baseExponent broker.numericType = .ok v.baseExponent := by
  have hexp : AssetPool.exponent v broker.numericType = .ok v.baseExponent := by
    unfold Loan.canCreate at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    walk_ok
    all_goals first
      | exact absurd ‹(!TER.tesSUCCESS.isTesSuccess) = true› (by decide)
      | exact canFundLoan_exponent' v schedule now broker.numericType _ ‹_› ‹_›
  unfold AssetPool.exponent at hexp
  obtain ⟨atot, hat, he⟩ := bind_ok_peel _ _ _ hexp
  exact ⟨atot, hat, he⟩

/-- A `Number` input that passed its check is normalized and at least zero. -/
private lemma isNonnegativeInput_facts {n : Number} (h : isNonnegativeInput n = true) :
    n.isNormalized ∧ 0 ≤ n.toRat := by
  unfold isNonnegativeInput at h
  rw [Bool.and_eq_true] at h
  have hn := of_decide_eq_true h.1
  refine ⟨hn, ?_⟩
  have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp h.2
  rwa [Number.toRat_zero] at this

/-- The LoanSet preflight and checks fix every field `create` assumes: the principal, the fees, the rates and
the schedule are in range, and the principal and fees are amounts the asset stores. -/
lemma LendingTx.loanSet_createPreflight (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (pi pt gp : Option UInt32) (sd : UInt32) (twoStep ao : Bool) (broker : LoanBroker)
    (hpre : (LendingTx.loanSet i principal rates fees pi pt gp sd twoStep ao).preflight l = .tesSUCCESS)
    (hc : Loan.canCreate broker l.vault principal fees (LoanSchedule.build pi pt gp sd l.now twoStep) l.now twoStep =
      .ok .tesSUCCESS) :
    Loan.CreatePreflight broker principal rates fees (LoanSchedule.build pi pt gp sd l.now twoStep) := by
  have hp := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao
    (by rw [hpre]; rfl)
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hall
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hall
    obtain ⟨-, ho, hole, hsv, hlf, hcf, hir, hlr, hcr, hor, hof, hn, hint, hg1, hg2⟩ := hall
    obtain ⟨hoN, ho0⟩ := isNonnegativeInput_facts ho
    obtain ⟨hsvN, hsv0⟩ := isNonnegativeInput_facts hsv
    obtain ⟨hlfN, hlf0⟩ := isNonnegativeInput_facts hlf
    obtain ⟨hcfN, hcf0⟩ := isNonnegativeInput_facts hcf
    set schedule := LoanSchedule.build pi pt gp sd l.now twoStep
    have hn' : 0 < schedule.paymentTotal := hn
    have hi' : 0 < schedule.paymentInterval := by
      show 0 < pi.getD defaultPaymentInterval
      have : minPaymentInterval ≤ pi.getD defaultPaymentInterval := hint
      have h60 := UInt32.le_iff_toNat_le.mp this
      have hm : minPaymentInterval.toNat = 60 := rfl
      rw [UInt32.lt_iff_toNat_lt]
      show 0 < (pi.getD defaultPaymentInterval).toNat
      omega
    obtain ⟨atot, hat, hexp⟩ := Loan.canCreate_exponent broker l.vault principal fees schedule l.now twoStep hc
    obtain ⟨hfits, -, -, -, hexact⟩ := (Loan.canCreate_lawful_iff_proof broker l.vault principal fees schedule l.now
      twoStep atot _ hn' hi' hat hexp).mp hc
    have hfee : ∀ fee ∈ fees.amountFields, fee.isNormalized ∧ 0 ≤ fee.toRat := by
      intro fee hf
      simp only [LoanFees.amountFields, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact ⟨hoN, ho0⟩
      · exact ⟨hsvN, hsv0⟩
      · exact ⟨hlfN, hlf0⟩
      · exact ⟨hcfN, hcf0⟩
    exact { principal_norm := hp.1
            principal_pos := hp.2
            principal_exact := hexact principal List.mem_cons_self
            fees_norm := fun fee hf => (hfee fee hf).1
            fees_nonneg := fun fee hf => (hfee fee hf).2
            originationFee_le := (operator_le_iff _ _ hoN hp.1).mp hole
            originationFee_exact := hexact fees.originationFee (by simp [LoanFees.amountFields])
            interestRate_cap := hir
            lateInterestRate_cap := hlr
            closeInterestRate_cap := hcr
            overpaymentInterestRate_cap := hor
            overpaymentFee_cap := hof
            paymentInterval_min := hint
            gracePeriod_range := ⟨hg1, hg2⟩
            fits := hfits }
  · cases hpre


/-- A LoanSet past its broker lookup fails the model only in its checks or in the create. -/
lemma LendingLedger.loanSetChecked_error (l : LendingLedger) (i : Nat) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (twoStep ao : Bool)
    (checks : Except Error TER) (e : Error)
    (h : (l.loanSetChecked i broker principal rates fees schedule twoStep ao checks).run = .error e) :
    checks = .error e ∨
      (checks = .ok .tesSUCCESS ∧
        (Loan.create broker l.vault principal rates fees schedule ao twoStep).run = .error e) := by
  unfold LendingLedger.loanSetChecked at h
  cases checks with
  | error e' =>
    left
    have : e' = e := by simpa [ExceptT.run, ExceptT.mk] using h
    rw [this]
  | ok ter =>
    right
    dsimp only at h
    by_cases ht : ter.isTesSuccess = true
    · rw [if_neg (by simp [ht])] at h
      exact ⟨by rw [(TER.isTesSuccess_iff _).mp ht], TerExcept.map_error h⟩
    · rw [if_pos (by simp [ht])] at h
      cases h

/-- A LoanSet that fails the model found its broker and failed in the checks or the create. -/
lemma LendingLedger.applyLoanSet_error (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (twoStep ao : Bool) (e : Error)
    (h : (l.applyLoanSet i principal rates fees schedule twoStep ao).run = .error e) :
    ∃ broker, l.broker? i = some broker ∧
      (l.loanSetChecked i broker principal rates fees schedule twoStep ao
        (Loan.canCreate broker l.vault principal fees schedule l.now twoStep)).run = .error e := by
  unfold LendingLedger.applyLoanSet at h
  obtain ⟨t, ht⟩ : ∃ t, schedule.checkTimeAvailability = .ok t := by
    rw [LoanSchedule.checkTimeAvailability_eq]; split <;> exact ⟨_, rfl⟩
  rw [ht] at h
  dsimp only at h
  by_cases hs : t.isTesSuccess = true
  · rw [if_neg (by simp [hs])] at h
    cases hb : l.broker? i with
    | none => rw [hb] at h; cases h
    | some broker => rw [hb] at h; exact ⟨broker, rfl, h⟩
  · rw [if_pos (by simp [hs])] at h; cases h

/-- On an integral asset a zero-rate total value is within twenty units of PrincipalRequested. `P / n × n`
moves by less than `2·10^-18` of PrincipalRequested, and the whole-unit rounding by at most a half. -/
private lemma computeLoanProperties_zero_rate_close (principal : Number) (interval n : UInt32) (mgmt : TenthBips16)
    (nt : NumericType) (minScale : Int) (props : LoanProperties) (hp : principal.isNormalized)
    (hn : 0 < n) (hint : nt.isIntegral = true) (hP1 : 1 ≤ principal.toRat) (hP63 : principal.toRat < 2 ^ 63)
    (h : computeLoanProperties principal 0 interval n mgmt nt minScale = .ok props) :
    |props.totalValueOutstanding.toRat - principal.toRat| < 20 := by
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, -, -, -⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ h
  have hr0 := loanPeriodicRate_zero _ rate hrt
  have hmode : valueMode rate = .to_nearest := by rw [hr0]; rfl
  rw [hmode] at hamt hst' htvo
  rw [hr0] at hpp
  have hP0 : 0 < principal.toRat := by linarith
  have hPmin : (10 : ℚ) ^ (-10 : ℤ) ≤ principal.toRat := le_trans (by norm_num) hP1
  have hn' : n ≠ 0 := by intro h0; rw [h0] at hn; exact absurd hn (by decide)
  have hdiv := loanPeriodicPayment_zero_rate _ _ _ hp hP0.ne' hn' hpp
  have hN := Number.ofInt64_isNormalized n.toInt64
  have hNv := Number.ofInt64_count n
  have hn0 : (0 : ℚ) < n.toNat := by
    rw [UInt32.lt_iff_toNat_lt] at hn; exact_mod_cast hn
  have hn32 : (n.toNat : ℚ) < 10 ^ (10 : ℕ) := by
    have := n.toNat_lt; have : n.toNat < 10 ^ 10 := by omega
    exact_mod_cast this
  have hmode' : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  have hw : ∀ e : ℕ, e ≤ 30 → ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (-(e : ℤ)) := by
    intro e he
    obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (-(e : ℤ)) (by norm_num)
      (by unfold minExponent maxExponent; omega)
    exact ⟨w, hwn, by rw [hwv]; simp⟩
  -- the payment is positive, at least `10^-20`
  have hppN := Number.operator_div_isNormalized _ _ _ _ hp hN hdiv
  have hR1 := operator_div_rounded_to_nearest _ _ _ hp hN hdiv
  obtain ⟨w20, hw20, hw20v⟩ := hw 20 (by norm_num)
  have hpp20 : (10 : ℚ) ^ (-((20 : ℕ) : ℤ)) ≤ props.periodicPayment.toRat := by
    have := hR1.ge_of_le hmode' w20 hw20 (by
      rw [hw20v, hNv, le_div_iff₀ hn0]
      calc (10 : ℚ) ^ (-((20 : ℕ) : ℤ)) * n.toNat ≤ 10 ^ (-((20 : ℕ) : ℤ)) * 10 ^ (10 : ℕ) :=
            mul_le_mul_of_nonneg_left hn32.le (by positivity)
        _ = 10 ^ (-10 : ℤ) := by norm_num
        _ ≤ principal.toRat := hPmin)
    rwa [hw20v] at this
  have hpp0 : 0 < props.periodicPayment.toRat := lt_of_lt_of_le (by positivity) hpp20
  have hpp_ne : props.periodicPayment.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hpp0; exact lt_irrefl _ hpp0
  -- the two roundings of `P / n × n` move it by less than `2·10^-18` of itself
  have hW1 := operator_div_rounds_to_nearest _ _ _ hp hN hdiv hpp_ne
  simp only [RoundsWithin] at hW1
  change |props.periodicPayment.toRat - principal.toRat / _| ≤ _ at hW1
  rw [hNv] at hW1
  set nq : ℚ := (n.toNat : ℚ)
  set P := principal.toRat
  set pp := props.periodicPayment.toRat
  have hq0 : 0 < P / nq := div_pos hP0 hn0
  rw [abs_of_pos hq0] at hW1
  have hε1 : (6 : ℚ) / (2 ^ 63 - 3) ≤ 7 / 10 ^ 19 := by norm_num
  have hε2 : (5 : ℚ) / (2 ^ 63 + 7) ≤ 6 / 10 ^ 19 := by norm_num
  have hppn : |pp * nq - P| ≤ P * (7 / 10 ^ 19) := by
    have h1 : pp * nq - P = (pp - P / nq) * nq := by field_simp
    rw [h1, abs_mul, abs_of_pos hn0]
    calc |pp - P / nq| * nq ≤ (P / nq * (6 / (2 ^ 63 - 3))) * nq := mul_le_mul_of_nonneg_right hW1 hn0.le
      _ = P * (6 / (2 ^ 63 - 3)) := by field_simp
      _ ≤ P * (7 / 10 ^ 19) := mul_le_mul_of_nonneg_left hε1 hP0.le
  -- `amount` is at least `10^-11`, so nonzero
  have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
  have hRa := operator_mul_rounded_to_nearest _ _ amount hppN hN hamt
  obtain ⟨w11, hw11, hw11v⟩ := hw 11 (by norm_num)
  have hamt11 : (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ amount.toRat := by
    have := hRa.ge_of_le hmode' w11 hw11 (by
      rw [hw11v, hNv]
      change _ ≤ pp * nq
      have := (abs_le.mp hppn).1
      have h2 : (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ P * (1 - 7 / 10 ^ 19) := by
        calc (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ 10 ^ (-10 : ℤ) * (1 - 7 / 10 ^ 19) := by norm_num
          _ ≤ P * (1 - 7 / 10 ^ 19) := mul_le_mul_of_nonneg_right hPmin (by norm_num)
      calc (10 : ℚ) ^ (-((11 : ℕ) : ℤ)) ≤ P * (1 - 7 / 10 ^ 19) := h2
        _ = P - P * (7 / 10 ^ 19) := by ring
        _ ≤ pp * nq := by linarith [this])
    rwa [hw11v] at this
  have hamt0 : 0 ≤ amount.toRat := le_trans (by positivity) hamt11
  have hm0 : amount.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hamt11
    exact absurd hamt11 (not_le.mpr (by positivity))
  have hW2 := operator_mul_rounds_to_nearest _ _ _ hppN hN hamt hm0
  simp only [RoundsWithin] at hW2
  change |amount.toRat - props.periodicPayment.toRat * _| ≤ _ at hW2
  rw [hNv, abs_of_pos (mul_pos hpp0 hn0)] at hW2
  have hppn2 : pp * nq ≤ 2 * P := by have := (abs_le.mp hppn).2; nlinarith
  have hdist : |amount.toRat - P| ≤ P * (2 / 10 ^ 18) := by
    calc |amount.toRat - P| ≤ |amount.toRat - pp * nq| + |pp * nq - P| := abs_sub_le _ _ _
      _ ≤ pp * nq * (6 / 10 ^ 19) + P * (7 / 10 ^ 19) := by
        gcongr
        exact hW2.trans (mul_le_mul_of_nonneg_left hε2 (by positivity))
      _ ≤ P * (2 / 10 ^ 18) := by nlinarith
  -- the whole-unit amount is within a half of `amount`, and the total value is that amount
  have hneg := Number.negative_false_of_nonneg amount hamtN hamt0
  have hhalf := STAmount.ofNumber_integral_within_half _ amount amountSt hint hamtN hneg hst'
  unfold STAmount.roundToNumericType at htvo
  rw [hst'] at htvo
  have hty := STAmount.ofNumber_mNumericType _ _ _ amountSt hst'
  have hsint : amountSt.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
  simp only [hsint, if_true] at htvo
  have hic := (STAmount.ofNumber_integral_canonical _ _ _ amountSt hint hst').1
  have hsz : amountSt.mValue.toNat ≤ 2 ^ 63 - 1 := by
    by_cases hz : amountSt.mValue = 0
    · rw [hz]; decide
    · exact ((STAmount.ofNumber_exactCanonical _ amount _ amountSt hamtN hamt0 hst' hz).integralCanonical
        hsint).2
  obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact amountSt _ hic hsz
  rw [hsn, Except.ok.injEq] at htvo
  rw [← htvo, hv]
  have h18 : P * (2 / 10 ^ 18) < 19 := by nlinarith
  calc |amountSt.toRat - P| ≤ |amountSt.toRat - amount.toRat| + |amount.toRat - P| := abs_sub_le _ _ _
    _ < 20 := by linarith

/-- A zero-rate loan on an integral asset lends below `10^17` units once its checks passed. Its interest
is at least `-10^7` units, so the passed Open-limit check keeps AssetsAvailable, and the principal, low. -/
private lemma Loan.create_zero_rate_lt (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number) (hpre : Loan.CreatePreflight broker principal rates fees schedule)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal')
    (hmax : broker.numericType.isIntegral = true → broker.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hvi : v.numericType.isIntegral = true) (hint : broker.numericType.isIntegral = true)
    (hir : rates.interestRate = 0) : principal.toRat < 10 ^ 17 := by
  have hp := hpre.principal_norm
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  have hbase := Vault.baseExponent_scale_range v
  have hb0 := Vault.baseExponent_integral v hvi
  -- PrincipalRequested is a whole number of units, at most `2^63 - 1`
  have hrep := ((STAmount.isRounded_eq_false_iff _ _ hp hpos.le).mp hst).resolve_left hpos.ne'
  obtain ⟨k, hk63, hPk⟩ : ∃ k : ℕ, k ≤ 2 ^ 63 - 1 ∧ principal.toRat = k := by
    cases hnt : broker.numericType with
    | fractional => rw [hnt] at hint; cases hint
    | integral mv mo ms msh =>
      rw [hnt] at hrep
      obtain ⟨-, k, -, hk, hkv⟩ := hrep
      exact ⟨k, hk, hkv⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [hPk, h0] at hpos; simp at hpos
    · exact h0
  have hP1 : 1 ≤ principal.toRat := by rw [hPk]; exact_mod_cast hk1
  have hP63 : principal.toRat < 2 ^ 63 := by
    rw [hPk]
    have hk' : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
    linarith [show (2 : ℚ) ^ 63 = 9223372036854775808 by norm_num]
  -- the total value is within twenty units of the principal
  have hprops := hchecks.properties_ok
  rw [hir] at hprops
  have hclose := computeLoanProperties_zero_rate_close principal _ _ _ _ _ _ hp hpre.fits.paymentTotal_pos hint hP1
    hP63 hprops
  obtain ⟨-, hls0⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hprops hbase.2
  have hls := hls0 hint
  obtain ⟨_, _, _, ti, -, -, -, -, -, htvo, hpo, hti, hmfo⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ hprops
  rw [hls] at hpo hmfo
  have htvN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest 0 hp hpos.le
      (Or.inl rfl) ⟨by norm_num, by norm_num⟩ (fun _ => rfl) hst k (by rw [hPk]; simp)
      (fun hf => by rw [hf] at hint; cases hint) hpo
  have hw : ∀ a : ℤ, -2 ^ 63 < a ∧ a < 2 ^ 63 → ∃ w : Number, w.isNormalized ∧ w.toRat = (a : ℚ) := by
    intro a ha
    obtain ⟨w, hwn, hwv⟩ := Number.exists_normalized_int_mul_pow a 0 ha (by unfold minExponent maxExponent; omega)
    exact ⟨w, hwn, by rw [hwv]; simp⟩
  have hmode : rounding_mode.to_nearest = .to_nearest ∨ rounding_mode.to_nearest = .upward ∨
      rounding_mode.to_nearest = .downward := Or.inl rfl
  -- the interest the fee is taken on is at most twenty units
  have htiN := operator_sub_isNormalized_to_nearest_sz _ _ _ htvN hpoN hti
  obtain ⟨w20, hw20, hw20v⟩ := hw 20 (by norm_num)
  have hti20 : ti.toRat ≤ 20 := by
    have := Number.RoundsToRepresentable.le_of_le_normalized _ _
      (operator_sub_rounded_to_nearest _ _ _ htvN hpoN hti) w20 hw20 (by
      rw [hw20v, hpov]; push_cast; linarith [(abs_lt.mp hclose).2])
    rwa [hw20v] at this
  -- so the management fee is at most `10^6` units
  have hmf : props.managementFeeOutstanding.toRat ≤ 10 ^ 6 := by
    have heq : computeManagementFee broker.numericType ti broker.managementFeeRate 0 =
        (tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest) >>=
          (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some 0)) := rfl
    rw [heq] at hmfo
    obtain ⟨raw, hraw, hmfo⟩ := bind_ok_peel _ _ _ hmfo
    have heq2 : tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest =
        (ti.operator_mul broker.managementFeeRate.toTenthBips32.toNumber .to_nearest) >>=
          (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
    rw [heq2] at hraw
    obtain ⟨pr, hpr, hraw⟩ := bind_ok_peel _ _ _ hraw
    obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts broker.managementFeeRate.toTenthBips32
    obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
    have hu5 : kTenthBipsPerUnity.toNumber.toRat = 100000 := by rw [huv]; rfl
    have hr32 : (broker.managementFeeRate.toTenthBips32.toNat : ℚ) < 2 ^ 32 := by
      have := broker.managementFeeRate.toTenthBips32.toNat_lt_size
      have hs : UInt32.size = 2 ^ 32 := rfl
      rw [hs] at this; exact_mod_cast this
    have hr0 : (0 : ℚ) ≤ broker.managementFeeRate.toTenthBips32.toNat := by positivity
    have hprN := Number.operator_mul_isNormalized _ _ pr _ htiN hrn hpr
    obtain ⟨w11, hw11, hw11v⟩ := hw (10 ^ 11) (by norm_num)
    have hpr11 : pr.toRat ≤ 10 ^ 11 := by
      have := Number.RoundsToRepresentable.le_of_le_normalized _ _
        (operator_mul_rounded_to_nearest _ _ _ htiN hrn hpr) w11 hw11 (by
        rw [hw11v, hrv]; push_cast
        rcases le_total 0 ti.toRat with h0 | h0
        · nlinarith
        · nlinarith)
      rwa [hw11v] at this
    have hrawN := Number.operator_div_isNormalized _ _ raw _ hprN hun hraw
    obtain ⟨w6, hw6, hw6v⟩ := hw (10 ^ 6) (by norm_num)
    have hraw6 : raw.toRat ≤ 10 ^ 6 := by
      have := Number.RoundsToRepresentable.le_of_le_normalized _ _
        (operator_div_rounded_to_nearest _ _ _ hprN hun hraw) w6 hw6 (by
        rw [hw6v, hu5, div_le_iff₀ (by norm_num)]; push_cast; linarith)
      rwa [hw6v] at this
    unfold STAmount.roundToNumericType at hmfo
    cases hof : STAmount.ofNumber broker.numericType raw .downward with
    | error e => rw [hof] at hmfo; cases hmfo
    | ok ret =>
      rw [hof] at hmfo
      have hty := STAmount.ofNumber_mNumericType _ _ _ ret hof
      have hsint : ret.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
      simp only [hsint, if_true] at hmfo
      have hic := (STAmount.ofNumber_integral_canonical _ _ _ ret hint hof).1
      have hsz : ret.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have := hic.in_range
        rw [hty] at this
        have hmr := hmax hint
        have hmr' : maxRep.toNat = 9223372036854775807 := by decide
        omega
      obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact ret _ hic hsz
      rw [hsn, Except.ok.injEq] at hmfo
      rw [← hmfo, hv]
      by_cases h0 : 0 ≤ raw.toRat
      · have := STAmount.ofNumber_downward_le_max _ raw ret hrawN (fun _ => h0) hof
        rw [max_eq_left h0] at this
        linarith
      · push Not at h0
        have hneg : raw.negative_ = true := by
          cases hn : raw.negative_
          · have := Number.toRat_nonneg_of_nonnegative raw hn; linarith
          · rfl
        have := STAmount.ofNumber_integral_negative_nonpos _ raw _ ret hint hneg hof
        linarith
  -- the interest of the new loan is at least `-(10^6 + 20)` units
  obtain ⟨hsT, hsP, hsM, v1, hv1, hid⟩ := LoanState.build_ok hchecks.state
  have hmfN : props.managementFeeOutstanding.isNormalized := by
    have heq : computeManagementFee broker.numericType ti broker.managementFeeRate 0 =
        (tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest) >>=
          (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some 0)) := rfl
    rw [heq] at hmfo
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ hmfo
    exact STAmount.roundToNumericType_isNormalized _ _ _ _ _ h
  have hv1N := operator_sub_isNormalized_to_nearest_sz _ _ _ htvN hp hv1
  obtain ⟨wm, hwm, hwmv⟩ := hw (-20) (by norm_num)
  have hv1lo : -20 ≤ v1.toRat := by
    have := (operator_sub_rounded_to_nearest _ _ _ htvN hp hv1).ge_of_le hmode wm hwm (by
      rw [hwmv]; push_cast; linarith [(abs_lt.mp hclose).1])
    rwa [hwmv] at this
  have hiN := operator_sub_isNormalized_to_nearest_sz _ _ _ hv1N hmfN hid
  obtain ⟨wi, hwi, hwiv⟩ := hw (-(10 ^ 6 + 20)) (by norm_num)
  have hilo : -(10 ^ 6 + 20) ≤ loanState.interestDue.toRat := by
    have := (operator_sub_rounded_to_nearest _ _ _ hv1N hmfN hid).ge_of_le hmode wi hwi (by
      rw [hwiv]; push_cast; linarith)
    rw [hwiv] at this; push_cast at this; linarith
  -- the passed Open-limit check keeps AssetsAvailable, and so the principal, below `10^17` units
  obtain ⟨hAA, -, -⟩ := Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiN hchecks.open_zone
  rw [hb0] at hAA
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h2 := hchecks.funds
    by_contra hlt
    push Not at hlt
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hlt] at h2
    exact absurd h2 (by decide)
  norm_num at hAA
  linarith

/-- A LoanSet on a reachable ledger never fails its lawfulness re-check. `hcount` - LoanCount does not wrap.
C++ LoanSequence stops a broker before `2^32` loans. -/
lemma LendingLedger.loanSet_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (paymentInterval paymentTotal gracePeriod : Option UInt32)
    (startDate : UInt32) (twoStep allowsOverpayment : Bool)
    (hcount : ∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) :
    (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_loan rfl
  intro hpre _ h
  obtain ⟨broker, hb, h1⟩ := LendingLedger.applyLoanSet_error l i principal rates fees _ twoStep allowsOverpayment
    .notLawful h
  rcases LendingLedger.loanSetChecked_error l i broker principal rates fees _ twoStep allowsOverpayment _ _ h1 with
    hc | ⟨hc', hcr⟩
  · exact Loan.canCreate_ne_notLawful _ _ _ _ _ _ _ hc
  set schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep
  have hpf := LendingTx.loanSet_createPreflight l i principal rates fees paymentInterval paymentTotal
    gracePeriod startDate twoStep allowsOverpayment broker hpre hc'
  have hnt := hr.scaleInv.brokers i broker hb
  refine Loan.create_ne_notLawful broker l.vault principal rates fees schedule allowsOverpayment twoStep hpf
    hr.holdsAsset (hcount broker hb) (fun props loanState debtTotal' hchecks => ?_) hcr
  -- the principal sits within AssetsAvailable, below `10^16` base units on an IOU
  have hfunds : principal.toRat ≤ l.vault.assetsAvailable.toRat := by
    have h2 := hchecks.funds
    by_contra hlt
    push Not at hlt
    rw [(operator_lt_iff _ _ l.vault.wf.assetsAvailable_norm hpf.principal_norm).mpr hlt] at h2
    exact absurd h2 (by decide)
  have hfrac : broker.numericType = .fractional →
      principal.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    intro hfr
    obtain ⟨atot, hat, hexp⟩ := Loan.canCreate_exponent broker l.vault principal fees schedule l.now twoStep
      hc'
    obtain ⟨hatN, hatge⟩ := Vault.assetsTotal_ge_available l.vault atot hat
    rw [hfr] at hexp
    have hbase := Vault.baseExponent_scale_range l.vault
    have hlt := numberExponent_frac_lt atot _ _ hatN (by omega) hexp
    rw [show l.vault.baseExponent + 16 = 16 + l.vault.baseExponent by ring, zpow_add₀ (by norm_num)] at hlt
    norm_num at hlt
    linarith
  -- a zero-rate loan on XRP or an MPT lends below `10^17` units
  have hint : broker.numericType.isIntegral = true → rates.interestRate = 0 → principal.toRat < 10 ^ 17 :=
    fun hi hir => Loan.create_zero_rate_lt broker l.vault principal rates fees schedule props loanState debtTotal'
      hpf hchecks (fun _ => by rw [hnt]; exact hr.holdsAsset.maxValue_le (by rw [← hnt]; exact hi))
      (by rw [← hnt]; exact hi) hi hir
  obtain ⟨hiN, hi0⟩ := Loan.create_checks_interest broker l.vault principal rates fees schedule props
    loanState debtTotal' hpf hfrac hint hchecks
  exact hr.createGrid_of_checks hb hchecks hiN hi0


end XRPL.Model.Lending
