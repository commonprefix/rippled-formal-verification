import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.XrpTotal
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetChecks
import XRPL.Properties.Lending.Ledger.Common.RecheckLoanSet
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # LoanSet never ends in an exception

On a reachable ledger a LoanSet returns a result code while PeriodicPayment × PaymentTotal fits XRP or an MPT.
An MPT vault total of `2^63` or `2^63 + 1` is stored rounded down, so there the sum itself is assumed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private canFundLoan checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet
open private Loan.createChecks_of_steps from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Loan.create_checks_interest Loan.create_zero_rate_lt
  from XRPL.Properties.Lending.Ledger.Common.RecheckLoanSet
open private Vault.assetsTotal_ge_available from XRPL.Properties.Lending.Loan.Common.SetScale
open private STAmount.roundsInRange_of_le_max from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetValue
open private STAmount.roundsInRange_of_representable isRounded_computes LoanState.build_computes
  Vault.exceedsOpenLimit_computes from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetChecks

/-- The vault scale a LoanSet reads computes while AssetsAvailable + AssetsDeployed is an amount of the asset. -/
private lemma Vault.exponent_computes (v : Vault) (nt : NumericType)
    (hts : XRPL.Model.SingleAssetVault.TotalStores nt v.assetsAvailable v.assetsDeployed) :
    ∃ E, AssetPool.exponent v nt = .ok E := by
  obtain ⟨atot, st, hat, hst⟩ := hts
  have hat' : v.assetsTotal = .ok atot := hat
  unfold AssetPool.exponent
  rw [Vault.pool_assetsTotal, hat', ok_bind]
  unfold numberExponent
  by_cases hz : atot.operator_eq Number.zero = true
  · rw [ite_eq_left hz]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hz, hst, ok_bind]
    exact ⟨_, rfl⟩

/-- The LoanSet checks return a result code once the vault scale computes. -/
lemma Loan.canCreate_ne_error (broker : LoanBroker) (v : Vault) (principal : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (now : UInt32) (twoStep : Bool)
    (hexp : ∃ E, AssetPool.exponent v broker.numericType = .ok E) (e : Error) :
    Loan.canCreate broker v principal fees schedule now twoStep ≠ .error e := by
  obtain ⟨E, hE⟩ := hexp
  have hfund : canFundLoan v schedule now broker.numericType ≠ .error e := by
    intro h
    unfold canFundLoan at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    walk_ok
    all_goals simp_all
  have hprec : checkPrecisionFields principal fees
      (fun value => pure !(STAmount.isRounded broker.numericType value)) ≠ .error e := by
    obtain ⟨t, ht⟩ := checkPrecisionFields_computes principal fees
      (fun value => pure !(STAmount.isRounded broker.numericType value)) (fun x _ => ⟨_, rfl⟩)
    rw [ht]; exact nofun
  have hsched : schedule.checkTimeAvailability ≠ .error e := by
    rw [LoanSchedule.checkTimeAvailability_eq]; split <;> exact nofun
  intro h
  unfold Loan.canCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all

/-- A create never fails the model on a vault and a broker as a reachable ledger keeps them, while on XRP or an
MPT PeriodicPayment × PaymentTotal is within the asset's maximum (`hvalue`). -/
lemma Loan.create_ne_error (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hasset : Vault.HoldsAsset v)
    (hnt : broker.numericType = v.numericType) (hcount : broker.loanCount + 1 ≠ 0)
    (hgrid : ∀ props loanState debtTotal', Loan.CreateChecks broker v principal rates fees schedule props loanState
      debtTotal' → Loan.CreateGrid broker v)
    (hexact : ∀ x ∈ principal :: fees.amountFields, STAmount.isRounded broker.numericType x = false)
    (hfrac : broker.numericType = .fractional → v.assetsAvailable.toRat < 10 ^ 16)
    (hvalue : broker.numericType.isIntegral = true → ∀ rate pp : Number,
      loanPeriodicRate rates.interestRate schedule.paymentInterval = .ok rate →
      loanPeriodicPayment principal rate schedule.paymentTotal = .ok pp →
      pp.toRat * schedule.paymentTotal.toNat ≤ broker.numericType.maxValue.toNat)
    (hbal : v.assetsAvailable.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat < 10 ^ 100)
    (hK : ∃ K : ℕ, K < 2 ^ 63 ∧ broker.debtTotal.toRat + v.assetsAvailable.toRat ≤ K ∧
      ∀ w : ℚ, 0 ≤ w → w ≤ K → STAmount.RoundsInRange broker.numericType .upward w)
    (e : Error) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run ≠ .error e := by
  intro h
  have hp := hpre.principal_norm

  -- a principal above AssetsAvailable is rejected before any computation
  by_cases hf : v.assetsAvailable.operator_lt principal = true
  · rw [Loan.create_insufficient_funds_proof broker v principal rates fees schedule allowsOverpayment pending hf]
      at h
    cases h
  have hPle : principal.toRat ≤ v.assetsAvailable.toRat := by
    by_contra hlt
    push Not at hlt
    exact hf ((Number.operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hlt)
  have hfrac' : broker.numericType = .fractional → principal.toRat < 10 ^ 16 :=
    fun hfr => lt_of_le_of_lt hPle (hfrac hfr)
  have hbnt : broker.numericType = .fractional ∨ broker.numericType = NumericType.native ∨
      broker.numericType = NumericType.int64 := by rw [hnt]; exact hasset
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  have hbase := Vault.baseExponent_scale_range v
  have hir : rates.interestRate.toNat ≤ 100000 := UInt32.le_iff_toNat_le.mp hpre.interestRate_cap
  have hiv : 60 ≤ schedule.paymentInterval.toNat := UInt32.le_iff_toNat_le.mp hpre.paymentInterval_min
  have hn0 : schedule.paymentTotal ≠ 0 := by
    intro h0
    have := hpre.fits.paymentTotal_pos
    rw [h0] at this
    exact absurd this (by decide)
  have hk : schedule.paymentTotal.toNat * schedule.paymentInterval.toNat < 2 ^ 32 := by
    have := hpre.fits.ends_in_time
    have hmax : maxTime.toNat = 2 ^ 32 - 1 := rfl
    omega
  have hmgmt : broker.managementFeeRate.toNat ≤ 10000 :=
    UInt16.le_iff_toNat_le.mp broker.valid.managementFeeRate_cap
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hD0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  obtain ⟨K, hK63, hKle, hKfit⟩ := hK
  have hKq : (K : ℚ) < 2 ^ 63 := by exact_mod_cast hK63
  have hp96 : principal.toRat < 10 ^ 96 :=
    STAmount.Representable.lt_pow _ _ ((STAmount.isRounded_eq_false_iff _ _ hp hpos.le).mp hst)
  have hpabs : |principal.toRat| < 10 ^ 100 := by
    rw [abs_of_nonneg hpos.le]; linarith [show (10 : ℚ) ^ 96 < 10 ^ 100 by norm_num]

  -- the values of the loan compute, with their sizes
  have hclp := computeLoanProperties_computes principal rates.interestRate schedule.paymentInterval
    schedule.paymentTotal broker.managementFeeRate broker.numericType v.baseExponent hp hpos hst hir hiv hn0 hk
    hmgmt hbnt hbase hfrac' hvalue
  have hsized : ∀ props, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      props.SetSizes broker.numericType := by
    intro props h
    obtain ⟨p', hp', hsz⟩ := hclp
    obtain rfl := Except.ok.inj (hp'.symm.trans h)
    exact hsz
  have htvoabs : ∀ props : LoanProperties, props.SetSizes broker.numericType →
      |props.totalValueOutstanding.toRat| < 10 ^ 100 := by
    intro props hsz
    obtain ⟨k, hk63, hkv⟩ := hsz.totalValue_units
    have hkq : (k : ℚ) < 2 ^ 63 := by exact_mod_cast hk63
    have hp10 : (10 : ℚ) ^ props.loanScale ≤ 10 ^ 30 := by
      have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hsz.loanScale_range.2
      norm_num at this ⊢
      exact this
    rw [abs_of_nonneg hsz.totalValue_nonneg, hkv]
    calc (k : ℚ) * 10 ^ props.loanScale ≤ 2 ^ 63 * 10 ^ 30 := by gcongr
      _ < 10 ^ 100 := by norm_num

  -- each step before the vault update returns a value
  have key1 : computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) ≠ .error e := by
    intro he
    obtain ⟨p', hp', -⟩ := hclp
    exact absurd (hp'.symm.trans he) (by simp)
  have key2 : ∀ props, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      checkPrecisionFields principal fees (fun value => isRounded value props.loanScale broker.numericType) ≠
        .error e := by
    intro props h
    have hls := (hsized props h).loanScale_range
    obtain ⟨t, ht⟩ := checkPrecisionFields_computes principal fees
      (fun value => isRounded value props.loanScale broker.numericType) (fun x hx => by
        have hxN : x.isNormalized := by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hp
          · exact hpre.fees_norm x hx'
        have hx0 : 0 ≤ x.toRat := by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hpos.le
          · exact hpre.fees_nonneg x hx'
        exact isRounded_computes broker.numericType hbnt x props.loanScale hxN hx0 (hexact x hx)
          ⟨by omega, by omega⟩)
    rw [ht]; exact nofun
  have key3 : ∀ props, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      props.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType ≠ .error e := by
    intro props h
    obtain ⟨t, ht⟩ := LoanProperties.checkGuards_computes props broker.numericType hbnt (hsized props h) principal
      hp (by linarith [show (10 : ℚ) ^ 100 < 10 ^ 200 by norm_num]) rates.interestRate schedule.paymentTotal
    rw [ht]; exact nofun
  have hstate : ∀ props, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      ∃ st, LoanState.build props.totalValueOutstanding principal props.managementFeeOutstanding = .ok st ∧
        st.interestDue.isNormalized ∧ |st.interestDue.toRat| < 10 ^ 102 := by
    intro props h
    have hsz := hsized props h
    exact LoanState.build_computes _ _ _ hsz.totalValue_norm hp hsz.managementFee_norm (htvoabs props hsz) hpabs
      hsz.managementFee_abs
  have key4 : ∀ props, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      LoanState.build props.totalValueOutstanding principal props.managementFeeOutstanding ≠ .error e := by
    intro props h
    obtain ⟨st, hst', -⟩ := hstate props h
    rw [hst']; exact nofun
  have key5 : ∀ props st, computeLoanProperties principal rates.interestRate schedule.paymentInterval
      schedule.paymentTotal broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props →
      LoanState.build props.totalValueOutstanding principal props.managementFeeOutstanding = .ok st →
      AssetPool.exceedsOpenLimit v st.interestDue ≠ .error e := by
    intro props st h hb
    obtain ⟨st', hst', hidN, hidabs⟩ := hstate props h
    obtain rfl := Except.ok.inj (hst'.symm.trans hb)
    obtain ⟨b, hb'⟩ := Vault.exceedsOpenLimit_computes v st'.interestDue hidN
      (by linarith [show (10 : ℚ) ^ 102 < 10 ^ 190 by norm_num]) hbal
    rw [Vault.pool_exceedsOpenLimit, hb']; exact nofun
  have hD200 : |broker.debtTotal.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg hD0]; linarith [show (2 : ℚ) ^ 63 < 10 ^ 200 by norm_num]
  have hP200 : |principal.toRat| < 10 ^ 200 := by linarith [show (10 : ℚ) ^ 100 < 10 ^ 200 by norm_num]
  have key6 : broker.debtTotal.operator_add principal .to_nearest ≠ .error e := by
    obtain ⟨d, hd⟩ := Number.operator_add_ok_of_abs broker.debtTotal principal .to_nearest
      broker.wf.debtTotal_norm hp hD200 hP200
    rw [hd]; exact nofun
  have key7 : ∀ d, broker.debtTotal.operator_add principal .to_nearest = .ok d →
      broker.checkLimits d (AssetPool.baseExponent v) ≠ .error e := by
    intro d hd
    -- the principal is within AssetsAvailable, so the new debt is at most `K`
    have hdN := Number.operator_add_isNormalized_to_nearest_sz _ _ d broker.wf.debtTotal_norm hp hd
    have hd0 : 0 ≤ d.toRat :=
      (Number.add_near _ _ _ broker.wf.debtTotal_norm hp hd).nonneg (by linarith)
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (K : ℤ) 0
      ⟨by have : (0 : ℤ) ≤ (K : ℤ) := by positivity
          linarith, by exact_mod_cast hK63⟩
      (by unfold minExponent maxExponent; norm_num)
    have hwv' : w.toRat = (K : ℚ) := by rw [hwv]; simp
    have hdK : d.toRat ≤ K := by
      have := Number.RoundsToRepresentable.le_of_le_normalized d _
        (Number.operator_add_rounded_to_nearest _ _ _ broker.wf.debtTotal_norm hp hd) w hw (by
          rw [hwv']; linarith)
      rwa [hwv'] at this
    obtain ⟨t, ht⟩ := LoanBroker.checkLimits_computes broker hbnt d v.baseExponent K hK63 hdN hd0 hdK hKfit
      ⟨by omega, by omega⟩
    rw [Vault.pool_baseExponent, ht]; exact nofun

  have h0 := h
  simp only [Loan.create] at h
  unfold_ter at h
  walk_ok
  · exact key1 ‹_›
  · exact key2 _ ‹_› ‹_›
  · exact key3 _ ‹_› ‹_›
  · exact key4 _ ‹_› ‹_›
  · exact key5 _ _ ‹_› ‹_› ‹_›
  · exact key6 ‹_›
  · exact key7 _ ‹_› ‹_›
  -- the vault update is reached only once every check passed, and then the create succeeds
  all_goals
    have hchecks := Loan.createChecks_of_steps broker v principal rates fees schedule _ _ _ _ _ _ _ ‹_› ‹_›
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    obtain ⟨loan, v', _, hrun⟩ := Loan.create_success_lawful broker v principal rates fees schedule
      allowsOverpayment pending _ _ _ hpre hasset (hgrid _ _ _ hchecks) hcount hchecks
    rw [hrun] at h0
    exact absurd h0 (by simp)

/-- LoanSet on a reachable ledger returns a result code, while on XRP or an MPT PeriodicPayment × PaymentTotal
(`hvalue`) is within the asset's maximum, and on an MPT AssetsAvailable + AssetsDeployed is (`htotal`). -/
lemma LendingLedger.loanSet_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (paymentInterval paymentTotal gracePeriod : Option UInt32)
    (startDate : UInt32) (twoStep allowsOverpayment : Bool)
    -- LoanCount does not wrap. C++ LoanSequence stops a broker before `2^32` loans
    (hcount : ∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0)
    -- an MPT total of `2^63` or `2^63 + 1` is stored rounded down, as `2^63 - 8`. XRP sums are exact
    (htotal : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat)
    (hvalue : l.vault.numericType.isIntegral = true → ∀ rate periodicPayment : Number,
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate →
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment →
      periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ≤ l.vault.numericType.maxValue.toNat) :
    ∃ r, (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok r := by
  cases hrun : (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, ha⟩ := LendingLedger.apply_error hrun
    simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at ha
    split at ha
    · cases ha
    have h := TerExcept.map_error ha
    obtain ⟨broker, hb, h1⟩ := LendingLedger.applyLoanSet_error l i principal rates fees _ twoStep
      allowsOverpayment e h
    have hasset := hr.holdsAsset
    -- on XRP the stored total is the exact sum, so it is within the maximum
    have htotal' : l.vault.numericType.isIntegral = true →
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat := by
      intro hint
      rcases hasset with h | h | h
      · rw [h] at hint; cases hint
      · exact hr.total_le_native h
      · exact htotal h
    have hnt := hr.scaleInv.brokers i broker hb
    have hbnt : broker.numericType = .fractional ∨ broker.numericType = NumericType.native ∨
        broker.numericType = NumericType.int64 := by rw [hnt]; exact hasset
    have hbase := Vault.baseExponent_scale_range l.vault
    have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
    have hp0 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
    have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
    have hYU0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg

    -- the balances of a reachable vault: AssetsDeployed and YieldUnrealized are below `10^16` base units
    obtain ⟨d, hd16, hdv⟩ := hr.deployed_units
    have hAD16 : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 := by
      have hdq : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16
      rw [hdv]
      calc (d : ℚ) * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 * 1 := by gcongr
        _ = 10 ^ 16 := by ring
    have hAArep := (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm hAA0).mp hr.availableStored
    have hAA96 := STAmount.Representable.lt_pow _ _ hAArep
    have hYU16 : l.vault.yieldUnrealized.toRat ≤ 10 ^ 16 := by
      have := hr.deployed_yield_le
      unfold LendingLedger.openLimit at this
      nlinarith
    have hbal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat <
        10 ^ 100 := by linarith [show (10 : ℚ) ^ 96 + 10 ^ 16 + 10 ^ 16 < 10 ^ 100 by norm_num]
    have hdebt : broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
      rw [hr.debtInv.debt i broker hb, hr.debtInv.deployed]
      exact l.brokerPrincipal_le i

    -- the vault scale computes: the vault stored its total as an amount of the asset
    have hexp : ∃ E, AssetPool.exponent l.vault broker.numericType = .ok E :=
      Vault.exponent_computes l.vault broker.numericType (by rw [hnt]; exact hr.totalStored)

    rcases LendingLedger.loanSetChecked_error l i broker principal rates fees _ twoStep allowsOverpayment _ _ h1 with
      hc | ⟨hc', hcr⟩
    · exact Loan.canCreate_ne_error broker l.vault principal fees _ l.now twoStep hexp e hc
    set schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep
    have hpf := LendingTx.loanSet_createPreflight l i principal rates fees paymentInterval paymentTotal
      gracePeriod startDate twoStep allowsOverpayment broker hpre hc'
    have hexact := Loan.canCreate_exact broker l.vault principal fees schedule l.now twoStep hc'

    -- an IOU vault that passed the LoanSet checks is at its base scale, below `10^16` base units
    have hAAfrac : broker.numericType = .fractional → l.vault.assetsAvailable.toRat < 10 ^ 16 := by
      intro hfr
      obtain ⟨atot, hat, hexp'⟩ := Loan.canCreate_exponent broker l.vault principal fees schedule l.now twoStep hc'
      obtain ⟨hatN, hatge⟩ := Vault.assetsTotal_ge_available l.vault atot hat
      rw [hfr] at hexp'
      have hlt := numberExponent_frac_lt atot _ _ hatN (by omega) hexp'
      rw [show l.vault.baseExponent + 16 = 16 + l.vault.baseExponent by ring, zpow_add₀ (by norm_num)] at hlt
      norm_num at hlt
      nlinarith

    -- DebtTotal and AssetsAvailable together are an amount of the asset
    have hK : ∃ K : ℕ, K < 2 ^ 63 ∧ broker.debtTotal.toRat + l.vault.assetsAvailable.toRat ≤ K ∧
        ∀ w : ℚ, 0 ≤ w → w ≤ K → STAmount.RoundsInRange broker.numericType .upward w := by
      rcases hbnt with hfr | hint'
      · refine ⟨10 ^ 18, by norm_num, ?_, fun w hw0 hwle => ?_⟩
        · have := hAAfrac hfr
          push_cast
          linarith [show (10 : ℚ) ^ 16 + 10 ^ 16 ≤ 10 ^ 18 by norm_num]
        · rw [hfr]
          simp only [STAmount.RoundsInRange]
          push_cast at hwle
          exact ⟨by linarith, by linarith [show (10 : ℚ) ^ 18 ≤ 9999999999999999 * 10 ^ 80 by norm_num]⟩
      · have hint : l.vault.numericType.isIntegral = true := by
          rw [← hnt]; rcases hint' with h' | h' <;> rw [h'] <;> rfl
        refine ⟨broker.numericType.maxValue.toNat, by rcases hint' with h' | h' <;> rw [h'] <;> decide, ?_,
          fun w hw0 hwle => STAmount.roundsInRange_of_le_max _ hint' .upward w hw0 hwle⟩
        have := htotal' hint
        rw [hnt]
        linarith

    refine Loan.create_ne_error broker l.vault principal rates fees schedule allowsOverpayment twoStep hpf hasset
      hnt (hcount broker hb) (fun props loanState debtTotal' hchecks => ?_) hexact hAAfrac
      (fun hint => by rw [hnt]; exact hvalue (by rw [← hnt]; exact hint)) hbal hK e hcr

    -- a create whose checks passed reads its vault and broker on the base grid
    have hfunds : principal.toRat ≤ l.vault.assetsAvailable.toRat := by
      have h2 := hchecks.funds
      by_contra hlt
      push Not at hlt
      rw [(Number.operator_lt_iff _ _ l.vault.wf.assetsAvailable_norm hpf.principal_norm).mpr hlt] at h2
      exact absurd h2 (by decide)
    have hfrac : broker.numericType = .fractional →
        principal.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent := by
      intro hfr
      obtain ⟨atot, hat, hexp'⟩ := Loan.canCreate_exponent broker l.vault principal fees schedule l.now twoStep hc'
      obtain ⟨hatN, hatge⟩ := Vault.assetsTotal_ge_available l.vault atot hat
      rw [hfr] at hexp'
      have hlt := numberExponent_frac_lt atot _ _ hatN (by omega) hexp'
      rw [show l.vault.baseExponent + 16 = 16 + l.vault.baseExponent by ring, zpow_add₀ (by norm_num)] at hlt
      norm_num at hlt
      linarith
    have hint : broker.numericType.isIntegral = true → rates.interestRate = 0 → principal.toRat < 10 ^ 17 :=
      fun hi hir => Loan.create_zero_rate_lt broker l.vault principal rates fees schedule props loanState debtTotal'
        hpf hchecks (fun _ => by rw [hnt]; exact hr.holdsAsset.maxValue_le (by rw [← hnt]; exact hi))
        (by rw [← hnt]; exact hi) hi hir
    obtain ⟨hiN, hi0⟩ := Loan.create_checks_interest broker l.vault principal rates fees schedule props
      loanState debtTotal' hpf hfrac hint hchecks
    exact hr.createGrid_of_checks hb hchecks hiN hi0

end XRPL.Model.Lending
