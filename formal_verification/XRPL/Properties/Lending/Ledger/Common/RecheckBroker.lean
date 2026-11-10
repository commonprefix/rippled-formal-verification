import XRPL.Properties.Lending.Ledger.Common.RecheckVault
import XRPL.Properties.Lending.Ledger.Common.RecheckLoan
import XRPL.Properties.Lending.Ledger.Common.RecheckLoanSet
import XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid

/-! # Broker transactions pass their lawfulness re-check

A broker transaction on a reachable ledger never fails the model with `notLawful`, and a cover clawback does not
either once the asset stores CoverAvailable exactly (C++ associateAsset, which the model leaves out). The preflight
keeps a new DebtMaximum and the rates in range, the checks keep a nonzero DebtMaximum at least DebtTotal and a
withdrawal within the cover, and a deposit never takes the cover below zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private STAmount.roundtrip_of_isRounded_false from XRPL.Properties.Protocol.STAmount.Common.Representable

lemma LoanBroker.canCreate_ne_notLawful (v : Vault) (dm : Option Number) (nt : NumericType) :
    LoanBroker.canCreate v dm nt ≠ .error .notLawful := by
  unfold LoanBroker.canCreate
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.isOnExponentGrid_ne_notLawful]

lemma LoanBroker.canUpdate_ne_notLawful (lb : LoanBroker) (v : Vault) (dm : Option Number) :
    lb.canUpdate v dm ≠ .error .notLawful := by
  unfold LoanBroker.canUpdate
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.isOnExponentGrid_ne_notLawful]

/-- An update that passed its checks has a zero DebtMaximum or one at least DebtTotal. -/
lemma LoanBroker.canUpdate_limit (lb : LoanBroker) (v : Vault) (d : Number)
    (h : lb.canUpdate v (some d) = .ok .tesSUCCESS) : (d.signum != 0 && d.operator_lt lb.debtTotal) = false := by
  unfold LoanBroker.canUpdate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i hc; simpa using hc

/-- The preflight of a LoanBrokerSet that creates a broker keeps DebtMaximum and the rates in range. -/
lemma LendingTx.preflight_loanBrokerCreate (l : LendingLedger) (tx : LoanBrokerSetCreate)
    (h : (LendingTx.loanBrokerCreate tx).preflight l = .tesSUCCESS) :
    (∀ d ∈ tx.debtMaximum, d.isNormalized ∧ Number.zero.operator_le d = true ∧
      d.operator_le debtMaximumCap = true) ∧
    tx.managementFeeRate.getD 0 ≤ maxManagementFeeRate ∧ tx.coverRateMinimum.getD 0 ≤ maxCoverRate ∧
    tx.coverRateLiquidation.getD 0 ≤ maxCoverRate ∧
    (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0) := by
  cases hdmo : tx.debtMaximum with
  | none =>
    simp only [LendingTx.preflight, hdmo] at h
    split at h
    · rename_i hc
      simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hfee, hmin⟩, hliq⟩, hcoup⟩ := hc
      refine ⟨fun d hd => absurd hd (by simp), hfee, hmin, hliq, ?_⟩
      have := congrArg (· = true) hcoup
      simpa using this
    · cases h
  | some d =>
    simp only [LendingTx.preflight, hdmo] at h
    split at h
    · rename_i hc
      simp only [isNonnegativeInput, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hn, hnn⟩, hcap⟩, hfee⟩, hmin⟩, hliq⟩, hcoup⟩ := hc
      refine ⟨fun d' hd => ?_, hfee, hmin, hliq, ?_⟩
      swap
      · have := congrArg (· = true) hcoup
        simpa using this
      obtain rfl : d = d' := Option.some.inj hd
      exact ⟨hn, hnn, hcap⟩
    · cases h

/-- A new broker that passed the preflight is lawful. -/
lemma LoanBroker.create_ok_of_preflight (l : LendingLedger) (tx : LoanBrokerSetCreate) (nt : NumericType)
    (h : (LendingTx.loanBrokerCreate tx).preflight l = .tesSUCCESS) : ∃ b, LoanBroker.create tx nt = .ok b := by
  obtain ⟨hdm, hfee, hmin, hliq, hcoup⟩ := LendingTx.preflight_loanBrokerCreate l tx h
  obtain ⟨hcv, hcn⟩ := debtMaximumCap_facts
  have hz : Number.zero.operator_le Number.zero = true := by decide
  have hdm' : (tx.debtMaximum.getD Number.zero).isNormalized ∧
      Number.zero.operator_le (tx.debtMaximum.getD Number.zero) = true ∧
      (tx.debtMaximum.getD Number.zero).operator_le debtMaximumCap = true := by
    cases hd : tx.debtMaximum with
    | none =>
      refine ⟨Number.zero_isNormalized, hz, ?_⟩
      rw [Option.getD_none, operator_le_iff _ _ Number.zero_isNormalized hcn, Number.toRat_zero, hcv]
      norm_num
    | some d => simpa using hdm d hd
  have hwf : (LoanBroker.createRaw tx nt).WF := ⟨Number.zero_isNormalized, hdm'.1, Number.zero_isNormalized⟩
  have hv : (LoanBroker.createRaw tx nt).Valid :=
    { debtTotal_nonneg := hz
      coverAvailable_nonneg := hz
      debt_within_cap := fun _ => hdm'.2.1
      empty_broker := fun _ => rfl
      debtMaximum_nonneg := hdm'.2.1
      debtMaximum_cap := hdm'.2.2
      managementFeeRate_cap := hfee
      coverRateMinimum_cap := hmin
      coverRateLiquidation_cap := hliq
      coverRates_coupled := hcoup }
  obtain ⟨b, hb, -⟩ := RawLoanBroker.to_lawful_ok_of hwf hv
  exact ⟨b, hb⟩

/-- A LoanBrokerSet that creates a broker never fails its lawfulness re-check. -/
lemma LendingLedger.loanBrokerCreate_ne_notLawful (l : LendingLedger) (tx : LoanBrokerSetCreate) :
    (l.apply (.loanBrokerCreate tx)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro hpre _ hrun
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact LoanBroker.canCreate_ne_notLawful _ _ _ ‹_›
  · obtain ⟨b, hb⟩ := LoanBroker.create_ok_of_preflight l tx l.vault.numericType hpre
    have hc := ‹LoanBroker.create tx l.vault.numericType = .error .notLawful›
    rw [hb] at hc
    cases hc

/-- A broker update that passed its preflight and checks is lawful. A new DebtMaximum is normalized,
in range, and zero or at least DebtTotal. -/
lemma LoanBroker.update_ok_of_checks (l : LendingLedger) (i : Nat) (lb : LoanBroker) (v : Vault)
    (dm : Option Number) (hpre : (LendingTx.loanBrokerUpdate i dm).preflight l = .tesSUCCESS)
    (hcan : lb.canUpdate v dm = .ok .tesSUCCESS) : ∃ b, lb.update dm = .ok b := by
  cases dm with
  | none =>
    obtain ⟨b, hb, -⟩ := RawLoanBroker.to_lawful_ok_of lb.wf lb.valid
    exact ⟨b, hb⟩
  | some d =>
    have hc : (isNonnegativeInput d && d.operator_le debtMaximumCap) = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp [LendingTx.preflight, hne] at hpre
    simp only [isNonnegativeInput, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hn, hnn⟩, hcap⟩ := hc
    have hlim := LoanBroker.canUpdate_limit lb v d hcan
    have hwf : ({ lb.toRawLoanBroker with debtMaximum := d } : RawLoanBroker).WF :=
      ⟨lb.wf.debtTotal_norm, hn, lb.wf.coverAvailable_norm⟩
    have hv : ({ lb.toRawLoanBroker with debtMaximum := d } : RawLoanBroker).Valid :=
      { lb.valid with
        debt_within_cap := fun hne => by
          have hs : d.signum ≠ 0 := fun h0 =>
            hne ((Number.toRat_eq_zero_iff_eq_zero hn).mp ((signum_eq_zero_iff d hn).mp h0))
          have hlt : d.operator_lt lb.debtTotal = false := by simpa [hs] using hlim
          exact (operator_le_iff _ _ lb.wf.debtTotal_norm hn).mpr
            ((operator_lt_eq_false_iff _ _ hn lb.wf.debtTotal_norm).mp hlt)
        debtMaximum_nonneg := hnn
        debtMaximum_cap := hcap }
    obtain ⟨b, hb, -⟩ := RawLoanBroker.to_lawful_ok_of hwf hv
    exact ⟨b, hb⟩

/-- A LoanBrokerSet that updates a broker never fails its lawfulness re-check. -/
lemma LendingLedger.loanBrokerUpdate_ne_notLawful (l : LendingLedger) (i : Nat) (dm : Option Number) :
    (l.apply (.loanBrokerUpdate i dm)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro hpre _ hrun
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact LoanBroker.canUpdate_ne_notLawful _ _ _ ‹_›
  · have hcan := ‹LoanBroker.canUpdate _ l.vault dm = .ok _›
    have hter := ‹¬ (!(_ : TER).isTesSuccess) = true›
    have hup := ‹LoanBroker.update _ dm = .error .notLawful›
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hter
    rw [(TER.isTesSuccess_iff _).mp hter] at hcan
    obtain ⟨b, hb⟩ := LoanBroker.update_ok_of_checks l i _ l.vault dm hpre hcan
    rw [hb] at hup
    cases hup

/-- The broker delete checks read the debt through Number and STAmount operations only. -/
lemma LoanBroker.canDelete_ne_notLawful (lb : LoanBroker) (v : Vault) : lb.canDelete v ≠ .error .notLawful := by
  have hexp : AssetPool.exponent v lb.numericType ≠ .error .notLawful := by
    unfold AssetPool.exponent
    simp only [bind, Except.bind, Vault.pool_assetsTotal]
    split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, numberExponent_ne_notLawful]
  unfold LoanBroker.canDelete
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [hexp, STAmount.roundToNumericType_ne_notLawful]

/-- A LoanBrokerDelete never fails its lawfulness re-check. It re-checks no ledger object. -/
lemma LendingLedger.loanBrokerDelete_ne_notLawful (l : LendingLedger) (i : Nat) :
    (l.apply (.loanBrokerDelete i)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro _ _ hrun
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  all_goals first
    | exact LoanBroker.canDelete_ne_notLawful _ _ ‹_›
    | exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›

/-- A broker with only CoverAvailable replaced by a normalized amount at least zero is lawful. -/
private lemma LoanBroker.withCover_ok (lb : LoanBroker) (c' : Number) (hn' : c'.isNormalized) (h0' : 0 ≤ c'.toRat) :
    ∃ b, ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok b := by
  have hwf : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).WF :=
    ⟨lb.wf.debtTotal_norm, lb.wf.debtMaximum_norm, hn'⟩
  have hv : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).Valid :=
    { lb.valid with
      coverAvailable_nonneg := (operator_le_iff _ _ Number.zero_isNormalized hn').mpr
        (by rw [Number.toRat_zero]; exact h0') }
  obtain ⟨b, hb, -⟩ := RawLoanBroker.to_lawful_ok_of hwf hv
  exact ⟨b, hb⟩

/-- A cover credit that leaves the cover at least zero passes the broker re-check. -/
lemma LoanBroker.applyCoverTransaction_credit_ne_notLawful (lb : LoanBroker) (a : STAmount) (aN : Number)
    (ha : a.toNumber .to_nearest = .ok aN) (h0 : 0 ≤ lb.coverAvailable.toRat + aN.toRat) :
    lb.applyCoverTransaction .credit a ≠ .error .notLawful := by
  have haN := STAmount.toNumber_isNormalized a _ aN ha
  have hcn := lb.wf.coverAvailable_norm
  intro h
  unfold LoanBroker.applyCoverTransaction at h
  rw [ha] at h
  simp only [bind, Except.bind] at h
  split at h
  · simp_all [Number.operator_add_ne_notLawful]
  · rename_i c' hc'
    obtain ⟨b, hb⟩ := LoanBroker.withCover_ok lb c' (operator_add_isNormalized_to_nearest_sz _ _ _ hcn haN hc')
      (operator_add_nonneg _ _ _ hcn haN hc' h0)
    rw [hb] at h
    cases h

/-- A cover debit of at most the cover passes the broker re-check. -/
lemma LoanBroker.applyCoverTransaction_debit_ne_notLawful (lb : LoanBroker) (a : STAmount) (aN : Number)
    (ha : a.toNumber .to_nearest = .ok aN) (hle : aN.toRat ≤ lb.coverAvailable.toRat) :
    lb.applyCoverTransaction .debit a ≠ .error .notLawful := by
  have haN := STAmount.toNumber_isNormalized a _ aN ha
  have hcn := lb.wf.coverAvailable_norm
  have hneg := Number.operator_neg_isNormalized aN haN
  intro h
  unfold LoanBroker.applyCoverTransaction at h
  rw [ha] at h
  simp only [bind, Except.bind] at h
  split at h
  · simp_all [Number.operator_sub_ne_notLawful]
  · rename_i c' hc'
    have hc'' : lb.coverAvailable.operator_add aN.operator_neg .to_nearest = .ok c' := hc'
    obtain ⟨b, hb⟩ := LoanBroker.withCover_ok lb c' (operator_add_isNormalized_to_nearest_sz _ _ _ hcn hneg hc'')
      (operator_add_nonneg _ _ _ hcn hneg hc'' (by rw [Number.toRat_neg]; linarith))
    rw [hb] at h
    cases h

lemma LoanBroker.canCoverWithdraw_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount) :
    lb.canCoverWithdraw v amount ≠ .error .notLawful := by
  unfold LoanBroker.canCoverWithdraw
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [clampToSumExponent_ne_notLawful, STAmount.toNumber_ne_notLawful,
    Number.operator_sub_ne_notLawful, RawLoanBroker.hasMinimumCover_ne_notLawful]

/-- A cover withdrawal that passed its checks withdraws at most the cover. -/
lemma LoanBroker.canCoverWithdraw_le (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (h : lb.canCoverWithdraw v amount = .ok .tesSUCCESS) :
    ∃ a aN, clampToSumExponent lb.coverAvailable amount.operator_neg v.baseExponent = .ok a ∧
      a.toNumber .to_nearest = .ok aN ∧ aN.toRat ≤ lb.coverAvailable.toRat := by
  unfold LoanBroker.canCoverWithdraw at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  refine ⟨_, _, ‹clampToSumExponent _ _ _ = .ok _›, ‹STAmount.toNumber _ _ = .ok _›, ?_⟩
  have hn := STAmount.toNumber_isNormalized _ _ _ ‹STAmount.toNumber _ _ = .ok _›
  exact (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hn).mp (by simpa using ‹¬ _ = true›)

/-- A cover withdrawal that passed its checks never fails the broker re-check. -/
lemma LoanBroker.coverWithdraw_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS) :
    (lb.coverWithdraw v amount).run ≠ .error .notLawful := by
  obtain ⟨a, aN, hcl, ha, hle⟩ := LoanBroker.canCoverWithdraw_le lb v amount hcan
  intro h
  simp only [LoanBroker.coverWithdraw, Vault.pool_baseExponent] at h
  unfold_ter at h
  rw [hcl] at h
  walk_ok
  exact LoanBroker.applyCoverTransaction_debit_ne_notLawful lb a aN ha hle ‹_›

/-- A LoanBrokerCoverWithdraw never fails its lawfulness re-check. Its checks keep the amount within the
cover. -/
lemma LendingLedger.loanBrokerCoverWithdraw_ne_notLawful (l : LendingLedger) (i : Nat) (amount : STAmount) :
    (l.apply (.loanBrokerCoverWithdraw i amount)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro _ _ hrun
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact LoanBroker.canCoverWithdraw_ne_notLawful _ _ _ ‹_›
  · have hter := ‹¬ (!(_ : TER).isTesSuccess) = true›
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hter
    have hcan := ‹LoanBroker.canCoverWithdraw _ l.vault amount = .ok _›
    rw [(TER.isTesSuccess_iff _).mp hter] at hcan
    exact LoanBroker.coverWithdraw_ne_notLawful _ _ _ hcan ‹_›

lemma LoanBroker.roundedCoverAmount_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount) :
    (lb.roundedCoverAmount v amount).run ≠ .error .notLawful := by
  intro h
  simp only [LoanBroker.roundedCoverAmount] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [STAmount.toNumber_ne_notLawful, sumRoundAndSubtract_ne_notLawful]

lemma LoanBroker.checkCoverOpenLimit_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount) :
    lb.checkCoverOpenLimit v amount ≠ .error .notLawful := by
  have hlim : AssetPool.openLimit v ≠ .error .notLawful := by
    show XRPL.Model.SingleAssetVault.Vault.openLimit v ≠ _
    unfold XRPL.Model.SingleAssetVault.Vault.openLimit
    exact Number.from_rep_ne_notLawful _ _ _ _ _
  unfold LoanBroker.checkCoverOpenLimit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.toNumber_ne_notLawful, postSumExponent_ne_notLawful, Number.operator_add_ne_notLawful,
    hlim]

lemma LoanBroker.canCoverDeposit_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount) :
    lb.canCoverDeposit v amount ≠ .error .notLawful := by
  intro h
  unfold LoanBroker.canCoverDeposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact LoanBroker.roundedCoverAmount_ne_notLawful lb v amount (by simp_all [ExceptT.run])
  · split at h
    · cases h
    · exact LoanBroker.checkCoverOpenLimit_ne_notLawful lb v _ h

/-- A balance whose sum exponent an IOU reads is below `10^96`. A normalized sum at or above it has an
exponent too high for any IOU amount, so `ofNumber` would fail. -/
lemma postSumExponent_frac_lt_pow (A c : Number) (b E : Int) (hA : A.isNormalized) (hc : c.isNormalized)
    (hc0 : 0 ≤ c.toRat) (h : postSumExponent A c b .fractional = .ok E) :
    A.toRat < 10 ^ 96 := by
  obtain ⟨sum, hsum, hne⟩ := postSumExponent_reduces A c b .fractional E h
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hsum
  have hge : A.toRat ≤ sum.toRat :=
    (operator_add_rounded_to_nearest _ _ _ hA hc hsum).ge_of_le (Or.inl rfl) A hA (by linarith)
  by_contra hbig
  push Not at hbig
  have hs0 : sum.mantissa_ ≠ 0 := fun h0 => by
    have := Number.toRat_eq_zero_of_mantissa_zero sum h0; linarith
  have hsneg : sum.negative_ = false := Number.negative_false_of_nonneg sum hsn (by linarith)
  obtain ⟨hlo, hhi⟩ := hsn.mantissaBounds_nat hs0
  have hsv := Number.toRat_of_nonneg sum hsneg
  have hz : sum.operator_eq Number.zero = false := by
    cases hq : sum.operator_eq Number.zero
    · rfl
    · have := (Number.operator_eq_iff_eq _ _).mp hq
      rw [this, Number.toRat_zero] at hge; linarith
  unfold numberExponent at hne
  rw [hz] at hne
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at hne
  cases hst : STAmount.ofNumber .fractional sum .downward with
  | error e => rw [hst] at hne; cases hne
  | ok st =>
    have hexp : (-99 : ℤ) ≤ sum.exponent_ := by
      by_contra hlt
      push Not at hlt
      have hm : (sum.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
      have hp : (10 : ℚ) ^ sum.exponent_ ≤ 10 ^ (-100 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : sum.toRat < 10 ^ 19 * 10 ^ (-100 : ℤ) := by
        rw [hsv]
        calc (sum.mantissa_.toNat : ℚ) * 10 ^ sum.exponent_ < 10 ^ 19 * 10 ^ sum.exponent_ :=
              mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
          _ ≤ 10 ^ 19 * 10 ^ (-100 : ℤ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      have h2 : (10 : ℚ) ^ 19 * 10 ^ (-100 : ℤ) < 10 ^ 96 := by norm_num
      linarith
    have hstnz := STAmount.ofNumber_iou_ne_zero_of_exponent sum .downward st hsn hs0 hexp hst
    obtain ⟨hcan, hse, -, -, -⟩ :=
      STAmount.ofNumber_frac_stage sum .downward st hsn (by linarith) (Or.inr (Or.inr rfl)) hst hstnz
    -- an IOU amount has an exponent at most `80`, so the sum has one at most `77`
    have hse' : sum.exponent_ ≤ 77 := by have := hcan.exp_hi; unfold STAmount.exponent at hse; omega
    have hm : (sum.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
    have hp : (10 : ℚ) ^ sum.exponent_ ≤ 10 ^ (77 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hse'
    have : sum.toRat < 10 ^ 19 * 10 ^ (77 : ℤ) := by
      rw [hsv]
      calc (sum.mantissa_.toNat : ℚ) * 10 ^ sum.exponent_ < 10 ^ 19 * 10 ^ sum.exponent_ :=
            mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
        _ ≤ 10 ^ 19 * 10 ^ (77 : ℤ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    have h2 : (10 : ℚ) ^ 19 * 10 ^ (77 : ℤ) = 10 ^ 96 := by norm_num
    linarith

/-- A cover deposit of an amount at least zero never fails the broker re-check. The credit, floored onto
the grid of the new cover, never takes the cover below zero. -/
lemma LoanBroker.coverDeposit_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hamt : ∀ m, amount.toNumber .to_nearest = .ok m → m.isNormalized ∧ 0 ≤ m.toRat) :
    (lb.coverDeposit v amount).run ≠ .error .notLawful := by
  have hbe := Vault.baseExponent_range v
  intro h
  simp only [LoanBroker.coverDeposit] at h
  unfold_ter at h
  simp only [LoanBroker.roundedCoverAmount, Vault.pool_baseExponent] at h
  unfold_ter at h
  walk_ok
  all_goals try first
    | exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    | exact sumRoundAndSubtract_ne_notLawful _ _ _ _ _ ‹_›
  have hm := ‹amount.toNumber .to_nearest = .ok _›
  obtain ⟨hmn, hm0⟩ := hamt _ hm
  have hsr := ‹sumRoundAndSubtract lb.coverAvailable _ v.baseExponent lb.numericType .downward = .ok _›
  have hab : lb.numericType = .fractional → lb.coverAvailable.toRat < 10 ^ 96 := by
    intro hfr
    have hsr' := hsr
    unfold sumRoundAndSubtract at hsr'
    rw [if_neg (by rw [hfr]; decide)] at hsr'
    obtain ⟨_, -, hsr'⟩ := bind_ok_peel _ _ _ hsr'
    obtain ⟨E, hE, -⟩ := bind_ok_peel _ _ _ hsr'
    rw [hfr] at hE
    exact postSumExponent_frac_lt_pow _ _ _ _ lb.wf.coverAvailable_norm hmn hm0 hE
  have happ := ‹lb.applyCoverTransaction .credit _ = .error .notLawful›
  cases hrN : STAmount.toNumber ‹STAmount› .to_nearest with
  | error e =>
    unfold LoanBroker.applyCoverTransaction at happ
    rw [hrN] at happ
    cases happ
    exact STAmount.toNumber_ne_notLawful _ _ hrN
  | ok rN =>
    exact LoanBroker.applyCoverTransaction_credit_ne_notLawful lb _ rN hrN
      (sumRoundAndSubtract_downward_cover_nonneg _ _ _ _ _ _ lb.wf.coverAvailable_norm lb.exact.coverAvailable_nonneg
        hab hmn hm0 hbe hsr hrN) happ

/-- A cover deposit that passed its preflight deposits an amount whose Number is normalized and at least zero. -/
lemma LendingTx.preflight_coverDeposit_amount (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (amount : STAmount) (hpre : (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS) :
    ∀ m, amount.toNumber .to_nearest = .ok m → m.isNormalized ∧ 0 ≤ m.toRat := by
  have hc : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true] at hc
  have hpos := hc.2
  simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hpos
  obtain ⟨hcan, -⟩ := isCanonicalAmount_canonical amount _ hasset.maxValue_le hc.1 hpos.2
  intro m hm
  obtain ⟨hv, hn⟩ := STAmount.toNumber_exact_of amount m (STAmount.Canonical.exactCanonical amount hcan) hm
  exact ⟨hn, by rw [hv]; exact STAmount.toRat_nonneg_of amount hpos.1⟩

/-- A LoanBrokerCoverDeposit never fails its lawfulness re-check. The credit, floored onto the grid of the new
cover, never takes the cover below zero. -/
lemma LendingLedger.loanBrokerCoverDeposit_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : STAmount) : (l.apply (.loanBrokerCoverDeposit i amount)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro hpre _ hrun
  have hamt := LendingTx.preflight_coverDeposit_amount l hr.holdsAsset i amount hpre
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact LoanBroker.canCoverDeposit_ne_notLawful _ _ _ ‹_›
  · exact LoanBroker.coverDeposit_ne_notLawful _ _ _ hamt ‹_›

lemma minimumBrokerCover_ne_notLawful (nt : NumericType) (d : Number) (rate : TenthBips32) (e : Int) :
    minimumBrokerCover nt d rate e ≠ .error .notLawful := by
  unfold minimumBrokerCover
  simp only [bind, Except.bind]
  split_ne_notLawful [tenthBipsOfValue_ne_notLawful, STAmount.roundToNumericType_ne_notLawful]

lemma LoanBroker.roundedCoverClawback_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : Option STAmount) :
    (lb.roundedCoverClawback v amount).run ≠ .error .notLawful := by
  have hmin := minimumBrokerCover_ne_notLawful lb.numericType lb.debtTotal lb.coverRateMinimum
  intro h
  simp only [LoanBroker.roundedCoverClawback] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hmin _ ‹_›
    | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
    | exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    | exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›
    | exact clampToSumExponent_ne_notLawful _ _ _ ‹_›

lemma LoanBroker.canCoverClawback_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : Option STAmount) :
    lb.canCoverClawback v amount ≠ .error .notLawful := by
  intro h
  unfold LoanBroker.canCoverClawback at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · exact LoanBroker.roundedCoverClawback_ne_notLawful lb v amount (by simp_all [ExceptT.run])
    · split at h <;> cases h

/-- A clawed amount at most a cover the asset stores, rounded to the asset and clamped, is at most the cover. -/
private lemma LoanBroker.claw_le (lb : LoanBroker) (v : Vault) (claw : Number) (c' cov : STAmount) (m : Number)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hrep : STAmount.isRounded lb.numericType lb.coverAvailable = false) (hCA : 0 < lb.coverAvailable.toRat)
    (hcn : claw.isNormalized) (hc0 : 0 ≤ claw.toRat) (hcle : claw.toRat ≤ lb.coverAvailable.toRat)
    (hc' : STAmount.ofNumber lb.numericType claw .to_nearest = .ok c')
    (hcl : clampToSumExponent lb.coverAvailable c'.operator_neg v.baseExponent = .ok cov)
    (hm : cov.toNumber .to_nearest = .ok m) : m.toRat ≤ lb.coverAvailable.toRat := by
  have hbe := Vault.baseExponent_range v
  have hcan := lb.wf.coverAvailable_norm
  obtain ⟨a, n, ha, han, hnv⟩ := STAmount.roundtrip_of_isRounded_false _ _ hcan hrep
  have hanz : a.mValue ≠ 0 := by
    intro hz
    have := (STAmount.toNumber_zero_facts a _ n hz han).1
    rw [STAmount.toRat_eq_zero_of_mValue_zero a hz] at this
    linarith
  have hac := STAmount.ofNumber_exactCanonical _ _ _ a hcan hCA.le ha hanz
  have hav : a.toRat = lb.coverAvailable.toRat := by rw [← hnv, (STAmount.toNumber_exact_of a n hac han).1]
  have hc'0 : 0 ≤ c'.toRat :=
    STAmount.ofNumber_nonneg _ _ _ c' hcn (Number.negative_false_of_nonneg claw hcn hc0) hc'
  have hc'le : c'.toRat ≤ lb.coverAvailable.toRat := by
    by_cases hz : c'.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero c' hz]; exact hCA.le
    · rw [← hav]
      exact STAmount.ofNumber_to_nearest_le_of_canonical _ claw c' a hcn hc0 hac
        (STAmount.ofNumber_mNumericType _ _ _ a ha) (by rw [hav]; exact hcle) hc' hz
  have hd := (STAmount.ofNumber_canonicalOrZero _ _ _ c' hmax hc').1.operator_neg
  have hle := clampToSumExponent_le_abs _ _ _ _ hd hbe.1 hbe.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hc'0] at hle
  obtain ⟨hcc, -, -⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hd hbe.1 hbe.2 hcl
  have hmv : m.toRat = cov.toRat := by
    rcases hcc with hc | hz
    · exact (STAmount.toNumber_exact_of cov m (STAmount.Canonical.exactCanonical cov hc) hm).1
    · exact (STAmount.toNumber_zero_facts cov _ m (by simpa [STAmount.isZero] using hz) hm).1
  linarith

/-- The most a clawback may take, CoverAvailable less the minimum cover rounded down, is normalized and at most
CoverAvailable when it is above zero. -/
private lemma LoanBroker.maxClaw_facts (lb : LoanBroker) (e : Int) (he : -81 ≤ e ∧ e ≤ 80) (mc mx : Number)
    (hmc : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok mc)
    (hmx : lb.coverAvailable.operator_sub mc .downward = .ok mx) (hsig : ¬ mx.signum ≤ 0) :
    mx.isNormalized ∧ 0 < mx.toRat ∧ mx.toRat ≤ lb.coverAvailable.toRat := by
  unfold minimumBrokerCover at hmc
  obtain ⟨raw, hraw, hmc⟩ := bind_ok_peel _ _ _ hmc
  obtain ⟨hrn, hr0⟩ := tenthBipsOfValue_upward_facts _ _ _ lb.wf.debtTotal_norm lb.exact.debtTotal_nonneg hraw
  have hmcn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hmc
  have hmc0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hrn hr0 (Or.inr (Or.inl rfl)) he hmc
  have hmxn := Number.operator_sub_isNormalized_any _ _ _ _ lb.wf.coverAvailable_norm hmcn hmx
  have hmx0 : 0 < mx.toRat := (Number.signum_pos_iff_toRat hmxn).mp (by omega)
  have hmxz : mx.mantissa_ ≠ 0 := fun h0 => by rw [Number.toRat_eq_zero_of_mantissa_zero mx h0] at hmx0; linarith
  obtain ⟨n, hn, hv⟩ := operator_sub_rounded_downward _ _ _ lb.wf.coverAvailable_norm hmcn hmx hmxz
  have := Number.lower_le _ n hn
  exact ⟨hmxn, hmx0, by rw [hv]; linarith⟩

/-- A cover clawback of a cover the asset stores never fails the broker re-check. The clawed amount stays at
most the cover above its minimum, and its rounding to the asset never passes the cover. -/
lemma LoanBroker.coverClawback_ne_notLawful (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hamt : ∀ a ∈ amount, a.isZero = false → ∀ m, a.toNumber .to_nearest = .ok m → m.isNormalized ∧ 0 ≤ m.toRat)
    (hrep : STAmount.isRounded lb.numericType lb.coverAvailable = false) :
    (lb.coverClawback v amount).run ≠ .error .notLawful := by
  have hbe := Vault.baseExponent_scale_range v
  have he : -81 ≤ v.baseExponent ∧ v.baseExponent ≤ 80 := ⟨by omega, by omega⟩
  have hfin : ∀ (claw mc mx : Number) (c' cov : STAmount),
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok mc →
      lb.coverAvailable.operator_sub mc .downward = .ok mx → ¬ mx.signum ≤ 0 →
      claw.isNormalized → 0 ≤ claw.toRat → claw.toRat ≤ mx.toRat →
      STAmount.ofNumber lb.numericType claw .to_nearest = .ok c' →
      clampToSumExponent lb.coverAvailable c'.operator_neg v.baseExponent = .ok cov →
      lb.applyCoverTransaction .debit cov = .error .notLawful → False := by
    intro claw mc mx c' cov hmc hmx hsig hcn hc0 hcle hc' hcl happ
    obtain ⟨-, hmx0, hmxle⟩ := LoanBroker.maxClaw_facts lb _ he mc mx hmc hmx hsig
    cases hm : cov.toNumber .to_nearest with
    | error e =>
      unfold LoanBroker.applyCoverTransaction at happ
      rw [hm] at happ
      cases happ
      exact STAmount.toNumber_ne_notLawful _ _ hm
    | ok m =>
      exact LoanBroker.applyCoverTransaction_debit_ne_notLawful lb cov m hm
        (LoanBroker.claw_le lb v claw c' cov m hmax hrep (by linarith) hcn hc0 (by linarith) hc' hcl hm) happ
  intro h
  simp only [LoanBroker.coverClawback] at h
  unfold_ter at h
  simp only [LoanBroker.roundedCoverClawback, Vault.pool_baseExponent] at h
  unfold_ter at h
  walk_ok
  all_goals try first
    | exact Number.operator_sub_ne_notLawful _ _ _ ‹_›
    | exact STAmount.toNumber_ne_notLawful _ _ ‹_›
    | exact STAmount.ofNumber_ne_notLawful _ _ _ ‹_›
    | exact clampToSumExponent_ne_notLawful _ _ _ ‹_›
    | exact minimumBrokerCover_ne_notLawful _ _ _ _ ‹_›
  -- the claw is the most the clawback may take
  all_goals try
    (have hmc := ‹minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok _›
     have hmx := ‹lb.coverAvailable.operator_sub _ .downward = .ok _›
     obtain ⟨hmxn, hmx0, -⟩ := LoanBroker.maxClaw_facts lb _ he _ _ hmc hmx ‹_›
     exact hfin _ _ _ _ _ hmc hmx ‹_› hmxn hmx0.le (le_refl _) ‹_› ‹_› ‹_›)
  -- the claw is the requested amount, at most the most the clawback may take
  have hmc := ‹minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok _›
  have hmx := ‹lb.coverAvailable.operator_sub _ .downward = .ok _›
  obtain ⟨hmxn, -, -⟩ := LoanBroker.maxClaw_facts lb _ he _ _ hmc hmx ‹_›
  obtain ⟨hmn, hm0⟩ := hamt _ rfl (by simpa using ‹¬ (_ : STAmount).isZero = true›) _ ‹STAmount.toNumber _ _ = .ok _›
  have hgt := ‹¬ (_ : Number).operator_gt _ = true›
  unfold Number.operator_gt at hgt
  have hle := (operator_lt_eq_false_iff _ _ hmxn hmn).mp (by simpa using hgt)
  exact hfin _ _ _ _ _ hmc hmx ‹_› hmn hm0 hle ‹_› ‹_› ‹_›

/-- A cover clawback that passed its preflight names no amount, zero, or an amount whose Number is normalized and
at least zero. -/
lemma LendingTx.preflight_coverClawback_amount (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (amount : Option STAmount) (hpre : (LendingTx.loanBrokerCoverClawback i amount).preflight l = .tesSUCCESS) :
    ∀ a ∈ amount, a.isZero = false → ∀ m, a.toNumber .to_nearest = .ok m → m.isNormalized ∧ 0 ≤ m.toRat := by
  intro a ha hz m hm
  rw [Option.mem_def] at ha
  subst ha
  have hc : (isCanonicalAmount a l.vault.numericType && !a.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hnz : a.mValue ≠ 0 := by simpa [STAmount.isZero] using hz
  obtain ⟨hcan, -⟩ := isCanonicalAmount_canonical a _ hasset.maxValue_le hc.1 hnz
  obtain ⟨hv, hn⟩ := STAmount.toNumber_exact_of a m (STAmount.Canonical.exactCanonical a hcan) hm
  exact ⟨hn, by rw [hv]; exact STAmount.toRat_nonneg_of a hc.2⟩

/-- A LoanBrokerCoverClawback never fails its lawfulness re-check when the broker's CoverAvailable is an
amount its asset stores. -/
lemma LendingLedger.loanBrokerCoverClawback_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : Option STAmount)
    (hrep : ∀ b, l.broker? i = some b → STAmount.isRounded b.numericType b.coverAvailable = false) :
    (l.apply (.loanBrokerCoverClawback i amount)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_broker rfl
  intro hpre _ hrun
  have hamt := LendingTx.preflight_coverClawback_amount l hr.holdsAsset i amount hpre
  simp only [LendingLedger.applyBroker] at hrun
  unfold_ter at hrun
  walk_ok'
  · exact LoanBroker.canCoverClawback_ne_notLawful _ _ _ ‹_›
  · rename_i b hb _ _ _ _ _ _ _ _
    have hmax : b.numericType.isIntegral = true → b.numericType.maxValue.toNat ≤ maxRep.toNat := by
      rw [hr.scaleInv.brokers i b hb]; exact hr.holdsAsset.maxValue_le
    exact LoanBroker.coverClawback_ne_notLawful b _ _ hmax hamt (hrep b hb) ‹_›

end XRPL.Model.Lending
