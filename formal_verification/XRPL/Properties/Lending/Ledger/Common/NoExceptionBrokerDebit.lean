import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerCover
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # A cover withdrawal and a cover clawback never end in an exception within the asset's range

Both take cover out. They read CoverAvailable, the amount asked for and the minimum cover of DebtTotal, and build
amounts no larger than these. CoverAvailable is a balance of the asset, so it is within the asset's maximum. -/

namespace XRPL.Model.Protocol

/-- An IOU amount made from a Number below `10^90` in size is at most twice its size. -/
lemma STAmount.ofNumber_fractional_abs_le_two (n : Number) (mode : rounding_mode) (st : STAmount)
    (hn : n.isNormalized) (hlt : |n.toRat| < 10 ^ 90) (hok : STAmount.ofNumber .fractional n mode = .ok st) :
    |st.toRat| ≤ 2 * |n.toRat| := by
  rcases (STAmount.ofNumber_fractional_fczr n mode st hok).2 with hcr | hz
  · have hrne : st.mValue ≠ 0 := fun h => by have := hcr.mant_lo; rw [h] at this; simp at this
    have hm := STAmount.ofNumber_source_ne_zero _ n mode st hok hrne
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hm
    have he := Number.exponent_lt_of_abs_lt n hn hm 72 (by norm_num; exact hlt)
    obtain ⟨hw, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional n mode st rfl hlo hhi
      (Number.exponent_ge_min n hn hm) (by unfold maxExponent; omega) hok hrne
    have hxa := abs_toRat_eq n
    have hml : (10 : ℚ) ^ 18 ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
    have hpe : (10 : ℚ) ^ (n.exponent_ + 3) = 1000 * 10 ^ n.exponent_ := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    have hpp : (0 : ℚ) < 10 ^ n.exponent_ := zpow_pos (by norm_num) _
    have hulp : (10 : ℚ) ^ (n.exponent_ + 3) ≤ |n.toRat| := by rw [hpe, hxa]; nlinarith
    have := abs_sub_abs_le_abs_sub st.toRat n.toRat
    linarith
  · rw [STAmount.toRat_eq_zero_of_mValue_zero st hz, abs_zero]; positivity

/-- The debit of a cover withdrawal or clawback always computes. An XRP or MPT amount is taken as it is, and an IOU
amount is rounded at the exponent of CoverAvailable less the amount, both within `2 * 10^89`. -/
lemma clampToSumExponent_debit_total (A : Number) (a : STAmount) (b : Int) (hA : A.isNormalized)
    (hA0 : 0 ≤ A.toRat) (hAl : A.toRat < 10 ^ 96) (ha : a.CanonicalOrZero) (ha0 : 0 ≤ a.toRat)
    (hb : -10 ≤ b ∧ b ≤ 0)
    (hiou : a.integral = false → A.toRat ≤ 2 * iouProofCap ∧ a.toRat ≤ 2 * iouProofCap) :
    ∃ d, clampToSumExponent A a.operator_neg b = .ok d := by
  obtain ⟨hnt, hoff, hval⟩ := STAmount.operator_neg_fields a
  by_cases hint : a.integral = true
  · exact ⟨_, clampToSumExponent_integral A a.operator_neg b (by unfold STAmount.integral; rw [hnt]; exact hint)⟩
  have hfr : a.integral = false := by simpa using hint
  obtain ⟨hA2, ha2⟩ := hiou hfr
  have h2cap : 2 * iouProofCap < 10 ^ 96 := by unfold iouProofCap; norm_num
  have hδc : a.operator_neg.CanonicalOrZero := STAmount.CanonicalOrZero.operator_neg ha
  have hδfr : a.operator_neg.integral = false := by unfold STAmount.integral; rw [hnt]; exact hfr
  have hδty : a.operator_neg.numericType = .fractional := by
    unfold STAmount.numericType; rw [hnt]; exact NumericType.eq_fractional_of_not_integral hfr
  obtain ⟨δN, hδN⟩ := hδc.toNumber_ok
  obtain ⟨hδNv, hδNn⟩ := hδc.toNumber_exact δN hδN
  rw [STAmount.operator_neg_toRat] at hδNv
  obtain ⟨e, he, hbe, he79⟩ := postSumExponent_frac_ok_of_cap A δN b hA hδNn
    (by rw [abs_of_nonneg hA0]; exact hAl) (by rw [hδNv, abs_neg, abs_of_nonneg ha0]; linarith)
    hb.2 (by rw [hδNv, abs_le]; constructor <;> linarith)

  -- the amount rounded is the amount without its sign: canonical and not negative, or zero
  have hv : ((if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg).IOUCanonical ∧
      (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg).mIsNegative = false) ∨
      (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg).mValue = 0 := by
    by_cases hz : a.mValue = 0
    · right
      split_ifs
      · rw [(STAmount.operator_neg_fields a.operator_neg).2.2, hval, hz]
      · rw [hval, hz]
    · left
      have hc : a.Canonical := ha.resolve_right (by simp [STAmount.isZero, hz])
      have hic := hc.2 hfr
      have hneg : a.mIsNegative = false := STAmount.mIsNegative_false_of_nonneg a ha0 hz
      have habs : (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg) =
          { a with mIsNegative := false } := by
        simp [STAmount.operator_neg, STAmount.negative, hz, hneg]
      rw [habs]
      exact ⟨⟨hic.is_fractional, hic.mant_lo, hic.mant_hi, hic.exp_lo, hic.exp_hi⟩, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, STAmount.roundToExponent
      (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg) e .towards_zero = .ok d := by
    cases h : STAmount.roundToExponent
        (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg) e .towards_zero with
    | error err => exact absurd h (STAmount.roundToExponent_ne_overflow _ e _ hv (by omega) he79)
    | ok d => exact ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  unfold clampToSumExponent
  simp only [hδfr, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, hδN, hδty, he]
  exact hd

/-- An amount of the asset, canonical or zero, is below `10^96` in size. -/
lemma STAmount.CanonicalOrZero.abs_lt {a : STAmount} (ha : a.CanonicalOrZero) : |a.toRat| < 10 ^ 96 := by
  rcases ha with hc | hz
  · exact STAmount.Canonical.abs_lt a hc
  · rw [STAmount.toRat_eq_zero_of_mValue_zero a (by simpa [STAmount.isZero] using hz), abs_zero]; norm_num

/-- A value the asset stores exactly is within the asset's maximum. -/
lemma STAmount.Representable.le_maxAmount {nt : NumericType} {x : ℚ} (h : STAmount.Representable nt x) :
    x ≤ nt.maxAmount := by
  rcases h with rfl | h
  · unfold NumericType.maxAmount; split <;> positivity
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, hk, -, rfl⟩ := h
    unfold NumericType.maxAmount
    rw [if_pos (show (NumericType.integral mv mo ms msh).isIntegral = true from rfl)]
    exact_mod_cast hk
  | fractional =>
    obtain ⟨m, e, -, hm, -, he, rfl⟩ := h
    rw [NumericType.maxAmount_fractional]
    have hm' : (m : ℚ) ≤ 10 ^ 16 - 1 := by
      have : (m : ℚ) + 1 ≤ 10 ^ 16 := by exact_mod_cast Nat.succ_le_of_lt hm
      linarith
    have hp : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
    have hp0 : (0 : ℚ) ≤ 10 ^ e := (zpow_pos (by norm_num) _).le
    calc (m : ℚ) * 10 ^ e ≤ (10 ^ 16 - 1) * 10 ^ e := mul_le_mul_of_nonneg_right hm' hp0
      _ ≤ (10 ^ 16 - 1) * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = (10 ^ 16 - 1) * 10 ^ 80 := by norm_num

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A broker's cover rate is at most 100%. -/
private lemma LoanBroker.coverRateMinimum_le (lb : LoanBroker) : lb.coverRateMinimum.toNat ≤ 100000 := by
  have h := lb.valid.coverRateMinimum_cap
  rw [UInt32.le_iff_toNat_le] at h
  exact h

/-- The LoanBrokerCoverWithdraw checks never throw while CoverAvailable is within the asset's maximum, and for an
IOU CoverAvailable and the amount are within `10^89`. -/
lemma LoanBroker.canCoverWithdraw_total (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType) (hcan : amount.Canonical)
    (hnn : 0 ≤ amount.toRat) (hamt : amount.mNumericType = v.numericType) (t : ℕ) (ht : t ≤ 10 ^ 16)
    (hdv : lb.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent)
    (hcover : lb.coverAvailable.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false →
      lb.coverAvailable.toRat ≤ iouProofCap ∧ amount.toRat ≤ iouProofCap) :
    ∃ ter, lb.canCoverWithdraw v amount = .ok ter := by
  have hbase := v.baseExponent_bounds
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  have hcap0 : (0 : ℚ) ≤ iouProofCap := by unfold iouProofCap; positivity
  have hal := STAmount.Canonical.abs_lt amount hcan
  rw [abs_of_nonneg hnn] at hal
  have hδc := STAmount.CanonicalOrZero.operator_neg (Or.inl hcan : amount.CanonicalOrZero)
  obtain ⟨d, hd⟩ := clampToSumExponent_debit_total lb.coverAvailable amount v.baseExponent hcn hc0 (by linarith)
    (Or.inl hcan) hnn ⟨hbase.1, hbase.2.1⟩ (fun hfr => by
      have := hiou (by rw [← hamt]; exact hfr)
      constructor <;> linarith)
  obtain ⟨hdc, -, hd0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ d v.baseExponent hδc (by omega)
    (by omega) hd
  have hdle := clampToSumExponent_le_abs lb.coverAvailable _ d v.baseExponent hδc (by omega) (by omega) hd
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hnn] at hdle
  obtain ⟨dN, hdN⟩ := hdc.toNumber_ok
  obtain ⟨hdNv, hdNn⟩ := hdc.toNumber_exact dN hdN
  obtain ⟨c', hc', -⟩ := Number.operator_sub_total_of_abs lb.coverAvailable dN .to_nearest hcn hdNn
    (by rw [abs_of_nonneg hc0]; linarith) (by rw [hdNv, abs_of_nonneg hd0]; linarith)
  obtain ⟨m, hm, -, -⟩ := minimumBrokerCover_ok_of_units lb.numericType lb.debtTotal lb.coverRateMinimum
    v.baseExponent (by rw [hnt]; exact hasset) ⟨hbase.1, hbase.2.1⟩ lb.wf.debtTotal_norm t ht hdv
    lb.coverRateMinimum_le
  unfold LoanBroker.canCoverWithdraw
  simp only [bind, Except.bind, pure, Except.pure, Vault.pool_baseExponent, hd, hdN, hc',
    RawLoanBroker.hasMinimumCover, hm]
  split_ifs <;> exact ⟨_, rfl⟩

/-- A cover withdrawal that passed its checks fails only the broker re-check. -/
lemma LoanBroker.coverWithdraw_error_notLawful (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (hcan : amount.Canonical) (hnn : 0 ≤ amount.toRat) (hamt : amount.mNumericType = v.numericType)
    (hcover : lb.coverAvailable.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false →
      lb.coverAvailable.toRat ≤ iouProofCap ∧ amount.toRat ≤ iouProofCap) {e : Error}
    (h : (lb.coverWithdraw v amount).run = .error e) : e = .notLawful := by
  have hbase := v.baseExponent_bounds
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  have hcap0 : (0 : ℚ) ≤ iouProofCap := by unfold iouProofCap; positivity
  have hal := STAmount.Canonical.abs_lt amount hcan
  rw [abs_of_nonneg hnn] at hal
  have hδc := STAmount.CanonicalOrZero.operator_neg (Or.inl hcan : amount.CanonicalOrZero)
  obtain ⟨d, hd⟩ := clampToSumExponent_debit_total lb.coverAvailable amount v.baseExponent hcn hc0 (by linarith)
    (Or.inl hcan) hnn ⟨hbase.1, hbase.2.1⟩ (fun hfr => by
      have := hiou (by rw [← hamt]; exact hfr)
      constructor <;> linarith)
  obtain ⟨hdc, -, hd0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ d v.baseExponent hδc (by omega)
    (by omega) hd
  have hdle := clampToSumExponent_le_abs lb.coverAvailable _ d v.baseExponent hδc (by omega) (by omega) hd
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hnn] at hdle
  simp only [LoanBroker.coverWithdraw] at h
  unfold_ter at h
  simp only [Vault.pool_baseExponent, hd] at h
  cases happ : lb.applyCoverTransaction .debit d with
  | error e' =>
    rw [happ] at h
    cases h
    exact LoanBroker.applyCoverTransaction_error lb .debit d hdc (by rw [abs_of_nonneg hd0]; linarith)
      (by linarith) happ
  | ok y => rw [happ] at h; cases h

/-- On a reachable ledger a broker's DebtTotal is a whole number of base units, at most `10^16` of them. -/
lemma LendingLedger.Reachable.broker_debt_units {l : LendingLedger} (hr : l.Reachable) {j : Nat} {b : LoanBroker}
    (hb : l.broker? j = some b) :
    ∃ t : ℕ, t ≤ 10 ^ 16 ∧ b.debtTotal.toRat = (t : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨t, ht⟩ := hr.scaleInv.brokerPrincipal_grid j
  have hdt := hr.debtInv.debt _ _ hb
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hle : (t : ℚ) * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    rw [← ht]
    refine le_trans (l.brokerPrincipal_le _) ?_
    rw [← hr.debtInv.deployed]
    exact hr.lossInv.deployed
  have ht16 : (t : ℚ) ≤ 10 ^ 16 := le_of_mul_le_mul_right hle hp
  exact ⟨t, by exact_mod_cast ht16, by rw [hdt, ht]⟩

/-- A cover withdrawal that passed its preflight names a canonical amount of the vault's asset above zero. -/
lemma LendingTx.preflight_coverWithdraw_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (amount : STAmount) (hpre : (LendingTx.loanBrokerCoverWithdraw i amount).preflight l = .tesSUCCESS) :
    amount.Canonical ∧ 0 ≤ amount.toRat ∧ amount.mNumericType = l.vault.numericType := by
  have hc : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true] at hc
  have hpos := hc.2
  simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hpos
  obtain ⟨hcan, hty⟩ := isCanonicalAmount_canonical amount _ hasset.maxValue_le hc.1 hpos.2
  exact ⟨hcan, STAmount.toRat_nonneg_of amount hpos.1, hty⟩

/-- Proof body of the LoanBrokerCoverWithdraw line: on a reachable ledger it returns a result code while
CoverAvailable is within the asset's maximum, and for an IOU CoverAvailable and the amount are within `10^89`. -/
lemma LendingLedger.loanBrokerCoverWithdraw_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : STAmount)
    (hcover : ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount)
    (hiou : l.vault.numericType.isIntegral = false → amount.toRat ≤ iouProofCap ∧
      ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverWithdraw i amount)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerCoverWithdraw i amount)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    obtain ⟨hcan, hnn, hamt⟩ := LendingTx.preflight_coverWithdraw_canonical l hr.holdsAsset i amount hpre
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · have hc := ‹LoanBroker.canCoverWithdraw _ l.vault amount = .error e›
      have hbr := ‹l.broker? i = some _›
      obtain ⟨t, ht, hdv⟩ := hr.broker_debt_units hbr
      obtain ⟨ter, hter⟩ := LoanBroker.canCoverWithdraw_total _ l.vault amount hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hcan hnn hamt t ht hdv (hcover _ hbr)
        (fun hint => ⟨(hiou hint).2 _ hbr, (hiou hint).1⟩)
      rw [hter] at hc
      cases hc
    · have hbr := ‹l.broker? i = some _›
      have hd := ‹LoanBroker.coverWithdraw _ l.vault amount = .error e›
      obtain rfl := LoanBroker.coverWithdraw_error_notLawful _ l.vault amount hcan hnn hamt (hcover _ hbr)
        (fun hint => ⟨(hiou hint).2 _ hbr, (hiou hint).1⟩) hd
      exact LendingLedger.loanBrokerCoverWithdraw_ne_notLawful l i amount hrun

/-- The amount a cover clawback takes always computes while CoverAvailable is within the asset's maximum, and within
`10^89` for an IOU. A result is an amount of the asset at least zero. -/
lemma LoanBroker.roundedCoverClawback_total (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType)
    (hamt : ∀ a ∈ amount, a.isZero = false → a.Canonical ∧ 0 ≤ a.toRat) (t : ℕ) (ht : t ≤ 10 ^ 16)
    (hdv : lb.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent)
    (hcover : lb.coverAvailable.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat ≤ iouProofCap) :
    ∃ x, (lb.roundedCoverClawback v amount).run = .ok x ∧
      ∀ d, x = .ok d → d.CanonicalOrZero ∧ 0 ≤ d.toRat := by
  have hbase := v.baseExponent_bounds
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  have hcap90 : iouProofCap < 10 ^ 90 := by unfold iouProofCap; norm_num
  obtain ⟨m, hm, hmn, hmabs⟩ := minimumBrokerCover_ok_of_units lb.numericType lb.debtTotal lb.coverRateMinimum
    v.baseExponent (by rw [hnt]; exact hasset) ⟨hbase.1, hbase.2.1⟩ lb.wf.debtTotal_norm t ht hdv
    lb.coverRateMinimum_le
  have hm0 : 0 ≤ m.toRat := LoanBroker.minimumCover_nonneg lb v.baseExponent m (by omega) hm
  rw [abs_of_nonneg hm0] at hmabs
  obtain ⟨mc, hmc, hmcn⟩ := Number.operator_sub_total_of_abs lb.coverAvailable m .downward hcn hmn
    (by rw [abs_of_nonneg hc0]; linarith) (by rw [abs_of_nonneg hm0]; linarith)

  -- a Number at least CoverAvailable and within the range of the asset
  obtain ⟨W, hW, hcW, hWint, hWfrac⟩ : ∃ W : Number, W.isNormalized ∧ lb.coverAvailable.toRat ≤ W.toRat ∧
      (v.numericType.isIntegral = true → W.toRat ≤ v.numericType.maxValue.toNat) ∧
      (v.numericType.isIntegral = false → W.toRat ≤ iouProofCap) := by
    cases hint : v.numericType.isIntegral
    · obtain ⟨-, hi, -, hhi, -, hhiv⟩ := iouProofCap_number
      exact ⟨hi, hhi, by rw [hhiv]; exact hiou hint, (fun h => by cases h), fun _ => by rw [hhiv]⟩
    · obtain ⟨w, hw, hwv⟩ := NumericType.maxAmount_number v.numericType hasset
      have hmax : v.numericType.maxAmount = v.numericType.maxValue.toNat := by
        unfold NumericType.maxAmount; rw [if_pos hint]
      exact ⟨w, hw, by rw [hwv]; exact hcover, (fun _ => by rw [hwv, hmax]), fun h => by cases h⟩
  obtain ⟨L, hL, hLv⟩ := Number.exists_normalized_of_int (-(2 * 10 ^ 16 + 1)) (by norm_num)
  obtain ⟨-, hmcW⟩ := Number.operator_sub_between lb.coverAvailable m mc L W .downward hcn hmn hmc hL hW
    (by rw [hLv]; norm_num) (by linarith) (by rw [hLv]; push_cast; linarith) (by linarith)

  -- from the amount to claw on: convert it to the asset and clamp it at the exponent of the cover left
  have tail : ∀ claw : Number, claw.isNormalized → 0 ≤ claw.toRat → claw.toRat ≤ W.toRat →
      ∃ c' d, STAmount.ofNumber lb.numericType claw .to_nearest = .ok c' ∧
        clampToSumExponent lb.coverAvailable c'.operator_neg v.baseExponent = .ok d ∧
        d.CanonicalOrZero ∧ 0 ≤ d.toRat := by
    intro claw hcln hcl0 hclW
    obtain ⟨c', hof⟩ := STAmount.ofNumber_ok_of_asset_cap lb.numericType claw .to_nearest
      (by rw [hnt]; exact hasset) hcln hcl0 (fun hi => by rw [hnt] at hi ⊢; linarith [hWint hi])
      (fun hf => by rw [hnt] at hf; linarith [hWfrac hf])
    have hc'c := (STAmount.ofNumber_canonicalOrZero _ _ _ _
      (fun hi => by rw [hnt] at hi ⊢; exact hasset.maxValue_le hi) hof).1
    have hc'0 := STAmount.ofNumber_nonneg _ claw _ c' hcln (Number.negative_false_of_nonneg claw hcln hcl0) hof
    have hc'ty := STAmount.ofNumber_mNumericType _ _ _ c' hof
    obtain ⟨d, hd⟩ := clampToSumExponent_debit_total lb.coverAvailable c' v.baseExponent hcn hc0 (by linarith)
      hc'c hc'0 ⟨hbase.1, hbase.2.1⟩ (fun hfr => by
        have hf : v.numericType.isIntegral = false := by rw [← hnt, ← hc'ty]; exact hfr
        have hfrac : lb.numericType = .fractional := by
          rw [hnt]; exact NumericType.eq_fractional_of_not_integral hf
        have hof' : STAmount.ofNumber .fractional claw .to_nearest = .ok c' := by rw [← hfrac]; exact hof
        have h2 := STAmount.ofNumber_fractional_abs_le_two claw .to_nearest c' hcln
          (by rw [abs_of_nonneg hcl0]; linarith [hWfrac hf]) hof'
        rw [abs_of_nonneg hc'0, abs_of_nonneg hcl0] at h2
        exact ⟨by linarith [hiou hf], by linarith [hWfrac hf]⟩)
    obtain ⟨hdc, -, hd0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ d v.baseExponent
      (STAmount.CanonicalOrZero.operator_neg hc'c) (by omega) (by omega) hd
    exact ⟨c', d, hof, hd, hdc, hd0⟩

  simp only [LoanBroker.roundedCoverClawback]
  unfold_ter
  simp only [Vault.pool_baseExponent, hm, hmc]
  by_cases hsig : mc.signum ≤ 0
  · rw [if_pos hsig]
    exact ⟨_, rfl, fun d hd => by cases hd⟩
  rw [if_neg hsig]
  have hmc0 : 0 ≤ mc.toRat := le_of_lt ((Number.signum_pos_iff_toRat hmcn).mp (by omega))
  cases amount with
  | none =>
    obtain ⟨c', d, hof, hcl, hdc, hd0⟩ := tail mc hmcn hmc0 hmcW
    simp only [hof, hcl]
    split_ifs
    · exact ⟨_, rfl, fun d' hd' => by cases hd'⟩
    · exact ⟨_, rfl, fun d' hd' => by cases hd'; exact ⟨hdc, hd0⟩⟩
  | some a =>
    by_cases hz : a.isZero = true
    · obtain ⟨c', d, hof, hcl, hdc, hd0⟩ := tail mc hmcn hmc0 hmcW
      simp only [hz, ↓reduceIte, hof, hcl]
      split_ifs
      · exact ⟨_, rfl, fun d' hd' => by cases hd'⟩
      · exact ⟨_, rfl, fun d' hd' => by cases hd'; exact ⟨hdc, hd0⟩⟩
    · obtain ⟨hac, ha0⟩ := hamt a rfl (by simpa using hz)
      obtain ⟨aN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok (Or.inl hac)
      obtain ⟨haNv, haNn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hac) aN haN
      have hclawn : (if aN.operator_gt mc = true then mc else aN).isNormalized := by
        split_ifs
        · exact hmcn
        · exact haNn
      have hclaw0 : 0 ≤ (if aN.operator_gt mc = true then mc else aN).toRat := by
        split_ifs
        · exact hmc0
        · rw [haNv]; exact ha0
      have hclawW : (if aN.operator_gt mc = true then mc else aN).toRat ≤ W.toRat := by
        split_ifs with hgt
        · exact hmcW
        · have := (Number.operator_gt_iff aN mc haNn hmcn).not.mp hgt
          linarith
      obtain ⟨c', d, hof, hcl, hdc, hd0⟩ := tail _ hclawn hclaw0 hclawW
      simp only [hz, Bool.false_eq_true, ↓reduceIte, haN, hof, hcl]
      split_ifs
      · exact ⟨_, rfl, fun d' hd' => by cases hd'⟩
      · exact ⟨_, rfl, fun d' hd' => by cases hd'; exact ⟨hdc, hd0⟩⟩

/-- The LoanBrokerCoverClawback checks never throw while CoverAvailable is within the asset's maximum, and within
`10^89` for an IOU. -/
lemma LoanBroker.canCoverClawback_total (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType)
    (hamt : ∀ a ∈ amount, a.isZero = false → a.Canonical ∧ 0 ≤ a.toRat) (t : ℕ) (ht : t ≤ 10 ^ 16)
    (hdv : lb.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent)
    (hcover : lb.coverAvailable.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat ≤ iouProofCap) :
    ∃ ter, lb.canCoverClawback v amount = .ok ter := by
  obtain ⟨x, hx, -⟩ := LoanBroker.roundedCoverClawback_total lb v amount hasset hnt hamt t ht hdv hcover hiou
  unfold LoanBroker.canCoverClawback
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · exact ⟨_, rfl⟩
  · rw [hx]
    cases x <;> exact ⟨_, rfl⟩

/-- A cover clawback that passed its checks fails only the broker re-check. -/
lemma LoanBroker.coverClawback_error_notLawful (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType)
    (hamt : ∀ a ∈ amount, a.isZero = false → a.Canonical ∧ 0 ≤ a.toRat) (t : ℕ) (ht : t ≤ 10 ^ 16)
    (hdv : lb.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent)
    (hcover : lb.coverAvailable.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType.isIntegral = false → lb.coverAvailable.toRat ≤ iouProofCap) {e : Error}
    (h : (lb.coverClawback v amount).run = .error e) : e = .notLawful := by
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  obtain ⟨x, hx, hxd⟩ := LoanBroker.roundedCoverClawback_total lb v amount hasset hnt hamt t ht hdv hcover hiou
  simp only [ExceptT.run] at hx
  simp only [LoanBroker.coverClawback] at h
  unfold_ter at h
  rw [hx] at h
  cases x with
  | error ter => simp at h
  | ok d =>
    obtain ⟨hdc, -⟩ := hxd d rfl
    dsimp only at h
    cases happ : lb.applyCoverTransaction .debit d with
    | error e' =>
      rw [happ] at h
      cases h
      exact LoanBroker.applyCoverTransaction_error lb .debit d hdc hdc.abs_lt (by linarith) happ
    | ok y => rw [happ] at h; cases h

/-- A cover clawback that passed its preflight names no amount, zero, or a canonical amount above zero. -/
lemma LendingTx.preflight_coverClawback_canonical (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault) (i : Nat)
    (amount : Option STAmount) (hpre : (LendingTx.loanBrokerCoverClawback i amount).preflight l = .tesSUCCESS) :
    ∀ a ∈ amount, a.isZero = false → a.Canonical ∧ 0 ≤ a.toRat := by
  intro a ha hz
  rw [Option.mem_def] at ha
  subst ha
  have hc : (isCanonicalAmount a l.vault.numericType && !a.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hnz : a.mValue ≠ 0 := by simpa [STAmount.isZero] using hz
  obtain ⟨hcan, -⟩ := isCanonicalAmount_canonical a _ hasset.maxValue_le hc.1 hnz
  exact ⟨hcan, STAmount.toRat_nonneg_of a hc.2⟩

/-- Proof body of the LoanBrokerCoverClawback line: on a reachable ledger it returns a result code while the asset
stores CoverAvailable, and for an IOU CoverAvailable is within `10^89`. -/
lemma LendingLedger.loanBrokerCoverClawback_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : Option STAmount)
    (hrep : ∀ b, l.broker? i = some b → STAmount.isRounded b.numericType b.coverAvailable = false)
    (hiou : l.vault.numericType.isIntegral = false →
      ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverClawback i amount)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerCoverClawback i amount)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    have hamt := LendingTx.preflight_coverClawback_canonical l hr.holdsAsset i amount hpre
    have hcover : ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount := by
      intro b hbr
      rw [← hr.scaleInv.brokers i b hbr]
      exact ((STAmount.isRounded_eq_false_iff _ _ b.wf.coverAvailable_norm b.exact.coverAvailable_nonneg).mp
        (hrep b hbr)).le_maxAmount
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · have hc := ‹LoanBroker.canCoverClawback _ l.vault amount = .error e›
      have hbr := ‹l.broker? i = some _›
      obtain ⟨t, ht, hdv⟩ := hr.broker_debt_units hbr
      obtain ⟨ter, hter⟩ := LoanBroker.canCoverClawback_total _ l.vault amount hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hamt t ht hdv (hcover _ hbr) (fun hint => hiou hint _ hbr)
      rw [hter] at hc
      cases hc
    · have hbr := ‹l.broker? i = some _›
      have hd := ‹LoanBroker.coverClawback _ l.vault amount = .error e›
      obtain ⟨t, ht, hdv⟩ := hr.broker_debt_units hbr
      obtain rfl := LoanBroker.coverClawback_error_notLawful _ l.vault amount hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hamt t ht hdv (hcover _ hbr) (fun hint => hiou hint _ hbr) hd
      exact LendingLedger.loanBrokerCoverClawback_ne_notLawful l hr i amount hrep hrun

end XRPL.Model.Lending
