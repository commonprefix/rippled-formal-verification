import XRPL.Properties.Lending.LoanBroker.Common.CoverSequenceProofs
import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy

/-! # Proof bodies for what a cover operation can do

On a reachable broker each cover operation moves CoverAvailable by whole base units, stored exactly. So the applied
amount converts back exactly, a one-unit deposit fits, and the whole cover can be taken out. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)


/-- A debit of `d` whole base units that takes a cover in the Open zone to a cover on the base grid
leaves a difference of covers that computes and converts to an amount worth `d`. -/
private lemma LoanBroker.debit_delta (lb lb' : LoanBroker) (v : Vault) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType) (hg : Number.OnGrid v.baseExponent lb'.coverAvailable)
    (d : ℚ) (j : ℕ) (hj : d = (j : ℚ) * 10 ^ v.baseExponent) (hle : d ≤ lb.toExact.coverAvailable)
    (hcov : lb'.toExact.coverAvailable = lb.toExact.coverAvailable - d) :
    ∃ (deltaCover : Number) (deltaAmount : STAmount),
      lb.coverAvailable.operator_sub lb'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧ deltaAmount.toRat = d := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hd0 : 0 ≤ d := by rw [hj]; positivity
  have hC : lb'.coverAvailable.toRat = lb.coverAvailable.toRat - d := hcov
  -- both covers are at most the Open limit, far below `10^96`, so their difference computes
  have hlt : lb.coverAvailable.toRat < 10 ^ 96 := (LoanBroker.OpenZone.cover_le lb _ hz hbhi).trans_lt (by norm_num)
  obtain ⟨deltaCover, hsub⟩ := Number.operator_sub_ok_of_lt lb.coverAvailable lb'.coverAvailable .to_nearest
    lb.wf.coverAvailable_norm lb'.wf.coverAvailable_norm lb.exact.coverAvailable_nonneg hlt
    lb'.exact.coverAvailable_nonneg (by rw [hC]; linarith)
  -- the two covers are on the base grid, so their difference is exact
  have hd := grid_sub_exact _ _ _ _ hz.cover hg (Vault.baseExponent_grid v).2 lb'.exact.coverAvailable_nonneg
    (by rw [hC]; linarith) hz.coverLimit hsub
  have hdv : deltaCover.toRat = d := by rw [hd, hC]; ring
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ lb.wf.coverAvailable_norm lb'.wf.coverAvailable_norm hsub
  -- a whole number of base units at most the cover converts exactly
  obtain ⟨st, hst, hstv⟩ := LoanBroker.ofNumber_units lb _ hz ⟨hblo, hbhi⟩ (fun h => hbint (hnt ▸ h))
    deltaCover j hdn (by rw [hdv]; exact hj) (by rw [hdv]; exact hle)
  exact ⟨deltaCover, st, hsub, hst, by rw [hstv, hdv]⟩

/-- On a reachable broker the whole cover, converted to a nonzero amount, is a canonical amount of the
asset worth the cover, a positive whole number of base units. -/
private lemma LoanBroker.Reachable.cover_amount (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s) (hnz : s.mValue ≠ 0) :
    s.Canonical ∧ s.mNumericType = lb.numericType ∧ s.toRat = lb.toExact.coverAvailable ∧ 0 < s.toRat ∧
      ∃ k : ℕ, 0 < k ∧ s.toRat = (k : ℚ) * 10 ^ base := by
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  have hv := LoanBroker.roundedCoverAvailable_of_exact lb s hz.coverExact hs
  obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ s hmax hs
  have hC0 : (0 : ℚ) ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hpos : 0 < s.toRat :=
    lt_of_le_of_ne (hv ▸ hC0) (fun h => hnz ((STAmount.toRat_eq_zero_iff s).mp h.symm))
  obtain ⟨-, jc, hjc⟩ := hz.cover
  rw [hvb] at hjc
  have hp : (0 : ℚ) < 10 ^ base := zpow_pos (by norm_num) _
  have hjc0 : 0 ≤ jc := by
    have : (0 : ℚ) ≤ (jc : ℚ) * 10 ^ base := hjc ▸ hC0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hk : s.toRat = (jc.toNat : ℚ) * 10 ^ base := by
    rw [hv]
    show lb.coverAvailable.toRat = _
    rw [hjc]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hjc0).symm
  exact ⟨hcz.resolve_right (by simp [STAmount.isZero, hnz]), hty, hv, hpos, jc.toNat, units_pos hk hpos, hk⟩

/-- On a reachable broker with a positive cover, the whole cover converts to a canonical amount of the
asset worth the cover, a positive whole number of base units. -/
private lemma LoanBroker.Reachable.exists_cover_amount (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hpos : 0 < lb.toExact.coverAvailable) :
    ∃ s : STAmount, s.Canonical ∧ s.mNumericType = lb.numericType ∧ s.toRat = lb.toExact.coverAvailable ∧
      0 < s.toRat ∧ ∃ k : ℕ, 0 < k ∧ s.toRat = (k : ℚ) * 10 ^ base := by
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  obtain ⟨s, hs⟩ := STAmount.ofNumber_ok_of_isRounded_false _ _ hz.coverExact
  have hv := LoanBroker.roundedCoverAvailable_of_exact lb s hz.coverExact hs
  refine ⟨s, LoanBroker.Reachable.cover_amount lb base hr hmax v hvb s hs fun h0 => ?_⟩
  rw [STAmount.toRat_eq_zero_of_mValue_zero s h0] at hv
  linarith

/-- Proof body of the applied delta line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_applied_delta_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    (∃ (deltaCover : Number) (deltaAmount : STAmount),
      res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.toRat = res.amount'.toRat) ∧
    ∃ amount'' : STAmount, (lb.roundedCoverAmount v res.amount').run = .ok (.ok amount'') ∧
      amount''.toRat = res.amount'.toRat := by
  obtain ⟨hr1, hnt1, hcr, htr, hpos', ⟨j, hj⟩, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  subst hvb
  have hmax1 : res.loanBroker'.numericType.isIntegral = true →
      res.loanBroker'.numericType.maxValue.toNat ≤ maxRep.toNat := by rw [hnt1]; exact hmax
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨hz1, -⟩ := LoanBroker.Reachable.zone_setup _ _ hr1 hmax1 v rfl
  have hC : res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + res.amount'.toRat := hcov
  have hC0 : (0 : ℚ) ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  constructor
  · obtain ⟨deltaCover, deltaAmount, hsub, hda, hdv⟩ := LoanBroker.debit_delta res.loanBroker' lb v hz1
      (by rw [hnt1]; exact hnt) hz.cover _ j hj (by rw [hcov]; linarith [lb.exact.coverAvailable_nonneg])
      (by rw [hcov]; ring)
    exact ⟨deltaCover, deltaAmount, hsub, by rw [← hnt1]; exact hda, hdv⟩
  · -- depositing the credit again on the same broker passes the checks and credits it whole
    have hcap1 : lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + res.amount'.toRat ≤ lb.numericType.maxValue.toNat := by
      intro hi
      have h := LoanBroker.OpenZone.cover_le_maxValue _ _ hz1 (by rw [hnt1]; exact hi)
      rw [hnt1, hcov] at h
      exact h
    -- the cover after the deposit is not zero and stored exactly, so an XRP or MPT asset admits offset `0`
    have hoff : lb.numericType.isIntegral = true → (0 : Int) ≤ lb.numericType.maxOffset := by
      intro hi
      have h := LoanBroker.OpenZone.maxOffset_nonneg _ _ hz1 (by rw [hnt1]; exact hi)
        (show (0 : ℚ) < res.loanBroker'.coverAvailable.toRat by rw [hC]; linarith)
      rw [hnt1] at h
      exact h
    have hcan1 := LoanBroker.canCoverDeposit_of_units lb v _ hz hnt hcr htr ⟨j, units_pos hj hpos', hj⟩ hcap1
      hoff (by rw [← hcov]; exact hz1.coverLimit)
    obtain ⟨r, res2, hr2, hres2, hamt⟩ :=
      LoanBroker.coverDeposit_total_proof lb v _ hcr hpos'.le v.baseExponent_range hcan1
    have hfl := LoanBroker.coverDeposit_floor lb v _ res2 hz hnt hcr htr hpos' hcan1 hres2
    rw [hamt, floor_units_self _ _ (j : ℤ) (by rw [hj]; norm_cast)] at hfl
    exact ⟨r, hr2, hfl⟩

/-- Proof body of the STAmount part of `LoanBroker.coverWithdraw_debit`. -/
lemma LoanBroker.coverWithdraw_applied_delta_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    ∃ (deltaCover : Number) (deltaAmount : STAmount),
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.toRat = res.amount'.toRat := by
  subst hvb
  have hz := LoanBroker.Reachable.openZone lb _ hr
  obtain ⟨-, ⟨j, hj⟩, -, -, hle, hcov⟩ := LoanBroker.coverWithdraw_exact lb v amount res hz hc hpos hcan hok
  exact LoanBroker.debit_delta lb _ v hz hnt (LoanBroker.coverWithdraw_openZone lb v amount res hz hnt hc hok).cover
    _ j hj hle hcov

/-- Proof body of the STAmount part of `LoanBroker.coverClawback_debit`. -/
lemma LoanBroker.coverClawback_applied_delta_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    ∃ (deltaCover : Number) (deltaAmount : STAmount),
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.toRat = res.amount'.toRat := by
  subst hvb
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨-, ⟨j, hj⟩, -, hle, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz hmax hok
  exact LoanBroker.debit_delta lb _ v hz hnt (LoanBroker.coverClawback_openZone lb v amount res hz hnt hmax hok).cover
    _ j hj hle hcov

/-- Proof body of `coverDeposit_increase_possible`. -/
lemma LoanBroker.coverDeposit_increase_possible_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hroom : lb.toExact.coverAvailable + 10 ^ base ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ base)
    (hone : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + 1 ≤ lb.numericType.maxValue.toNat)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
        lb.canCoverDeposit v amount = .ok .tesSUCCESS ∧ (lb.coverDeposit v amount).run = .ok (.ok res) ∧
        lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable := by
  subst hvb
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨-, -, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  have hC0 : (0 : ℚ) ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  -- one base unit is a `Number` the asset stores exactly
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 v.baseExponent (by constructor <;> norm_num)
    (Vault.baseExponent_grid v).2
  have hw0 : 0 ≤ w.toRat := by rw [hwv]; positivity
  have hrep : STAmount.isRounded lb.numericType w = false := by
    rw [STAmount.isRounded_eq_false_iff _ w hw hw0, hwv]
    cases hnt' : lb.numericType with
    | fractional =>
      have h := STAmount.representable_fractional_of_units 1 v.baseExponent (by norm_num)
        (by have := (Vault.baseExponent_grid v).1; omega) (by have := v.baseExponent_range.2; omega)
      simpa using h
    | integral mv mo ms msh =>
      rw [hnt'] at hint hone hmaxoff
      have h1 := hone rfl
      have hmv : (1 : ℚ) ≤ (mv.toNat : ℚ) := by
        have : lb.toExact.coverAvailable + 1 ≤ (mv.toNat : ℚ) := h1
        linarith
      refine Or.inr ⟨hmaxoff, 1, by exact_mod_cast hmv, by norm_num, ?_⟩
      rw [hint rfl]
      simp
  -- so it converts to a canonical amount worth one base unit
  obtain ⟨st, hst⟩ := STAmount.ofNumber_ok_of_isRounded_false _ w hrep
  have hsv : st.toRat = 10 ^ v.baseExponent := by
    rw [STAmount.ofNumber_eq_of_isRounded_false _ w st hw hw0 hrep hst, hwv]
    simp
  have hspos : 0 < st.toRat := by rw [hsv]; positivity
  obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ st hmax hst
  have hcs : st.Canonical := hcz.resolve_right (by simp [(STAmount.isZero_eq_false_iff_pos _ hspos.le).2 hspos])
  -- the deposit fits under the asset's maximum and the Open limit, so it passes and credits a unit
  have hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + st.toRat ≤ lb.numericType.maxValue.toNat := by
    intro hi
    rw [hsv, hint hi, zpow_zero]
    exact hone hi
  have hcan := LoanBroker.canCoverDeposit_of_units lb v st hz hnt hcs hty ⟨1, by norm_num, by rw [hsv]; simp⟩ hcap
    (fun _ => hmaxoff) (by rw [hsv]; exact hroom)
  obtain ⟨-, res, -, hres, -⟩ := LoanBroker.coverDeposit_total_proof lb v st hcs hspos.le v.baseExponent_range hcan
  obtain ⟨-, -, -, -, hpos', -, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb _ hr hmax v rfl hnt st hcs hty hspos hcap hcan res hres
  exact ⟨st, res, hcs, hty, hspos, hcan, hres, by rw [hcov]; linarith⟩

/-- Proof body of `coverDeposit_empty`. -/
lemma LoanBroker.coverDeposit_empty_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hzero : lb.coverAvailable = Number.zero)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.toExact.coverAvailable = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base := by
  have h0 : lb.toExact.coverAvailable = 0 := by
    show lb.coverAvailable.toRat = 0
    rw [hzero, Number.toRat_zero]
  -- an empty cover plus a canonical XRP or MPT amount is within the asset's maximum
  have hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat := by
    intro hi
    have hic := (hc.1 (by unfold STAmount.integral; rw [hat]; exact hi)).1
    have habs := STAmount.abs_toRat amount
    rw [hic.offset_zero, zpow_zero, mul_one, abs_of_pos hpos] at habs
    rw [h0, zero_add, habs, ← hat]
    exact_mod_cast hic.in_range
  obtain ⟨-, -, -, -, -, -, hfl, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  rw [hcov, h0, zero_add, hfl]

/-- Proof body of `coverWithdraw_decrease_possible`. -/
lemma LoanBroker.coverWithdraw_decrease_possible_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hpos : 0 < lb.toExact.coverAvailable) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
        lb.canCoverWithdraw v amount = .ok .tesSUCCESS ∧ (lb.coverWithdraw v amount).run = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable < lb.toExact.coverAvailable := by
  subst hvb
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  -- withdraw the whole cover
  obtain ⟨s, hcs, hst, hv, hspos, k, hk0, hk⟩ := LoanBroker.Reachable.exists_cover_amount lb _ hr hmax v rfl hpos
  have hcan := LoanBroker.canCoverWithdraw_of_units lb v s _ hz hcs ⟨k, hk0, hk⟩ hm
    (by rw [Number.toRat_zero, zero_add, hv])
  obtain ⟨-, res, -, hres, -⟩ := LoanBroker.coverWithdraw_total_proof lb v s hcan
  obtain ⟨-, -, -, -, hpos', -, -, hcov⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb _ hr hmax v rfl hnt s hcs hst hspos hcan res hres
  exact ⟨s, res, hcs, hst, hspos, hcan, hres, by rw [hcov]; linarith⟩

/-- Proof body of `coverWithdraw_all`. -/
lemma LoanBroker.coverWithdraw_all_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s) (hnz : s.mValue ≠ 0) :
    lb.canCoverWithdraw v s = .ok .tesSUCCESS ∧
      ∃ res, (lb.coverWithdraw v s).run = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0 := by
  subst hvb
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨hcs, hst, hv, hspos, k, hk0, hk⟩ := LoanBroker.Reachable.cover_amount lb _ hr hmax v rfl s hs hnz
  have hcan := LoanBroker.canCoverWithdraw_of_units lb v s _ hz hcs ⟨k, hk0, hk⟩ hm
    (by rw [Number.toRat_zero, zero_add, hv])
  obtain ⟨-, res, -, hres, -⟩ := LoanBroker.coverWithdraw_total_proof lb v s hcan
  -- the debit is the whole cover, already whole base units
  obtain ⟨-, -, -, -, -, -, hfl, hcov⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb _ hr hmax v rfl hnt s hcs hst hspos hcan res hres
  rw [floor_units_self _ _ (k : ℤ) (by rw [hk]; norm_cast)] at hfl
  exact ⟨hcan, res, hres, by rw [hcov, hfl, hv, sub_self]⟩

/-- Proof body of `coverClawback_decrease_possible`. -/
lemma LoanBroker.coverClawback_decrease_possible_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native)
    (hpos : 0 < lb.toExact.coverAvailable) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
        lb.canCoverClawback v (some amount) = .ok .tesSUCCESS ∧
        (lb.coverClawback v (some amount)).run = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable < lb.toExact.coverAvailable := by
  subst hvb
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  -- claw back the whole cover
  obtain ⟨s, hcs, hst, -, hspos, k, -, hk⟩ := LoanBroker.Reachable.exists_cover_amount lb _ hr hmax v rfl hpos
  have hreq : ∀ a ∈ some s, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat := by
    intro a ha
    cases ha
    exact ⟨Or.inl hcs, hst, hspos.le⟩
  have hcan := LoanBroker.canCoverClawback_of_units lb v (some s) _ hz hnt hxrp hmax hreq
    (fun a ha => by cases ha; exact ⟨k, hk⟩) hm (by rw [Number.toRat_zero]; exact hpos)
  obtain ⟨res, hres⟩ := LoanBroker.coverClawback_lawful_total_proof lb v (some s) hz hnt hmax hreq hcan
  obtain ⟨-, -, hpos', -, hcov⟩ := LoanBroker.coverClawback_exact lb v (some s) res hz hmax hres
  exact ⟨s, res, hcs, hst, hspos, hcan, hres, by rw [hcov]; linarith⟩

/-- Proof body of `coverClawback_all`. -/
lemma LoanBroker.coverClawback_all_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s) (hnz : s.mValue ≠ 0) :
    lb.canCoverClawback v none = .ok .tesSUCCESS ∧
      ∃ res, (lb.coverClawback v none).run = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0 := by
  subst hvb
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨-, -, hv, hspos, -⟩ := LoanBroker.Reachable.cover_amount lb _ hr hmax v rfl s hs hnz
  have hreq : ∀ a ∈ (none : Option STAmount),
      a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat := by
    intro a ha
    cases ha
  have hcan := LoanBroker.canCoverClawback_of_units lb v none _ hz hnt hxrp hmax hreq (fun a ha => by cases ha) hm
    (by rw [Number.toRat_zero, ← hv]; exact hspos)
  obtain ⟨res, hres⟩ := LoanBroker.coverClawback_lawful_total_proof lb v none hz hnt hmax hreq hcan
  -- clawing back with no amount takes all the cover above the minimum, which is zero
  refine ⟨hcan, res, hres, ?_⟩
  rw [LoanBroker.coverClawback_all_leaves_minimum_proof lb v none res _ hz hnt hmax hreq (Or.inl rfl) hm hres,
    Number.toRat_zero]

end XRPL.Model.Lending
