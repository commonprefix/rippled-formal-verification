import XRPL.Properties.Lending.LoanBroker.Common.ReachableDefs
import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs
import XRPL.Properties.Lending.LoanBroker.Common.Create
import XRPL.Properties.Lending.LoanBroker.Common.CoverGrid
import XRPL.Properties.Lending.LoanBroker.Common.CoverCredit
import XRPL.Properties.Lending.LoanBroker.Common.CoverDebit
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete

/-! # A broker-only history stays in the Open zone

Every cover operation moves CoverAvailable by whole base units, a deposit only past the Open-limit check, and
DebtMaximum is checked onto the base grid. So CoverAvailable stays whole base units within the limit, stored exactly. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Zero is on every exponent grid. -/
private lemma Number.zero_isOnExponentGrid (e : Int) (nt : NumericType) :
    Number.zero.isOnExponentGrid e nt = .ok true := by
  cases nt <;> rfl

/-- An XRP or MPT amount stored exactly and not zero admits offset `0` and is within the maximum. -/
private lemma integral_facts_of_exact (nt : NumericType) (c : Number) (hn : c.isNormalized)
    (h0 : 0 ≤ c.toRat) (hex : STAmount.isRounded nt c = false) (hint : nt.isIntegral = true)
    (hnz : c.toRat ≠ 0) : 0 ≤ nt.maxOffset ∧ c.toRat ≤ nt.maxValue.toNat := by
  rw [STAmount.isRounded_eq_false_iff nt c hn h0] at hex
  cases hnt : nt with
  | fractional => rw [hnt] at hint; cases hint
  | integral maxValue maxOffset mulSqrt mulShift =>
    rw [hnt] at hex
    rcases hex with h | ⟨hoff, k, hkm, -, hk⟩
    · exact absurd h hnz
    · refine ⟨hoff, ?_⟩
      rw [hk]
      exact_mod_cast hkm

/-- A new broker starts in the Open zone: no cover, and DebtMaximum zero or checked onto the base
grid. -/
lemma LoanBroker.create_openZone (v : Vault) (tx : LoanBrokerSetCreate) (lb : LoanBroker)
    (hcan : LoanBroker.canCreate v tx.debtMaximum v.numericType = .ok .tesSUCCESS)
    (hc : LoanBroker.create tx v.numericType = .ok lb) : lb.OpenZone v.baseExponent := by
  obtain ⟨-, hcov, -⟩ := LoanBroker.create_no_exposure_proof tx _ lb hc
  unfold LoanBroker.create at hc
  have hraw := (RawLoanBroker.to_lawful_ok hc).1
  have hnt : lb.numericType = v.numericType := by
    show lb.toRawLoanBroker.numericType = _; rw [hraw]; rfl
  have hdm : lb.debtMaximum = tx.debtMaximum.getD Number.zero := by
    show lb.toRawLoanBroker.debtMaximum = _; rw [hraw]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcov]; exact Number.OnGrid.zero _
  · show lb.coverAvailable.toRat ≤ _
    rw [hcov, Number.toRat_zero]; positivity
  · rw [hcov]; exact STAmount.isRounded_zero _
  · rw [hdm, hnt]
    cases hdt : tx.debtMaximum with
    | none => exact Number.zero_isOnExponentGrid _ _
    | some dm =>
      rw [hdt] at hcan
      exact LoanBroker.canCreate_grid v dm _ hcan

/-- An update keeps the Open zone: the cover does not move, and a new DebtMaximum passed the
base-grid check. -/
lemma LoanBroker.update_openZone (lb lb' : LoanBroker) (v : Vault) (dm : Option Number)
    (hz : lb.OpenZone v.baseExponent) (hcan : lb.canUpdate v dm = .ok .tesSUCCESS)
    (hok : lb.update dm = .ok lb') : lb'.OpenZone v.baseExponent := by
  rw [LoanBroker.update_eq] at hok
  have hraw := (RawLoanBroker.to_lawful_ok hok).1
  have hcov : lb'.coverAvailable = lb.coverAvailable := by
    show lb'.toRawLoanBroker.coverAvailable = _; rw [hraw]
  have hnt : lb'.numericType = lb.numericType := by
    show lb'.toRawLoanBroker.numericType = _; rw [hraw]
  have hdm : lb'.debtMaximum = dm.getD lb.debtMaximum := by
    show lb'.toRawLoanBroker.debtMaximum = _; rw [hraw]
  refine ⟨hcov ▸ hz.cover, ?_, by rw [hnt, hcov]; exact hz.coverExact, ?_⟩
  · show lb'.coverAvailable.toRat ≤ _
    rw [hcov]; exact hz.coverLimit
  · rw [hdm, hnt]
    cases dm with
    | none => exact hz.debtMaximum
    | some d => exact LoanBroker.canUpdate_grid lb v d hcan

/-- A deposit keeps the Open zone: the credit is whole base units, the Open-limit check keeps the
cover within the limit, and an XRP or MPT cover stays within the asset's maximum. -/
lemma LoanBroker.coverDeposit_openZone (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.OpenZone v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  have hb : (-96 : ℤ) ≤ AssetPool.baseExponent v ∧ AssetPool.baseExponent v ≤ 80 := v.baseExponent_range
  obtain ⟨r, hr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb v amount res hok
  obtain ⟨m, c', hm, hadd, -, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  have hnt' : res.loanBroker'.numericType = lb.numericType := by
    have h := congrArg RawLoanBroker.numericType hraw; exact h
  have hdm' : res.loanBroker'.debtMaximum = lb.debtMaximum := by
    have h := congrArg RawLoanBroker.debtMaximum hraw; exact h
  have hcv : res.loanBroker'.coverAvailable = c' := by
    have h := congrArg RawLoanBroker.coverAvailable hraw; exact h
  have hgrid := LoanBroker.coverDeposit_onGrid lb v amount res hint hz.cover hok
  have hlim : res.loanBroker'.toExact.coverAvailable ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent :=
    le_trans (LoanBroker.coverDeposit_le lb v amount res hz.cover hint hcan hok) (max_le hz.coverLimit le_rfl)
  obtain ⟨k, hk, hkv⟩ := Number.OnGrid.units_le _ _ hgrid res.loanBroker'.exact.coverAvailable_nonneg hlim
  refine ⟨hgrid, hlim, ?_, by rw [hdm', hnt']; exact hz.debtMaximum⟩
  rw [hnt']
  refine STAmount.isRounded_false_of_units _ _ _ k res.loanBroker'.wf.coverAvailable_norm hkv hk ⟨hblo, hbhi⟩ hint ?_
  intro hi _
  have hb0 := hint hi
  -- the credit is whole units, converts back exactly and is at most the amount
  obtain ⟨aN, hanum, hs, hrpos⟩ := LoanBroker.roundedCoverAmount_ok lb v amount r hr
  obtain ⟨hrle, hrnum⟩ := LoanBroker.roundedCoverAmount_le lb v amount r hc hpos.le hb hr
  obtain ⟨hmv, hmn⟩ := hrnum m hm
  have hmg := sumRoundAndSubtract_onGrid _ _ _ _ _ r m hz.cover ⟨hblo, hbhi⟩ hint hs hm
  have hsum0 : 0 ≤ lb.toExact.coverAvailable + m.toRat := add_nonneg lb.exact.coverAvailable_nonneg
    (by rw [hmv]; exact ((STAmount.signum_pos_iff_toRat_pos r).mp hrpos).le)
  -- an XRP or MPT asset has a maximum within `2^63 - 1`
  have hmaxRep : lb.numericType.maxValue.toNat ≤ 2 ^ 63 - 1 := by
    have hci := hc.1 (by unfold STAmount.integral; rw [hat]; exact hi)
    rw [hat] at hci
    have : lb.numericType.maxValue.toNat ≤ maxRep.toNat := hci.2
    have hrep : maxRep.toNat = 2 ^ 63 - 1 := by decide
    rw [hrep] at this
    exact this
  -- the sum of whole units is exact
  obtain ⟨-, jc, hjc⟩ := hz.cover
  obtain ⟨-, jm, hjm⟩ := hmg
  rw [hb0] at hjc hjm
  have hcap' := hcap hi
  have hsumle : lb.toExact.coverAvailable + m.toRat ≤ lb.numericType.maxValue.toNat := by
    rw [hmv]; linarith
  have hab : -2 ^ 63 < jc + jm ∧ jc + jm < 2 ^ 63 := by
    have h1 : ((jc + jm : ℤ) : ℚ) = lb.toExact.coverAvailable + m.toRat := by
      show _ = lb.coverAvailable.toRat + m.toRat
      rw [hjc, hjm]; push_cast; ring
    have h2 : (0 : ℚ) ≤ ((jc + jm : ℤ) : ℚ) := h1 ▸ hsum0
    have h3 : ((jc + jm : ℤ) : ℚ) ≤ ((lb.numericType.maxValue.toNat : ℤ) : ℚ) := by
      rw [h1]; push_cast; exact hsumle
    have h2' : (0 : ℤ) ≤ jc + jm := by exact_mod_cast h2
    have h3' : jc + jm ≤ (lb.numericType.maxValue.toNat : ℤ) := by exact_mod_cast h3
    omega
  have hexact := Number.operator_add_toRat_of_grid _ _ _ jc jm 0 lb.wf.coverAvailable_norm hmn hjc hjm hab
    (by unfold minExponent maxExponent; omega) hadd
  constructor
  · -- a nonzero XRP or MPT credit admits offset `0`
    unfold sumRoundAndSubtract at hs
    rw [if_pos hi] at hs
    simp only [bind_pure] at hs
    have hr0 : r.mValue ≠ 0 := by
      intro h0
      have : r.signum = 0 := by simp [STAmount.signum, h0]
      omega
    exact STAmount.ofNumber_integral_maxOffset_nonneg _ _ _ r hi hs hr0
  · have hkc : (k : ℚ) = c'.toRat := by rw [← hcv]; rw [hkv, hb0]; simp
    have : (k : ℚ) ≤ lb.numericType.maxValue.toNat := by
      rw [hkc, hexact]
      have h1 : ((jc + jm : ℤ) : ℚ) * (10 : ℚ) ^ (0 : ℤ) = lb.toExact.coverAvailable + m.toRat := by
        show _ = lb.coverAvailable.toRat + m.toRat
        rw [hjc, hjm]; push_cast; ring
      rw [h1]; exact hsumle
    exact_mod_cast this

/-- A debit that keeps the cover on the base grid keeps the Open zone: the cover only goes down. -/
private lemma LoanBroker.debit_openZone (lb : LoanBroker) (v : Vault) (a : STAmount) (res : LoanBrokerCoverResult)
    (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType) (ha : a.CanonicalOrZero)
    (ha0 : 0 ≤ a.toRat) (happ : lb.applyCoverTransaction .debit a = .ok res)
    (hgrid : Number.OnGrid v.baseExponent res.loanBroker'.coverAvailable) :
    res.loanBroker'.OpenZone v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  obtain ⟨m, c', -, -, -, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  have hnt' : res.loanBroker'.numericType = lb.numericType := by
    have h := congrArg RawLoanBroker.numericType hraw; exact h
  have hdm' : res.loanBroker'.debtMaximum = lb.debtMaximum := by
    have h := congrArg RawLoanBroker.debtMaximum hraw; exact h
  have hle := LoanBroker.applyCoverTransaction_debit_le lb a res ha ha0 happ
  have hlim : res.loanBroker'.toExact.coverAvailable ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent :=
    le_trans hle hz.coverLimit
  have h0 := res.loanBroker'.exact.coverAvailable_nonneg
  obtain ⟨k, hk, hkv⟩ := Number.OnGrid.units_le _ _ hgrid h0 hlim
  refine ⟨hgrid, hlim, ?_, by rw [hdm', hnt']; exact hz.debtMaximum⟩
  rw [hnt']
  refine STAmount.isRounded_false_of_units _ _ _ k res.loanBroker'.wf.coverAvailable_norm hkv hk ⟨hblo, hbhi⟩ hint ?_
  intro hi hk0
  -- the cover was at least the new cover, so it was not zero, and the asset stored it exactly
  have hb0 := hint hi
  have hkpos : (0 : ℚ) < res.loanBroker'.toExact.coverAvailable := by
    show (0 : ℚ) < res.loanBroker'.coverAvailable.toRat
    rw [hkv, hb0]; simp; omega
  have hcpos : lb.coverAvailable.toRat ≠ 0 := by
    have : (0 : ℚ) < lb.coverAvailable.toRat := lt_of_lt_of_le hkpos hle
    exact this.ne'
  obtain ⟨hoff, hcmax⟩ := integral_facts_of_exact _ _ lb.wf.coverAvailable_norm lb.exact.coverAvailable_nonneg
    hz.coverExact hi hcpos
  refine ⟨hoff, ?_⟩
  have : (k : ℚ) ≤ lb.numericType.maxValue.toNat := by
    have h1 : (k : ℚ) = res.loanBroker'.coverAvailable.toRat := by rw [hkv, hb0]; simp
    rw [h1]; exact le_trans hle hcmax
  exact_mod_cast this

/-- A withdrawal keeps the Open zone. -/
lemma LoanBroker.coverWithdraw_openZone (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    res.loanBroker'.OpenZone v.baseExponent := by
  obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb v amount res hok
  obtain ⟨hac, -, ha0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ a _
    (STAmount.CanonicalOrZero.operator_neg (Or.inl hc)) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  exact LoanBroker.debit_openZone lb v a res hz hnt hac ha0 happ
    (LoanBroker.coverWithdraw_onGrid lb v amount res (Or.inl hc) hz.cover hok)

/-- A clawback keeps the Open zone. -/
lemma LoanBroker.coverClawback_openZone (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.loanBroker'.OpenZone v.baseExponent := by
  obtain ⟨c, hc, happ⟩ := LoanBroker.coverClawback_ok_inv lb v amount res hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, _⟩ := LoanBroker.roundedCoverClawback_ok lb v amount c hc
  have hcz := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ c _
    (STAmount.CanonicalOrZero.operator_neg hcz) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hgrid : Number.OnGrid v.baseExponent res.loanBroker'.coverAvailable := by
    by_cases hi : lb.numericType.isIntegral = true
    · exact LoanBroker.coverClawback_onGrid_integral lb v amount res hi (hmax hi) hz.cover hok
    · exact LoanBroker.coverClawback_onGrid lb v amount res
        (NumericType.eq_fractional_of_not_integral (by simpa using hi)) hz.cover hok
  exact LoanBroker.debit_openZone lb v c res hz hnt hcc hc0 happ hgrid

/-- Every broker reachable from one in the Open zone stays in it. -/
lemma LoanBroker.ReachableFrom.openZone (base : Int) (start lb : LoanBroker)
    (hmax : start.numericType.isIntegral = true → start.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hz : start.OpenZone base) (hr : LoanBroker.ReachableFrom base start lb) : lb.OpenZone base := by
  induction hr with
  | refl => exact hz
  | update lb lb' v dm hrf hvb _ hcan hok ih =>
    rw [← hvb] at ih ⊢
    exact LoanBroker.update_openZone lb lb' v dm ih hcan hok
  | coverDeposit lb v amount res hrf hvb hnt hc hat hpos hcap hcan hok ih =>
    rw [← hvb] at ih ⊢
    exact LoanBroker.coverDeposit_openZone lb v amount res ih hnt hc hat hpos hcap hcan hok
  | coverWithdraw lb v amount res hrf hvb hnt hc _ _ _ hok ih =>
    rw [← hvb] at ih ⊢
    exact LoanBroker.coverWithdraw_openZone lb v amount res ih hnt hc hok
  | coverClawback lb v amount res hrf hvb hnt _ _ hok ih =>
    rw [← hvb] at ih ⊢
    have hnt' := (LoanBroker.ReachableFrom.fixed_fields base start lb hrf).numericType
    exact LoanBroker.coverClawback_openZone lb v amount res ih hnt (by rw [hnt']; exact hmax) hok

/-- Every reachable broker whose asset maximum fits an `int64` amount is in the Open zone of its vault. -/
lemma LoanBroker.Reachable.openZone_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) :
    lb.OpenZone base := by
  obtain ⟨v, tx, start, hvb, hcan, hc, hrf⟩ := hr
  have hz := LoanBroker.create_openZone v tx start hcan hc
  rw [hvb] at hz
  have hnt := (LoanBroker.ReachableFrom.fixed_fields base start lb hrf).numericType
  exact LoanBroker.ReachableFrom.openZone base start lb (by rw [← hnt]; exact hmax) hz hrf

/-- An XRP or MPT cover in the Open zone is within the asset's maximum amount. -/
lemma LoanBroker.OpenZone.cover_le_maxValue (lb : LoanBroker) (base : Int) (hz : lb.OpenZone base)
    (hint : lb.numericType.isIntegral = true) :
    lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat := by
  have h0 : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  by_cases hnz : lb.toExact.coverAvailable = 0
  · rw [hnz]; positivity
  · exact (integral_facts_of_exact _ _ lb.wf.coverAvailable_norm h0 hz.coverExact hint hnz).2

/-- An XRP or MPT asset holding a nonzero cover in the Open zone accepts whole amounts (offset 0). -/
lemma LoanBroker.OpenZone.maxOffset_nonneg (lb : LoanBroker) (base : Int) (hz : lb.OpenZone base)
    (hint : lb.numericType.isIntegral = true) (hpos : 0 < lb.toExact.coverAvailable) :
    (0 : Int) ≤ lb.numericType.maxOffset :=
  (integral_facts_of_exact _ _ lb.wf.coverAvailable_norm hpos.le hz.coverExact hint (ne_of_gt hpos)).1

/-- A cover the asset stores exactly is paid back exactly on deletion. -/
lemma LoanBroker.roundedCoverAvailable_of_exact (lb : LoanBroker) (s : STAmount)
    (hex : STAmount.isRounded lb.numericType lb.coverAvailable = false)
    (hok : lb.roundedCoverAvailable = .ok s) : s.toRat = lb.toExact.coverAvailable := by
  unfold STAmount.isRounded at hex
  unfold LoanBroker.roundedCoverAvailable at hok
  cases he : STAmount.equalAfterNumberConvert lb.numericType lb.coverAvailable with
  | error e => rw [he] at hex; cases hex
  | ok b =>
    rw [he] at hex
    have hb : b = true := by simpa using hex
    subst hb
    unfold STAmount.equalAfterNumberConvert at he
    rw [hok] at he
    simp only [bind, Except.bind] at he
    cases hn : s.toNumber .to_nearest with
    | error e => rw [hn] at he; cases he
    | ok num =>
      rw [hn] at he
      have heq : num.operator_eq lb.coverAvailable = true := by simpa [pure, Except.pure] using he
      obtain ⟨hmv, hmn⟩ := STAmount.ofNumber_toNumber_exact _ _ _ _ s num lb.wf.coverAvailable_norm
        (fun _ => lb.exact.coverAvailable_nonneg) hok hn
      have hv := (operator_eq_iff num lb.coverAvailable hmn lb.wf.coverAvailable_norm).mp heq
      show s.toRat = lb.coverAvailable.toRat
      rw [← hmv, hv]

/-- A cover in the Open zone is at most `9 * 10^15`. -/
lemma LoanBroker.OpenZone.cover_le (lb : LoanBroker) (b : Int) (hz : lb.OpenZone b) (hb : b ≤ 0) :
    lb.coverAvailable.toRat ≤ 9 * 10 ^ 15 := by
  have hL : lb.coverAvailable.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ b := hz.coverLimit
  have h1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hb
  linarith

/-- The minimum cover is a whole number of base units. -/
lemma minimumBrokerCover_onGrid (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (b : Int)
    (m : Number) (hb : (-81 : ℤ) ≤ b ∧ b ≤ 80) (hint : nt.isIntegral = true → b ≤ 0)
    (hm : minimumBrokerCover nt debtTotal rate b = .ok m) : Number.OnGrid b m := by
  unfold minimumBrokerCover at hm
  obtain ⟨_, _, hm⟩ := bind_ok_peel _ _ _ hm
  exact STAmount.roundToNumericType_onGrid _ _ _ _ _ hb hint hm

/-- A reachable broker whose asset maximum fits an `int64` amount is in the Open zone of its vault, and its
minimum cover is zero. -/
lemma LoanBroker.Reachable.zone_setup (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) :
    lb.OpenZone v.baseExponent ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok Number.zero := by
  refine ⟨hvb ▸ LoanBroker.Reachable.openZone_proof lb base hr hmax, ?_⟩
  rw [LoanBroker.Reachable.debtTotal_zero_proof lb base hr]
  exact minimumBrokerCover_zero_debt _ _ _

/-- A broker in the Open zone with no debt stores every amount exactly, so `associateAsset` changes
nothing. -/
lemma LoanBroker.OpenZone.not_assetsRounded (lb : LoanBroker) (base : Int) (hz : lb.OpenZone base)
    (hdebt : lb.debtTotal = Number.zero) : ¬ lb.assetsRounded := by
  unfold LoanBroker.assetsRounded
  rw [hdebt, STAmount.isRounded_zero, Number.isRounded_eq_false_of_isOnExponentGrid _ _ _ hz.debtMaximum,
    hz.coverExact]
  simp

/-- `associateAsset` changes nothing on a reachable broker whose asset maximum fits an `int64` amount. -/
lemma LoanBroker.Reachable.associateAsset_noop_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) :
    ¬ lb.assetsRounded :=
  LoanBroker.OpenZone.not_assetsRounded lb base (LoanBroker.Reachable.openZone_proof lb base hr hmax)
    (LoanBroker.Reachable.debtTotal_zero_proof lb base hr)

end XRPL.Model.Lending
