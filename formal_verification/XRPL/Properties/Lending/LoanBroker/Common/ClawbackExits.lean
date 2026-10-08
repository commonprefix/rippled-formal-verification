import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBrokerCoverClawback` exits

Proofs for the clawback exits. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- **Proof body of `roundedCoverClawback_no_excess`.** -/
lemma LoanBroker.roundedCoverClawback_no_excess_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.roundedCoverClawback pool amount = .ok (.rejected .tecINSUFFICIENT_FUNDS) := by
  simp [LoanBroker.roundedCoverClawback, hexp, hmin, hsub, hle]

/-- **Proof body of `roundedCoverClawback_zero_eq_none`.** -/
lemma LoanBroker.roundedCoverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α)
    (a : STAmount) (hz : a.isZero = true) :
    lb.roundedCoverClawback pool (some a) = lb.roundedCoverClawback pool none := by
  simp [LoanBroker.roundedCoverClawback, hz]

/-- **Proof body of `canCoverClawback_zero_eq_none`.** -/
lemma LoanBroker.canCoverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α)
    (a : STAmount) (hz : a.isZero = true) :
    lb.canCoverClawback pool (some a) = lb.canCoverClawback pool none := by
  unfold LoanBroker.canCoverClawback
  rw [LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hz]

/-- **Proof body of `coverClawback_zero_eq_none`.** -/
lemma LoanBroker.coverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α)
    (a : STAmount) (hz : a.isZero = true) :
    lb.coverClawback pool (some a) = lb.coverClawback pool none := by
  unfold LoanBroker.coverClawback
  rw [LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hz]

/-- **Proof body of `roundedCoverClawback_rejected_code`.** -/
lemma LoanBroker.roundedCoverClawback_rejected_code_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rejected ter)) :
    ter = .tecINSUFFICIENT_FUNDS := by
  unfold LoanBroker.roundedCoverClawback at hok
  dsimp only at hok
  cases he : AssetPool.exponent pool lb.numericType with
  | error e => rw [he, err_bind] at hok; exact absurd hok (by simp)
  | ok e =>
    rw [he, ok_bind] at hok
    cases hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e with
    | error e => rw [hm, err_bind] at hok; exact absurd hok (by simp)
    | ok m =>
      rw [hm, ok_bind] at hok
      cases hs : lb.coverAvailable.operator_sub m .downward with
      | error e => rw [hs, err_bind] at hok; exact absurd hok (by simp)
      | ok mx =>
        rw [hs, ok_bind] at hok
        by_cases hle : mx.signum ≤ 0
        · simpa [hle] using hok.symm
        · simp only [hle, if_false] at hok
          revert hok
          cases amount with
          | none =>
            cases ho : STAmount.ofNumber lb.numericType mx .to_nearest <;>
              simp [ho]
          | some a =>
            by_cases hz : a.isZero = true
            · cases ho : STAmount.ofNumber lb.numericType mx .to_nearest <;>
                simp [hz, ho]
            · cases hn : a.toNumber .to_nearest with
              | error e => simp [hz, hn]
              | ok mag =>
                cases ho : STAmount.ofNumber lb.numericType
                    (if mag.operator_gt mx = true then mx else mag) .to_nearest <;>
                  simp_all

/-- The cover above the minimum, rounded down, is normalized and not negative once
it is positive. -/
private lemma maxClaw_facts (lb : LoanBroker) (e : Int) (minimumCover maxClaw : Number)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hpos : 0 < maxClaw.signum) : maxClaw.isNormalized ∧ 0 ≤ maxClaw.toRat := by
  obtain ⟨hneg, hm0⟩ := (signum_pos_iff maxClaw).mp hpos
  exact ⟨operator_sub_isNormalized _ _ _ .downward lb.wf.coverAvailable_norm
      (minimumBrokerCover_isNormalized _ _ _ _ _ hmin) hsub hm0,
    Number.toRat_nonneg_of_nonnegative _ hneg⟩

/-- A clawback that returns an amount had cover above the minimum. -/
private lemma roundedCoverClawback_signum_pos (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw)) : 0 < maxClaw.signum := by
  by_contra hle
  rw [LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin
    hsub (not_lt.mp hle)] at hok
  simp at hok

/-- A full clawback that returns a nonzero amount is within half a unit in its last digit of the
cover above the minimum, because it rounds that cover to nearest. -/
private lemma roundedCoverClawback_all_within_half (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    |claw.toRat - maxClaw.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  have hpos := roundedCoverClawback_signum_pos lb pool amount e minimumCover maxClaw claw hexp hmin
    hsub hok
  have hnle : ¬ maxClaw.signum ≤ 0 := not_le.mpr hpos
  have hclaw : STAmount.ofNumber lb.numericType maxClaw .to_nearest = .ok claw := by
    revert hok
    rcases hall with rfl | ⟨a, rfl, hz⟩
    · cases hc : STAmount.ofNumber lb.numericType maxClaw .to_nearest <;>
        simp [LoanBroker.roundedCoverClawback, hexp, hmin, hsub, hnle, hc]
    · cases hc : STAmount.ofNumber lb.numericType maxClaw .to_nearest <;>
        simp [LoanBroker.roundedCoverClawback, hexp, hmin, hsub, hnle, hz, hc]
  obtain ⟨hxn, hx0⟩ := maxClaw_facts lb e minimumCover maxClaw hmin hsub hpos
  exact STAmount.ofNumber_to_nearest_within_half _ _ _ hxn hx0 hclaw hnz

/-- **Proof body of `roundedCoverClawback_all_upper_bound`.** -/
lemma LoanBroker.roundedCoverClawback_all_upper_bound_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    claw.toRat - maxClaw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  (abs_sub_le_iff.mp (roundedCoverClawback_all_within_half lb pool amount e minimumCover maxClaw
    claw hexp hmin hsub hall hok hnz)).1

/-- **Proof body of `roundedCoverClawback_all_lower_bound`.** -/
lemma LoanBroker.roundedCoverClawback_all_lower_bound_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    maxClaw.toRat - claw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  (abs_sub_le_iff.mp (roundedCoverClawback_all_within_half lb pool amount e minimumCover maxClaw
    claw hexp hmin hsub hall hok hnz)).2

/-- A clawback of a nonzero request that returns a nonzero amount is within half a unit in its last
digit of the smaller of the request and the cover above the minimum, because it rounds that
smaller value to nearest. -/
private lemma roundedCoverClawback_capped_within_half (lb : LoanBroker) (pool : α) (a : STAmount)
    (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hza : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    |claw.toRat - min a.toRat maxClaw.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  have hpos := roundedCoverClawback_signum_pos lb pool (some a) e minimumCover maxClaw claw hexp
    hmin hsub hok
  have hnle : ¬ maxClaw.signum ≤ 0 := not_le.mpr hpos
  obtain ⟨magnitude, hmag⟩ : ∃ magnitude, a.toNumber .to_nearest = .ok magnitude := by
    cases hm : a.toNumber .to_nearest with
    | error err => simp [LoanBroker.roundedCoverClawback, hexp, hmin, hsub, hnle, hza, hm] at hok
    | ok magnitude => exact ⟨magnitude, rfl⟩
  have hclaw : STAmount.ofNumber lb.numericType
      (if magnitude.operator_gt maxClaw = true then maxClaw else magnitude) .to_nearest =
        .ok claw := by
    revert hok
    cases hc : STAmount.ofNumber lb.numericType
        (if magnitude.operator_gt maxClaw = true then maxClaw else magnitude) .to_nearest <;>
      simp [LoanBroker.roundedCoverClawback, hexp, hmin, hsub, hnle, hza, hmag, hc]
  obtain ⟨hxn, hx0⟩ := maxClaw_facts lb e minimumCover maxClaw hmin hsub hpos
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of a magnitude hac hmag
  -- the converted value is the smaller of the request and the cover above the minimum
  have hc : (if magnitude.operator_gt maxClaw = true then maxClaw else magnitude).toRat =
      min a.toRat maxClaw.toRat := by
    split_ifs with hgt
    · rw [operator_gt_iff magnitude maxClaw hmn hxn, hmv] at hgt
      exact (min_eq_right hgt.le).symm
    · rw [operator_gt_iff magnitude maxClaw hmn hxn, hmv, not_lt] at hgt
      rw [hmv]
      exact (min_eq_left hgt).symm
  have hcn :
      (if magnitude.operator_gt maxClaw = true then maxClaw else magnitude).isNormalized := by
    split_ifs <;> assumption
  have h := STAmount.ofNumber_to_nearest_within_half _ _ _ hcn (by rw [hc]; exact le_min ha0 hx0)
    hclaw hnz
  rwa [hc] at h

/-- **Proof body of `roundedCoverClawback_capped_upper_bound`.** -/
lemma LoanBroker.roundedCoverClawback_capped_upper_bound_proof (lb : LoanBroker) (pool : α)
    (a : STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hza : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    claw.toRat - min a.toRat maxClaw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  (abs_sub_le_iff.mp (roundedCoverClawback_capped_within_half lb pool a e minimumCover maxClaw claw
    hexp hmin hsub hza hac ha0 hok hnz)).1

/-- **Proof body of `roundedCoverClawback_capped_lower_bound`.** -/
lemma LoanBroker.roundedCoverClawback_capped_lower_bound_proof (lb : LoanBroker) (pool : α)
    (a : STAmount) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hza : a.isZero = false)
    (hac : a.ExactCanonical) (ha0 : 0 ≤ a.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw))
    (hnz : claw.mValue ≠ 0) :
    min a.toRat maxClaw.toRat - claw.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent :=
  (abs_sub_le_iff.mp (roundedCoverClawback_capped_within_half lb pool a e minimumCover maxClaw claw
    hexp hmin hsub hza hac ha0 hok hnz)).2

/-- **Proof body of `canCoverClawback_no_excess`.** -/
lemma LoanBroker.canCoverClawback_no_excess_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.canCoverClawback pool amount = .ok .tecINSUFFICIENT_FUNDS := by
  simp [LoanBroker.canCoverClawback,
    LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin hsub hle]

/-- **Proof body of `canCoverClawback_precision_loss`.** -/
lemma LoanBroker.canCoverClawback_precision_loss_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw rn : STAmount)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hz : claw.isZero = true ∨
      (roundToCoverScale lb.numericType lb.coverAvailable claw .to_nearest = .ok rn ∧
        rn.signum = 0)) :
    lb.canCoverClawback pool amount = .ok .tecPRECISION_LOSS := by
  by_cases hza : claw.isZero = true
  · simp [LoanBroker.canCoverClawback, hrounded, canApplyToBrokerCover_zero _ _ _ hza]
  · have hza' : claw.isZero = false := by simpa using hza
    obtain ⟨hnear, hrn⟩ := hz.resolve_left hza
    simp [LoanBroker.canCoverClawback, hrounded,
      canApplyToBrokerCover_rounds_zero _ _ _ _ hza' hnear hrn]

/-- **Proof body of `canCoverClawback_success`.** -/
lemma LoanBroker.canCoverClawback_success_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw rn : STAmount)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.isZero = false)
    (hnear : roundToCoverScale lb.numericType lb.coverAvailable claw .to_nearest = .ok rn)
    (hrn : rn.signum ≠ 0) :
    lb.canCoverClawback pool amount = .ok .tesSUCCESS := by
  simp [LoanBroker.canCoverClawback, hrounded, canApplyToBrokerCover_pass _ _ _ _ hnz hnear hrn]

/-- **Proof body of `canCoverClawback_error_codes`.** -/
lemma LoanBroker.canCoverClawback_error_codes_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (ter : TER) (hok : lb.canCoverClawback pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS := by
  unfold LoanBroker.canCoverClawback at hok
  cases hr : lb.roundedCoverClawback pool amount with
  | error e => rw [hr, err_bind] at hok; exact absurd hok (by simp)
  | ok rr =>
    rw [hr, ok_bind] at hok
    cases rr with
    | rejected t =>
      have := LoanBroker.roundedCoverClawback_rejected_code_proof lb pool amount t hr
      subst this
      exact Or.inr (Or.inl (by simpa using hok.symm))
    | rounded claw =>
      rcases canApplyToBrokerCover_error_codes _ _ _ ter hok with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- A clawback whose checks passed computed a nonzero clawed amount. -/
lemma LoanBroker.canCoverClawback_success_inv (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS) :
    ∃ claw, lb.roundedCoverClawback pool amount = .ok (.rounded claw) ∧ claw.mValue ≠ 0 := by
  unfold LoanBroker.canCoverClawback at hcan
  obtain ⟨rr, hrr, hcan⟩ := bind_ok_peel _ _ _ hcan
  cases rr with
  | rejected t =>
    have := LoanBroker.roundedCoverClawback_rejected_code_proof lb pool amount t hrr
    subst this
    simp at hcan
  | rounded claw =>
    refine ⟨claw, hrr, fun h0 => ?_⟩
    have hz : claw.isZero = true := by simp [STAmount.isZero, h0]
    dsimp only at hcan
    rw [canApplyToBrokerCover_zero _ _ _ hz] at hcan
    simp at hcan

/-- A clawback whose checks passed claws a nonzero amount. -/
lemma LoanBroker.coverClawback_amount_nonzero (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res)) : res.amount'.mValue ≠ 0 := by
  obtain ⟨claw, hrr, hnz⟩ := LoanBroker.canCoverClawback_success_inv lb pool amount hcan
  obtain ⟨claw', hrr', happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  rw [hrr, Except.ok.injEq, RoundingResult.rounded.injEq] at hrr'
  subst hrr'
  rw [LoanBroker.applyCoverTransaction_amount' lb _ _ res happ]
  exact hnz

/-- **Proof body of `coverClawback_no_excess`.** -/
lemma LoanBroker.coverClawback_no_excess_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.coverClawback pool amount = .ok (.error .tecINTERNAL) := by
  simp [LoanBroker.coverClawback,
    LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin hsub hle]

/-- **Proof body of `coverClawback_negative_cover`.** -/
lemma LoanBroker.coverClawback_negative_cover_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw : STAmount) (clawN c' : Number)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnum : claw.toNumber .to_nearest = .ok clawN)
    (hsub : lb.coverAvailable.operator_sub clawN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    lb.coverClawback pool amount = .error .notLawful := by
  simp [LoanBroker.coverClawback, LoanBroker.applyCoverTransaction, hrounded, hnum, hsub,
    RawLoanBroker.to_lawful_negative_cover lb c' hneg]

/-- **Proof body of `coverClawback_success`.** -/
lemma LoanBroker.coverClawback_success_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw : STAmount) (clawN c' : Number)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hc : claw.ExactCanonical) (hnum : claw.toNumber .to_nearest = .ok clawN)
    (hge : lb.coverAvailable.operator_lt clawN = false)
    (hsub : lb.coverAvailable.operator_sub clawN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverClawback pool amount = .ok (.ok ⟨claw, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  obtain ⟨_, hcn⟩ := STAmount.toNumber_exact_of claw clawN hc hnum
  obtain ⟨lb', htl, hraw⟩ := LoanBroker.debit_lawful lb clawN c' hcn hge hsub
  refine ⟨lb', ?_, hraw⟩
  simp [LoanBroker.coverClawback, LoanBroker.applyCoverTransaction, hrounded, hnum, hsub, htl]

/-- **Proof body of `coverClawback_error_codes`.** -/
lemma LoanBroker.coverClawback_error_codes_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : lb.coverClawback pool amount = .ok (.error ter)) : ter = .tecINTERNAL := by
  unfold LoanBroker.coverClawback at hok
  obtain ⟨rr, _, hok⟩ := bind_ok_peel _ _ _ hok
  cases rr with
  | rejected t => simp at hok; exact hok.symm
  | rounded r =>
    simp only [except_pure_eq, ok_bind] at hok
    obtain ⟨res, _, hok⟩ := bind_ok_peel _ _ _ hok
    simp at hok

end XRPL.Model.Lending
