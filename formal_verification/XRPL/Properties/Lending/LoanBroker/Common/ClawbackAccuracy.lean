import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBroker.coverClawback` theorems

The clawed amount is the capped amount rounded to nearest. The capped amount is
at most the cover above the minimum cover, so the clawback can only overshoot
the minimum by the rounding. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- A rounded clawback computed the vault scale and the minimum cover. -/
lemma LoanBroker.roundedCoverClawback_minimum (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw : STAmount)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw)) :
    ∃ (e : Int) (minimumCover : Number), AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover := by
  unfold LoanBroker.roundedCoverClawback at hok
  obtain ⟨e, he, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨m, hm, _⟩ := bind_ok_peel _ _ _ hok
  exact ⟨e, m, he, hm⟩

/-- A rounded clawback amount is a capped amount converted to the vault asset.
The capped amount is normalized, nonnegative, at most `coverAvailable` minus the
minimum cover, and at most a nonzero requested amount. -/
private lemma LoanBroker.roundedCoverClawback_rounded_inv (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (claw : STAmount) (e : Int) (minimumCover : Number)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rounded claw)) :
    ∃ c : Number, c.isNormalized ∧ 0 ≤ c.toRat ∧
      c.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat ∧
      STAmount.ofNumber lb.numericType c .to_nearest = .ok claw ∧
      (∀ a ∈ amount, a.isZero = false → c.toRat ≤ a.toRat) := by
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  unfold LoanBroker.roundedCoverClawback at hok
  dsimp only at hok
  rw [hexp, ok_bind, hmin, ok_bind] at hok
  obtain ⟨mx, hs, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hle : mx.signum ≤ 0
  · simp [hle] at hok
  simp only [hle, if_false] at hok
  -- the cover above the minimum is positive, normalized, and at most the exact difference
  obtain ⟨hmxneg, hmx0⟩ := (signum_pos_iff mx).mp (not_le.mp hle)
  have hmxn : mx.isNormalized :=
    operator_sub_isNormalized _ _ _ .downward lb.wf.coverAvailable_norm hmn hs hmx0
  have hmxle : mx.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat := by
    obtain ⟨n, hn, heq⟩ :=
      operator_sub_rounded_downward _ _ _ lb.wf.coverAvailable_norm hmn hs hmx0
    exact heq ▸ Number.lower_le _ n hn
  have hmx0' : 0 ≤ mx.toRat := Number.toRat_nonneg_of_nonnegative mx hmxneg
  -- the capped amount is the cover above the minimum, or the smaller requested amount
  cases amount with
  | none =>
    simp only [pure_eq, except_pure_eq, ok_bind] at hok
    obtain ⟨claw', hcl, hok⟩ := bind_ok_peel _ _ _ hok
    simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hok
    subst hok
    exact ⟨mx, hmxn, hmx0', hmxle, hcl, fun a ha => absurd ha (by simp)⟩
  | some a =>
    by_cases hz : a.isZero = true
    · simp only [pure_eq, except_pure_eq, ok_bind, hz, if_true] at hok
      obtain ⟨claw', hcl, hok⟩ := bind_ok_peel _ _ _ hok
      simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hok
      subst hok
      refine ⟨mx, hmxn, hmx0', hmxle, hcl, fun a' ha' hz' => ?_⟩
      rw [Option.mem_def, Option.some_inj] at ha'
      subst ha'
      rw [hz] at hz'
      exact absurd hz' (by decide)
    · simp only [pure_eq, except_pure_eq, ok_bind, hz, Bool.false_eq_true, if_false] at hok
      obtain ⟨mag, hmag, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨claw', hcl, hok⟩ := bind_ok_peel _ _ _ hok
      simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hok
      subst hok
      obtain ⟨hac, ha0⟩ := hreq a rfl (by simpa using hz)
      obtain ⟨hmagv, hmagn⟩ := STAmount.toNumber_exact_of a mag hac hmag
      by_cases hgt : mag.operator_gt mx = true
      · rw [if_pos hgt] at hcl
        have hlt : mx.toRat < mag.toRat := (operator_gt_iff mag mx hmagn hmxn).mp hgt
        refine ⟨mx, hmxn, hmx0', hmxle, hcl, fun a' ha' _ => ?_⟩
        rw [Option.mem_def, Option.some_inj] at ha'
        subst ha'
        rw [← hmagv]; exact hlt.le
      · rw [if_neg hgt] at hcl
        have hnlt : ¬ mx.toRat < mag.toRat := by
          rw [← operator_gt_iff mag mx hmagn hmxn]; exact hgt
        refine ⟨mag, hmagn, by rw [hmagv]; exact ha0, le_trans (not_lt.mp hnlt) hmxle, hcl,
          fun a' ha' _ => ?_⟩
        rw [Option.mem_def, Option.some_inj] at ha'
        subst ha'
        exact hmagv.le

/-- A canonical request no larger than the cover above the minimum is no larger
than the cap the clawback computes, that difference rounded down. -/
private lemma LoanBroker.request_le_maxClaw (lb : LoanBroker) (a : STAmount) (minimumCover mx : Number)
    (hac : a.ExactCanonical) (hmn : minimumCover.isNormalized)
    (hs : lb.coverAvailable.operator_sub minimumCover .downward = .ok mx) (hmx0 : mx.mantissa_ ≠ 0)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat) : a.toRat ≤ mx.toRat := by
  obtain ⟨aN, _, hav, han⟩ := STAmount.toNumber_exact_canonical a .to_nearest hac
  obtain ⟨n, hn, heq⟩ := operator_sub_rounded_downward _ _ _ lb.wf.coverAvailable_norm hmn hs hmx0
  rw [heq, ← hav]
  exact Number.lower_tight _ n hn aN han (by rw [hav]; exact hfit)

/-- A rounded clawback of a nonzero request converts the smaller of the request
and the cover above the minimum to the vault asset. -/
private lemma LoanBroker.roundedCoverClawback_some_inv (lb : LoanBroker) (pool : α) (a claw : STAmount)
    (e : Int) (minimumCover : Number) (hac : a.ExactCanonical) (hnz : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw)) :
    ∃ mx mag : Number, lb.coverAvailable.operator_sub minimumCover .downward = .ok mx ∧
      mx.isNormalized ∧ mx.mantissa_ ≠ 0 ∧ mag.isNormalized ∧ mag.toRat = a.toRat ∧
      STAmount.ofNumber lb.numericType (if mag.operator_gt mx = true then mx else mag)
        .to_nearest = .ok claw := by
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  unfold LoanBroker.roundedCoverClawback at hok
  dsimp only at hok
  rw [hexp, ok_bind, hmin, ok_bind] at hok
  obtain ⟨mx, hs, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hsg : mx.signum ≤ 0
  · simp [hsg] at hok
  simp only [hsg, if_false] at hok
  have hmx0 := ((signum_pos_iff mx).mp (not_le.mp hsg)).2
  have hmxn : mx.isNormalized :=
    operator_sub_isNormalized _ _ _ .downward lb.wf.coverAvailable_norm hmn hs hmx0
  simp only [pure_eq, except_pure_eq, ok_bind, hnz, Bool.false_eq_true, if_false] at hok
  obtain ⟨mag, hmag, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨claw', hcl, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hok
  subst hok
  obtain ⟨hmagv, hmagn⟩ := STAmount.toNumber_exact_of a mag hac hmag
  exact ⟨mx, mag, hs, hmxn, hmx0, hmagn, hmagv, hcl⟩

/-- A request no larger than the cover above the minimum is not capped: the
clawed amount is the request converted to the vault asset. -/
lemma LoanBroker.roundedCoverClawback_request (lb : LoanBroker) (pool : α) (a claw : STAmount)
    (e : Int) (minimumCover : Number) (hac : a.ExactCanonical) (hnz : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw)) :
    ∃ mag : Number, mag.isNormalized ∧ mag.toRat = a.toRat ∧
      STAmount.ofNumber lb.numericType mag .to_nearest = .ok claw := by
  obtain ⟨mx, mag, hs, hmxn, hmx0, hmagn, hmagv, hcl⟩ :=
    LoanBroker.roundedCoverClawback_some_inv lb pool a claw e minimumCover hac hnz hexp hmin hok
  -- the request is at most the cap, so the clawback takes the request
  have hle := LoanBroker.request_le_maxClaw lb a minimumCover mx hac
    (minimumBrokerCover_isNormalized _ _ _ _ _ hmin) hs hmx0 hfit
  rw [if_neg (by rw [operator_gt_iff mag mx hmagn hmxn]; linarith)] at hcl
  exact ⟨mag, hmagn, hmagv, hcl⟩

/-- A larger request never claws less. Below the cap the smaller request is
clawed whole, and above it both requests claw the cap. -/
private lemma LoanBroker.roundedCoverClawback_monotone (lb : LoanBroker) (pool : α) (a b ca cb : STAmount)
    (hac : a.ExactCanonical) (hbc : b.ExactCanonical) (hat : a.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hza : a.isZero = false) (hzb : b.isZero = false)
    (hab : a.toRat ≤ b.toRat)
    (hoka : lb.roundedCoverClawback pool (some a) = .ok (.rounded ca))
    (hokb : lb.roundedCoverClawback pool (some b) = .ok (.rounded cb))
    (hnzb : cb.mValue ≠ 0) :
    ca.toRat ≤ cb.toRat := by
  obtain ⟨e, m, he, hm⟩ := LoanBroker.roundedCoverClawback_minimum lb pool _ ca hoka
  obtain ⟨mx, magA, hs, hmxn, _, hman, hmav, hcla⟩ :=
    LoanBroker.roundedCoverClawback_some_inv lb pool a ca e m hac hza he hm hoka
  obtain ⟨mx', magB, hs', _, _, hmbn, hmbv, hclb⟩ :=
    LoanBroker.roundedCoverClawback_some_inv lb pool b cb e m hbc hzb he hm hokb
  rw [hs, Except.ok.injEq] at hs'
  subst hs'
  by_cases hgtA : magA.operator_gt mx = true
  · -- the smaller request is capped, so the larger one is capped too
    have hgtB : magB.operator_gt mx = true := by
      have hlt := (operator_gt_iff magA mx hman hmxn).mp hgtA
      exact (operator_gt_iff magB mx hmbn hmxn).mpr (by rw [hmbv]; rw [hmav] at hlt; linarith)
    rw [if_pos hgtA] at hcla
    rw [if_pos hgtB, hcla, Except.ok.injEq] at hclb
    rw [hclb]
  · -- the smaller request is clawed whole, and the larger request claws at least it
    rw [if_neg hgtA] at hcla
    have hamx : a.toRat ≤ mx.toRat := by
      rw [← hmav]
      exact not_lt.mp (by rw [← operator_gt_iff magA mx hman hmxn]; exact hgtA)
    have hca : ca.toRat = a.toRat :=
      STAmount.ofNumber_to_nearest_eq_of_canonical _ magA ca a hman (by rw [hmav]; exact ha0) hac
        hat hmav hcla
    have hge : ∀ c : Number, c.isNormalized → a.toRat ≤ c.toRat →
        STAmount.ofNumber lb.numericType c .to_nearest = .ok cb → a.toRat ≤ cb.toRat :=
      fun c hcn hle hcl => STAmount.ofNumber_to_nearest_ge_of_canonical _ c cb a hcn
        (le_trans ha0 hle) hac hat hle hcl hnzb
    rw [hca]
    by_cases hgtB : magB.operator_gt mx = true
    · rw [if_pos hgtB] at hclb
      exact hge mx hmxn hamx hclb
    · rw [if_neg hgtB] at hclb
      exact hge magB hmbn (by rw [hmbv]; exact hab) hclb

/-- A successful clawback of a request no larger than the cover above the
minimum claws the request converted to the vault asset. -/
lemma LoanBroker.coverClawback_request (lb : LoanBroker) (pool : α) (a : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hok : lb.coverClawback pool (some a) = .ok (.ok res))
    (hac : a.ExactCanonical) (hnz : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat) :
    ∃ mag : Number, mag.isNormalized ∧ mag.toRat = a.toRat ∧
      STAmount.ofNumber lb.numericType mag .to_nearest = .ok res.amount' := by
  obtain ⟨claw, hrr, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool (some a) res hok
  obtain ⟨_, _, _, _, hamt, _⟩ := LoanBroker.applyCoverTransaction_debit_inv lb claw res happ
  rw [hamt]
  exact LoanBroker.roundedCoverClawback_request lb pool a claw e minimumCover hac hnz hexp hmin hfit
    hrr

/-- **Proof body of `coverClawback_monotone`.** -/
lemma LoanBroker.coverClawback_monotone_proof (lb : LoanBroker) (pool : α) (a b : STAmount)
    (ra rb : LoanBrokerCoverResult)
    (hoka : lb.coverClawback pool (some a) = .ok (.ok ra))
    (hokb : lb.coverClawback pool (some b) = .ok (.ok rb))
    (hac : a.ExactCanonical) (hbc : b.ExactCanonical) (hat : a.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hza : a.isZero = false) (hzb : b.isZero = false)
    (hab : a.toRat ≤ b.toRat)
    (hcanb : lb.canCoverClawback pool (some b) = .ok .tesSUCCESS) :
    ra.amount'.toRat ≤ rb.amount'.toRat := by
  have hnzb := LoanBroker.coverClawback_amount_nonzero lb pool _ rb hcanb hokb
  obtain ⟨ca, hra, happa⟩ := LoanBroker.coverClawback_ok_inv lb pool (some a) ra hoka
  obtain ⟨cb, hrb, happb⟩ := LoanBroker.coverClawback_ok_inv lb pool (some b) rb hokb
  rw [LoanBroker.applyCoverTransaction_amount' lb _ ca ra happa]
  rw [LoanBroker.applyCoverTransaction_amount' lb _ cb rb happb] at hnzb ⊢
  exact LoanBroker.roundedCoverClawback_monotone lb pool a b ca cb hac hbc hat ha0 hza hzb hab hra
    hrb hnzb

/-- **Proof body of `roundedCoverClawback_integral`.** -/
lemma LoanBroker.roundedCoverClawback_integral_proof (lb : LoanBroker) (pool : α)
    (a claw : STAmount) (e : Int) (minimumCover : Number) (hint : a.IntegralCanonical)
    (hsz : a.mValue.toNat ≤ 2 ^ 63 - 1) (ha0 : 0 ≤ a.toRat) (hat : a.mNumericType = lb.numericType)
    (hza : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hok : lb.roundedCoverClawback pool (some a) = .ok (.rounded claw)) :
    claw = a := by
  have hac : a.ExactCanonical := Or.inr ⟨hint, hsz⟩
  obtain ⟨mag, hmagn, hmagv, hcl⟩ := LoanBroker.roundedCoverClawback_request lb pool a claw e
    minimumCover hac hza hexp hmin hfit hok
  have hnt : lb.numericType.isIntegral = true := by rw [← hat]; exact hint.is_integral
  have hm0 : 0 ≤ mag.toRat := by rw [hmagv]; exact ha0
  -- an XRP or MPT amount is a whole number, so the conversion is exact
  have hval : claw.toRat = a.toRat := by
    rw [STAmount.ofNumber_integral_exact _ mag .to_nearest claw hnt hmagn
      (by rw [hmagv]; exact STAmount.IntegralCanonical.den_eq_one a hint) hcl, hmagv]
  have ha0' : a.mValue ≠ 0 := by simpa [STAmount.isZero] using hza
  have hnz : claw.mValue ≠ 0 := by
    intro h0
    apply STAmount.toRat_ne_zero a ha0'
    rw [← hval, STAmount.toRat_signed, h0]
    simp
  exact STAmount.eq_of_exactCanonical claw a
    (STAmount.ofNumber_exactCanonical _ mag .to_nearest claw hmagn hm0 hcl hnz) hac
    (by rw [STAmount.ofNumber_mNumericType _ _ _ _ hcl, hat]) hnz hval

/-- A clawback whose checks passed on a canonical nonnegative request claws a
canonical nonnegative amount of the vault's type. -/
lemma LoanBroker.coverClawback_amount_exactCanonical (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) :
    res.amount'.ExactCanonical ∧ res.amount'.mNumericType = lb.numericType ∧
      0 ≤ res.amount'.toRat := by
  obtain ⟨claw, hrr, hnz⟩ := LoanBroker.canCoverClawback_success_inv lb pool amount hcan
  obtain ⟨e, m, he, hm⟩ := LoanBroker.roundedCoverClawback_minimum lb pool amount claw hrr
  obtain ⟨c, hcn, hc0, _, hcl, _⟩ :=
    LoanBroker.roundedCoverClawback_rounded_inv lb pool amount claw e m hreq he hm hrr
  obtain ⟨claw', hrr', happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  rw [hrr, Except.ok.injEq, RoundingResult.rounded.injEq] at hrr'
  subst hrr'
  rw [LoanBroker.applyCoverTransaction_amount' lb _ _ res happ]
  exact ⟨STAmount.ofNumber_exactCanonical _ c .to_nearest _ hcn hc0 hcl hnz,
    STAmount.ofNumber_mNumericType _ _ _ _ hcl,
    STAmount.ofNumber_nonneg _ c .to_nearest _ hcn (Number.negative_false_of_nonneg c hcn hc0) hcl⟩

/-- On an XRP or MPT broker the same clawed amount is a canonical whole number
within `Int64`. -/
lemma LoanBroker.coverClawback_amount_integral (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true) :
    res.amount'.IntegralCanonical ∧ res.amount'.mValue.toNat ≤ 2 ^ 63 - 1 ∧
      0 ≤ res.amount'.toRat := by
  obtain ⟨hc, hty, hnn⟩ :=
    LoanBroker.coverClawback_amount_exactCanonical lb pool amount res hcan hok hreq
  have hint : res.amount'.integral = true := by
    show res.amount'.mNumericType.isIntegral = true
    rw [hty]
    exact hnt
  exact ⟨(hc.integralCanonical hint).1, (hc.integralCanonical hint).2, hnn⟩

/-- A clawback lowers `coverAvailable` by exactly a canonical clawed amount when
the true difference fits a `Number`. -/
lemma LoanBroker.coverClawback_debit_of_canonical (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverClawback pool amount = .ok (.ok res)) (hc : res.amount'.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  obtain ⟨claw, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  have hamt : res.amount' = claw :=
    LoanBroker.applyCoverTransaction_amount' lb _ claw res happ
  rw [hamt] at hc hexact ⊢
  rw [(LoanBroker.applyCoverTransaction_debit_value lb claw res happ hc hexact).1]
  ring

/-- **Proof body of `coverClawback_debit`.** -/
lemma LoanBroker.coverClawback_debit_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat :=
  LoanBroker.coverClawback_debit_of_canonical lb pool amount res hok
    (LoanBroker.coverClawback_amount_exactCanonical lb pool amount res hcan hok hreq).1 hexact

/-- A clawback of a canonical request that fits under the cap claws exactly the
request, and lowers `coverAvailable` by it when the difference fits a `Number`. -/
lemma LoanBroker.coverClawback_debit_request (lb : LoanBroker) (pool : α) (a : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hok : lb.coverClawback pool (some a) = .ok (.ok res))
    (hac : a.ExactCanonical) (hat : a.mNumericType = lb.numericType) (ha0 : 0 ≤ a.toRat)
    (hza : a.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hnz : res.amount'.mValue ≠ 0)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat) :
    res.amount'.toRat = a.toRat ∧
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = a.toRat := by
  obtain ⟨mag, hmagn, hmagv, hcl⟩ :=
    LoanBroker.coverClawback_request lb pool a res e minimumCover hok hac hza hexp hmin hfit
  have hm0 : 0 ≤ mag.toRat := by rw [hmagv]; exact ha0
  have hback : res.amount'.toRat = a.toRat :=
    STAmount.ofNumber_to_nearest_eq_of_canonical _ mag _ a hmagn hm0 hac hat hmagv hcl
  have hc' := STAmount.ofNumber_exactCanonical _ mag .to_nearest _ hmagn hm0 hcl hnz
  obtain ⟨w, hwn, hwv⟩ := hexact
  have hdeb := LoanBroker.coverClawback_debit_of_canonical lb pool _ res hok hc'
    ⟨w, hwn, by rw [hwv, hback]⟩
  exact ⟨hback, by rw [hdeb, hback]⟩

/-- **Proof body of `coverClawback_debit_integral`.** -/
lemma LoanBroker.coverClawback_debit_integral_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true) (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  obtain ⟨hint, hsz, hnn⟩ :=
    LoanBroker.coverClawback_amount_integral lb pool amount res hcan hok hreq hnt
  obtain ⟨claw, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, _, _, _, hamt, _⟩ := LoanBroker.applyCoverTransaction_debit_inv lb claw res happ
  rw [hamt] at hint hsz hnn ⊢
  obtain ⟨hv, _⟩ :=
    LoanBroker.applyCoverTransaction_debit_integral lb claw res happ hint hsz hnn hcint hbound
  rw [hv]; ring

/-- **Proof body of `coverClawback_decreases_cover`.** -/
lemma LoanBroker.coverClawback_decreases_cover_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable := by
  obtain ⟨hc, _, hnn⟩ :=
    LoanBroker.coverClawback_amount_exactCanonical lb pool amount res hcan hok hreq
  obtain ⟨claw, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_debit_inv lb claw res happ
  rw [hamt] at hc hnn
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of claw m hc hm
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat ≤ lb.coverAvailable.toRat
  rw [hraw]
  exact operator_sub_le_of_le_normalized _ _ _ _ lb.wf.coverAvailable_norm hmn hsub
    lb.wf.coverAvailable_norm (by rw [hmv]; linarith)

/-- A clawed amount converts exactly to a nonnegative `Number`, and taking it
from a cover below `10^96` never throws. -/
private lemma LoanBroker.coverClawback_sub_ok (lb : LoanBroker) (c : Number) (claw : STAmount)
    (hcn : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hcl : STAmount.ofNumber lb.numericType c .to_nearest = .ok claw) (hnz : claw.mValue ≠ 0)
    (hcap : lb.toExact.coverAvailable < 10 ^ 96) :
    ∃ clawN c' : Number, claw.toNumber .to_nearest = .ok clawN ∧ clawN.isNormalized ∧
      clawN.toRat = claw.toRat ∧ 0 ≤ claw.toRat ∧
      lb.coverAvailable.operator_sub clawN .to_nearest = .ok c' := by
  have hcc := STAmount.ofNumber_exactCanonical _ c .to_nearest claw hcn hc0 hcl hnz
  have hcl0 :=
    STAmount.ofNumber_nonneg _ c .to_nearest claw hcn
      (Number.negative_false_of_nonneg c hcn hc0) hcl
  obtain ⟨clawN, hN, hNv, hNn⟩ := STAmount.toNumber_exact_canonical claw .to_nearest hcc
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt lb.coverAvailable clawN .to_nearest
    lb.wf.coverAvailable_norm hNn lb.exact.coverAvailable_nonneg hcap (by rw [hNv]; exact hcl0)
    (by rw [hNv]; exact lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt claw hcc))
  exact ⟨clawN, c', hN, hNn, hNv, hcl0, hsub⟩

/-- **Proof body of `coverClawback_total`.** -/
lemma LoanBroker.coverClawback_total_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hcap : lb.toExact.coverAvailable < 10 ^ 96) :
    (∃ res, lb.coverClawback pool amount = .ok (.ok res)) ∨
      lb.coverClawback pool amount = .error .notLawful := by
  obtain ⟨claw, hrr, hnz⟩ := LoanBroker.canCoverClawback_success_inv lb pool amount hcan
  obtain ⟨e, m, he, hm⟩ := LoanBroker.roundedCoverClawback_minimum lb pool amount claw hrr
  obtain ⟨c, hcn, hc0, _, hcl, _⟩ :=
    LoanBroker.roundedCoverClawback_rounded_inv lb pool amount claw e m hreq he hm hrr
  obtain ⟨clawN, c', hN, _, _, _, hsub⟩ :=
    LoanBroker.coverClawback_sub_ok lb c claw hcn hc0 hcl hnz hcap
  cases htl : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful with
  | error err =>
    right
    have herr : err = .notLawful := by
      unfold RawLoanBroker.to_lawful at htl
      split at htl
      · simp at htl
      · simpa using htl.symm
    subst herr
    simp [LoanBroker.coverClawback, LoanBroker.applyCoverTransaction, hrr, hN, hsub, htl]
  | ok lb' =>
    left
    exact ⟨{ amount' := claw, loanBroker' := lb' },
      by simp [LoanBroker.coverClawback, LoanBroker.applyCoverTransaction, hrr, hN, hsub, htl]⟩

/-- **Proof body of `coverClawback_lawful_total`.** -/
lemma LoanBroker.coverClawback_lawful_total_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    ∃ res, lb.coverClawback pool amount = .ok (.ok res) := by
  obtain ⟨claw, hrr, hnz⟩ := LoanBroker.canCoverClawback_success_inv lb pool amount hcan
  obtain ⟨e, m, he, hm⟩ := LoanBroker.roundedCoverClawback_minimum lb pool amount claw hrr
  have hm0 := LoanBroker.minimumCover_nonneg lb pool e m he hm
  obtain ⟨c, hcn, hc0, hcle, hcl, _⟩ :=
    LoanBroker.roundedCoverClawback_rounded_inv lb pool amount claw e m hreq he hm hrr
  obtain ⟨a, hac, hat, hav⟩ := hrep
  have hcap : lb.toExact.coverAvailable < 10 ^ 96 := by
    rw [← hav]; exact lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt a hac)
  -- the clawed amount never exceeds `coverAvailable`, which the asset holds exactly
  have hclaw_le : claw.toRat ≤ lb.toExact.coverAvailable := by
    rw [← hav]
    exact STAmount.ofNumber_to_nearest_le_of_canonical _ c claw a hcn hc0 hac hat
      (by rw [hav]; linarith) hcl hnz
  obtain ⟨clawN, c', hN, hNn, hNv, _, hsub⟩ :=
    LoanBroker.coverClawback_sub_ok lb c claw hcn hc0 hcl hnz hcap
  -- the new `coverAvailable` is nonnegative and normalized, so the broker stays lawful
  have hc'0 : 0 ≤ c'.toRat := operator_sub_nonneg _ _ _ lb.wf.coverAvailable_norm hNn hsub
    (by rw [hNv]; exact sub_nonneg.mpr hclaw_le)
  have hcn' : c'.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ lb.wf.coverAvailable_norm hNn hsub
  obtain ⟨lb', htl, _⟩ := LoanBroker.withCover_lawful lb c' hcn' hc'0
  exact ⟨{ amount' := claw, loanBroker' := lb' },
    by simp [LoanBroker.coverClawback, LoanBroker.applyCoverTransaction, hrr, hN, hsub, htl]⟩

/-- **Proof body of `coverClawback_keeps_minimum_within_half`.** -/
lemma LoanBroker.coverClawback_keeps_minimum_within_half_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    minimumCover.toRat - res.loanBroker'.toExact.coverAvailable ≤
      (1 / 2 : ℚ) * (10 : ℚ) ^ res.amount'.exponent := by
  have hnz := LoanBroker.coverClawback_amount_nonzero lb pool amount res hcan hok
  obtain ⟨claw, hrr, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  have hamt : res.amount' = claw :=
    LoanBroker.applyCoverTransaction_amount' lb _ claw res happ
  rw [hamt] at hnz hexact ⊢
  obtain ⟨c, hcn, hc0, hcle, hcl, _⟩ :=
    LoanBroker.roundedCoverClawback_rounded_inv lb pool amount claw e minimumCover hreq hexp hmin
      hrr
  have hcc := STAmount.ofNumber_exactCanonical _ c .to_nearest claw hcn hc0 hcl hnz
  have hdeb := LoanBroker.coverClawback_debit_of_canonical lb pool amount res hok (hamt ▸ hcc)
    (hamt ▸ hexact)
  rw [hamt] at hdeb
  have hhalf := (abs_le.mp (STAmount.ofNumber_to_nearest_within_half _ c claw hcn hc0 hcl hnz)).2
  linarith

/-- **Proof body of `coverClawback_all_leaves_minimum`.** -/
lemma LoanBroker.coverClawback_all_leaves_minimum_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable - minimumCover.toRat) :
    res.loanBroker'.toExact.coverAvailable = minimumCover.toRat := by
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  obtain ⟨claw, hrr, hnz⟩ := LoanBroker.canCoverClawback_success_inv lb pool amount hcan
  obtain ⟨a, hac, hat, hav⟩ := hfit
  -- the clawed amount is the cover above the minimum, rounded down and converted
  have hrr0 := hrr
  unfold LoanBroker.roundedCoverClawback at hrr
  dsimp only at hrr
  rw [hexp, ok_bind, hmin, ok_bind] at hrr
  obtain ⟨mx, hs, hrr⟩ := bind_ok_peel _ _ _ hrr
  by_cases hle : mx.signum ≤ 0
  · simp [hle] at hrr
  simp only [hle, if_false] at hrr
  obtain ⟨hmxneg, hmx0⟩ := (signum_pos_iff mx).mp (not_le.mp hle)
  have hmxn : mx.isNormalized :=
    operator_sub_isNormalized _ _ _ .downward lb.wf.coverAvailable_norm hmn hs hmx0
  have hcl : STAmount.ofNumber lb.numericType mx .to_nearest = .ok claw := by
    rcases hall with rfl | ⟨a0, rfl, hz⟩
    · simp only [pure_eq, except_pure_eq, ok_bind] at hrr
      obtain ⟨claw', hcl, hrr⟩ := bind_ok_peel _ _ _ hrr
      simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hrr
      subst hrr; exact hcl
    · simp only [pure_eq, except_pure_eq, ok_bind, hz, if_true] at hrr
      obtain ⟨claw', hcl, hrr⟩ := bind_ok_peel _ _ _ hrr
      simp only [Except.ok.injEq, RoundingResult.rounded.injEq] at hrr
      subst hrr; exact hcl
  -- the asset holds the cover above the minimum, so rounding down keeps it exactly
  obtain ⟨w, _, hwv, hwn⟩ := STAmount.toNumber_exact_canonical a .to_nearest hac
  obtain ⟨n, hn, heq⟩ := operator_sub_rounded_downward _ _ _ lb.wf.coverAvailable_norm hmn hs hmx0
  have hmxv : mx.toRat = lb.toExact.coverAvailable - minimumCover.toRat := by
    apply le_antisymm
    · rw [heq]; exact Number.lower_le _ n hn
    · rw [heq, ← hav, ← hwv]
      exact Number.lower_tight _ n hn w hwn (by rw [hwv, hav]; exact le_rfl)
  have hmx0' : 0 ≤ mx.toRat := Number.toRat_nonneg_of_nonnegative mx hmxneg
  -- and converting it to the asset keeps it exactly too
  have hclaw : claw.toRat = a.toRat :=
    STAmount.ofNumber_to_nearest_eq_of_canonical _ mx claw a hmxn hmx0' hac hat
      (by rw [hmxv, hav]) hcl
  have hcc := STAmount.ofNumber_exactCanonical _ mx .to_nearest claw hmxn hmx0' hcl hnz
  obtain ⟨claw', hrr', happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  rw [hrr0, Except.ok.injEq, RoundingResult.rounded.injEq] at hrr'
  subst hrr'
  have hamt : res.amount' = claw := LoanBroker.applyCoverTransaction_amount' lb _ claw res happ
  -- the debit is exact because the new cover is the minimum cover, a `Number`
  have hdeb := LoanBroker.coverClawback_debit_of_canonical lb pool amount res hok (hamt ▸ hcc)
    ⟨minimumCover, hmn, by rw [hamt, hclaw, hav]; ring⟩
  rw [hamt, hclaw, hav] at hdeb
  linarith

/-- **Proof body of `coverClawback_all`.** -/
lemma LoanBroker.coverClawback_all_proof (lb : LoanBroker) (pool : α) (e : Int) (s : STAmount)
    (hdebt : lb.debtTotal = Number.zero)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) (hrep : s.toRat = lb.toExact.coverAvailable)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      ∃ res, lb.coverClawback pool none = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable = 0 := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hrep' : s.toRat = lb.coverAvailable.toRat := hrep
  have hc : s.ExactCanonical := STAmount.ofNumber_exactCanonical _ _ .to_nearest s hcn hcov0 hs hnz
  -- with no debt the minimum cover is zero, so the cap is the whole positive cover
  have hpos : 0 < lb.coverAvailable.toRat := by
    rw [← hrep']
    exact lt_of_le_of_ne (by rw [hrep']; exact hcov0) (Ne.symm (STAmount.toRat_ne_zero s hnz))
  have hsg : ¬ lb.coverAvailable.signum ≤ 0 := by
    rw [(signum_eq_one_iff _ hcn).mpr hpos]
    decide
  have hrr : lb.roundedCoverClawback pool none = .ok (.rounded s) := by
    unfold LoanBroker.roundedCoverClawback
    simp only [hexp, ok_bind, hdebt, minimumBrokerCover_zero_debt, Number.operator_sub_zero, hsg,
      if_false, pure_eq, except_pure_eq, hs]
  have hcan : lb.canCoverClawback pool none = .ok .tesSUCCESS := by
    unfold LoanBroker.canCoverClawback
    rw [hrr, ok_bind]
    exact canApplyToBrokerCover_whole _ _ _ hs hnz
  refine ⟨hcan, ?_⟩
  obtain ⟨res, hok⟩ := LoanBroker.coverClawback_lawful_total_proof lb pool none hcan
    (fun a ha => absurd ha (by simp)) ⟨s, hc, STAmount.ofNumber_mNumericType _ _ _ _ hs, hrep⟩
  -- the clawback takes exactly the whole cover
  obtain ⟨claw, hrr', happ⟩ := LoanBroker.coverClawback_ok_inv lb pool none res hok
  rw [hrr, Except.ok.injEq, RoundingResult.rounded.injEq] at hrr'
  subst hrr'
  have hamt : res.amount' = s := LoanBroker.applyCoverTransaction_amount' lb _ s res happ
  have hdeb := LoanBroker.coverClawback_debit_of_canonical lb pool none res hok (hamt ▸ hc)
    ⟨Number.zero, Number.zero_isNormalized, by
      rw [Number.toRat_zero, hamt]
      show (0 : ℚ) = lb.coverAvailable.toRat - s.toRat
      rw [hrep']
      ring⟩
  refine ⟨res, hok, ?_⟩
  rw [hamt] at hdeb
  have : lb.toExact.coverAvailable = s.toRat := hrep.symm
  linarith

end XRPL.Model.Lending
