import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Shared reductions for the cover operations

Deposit, withdraw and clawback share `applyCoverTransaction`. Withdraw and
clawback check the amount with `canApplyToBrokerCover`. This file gives the
`canApplyToBrokerCover` exits, inverts a successful operation into its steps,
shows it keeps every field but `coverAvailable`, and reads the new
`coverAvailable` when the true result fits a `Number`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- A zero amount: `tecPRECISION_LOSS`. -/
lemma canApplyToBrokerCover_zero (nt : NumericType) (cover : Number) (amount : STAmount)
    (hz : amount.isZero = true) :
    canApplyToBrokerCover nt cover amount = .ok .tecPRECISION_LOSS := by
  simp [canApplyToBrokerCover, hz]

/-- A nonzero amount that rounds to zero at the cover scale:
`tecPRECISION_LOSS`. -/
lemma canApplyToBrokerCover_rounds_zero (nt : NumericType) (cover : Number)
    (amount rn : STAmount) (hnz : amount.isZero = false)
    (hnear : roundToCoverScale nt cover amount .to_nearest = .ok rn) (hz : rn.signum = 0) :
    canApplyToBrokerCover nt cover amount = .ok .tecPRECISION_LOSS := by
  simp [canApplyToBrokerCover, hnz, hnear, hz]

/-- A nonzero amount that stays nonzero at the cover scale passes. -/
lemma canApplyToBrokerCover_pass (nt : NumericType) (cover : Number) (amount rn : STAmount)
    (hnz : amount.isZero = false)
    (hnear : roundToCoverScale nt cover amount .to_nearest = .ok rn) (hrn : rn.signum ≠ 0) :
    canApplyToBrokerCover nt cover amount = .ok .tesSUCCESS := by
  simp [canApplyToBrokerCover, hnz, hnear, hrn]

/-- `tecPRECISION_LOSS` is the only rejection `canApplyToBrokerCover` can
return. -/
lemma canApplyToBrokerCover_error_codes (nt : NumericType) (cover : Number) (amount : STAmount)
    (ter : TER) (hok : canApplyToBrokerCover nt cover amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS := by
  unfold canApplyToBrokerCover at hok
  dsimp only at hok
  by_cases hz : amount.isZero = true
  · simp only [hz, if_true, pure_eq, Except.ok.injEq] at hok
    exact Or.inr hok.symm
  · simp only [hz, Bool.false_eq_true, if_false] at hok
    cases hn : roundToCoverScale nt cover amount .to_nearest with
    | error e => rw [hn, err_bind] at hok; exact absurd hok (by simp)
    | ok rn =>
      rw [hn, ok_bind] at hok
      by_cases hs : (rn.signum == 0) = true
      · exact Or.inr (by simpa [hs] using hok.symm)
      · exact Or.inl (by simpa [hs] using hok.symm)

/-- Rounding to the cover scale is rounding to the `coverAvailable` exponent. -/
lemma roundToCoverScale_eq (nt : NumericType) (cover : Number) (amount : STAmount)
    (mode : rounding_mode) (e : Int) (hexp : numberExponent cover nt = .ok e) :
    roundToCoverScale nt cover amount mode = amount.roundToExponent e mode := by
  simp [roundToCoverScale, hexp]

/-- The whole cover, converted to the vault asset, passes the scale check: it
already sits at the cover scale. -/
lemma canApplyToBrokerCover_whole (nt : NumericType) (cover : Number) (s : STAmount)
    (hs : STAmount.ofNumber nt cover .to_nearest = .ok s) (hnz : s.mValue ≠ 0) :
    canApplyToBrokerCover nt cover s = .ok .tesSUCCESS := by
  have hz : s.isZero = false := by simp [STAmount.isZero, hnz]
  have hscale : numberExponent cover nt = .ok s.exponent := by
    simp [numberExponent, hs]
  have hround : roundToCoverScale nt cover s .to_nearest = .ok s := by
    rw [roundToCoverScale_eq _ _ _ _ _ hscale]
    simp [STAmount.roundToExponent]
  have hsg : s.signum ≠ 0 := by
    have hb : (s.mValue == 0) = false := by simpa using hnz
    unfold STAmount.signum
    rw [hb, if_neg Bool.false_ne_true]
    split <;> decide
  exact canApplyToBrokerCover_pass _ _ _ _ hz hround hsg

/-- A successful credit converts the amount, adds it to `coverAvailable`, and
stores the sum. -/
lemma LoanBroker.applyCoverTransaction_credit_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.applyCoverTransaction .credit amount = .ok res) :
    ∃ m c', amount.toNumber .to_nearest = .ok m ∧
      lb.coverAvailable.operator_add m .to_nearest = .ok c' ∧ res.amount' = amount ∧
      res.loanBroker'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  unfold LoanBroker.applyCoverTransaction at hok
  obtain ⟨m, hm, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨c', hc, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨lb', hl, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_eq, Except.ok.injEq] at hok
  subst hok
  exact ⟨m, c', hm, hc, rfl, (RawLoanBroker.to_lawful_ok hl).1⟩

/-- A successful debit converts the amount, subtracts it from `coverAvailable`,
and stores the difference. -/
lemma LoanBroker.applyCoverTransaction_debit_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.applyCoverTransaction .debit amount = .ok res) :
    ∃ m c', amount.toNumber .to_nearest = .ok m ∧
      lb.coverAvailable.operator_sub m .to_nearest = .ok c' ∧ res.amount' = amount ∧
      res.loanBroker'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  unfold LoanBroker.applyCoverTransaction at hok
  obtain ⟨m, hm, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨c', hc, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨lb', hl, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_eq, Except.ok.injEq] at hok
  subst hok
  exact ⟨m, c', hm, hc, rfl, (RawLoanBroker.to_lawful_ok hl).1⟩

/-- A successful cover movement reports the amount it was given. -/
lemma LoanBroker.applyCoverTransaction_amount' (lb : LoanBroker) (direction : CoverDirection)
    (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.applyCoverTransaction direction amount = .ok res) : res.amount' = amount := by
  cases direction with
  | credit =>
    obtain ⟨_, _, _, _, hamt, _⟩ := LoanBroker.applyCoverTransaction_credit_inv lb amount res hok
    exact hamt
  | debit =>
    obtain ⟨_, _, _, _, hamt, _⟩ := LoanBroker.applyCoverTransaction_debit_inv lb amount res hok
    exact hamt

/-- A successful deposit credits the rounded amount. -/
lemma LoanBroker.coverDeposit_ok_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res)) :
    ∃ r, lb.roundedCoverAmount amount = .ok (.rounded r) ∧
      lb.applyCoverTransaction .credit r = .ok res := by
  unfold LoanBroker.coverDeposit at hok
  obtain ⟨rr, hrr, hok⟩ := bind_ok_peel _ _ _ hok
  cases rr with
  | rejected t => simp at hok
  | rounded r =>
    simp only [except_pure_eq, ok_bind] at hok
    obtain ⟨res', hres, hok⟩ := bind_ok_peel _ _ _ hok
    simp only [pure_eq, Except.ok.injEq] at hok
    subst hok
    exact ⟨r, hrr, hres⟩

/-- A successful withdrawal debits the requested amount. -/
lemma LoanBroker.coverWithdraw_ok_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res)) :
    lb.applyCoverTransaction .debit amount = .ok res := by
  unfold LoanBroker.coverWithdraw at hok
  obtain ⟨res', hres, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_eq, Except.ok.injEq] at hok
  subst hok
  exact hres

/-- A successful clawback debits the clawed amount. -/
lemma LoanBroker.coverClawback_ok_inv (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverClawback pool amount = .ok (.ok res)) :
    ∃ claw, lb.roundedCoverClawback pool amount = .ok (.rounded claw) ∧
      lb.applyCoverTransaction .debit claw = .ok res := by
  unfold LoanBroker.coverClawback at hok
  obtain ⟨rr, hrr, hok⟩ := bind_ok_peel _ _ _ hok
  cases rr with
  | rejected t => simp at hok
  | rounded r =>
    simp only [except_pure_eq, ok_bind] at hok
    obtain ⟨res', hres, hok⟩ := bind_ok_peel _ _ _ hok
    simp only [pure_eq, Except.ok.injEq] at hok
    subst hok
    exact ⟨r, hrr, hres⟩

/-- The fields no LoanBroker operation writes: the numeric type, `debtTotal`,
`loanCount` and the three rates. -/
structure LoanBroker.SameFixedFields (a b : LoanBroker) : Prop where
  numericType : b.numericType = a.numericType
  debtTotal : b.debtTotal = a.debtTotal
  loanCount : b.loanCount = a.loanCount
  managementFeeRate : b.managementFeeRate = a.managementFeeRate
  coverRateMinimum : b.coverRateMinimum = a.coverRateMinimum
  coverRateLiquidation : b.coverRateLiquidation = a.coverRateLiquidation

/-- Fixed fields kept over two steps are kept over both. -/
lemma LoanBroker.SameFixedFields.trans {a b c : LoanBroker}
    (hab : LoanBroker.SameFixedFields a b) (hbc : LoanBroker.SameFixedFields b c) :
    LoanBroker.SameFixedFields a c :=
  ⟨hbc.numericType.trans hab.numericType, hbc.debtTotal.trans hab.debtTotal,
    hbc.loanCount.trans hab.loanCount, hbc.managementFeeRate.trans hab.managementFeeRate,
    hbc.coverRateMinimum.trans hab.coverRateMinimum,
    hbc.coverRateLiquidation.trans hab.coverRateLiquidation⟩

/-- A broker that only differs in `coverAvailable` keeps the fixed fields. -/
private lemma LoanBroker.sameFixedFields_cover (a b : LoanBroker) (c : Number)
    (h : b.toRawLoanBroker = { a.toRawLoanBroker with coverAvailable := c }) :
    LoanBroker.SameFixedFields a b := by
  have e1 := congrArg RawLoanBroker.numericType h
  have e2 := congrArg RawLoanBroker.debtTotal h
  have e3 := congrArg RawLoanBroker.loanCount h
  have e4 := congrArg RawLoanBroker.managementFeeRate h
  have e5 := congrArg RawLoanBroker.coverRateMinimum h
  have e6 := congrArg RawLoanBroker.coverRateLiquidation h
  exact ⟨e1, e2, e3, e4, e5, e6⟩

/-- A deposit only changes `coverAvailable`. -/
lemma LoanBroker.coverDeposit_fixed_fields (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- A withdrawal only changes `coverAvailable`. -/
lemma LoanBroker.coverWithdraw_fixed_fields (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb amount res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- A clawback only changes `coverAvailable`. -/
lemma LoanBroker.coverClawback_fixed_fields (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverClawback pool amount = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  obtain ⟨claw, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb claw res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- The new `coverAvailable` after a credit, as a rational. -/
lemma LoanBroker.applyCoverTransaction_credit_value (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult)
    (hok : lb.applyCoverTransaction .credit amount = .ok res) (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + amount.toRat) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable + amount.toRat ∧
      res.amount' = amount := by
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_credit_inv lb amount res hok
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of amount m hc hm
  refine ⟨?_, hamt⟩
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat = lb.coverAvailable.toRat + amount.toRat
  rw [hraw]
  show c'.toRat = lb.coverAvailable.toRat + amount.toRat
  obtain ⟨w, hw, hwt⟩ := hexact
  rw [← hmv] at hwt ⊢
  exact Number.roundsToRepresentable_eq c' _
    (operator_add_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hadd) w hw hwt

/-- The new `coverAvailable` after a debit, as a rational. -/
lemma LoanBroker.applyCoverTransaction_debit_value (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult)
    (hok : lb.applyCoverTransaction .debit amount = .ok res) (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - amount.toRat ∧
      res.amount' = amount := by
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_debit_inv lb amount res hok
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of amount m hc hm
  refine ⟨?_, hamt⟩
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat = lb.coverAvailable.toRat - amount.toRat
  rw [hraw]
  show c'.toRat = lb.coverAvailable.toRat - amount.toRat
  obtain ⟨w, hw, hwt⟩ := hexact
  rw [← hmv] at hwt ⊢
  exact Number.roundsToRepresentable_eq c' _
    (operator_sub_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hsub) w hw hwt

/-- A raw broker whose `coverAvailable` compares below zero is not lawful. -/
lemma RawLoanBroker.to_lawful_negative_cover (lb : LoanBroker) (c' : Number)
    (hneg : Number.zero.operator_le c' = false) :
    ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful =
      .error .notLawful := by
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨_, hv⟩
  have h : Number.zero.operator_le c' = true := hv.coverAvailable_nonneg
  rw [hneg] at h
  exact absurd h (by decide)

/-- A broker that only changes `coverAvailable`, to a normalized nonnegative
value, passes the `to_lawful` re-check. -/
lemma LoanBroker.withCover_lawful (lb : LoanBroker) (c' : Number) (hcn : c'.isNormalized)
    (hc0 : 0 ≤ c'.toRat) :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hwf : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).WF :=
    ⟨lb.wf.debtTotal_norm, lb.wf.debtMaximum_norm, hcn⟩
  have hlb := lb.exact
  have he : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).toExact.Valid :=
    { debtTotal_nonneg := hlb.debtTotal_nonneg
      coverAvailable_nonneg := hc0
      debt_within_cap := hlb.debt_within_cap
      empty_broker := hlb.empty_broker
      debtMaximum_nonneg := hlb.debtMaximum_nonneg
      debtMaximum_cap := hlb.debtMaximum_cap
      managementFeeRate_cap := hlb.managementFeeRate_cap
      coverRateMinimum_cap := hlb.coverRateMinimum_cap
      coverRateLiquidation_cap := hlb.coverRateLiquidation_cap
      coverRates_coupled := hlb.coverRates_coupled }
  exact RawLoanBroker.to_lawful_ok_of hwf ((RawLoanBroker.valid_iff_exact _ hwf).mpr he)

/-- Subtracting a normalized amount no larger than `coverAvailable` leaves a
broker that passes the `to_lawful` re-check. -/
lemma LoanBroker.debit_lawful (lb : LoanBroker) (m c' : Number) (hmn : m.isNormalized)
    (hge : lb.coverAvailable.operator_lt m = false)
    (hsub : lb.coverAvailable.operator_sub m .to_nearest = .ok c') :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hle := (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hmn).mp hge
  exact LoanBroker.withCover_lawful lb c'
    (operator_sub_isNormalized_to_nearest_sz _ _ _ lb.wf.coverAvailable_norm hmn hsub)
    (operator_sub_nonneg _ _ _ lb.wf.coverAvailable_norm hmn hsub (sub_nonneg.mpr hle))

/-- Adding a normalized nonnegative amount to `coverAvailable` leaves a broker that
passes the `to_lawful` re-check. -/
lemma LoanBroker.credit_lawful (lb : LoanBroker) (m c' : Number) (hmn : m.isNormalized)
    (hm0 : 0 ≤ m.toRat) (hadd : lb.coverAvailable.operator_add m .to_nearest = .ok c') :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hcn := lb.wf.coverAvailable_norm
  have hcn' : c'.isNormalized := by
    by_cases h0 : c'.mantissa_ = 0
    · rw [Number.operator_add_zero_shape_sz _ _ _ hcn hmn hadd h0]
      exact Or.inl rfl
    · exact operator_add_isNormalized_to_nearest _ _ _ hcn hmn hadd h0
  have hc0 : 0 ≤ c'.toRat :=
    le_trans lb.exact.coverAvailable_nonneg
      (operator_add_ge_of_ge_normalized _ _ _ _ hcn hmn hadd hcn (by linarith))
  exact LoanBroker.withCover_lawful lb c' hcn' hc0

/-- A whole `coverAvailable` below `2^63` minus a nonnegative canonical whole
amount is debited exactly. -/
lemma LoanBroker.applyCoverTransaction_debit_integral (lb : LoanBroker) (a : STAmount)
    (res : LoanBrokerCoverResult) (happ : lb.applyCoverTransaction .debit a = .ok res)
    (hic : a.IntegralCanonical) (hsz : a.mValue.toNat ≤ 2 ^ 63 - 1) (ha0 : 0 ≤ a.toRat)
    (hcint : lb.toExact.coverAvailable.den = 1) (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - a.toRat ∧
      res.amount' = a := by
  have hden := Rat.den_one_sub _ _ hcint (STAmount.IntegralCanonical.den_eq_one a hic)
  have hamax := (abs_le.mp (STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le a hic hsz)).2
  have hcov0 : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  exact LoanBroker.applyCoverTransaction_debit_value lb a res happ (Or.inr ⟨hic, hsz⟩)
    (Number.exists_of_int _ hden (by linarith) (by linarith))

end XRPL.Model.Lending
