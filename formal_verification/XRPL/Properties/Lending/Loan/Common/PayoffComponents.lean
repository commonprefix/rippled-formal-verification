import XRPL.Properties.Lending.Loan.Common.FullPaymentSize
import XRPL.Properties.Lending.Loan.Common.RoundTotal
import XRPL.Properties.Lending.Loan.Common.ScheduleComputes

/-! # The instalment that pays a loan off computes

The interest of an early payoff is a few products of the theoretical principal, the rate and the elapsed time.
They stay far below `10^200`, so the full payment's components compute once the interest and close fee fit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.fullComponents roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay

/-- A count of seconds is a normalized `Number` of that value, below `2^32`. -/
private lemma Number.ofInt64_seconds (n : UInt32) :
    (Number.ofInt64 n.toUInt64.toInt64).isNormalized ∧ |(Number.ofInt64 n.toUInt64.toInt64).toRat| < 2 ^ 32 ∧
      (n ≠ 0 → 1 ≤ |(Number.ofInt64 n.toUInt64.toInt64).toRat|) := by
  refine ⟨Number.ofInt64_isNormalized _, ?_, fun hn => ?_⟩
  · rw [Number.ofInt64_count, abs_of_nonneg (by positivity)]
    exact_mod_cast n.toNat_lt
  · rw [Number.ofInt64_count, abs_of_nonneg (by positivity)]
    have : n.toNat ≠ 0 := fun h0 => hn (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

/-- The interest accrued since the last payment computes for a theoretical principal below `10^150` and a rate
below `10^20`, and it stays below `10^185`. -/
private lemma loanAccruedInterest_ok (tpo rate : Number) (now start prev interval : UInt32) (htpo : tpo.isNormalized)
    (htl : |tpo.toRat| < 10 ^ 150) (hr : rate.isNormalized) (hrl : |rate.toRat| < 10 ^ 20) :
    ∃ a, loanAccruedInterest tpo rate now start prev interval = .ok a ∧ a.isNormalized ∧
      |a.toRat| < 10 ^ 185 := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  have hz : ∃ a, (Except.ok Number.zero : Except Error Number) = .ok a ∧ a.isNormalized ∧ |a.toRat| < 10 ^ 185 :=
    ⟨Number.zero, rfl, Number.zero_isNormalized, by rw [Number.toRat_zero, abs_zero]; norm_num⟩
  unfold loanAccruedInterest
  by_cases h1 : rate.operator_eq Number.zero = true
  · simp only [h1, ↓reduceIte]; exact hz
  by_cases h2 : (interval == 0) = true
  · simp only [h1, h2, ↓reduceIte, pure_bind]; exact hz
  by_cases h3 : now ≤ (if prev < start then start else prev)
  · simp only [h1, h2, h3, ↓reduceIte, pure_bind]; exact hz
  simp only [h1, h2, h3, ↓reduceIte, pure_bind, Bool.false_eq_true]
  have hint := h2
  obtain ⟨m1, hm1⟩ := Number.operator_mul_ok_of_abs tpo rate .to_nearest htpo hr (by linarith) (by linarith)
  have hm1n := Number.operator_mul_isNormalized _ _ _ _ htpo hr hm1
  have hm1l : |m1.toRat| < 10 ^ 171 := by
    have := (Number.mul_near _ _ _ htpo hr hm1).abs_le
    rw [abs_mul] at this
    calc |m1.toRat| ≤ |tpo.toRat| * |rate.toRat| * (1 + Number.nearestError) := this
      _ ≤ 10 ^ 150 * 10 ^ 20 * 2 := by gcongr; linarith
      _ < 10 ^ 171 := by norm_num
  obtain ⟨hsn, hsl, -⟩ := Number.ofInt64_seconds (now - (if prev < start then start else prev))
  obtain ⟨m2, hm2⟩ := Number.operator_mul_ok_of_abs m1 _ .to_nearest hm1n hsn (by linarith)
    (by linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num])
  have hm2n := Number.operator_mul_isNormalized _ _ _ _ hm1n hsn hm2
  have hm2l : |m2.toRat| < 10 ^ 182 := by
    have := (Number.mul_near _ _ _ hm1n hsn hm2).abs_le
    rw [abs_mul] at this
    calc |m2.toRat| ≤ _ := this
      _ ≤ 10 ^ 171 * 2 ^ 32 * 2 := by gcongr; linarith
      _ < 10 ^ 182 := by norm_num
  obtain ⟨hin, -, hil⟩ := Number.ofInt64_seconds interval
  have hint' : interval ≠ 0 := by simpa using hint
  obtain ⟨q, hq⟩ := Number.operator_div_ok_of_abs m2 _ .to_nearest hm2n hin (by linarith)
    (le_trans (by norm_num) (hil hint'))
  have hqn := Number.operator_div_isNormalized _ _ _ _ hm2n hin hq
  refine ⟨q, ?_, hqn, ?_⟩
  · simp only [hm1, ok_bind, hm2, hq]
  · have := (Number.div_near _ _ _ hm2n hin hq).abs_le
    rw [abs_div] at this
    have h1 := hil hint'
    calc |q.toRat| ≤ |m2.toRat| / |(Number.ofInt64 interval.toUInt64.toInt64).toRat| * (1 + Number.nearestError) :=
          this
      _ ≤ |m2.toRat| / 1 * (1 + Number.nearestError) := by gcongr
      _ ≤ 10 ^ 182 * 2 := by rw [div_one]; gcongr; linarith
      _ < 10 ^ 185 := by norm_num

/-- The interest of an early payoff computes for a theoretical principal below `10^150` and a rate below
`10^20`. -/
lemma computeFullPaymentInterest_ok (tpo rate : Number) (now interval prev start : UInt32) (cr : TenthBips32)
    (htpo : tpo.isNormalized) (htl : |tpo.toRat| < 10 ^ 150) (hr : rate.isNormalized) (hrl : |rate.toRat| < 10 ^ 20) :
    ∃ fi, computeFullPaymentInterest tpo rate now interval prev start cr = .ok fi := by
  obtain ⟨a, ha, han, hal⟩ := loanAccruedInterest_ok tpo rate now start prev interval htpo htl hr hrl
  obtain ⟨p, hp, hpn, hpl⟩ : ∃ p, (if cr == 0 then pure Number.zero else tenthBipsOfValue tpo cr .to_nearest :
      Except Error Number) = .ok p ∧ p.isNormalized ∧ |p.toRat| < 10 ^ 185 := by
    split
    · exact ⟨Number.zero, rfl, Number.zero_isNormalized, by rw [Number.toRat_zero, abs_zero]; norm_num⟩
    · obtain ⟨p, hp, hpn, hpl⟩ := tenthBipsOfValue_ok_of_abs tpo cr htpo (by linarith)
      refine ⟨p, hp, hpn, ?_⟩
      have hε := Number.nearestError_pos
      have hε' := Number.nearestError_le
      have hc : (cr.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast cr.toNat_lt
      calc |p.toRat| ≤ |tpo.toRat| * cr.toNat / 100000 * (1 + Number.nearestError) ^ 2 := hpl
        _ ≤ 10 ^ 150 * 2 ^ 32 / 100000 * 2 ^ 2 := by gcongr; linarith
        _ < 10 ^ 185 := by norm_num
  obtain ⟨fi, hfi⟩ := Number.operator_add_ok_of_abs a p .to_nearest han hpn (by linarith) (by linarith)
  refine ⟨fi, ?_⟩
  unfold computeFullPaymentInterest
  rw [ha, ok_bind]
  by_cases hc : (cr == 0) = true
  · rw [if_pos hc] at hp
    obtain rfl := Except.ok.inj hp
    simp only [hc, ↓reduceIte, pure_bind]
    exact hfi
  · rw [if_neg hc] at hp
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
    rw [hp, ok_bind]
    exact hfi

/-- A nonnegative amount the asset holds without overflow: below `10^90` for an IOU, a unit below the maximum for
XRP or an MPT. -/
def _root_.XRPL.Model.Protocol.NumericType.Fits (nt : NumericType) (x : ℚ) : Prop :=
  (nt = .fractional ∧ x < 10 ^ 90) ∨ ((nt = .native ∨ nt = .int64) ∧ x + 1 ≤ nt.maxValue.toNat)

/-- An amount no larger than one that fits also fits. -/
lemma _root_.XRPL.Model.Protocol.NumericType.Fits.mono {nt : NumericType} {x y : ℚ} (h : nt.Fits x) (hy : y ≤ x) :
    nt.Fits y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by linarith⟩
  · exact Or.inr ⟨h1, by linarith⟩

/-- A nonnegative amount that fits rounds to the asset at a scale in `[-96, 79]`, in every mode. -/
lemma STAmount.roundToNumericType_ok_of_fits (nt : NumericType) (x : Number) (mode : rounding_mode) (s : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hf : nt.Fits x.toRat) (hs : -96 ≤ s ∧ s ≤ 79) :
    ∃ y, STAmount.roundToNumericType nt x mode (some s) = .ok y := by
  rcases hf with ⟨rfl, hlt⟩ | ⟨hnt, hmax⟩
  · exact STAmount.roundToNumericType_frac_ok x mode s hx h0 hlt hs
  · exact STAmount.roundToNumericType_integral_ok nt x mode (some s) hnt hx h0 hmax

/-- A near value of a value at least zero is at least zero. -/
lemma _root_.XRPL.Model.Protocol.Number.Near.nonneg {r : Number} {t : ℚ} (h : r.Near t) (ht : 0 ≤ t) :
    0 ≤ r.toRat := by
  have hε' := Number.nearestError_le
  rcases h with h | h
  · rw [h]
  · rw [abs_of_nonneg ht] at h
    have := neg_abs_le (r.toRat - t)
    have : t * Number.nearestError ≤ t := by
      have : Number.nearestError ≤ 1 := le_trans hε' (by norm_num)
      nlinarith
    linarith

/-- The management fee of an amount that fits computes, at most the amount and at least zero. -/
lemma computeManagementFee_ok (nt : NumericType) (x : Number) (rate : TenthBips16) (s : Int) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hf : nt.Fits x.toRat) (hrate : rate.toNat ≤ 10000) (hs : -81 ≤ s ∧ s ≤ 79) :
    ∃ f, computeManagementFee nt x rate s = .ok f ∧ f.isNormalized ∧ 0 ≤ f.toRat ∧ f.toRat ≤ x.toRat := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  have hfl : x.toRat < 10 ^ 90 := by
    rcases hf with ⟨-, h⟩ | ⟨hnt, h⟩
    · exact h
    · have hm : nt.maxValue.toNat ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
      have : (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
      linarith [show (2 : ℚ) ^ 63 < 10 ^ 90 by norm_num]
  obtain ⟨raw, hraw, hrn, -⟩ := tenthBipsOfValue_ok_of_abs x rate.toTenthBips32 hx
    (by rw [abs_of_nonneg h0]; linarith [show (10 : ℚ) ^ 90 < 10 ^ 190 by norm_num])
  have hr32 : (rate.toTenthBips32.toNat : ℚ) ≤ 10000 := by
    show ((rate.toUInt32).toNat : ℚ) ≤ 10000
    rw [UInt16.toNat_toUInt32]; exact_mod_cast hrate
  -- the raw fee is near a tenth of the amount at most
  have hmul : ∀ m, x.operator_mul rate.toTenthBips32.toNumber .to_nearest = .ok m →
      0 ≤ m.toRat ∧ m.toRat ≤ x.toRat * 10000 * (1 + Number.nearestError) := by
    intro m hm
    obtain ⟨hbn, hbv⟩ := TenthBips32.toNumber_facts rate.toTenthBips32
    have hn := Number.mul_near _ _ _ hx hbn hm
    rw [hbv] at hn
    exact ⟨hn.nonneg (by positivity), le_trans (hn.le (by positivity)) (by gcongr)⟩
  have hraw' : 0 ≤ raw.toRat ∧ raw.toRat ≤ x.toRat := by
    unfold tenthBipsOfValue at hraw
    obtain ⟨m, hm, hraw⟩ := bind_ok_peel _ _ _ hraw
    obtain ⟨hm0, hmle⟩ := hmul m hm
    obtain ⟨hbn, -⟩ := TenthBips32.toNumber_facts rate.toTenthBips32
    obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
    have hu : (kTenthBipsPerUnity.toNat : ℚ) = 100000 := by decide
    rw [hu] at huv
    have hmn := Number.operator_mul_isNormalized _ _ _ _ hx hbn hm
    have hn := Number.div_near _ _ _ hmn hun hraw
    rw [huv] at hn
    refine ⟨hn.nonneg (by positivity), le_trans (hn.le (by positivity)) ?_⟩
    calc m.toRat / 100000 * (1 + Number.nearestError)
        ≤ x.toRat * 10000 * (1 + Number.nearestError) / 100000 * (1 + Number.nearestError) := by gcongr
      _ ≤ x.toRat := by
          have : (1 + Number.nearestError) * (1 + Number.nearestError) ≤ 10 := by nlinarith
          nlinarith
  obtain ⟨f, hfok⟩ := STAmount.roundToNumericType_ok_of_fits nt raw .downward s hrn hraw'.1 (hf.mono hraw'.2)
    ⟨by omega, hs.2⟩
  have hfn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfok
  have hf0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hrn hraw'.1 (Or.inr (Or.inr rfl))
    ⟨hs.1, by omega⟩ hfok
  have hfle := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hrn hraw'.1 ⟨hs.1, by omega⟩ hfok
  refine ⟨f, ?_, hfn, hf0, le_trans hfle hraw'.2⟩
  unfold computeManagementFee
  rw [hraw, ok_bind, hfok]

/-- A normalized number below `10^b` in size, for the bounds of a payoff's amounts. -/
def _root_.XRPL.Model.Protocol.Number.Below (x : Number) (b : ℕ) : Prop := x.isNormalized ∧ |x.toRat| < 10 ^ b

/-- A to-nearest sum of numbers below `10^b` is below `10^(b + 1)`. -/
lemma _root_.XRPL.Model.Protocol.Number.Below.add {x y r : Number} {b : ℕ} (hx : x.Below b) (hy : y.Below b)
    (h : x.operator_add y .to_nearest = .ok r) : r.Below (b + 1) := by
  have hε' := Number.nearestError_le
  refine ⟨operator_add_isNormalized_to_nearest_sz _ _ _ hx.1 hy.1 h, ?_⟩
  have := (Number.add_near _ _ _ hx.1 hy.1 h).abs_le
  have h1 := abs_add_le x.toRat y.toRat
  have hp : (10 : ℚ) ^ (b + 1) = 10 ^ b * 10 := by rw [pow_succ]
  rw [hp]
  have h2 : |x.toRat + y.toRat| < 2 * 10 ^ b := by linarith [hx.2, hy.2]
  nlinarith [abs_nonneg (x.toRat + y.toRat), Number.nearestError_pos]

/-- A to-nearest difference of numbers below `10^b` is below `10^(b + 1)`. -/
lemma _root_.XRPL.Model.Protocol.Number.Below.sub {x y r : Number} {b : ℕ} (hx : x.Below b) (hy : y.Below b)
    (h : x.operator_sub y .to_nearest = .ok r) : r.Below (b + 1) := by
  have hε' := Number.nearestError_le
  refine ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hx.1 hy.1 h, ?_⟩
  have := (Number.sub_near _ _ _ hx.1 hy.1 h).abs_le
  have h1 := abs_sub x.toRat y.toRat
  have hp : (10 : ℚ) ^ (b + 1) = 10 ^ b * 10 := by rw [pow_succ]
  rw [hp]
  have h2 : |x.toRat - y.toRat| < 2 * 10 ^ b := by linarith [hx.2, hy.2]
  nlinarith [abs_nonneg (x.toRat - y.toRat), Number.nearestError_pos]

/-- A number below `10^b` is below any larger power. -/
lemma _root_.XRPL.Model.Protocol.Number.Below.mono {x : Number} {b c : ℕ} (h : x.Below b) (hbc : b ≤ c) :
    x.Below c :=
  ⟨h.1, lt_of_lt_of_le h.2 (pow_le_pow_right₀ (by norm_num) hbc)⟩

/-- A to-nearest sum of numbers below `10^b` computes. -/
lemma _root_.XRPL.Model.Protocol.Number.Below.add_ok {x y : Number} {b : ℕ} (hb : b ≤ 190) (hx : x.Below b)
    (hy : y.Below b) :
    ∃ r, x.operator_add y .to_nearest = .ok r :=
  Number.operator_add_ok_of_abs x y _ hx.1 hy.1 (lt_of_lt_of_le hx.2 (pow_le_pow_right₀ (by norm_num) (by omega)))
    (lt_of_lt_of_le hy.2 (pow_le_pow_right₀ (by norm_num) (by omega)))

/-- A to-nearest difference of numbers below `10^b` computes. -/
lemma _root_.XRPL.Model.Protocol.Number.Below.sub_ok {x y : Number} {b : ℕ} (hb : b ≤ 190) (hx : x.Below b)
    (hy : y.Below b) :
    ∃ r, x.operator_sub y .to_nearest = .ok r :=
  Number.operator_sub_ok_of_abs x y _ hx.1 hy.1 (lt_of_lt_of_le hx.2 (pow_le_pow_right₀ (by norm_num) (by omega)))
    (lt_of_lt_of_le hy.2 (pow_le_pow_right₀ (by norm_num) (by omega)))

/-- An amount that fits is below `10^150`. -/
lemma _root_.XRPL.Model.Protocol.NumericType.Fits.below {nt : NumericType} {x : ℚ} (h : nt.Fits x) (h0 : 0 ≤ x) :
    |x| < 10 ^ 150 := by
  rw [abs_of_nonneg h0]
  rcases h with ⟨-, h⟩ | ⟨hnt, h⟩
  · linarith [show (10 : ℚ) ^ 90 < 10 ^ 150 by norm_num]
  · have hm : nt.maxValue.toNat ≤ 2 ^ 63 := by rcases hnt with rfl | rfl <;> decide
    have : (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
    linarith [show (2 : ℚ) ^ 63 < 10 ^ 150 by norm_num]

/-- The full payment's components compute once the rate and the theoretical principal do, the payoff interest
fits the asset and the close fee rounds to it. The instalment clears the loan, its amounts below `10^160`. -/
lemma Loan.fullComponents_ok (loan : Loan) (now : UInt32) (rate tpo cf : Number)
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (htpoN : tpo.isNormalized) (htl : |tpo.toRat| < 10 ^ 150) (hrN : rate.isNormalized)
    (hrl : |rate.toRat| < 10 ^ 20)
    (hfi : ∀ fi, computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fi →
      fi.isNormalized ∧ 0 ≤ fi.toRat ∧ loan.broker.numericType.Fits fi.toRat)
    (hcf : STAmount.roundToNumericType loan.broker.numericType loan.fees.closePaymentFee .to_nearest
      (some loan.loanScale) = .ok cf)
    (hcfl : |cf.toRat| < 10 ^ 150) (hcf0 : 0 ≤ cf.toRat) (hs : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 79)
    (hT : |loan.totalValueOutstanding.toRat| < 10 ^ 150) (hP : |loan.principalOutstanding.toRat| < 10 ^ 150)
    (hM : |loan.managementFeeOutstanding.toRat| < 10 ^ 150) :
    ∃ pc fi fi' fee, computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval
        loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate = .ok fi ∧
      STAmount.roundToNumericType loan.broker.numericType fi .downward (some loan.loanScale) = .ok fi' ∧
      computeManagementFee loan.broker.numericType fi' loan.broker.managementFeeRate loan.loanScale = .ok fee ∧
      0 ≤ fee.toRat ∧ fee.toRat ≤ fi'.toRat ∧ fi'.toRat ≤ fi.toRat ∧
      Loan.fullComponents loan now = .ok pc ∧ pc.isFinal = true ∧
      pc.principalDelta = loan.principalOutstanding ∧ pc.managementFeeDelta = loan.managementFeeOutstanding ∧
      pc.totalValueDelta.Below 160 ∧ pc.untrackedInterest.Below 160 ∧ pc.untrackedManagementFee.Below 160 ∧
      -loan.managementFeeOutstanding.toRat ≤ pc.untrackedManagementFee.toRat ∧
      pc.untrackedManagementFee.toRat ≤ (cf.toRat + fee.toRat) * (1 + Number.nearestError) ^ 2 := by
  have hcfN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf
  obtain ⟨fi, hfiok⟩ := computeFullPaymentInterest_ok tpo rate now loan.schedule.paymentInterval
    loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate htpoN htl hrN hrl
  obtain ⟨hfiN, hfi0, hfif⟩ := hfi fi hfiok
  obtain ⟨fi', hfi'⟩ := STAmount.roundToNumericType_ok_of_fits _ fi .downward loan.loanScale hfiN hfi0 hfif
    ⟨by omega, hs.2⟩
  have hfi'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfi'
  have hfi'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfiN hfi0 (Or.inr (Or.inr rfl))
    ⟨hs.1, by omega⟩ hfi'
  have hfi'le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfiN hfi0 ⟨hs.1, by omega⟩ hfi'
  obtain ⟨fee, hfee, hfeeN, hfee0, hfeele⟩ := computeManagementFee_ok _ fi' loan.broker.managementFeeRate
    loan.loanScale hfi'N hfi'0 (hfif.mono hfi'le) (by
      have := loan.broker.valid.managementFeeRate_cap
      unfold maxManagementFeeRate at this
      exact UInt16.le_iff_toNat_le.mp this) hs
  have hfib := hfif.below hfi0
  have hfi'B : fi'.Below 150 := by
    refine ⟨hfi'N, ?_⟩
    rw [abs_of_nonneg hfi'0]
    linarith [le_abs_self fi.toRat]
  have hfeeB : fee.Below 150 := by
    refine ⟨hfeeN, ?_⟩
    rw [abs_of_nonneg hfee0]
    linarith [hfi'B.2, le_abs_self fi'.toRat]
  obtain ⟨net, hnet⟩ := hfi'B.sub_ok (by norm_num) hfeeB
  have hnetB := hfi'B.sub hfeeB hnet
  have hsplit : roundAndSplitInterest fi loan.broker.managementFeeRate .downward loan.broker.numericType
      loan.loanScale = .ok (net, fee) := by
    unfold roundAndSplitInterest
    rw [hfi', ok_bind, hfee, ok_bind, hnet]
    rfl
  have hTB : loan.totalValueOutstanding.Below 150 := ⟨loan.wf.totalValueOutstanding_norm, hT⟩
  have hPB : loan.principalOutstanding.Below 150 := ⟨loan.wf.principalOutstanding_norm, hP⟩
  have hMB : loan.managementFeeOutstanding.Below 150 := ⟨loan.wf.managementFeeOutstanding_norm, hM⟩
  obtain ⟨d1, hd1⟩ := hTB.sub_ok (by norm_num) hPB
  have hd1B := hTB.sub hPB hd1
  obtain ⟨d2, hd2⟩ := hd1B.sub_ok (by norm_num) (hMB.mono (by norm_num))
  have hd2B := hd1B.sub (hMB.mono (by norm_num)) hd2
  have hstate : loan.state = .ok ⟨loan.totalValueOutstanding, loan.principalOutstanding, d2,
      loan.managementFeeOutstanding⟩ := by
    unfold Loan.state LoanState.build
    rw [hd1, ok_bind, hd2]
    rfl
  have hcfB : cf.Below 150 := ⟨hcfN, hcfl⟩
  obtain ⟨a1, ha1⟩ := (hPB.mono (by norm_num : 150 ≤ 152)).add_ok (by norm_num) hd2B
  have ha1B := (hPB.mono (by norm_num : 150 ≤ 152)).add hd2B ha1
  obtain ⟨a2, ha2⟩ := ha1B.add_ok (by norm_num) (hMB.mono (by norm_num))
  have ha2B := ha1B.add (hMB.mono (by norm_num)) ha2
  obtain ⟨a3, ha3⟩ := hcfB.add_ok (by norm_num) hfeeB
  have ha3B := hcfB.add hfeeB ha3
  obtain ⟨a4, ha4⟩ := ha3B.sub_ok (by norm_num) (hMB.mono (by norm_num))
  have ha4B := ha3B.sub (hMB.mono (by norm_num)) ha4
  obtain ⟨a5, ha5⟩ := (hnetB.mono (by norm_num : 151 ≤ 152)).sub_ok (by norm_num) hd2B
  have ha5B := (hnetB.mono (by norm_num : 151 ≤ 152)).sub hd2B ha5
  -- the untracked fee, at least minus ManagementFeeOutstanding and at most the close fee and the fee share
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have ha30 : 0 ≤ a3.toRat := operator_add_nonneg _ _ _ hcfN hfeeN ha3 (by linarith)
  have ha3le := (Number.add_near _ _ _ hcfN hfeeN ha3).le (by linarith)
  have ha4ge : -loan.managementFeeOutstanding.toRat ≤ a4.toRat := by
    have hR := operator_add_rounded_to_nearest _ _ _ ha3B.1
      (Number.operator_neg_isNormalized _ loan.wf.managementFeeOutstanding_norm) ha4
    have := hR.ge_of_le (Or.inl rfl) loan.managementFeeOutstanding.operator_neg
      (Number.operator_neg_isNormalized _ loan.wf.managementFeeOutstanding_norm)
      (by rw [Number.toRat_neg]; linarith)
    rwa [Number.toRat_neg] at this
  have ha4le : a4.toRat ≤ (cf.toRat + fee.toRat) * (1 + Number.nearestError) ^ 2 := by
    have h1 := (Number.sub_near _ _ _ ha3B.1 loan.wf.managementFeeOutstanding_norm ha4).le_max
    have h2 : Max.max (a3.toRat - loan.managementFeeOutstanding.toRat) 0 ≤ a3.toRat := max_le (by linarith) ha30
    have hε := Number.nearestError_pos
    calc a4.toRat ≤ Max.max (a3.toRat - loan.managementFeeOutstanding.toRat) 0 * (1 + Number.nearestError) := h1
      _ ≤ a3.toRat * (1 + Number.nearestError) := by gcongr
      _ ≤ (cf.toRat + fee.toRat) * (1 + Number.nearestError) * (1 + Number.nearestError) := by gcongr
      _ = (cf.toRat + fee.toRat) * (1 + Number.nearestError) ^ 2 := by ring
  refine ⟨⟨a2, loan.principalOutstanding, loan.managementFeeOutstanding, a5, a4, true⟩, fi, fi', fee, hfiok, hfi',
    hfee, hfee0, hfeele, hfi'le, ?_, rfl, rfl, rfl,
    ha2B.mono (by norm_num : 154 ≤ 160), ha5B.mono (by norm_num : 153 ≤ 160), ha4B.mono (by norm_num : 152 ≤ 160),
    ha4ge, ha4le⟩
  unfold Loan.fullComponents
  rw [hrate, ok_bind, htpo, ok_bind, hfiok, ok_bind, hsplit, ok_bind]
  simp only []
  rw [hstate, ok_bind, hcf, ok_bind]
  simp only []
  rw [ha1, ok_bind, ha2, ok_bind, ha3, ok_bind, ha4, ok_bind, ha5, ok_bind]
  rfl

end XRPL.Model.Lending
