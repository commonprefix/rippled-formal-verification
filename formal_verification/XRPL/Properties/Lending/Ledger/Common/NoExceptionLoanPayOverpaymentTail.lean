import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayOverpaymentProps
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayOverpaymentLoop
import XRPL.Properties.Lending.Loan.Common.OverpaymentSkip
import XRPL.Properties.Protocol.Common.Wrap

/-! # The overpayment tail of a LoanPay computes

After its scheduled instalments an overpayment spends what is left of its amount on extra principal and
re-amortizes the loan. Every step computes on a loan with the room of the instalment loop: the split of the
overpayment, the re-amortized loan values, the rebuilt state and the amortization guards. On XRP the rebuilt
total value has to be an XRP amount, which this proof gets from a bound on the payments left and the value owed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.overpaymentComponents Loan.tryOverpayment roundAndSplitInterest UnsettledPayment.applyOverpayment
  from XRPL.Model.Lending.Loan.LoanPay
open private rn_nonneg rn_ge from XRPL.Properties.Lending.Loan.Common.SetLawful
open private STAmount.roundToNumericType_asset_ok from XRPL.Properties.Lending.Loan.Common.NextInstalment
open private LoanState.buildTheoretical_tight from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayRoom
open private mgmt_toNat_le from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetValue
open private STAmount.roundToNumericType_towards_zero_ok from XRPL.Properties.Lending.Loan.Common.OverpaymentSkip
open private STAmount.roundToNumericType_towards_zero_some_le from XRPL.Properties.Lending.Loan.Common.PayCharge

local notation "ε" => Number.nearestError

/-- XRP and an MPT hold at least `10^17` units. -/
private lemma NumericType.maxValue_ge (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hint : nt.isIntegral = true) :
    (10 : ℚ) ^ 17 ≤ nt.maxValue.toNat := by
  rcases hasset with h | h | h
  · rw [h] at hint; cases hint
  · rw [h]
    have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
    rw [this]
  · rw [h]
    have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
    rw [this]; norm_num

/-- The split of an overpayment of at most `10^16 + 1` computes. The principal it pays is at most the overpayment
plus one, and every part is far below `10^18`. -/
lemma Loan.overpaymentComponents_computes (l : Loan) (ov : Number) (hovN : ov.isNormalized) (hov0 : 0 ≤ ov.toRat)
    (hovT : ov.toRat ≤ 10 ^ 16 + 1)
    (hasset : l.broker.numericType = .fractional ∨ l.broker.numericType = .native ∨
      l.broker.numericType = .int64)
    (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) :
    ∃ opc, Loan.overpaymentComponents l ov = .ok opc ∧ opc.principalDelta.isNormalized ∧
      opc.principalDelta.toRat ≤ ov.toRat + 1 ∧ |opc.principalDelta.toRat| ≤ 3 * 10 ^ 17 ∧
      opc.managementFeeDelta.isNormalized ∧ |opc.managementFeeDelta.toRat| ≤ 10 ^ 17 ∧
      opc.untrackedInterest.isNormalized ∧ |opc.untrackedInterest.toRat| ≤ 10 ^ 17 ∧
      opc.untrackedManagementFee.isNormalized ∧ |opc.untrackedManagementFee.toRat| ≤ 10 ^ 17 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hmaxge := NumericType.maxValue_ge l.broker.numericType hasset
  have h2 : (1 + ε) ^ 2 ≤ 1 + 1 / 10 ^ 17 := by
    have := one_add_pow_le_lin ε 2 he.le (by push_cast; linarith)
    push_cast at this; linarith
  -- a share of the overpayment at a rate of at most 100% is at most the overpayment plus one
  have hshare : ∀ (bips : TenthBips32) (r : Number), bips.toNat ≤ 100000 →
      tenthBipsOfValue ov bips .to_nearest = .ok r → r.isNormalized ∧ 0 ≤ r.toRat ∧ r.toRat ≤ ov.toRat + 1 := by
    intro bips r hb hr
    obtain ⟨hrN, hr0, hrle⟩ := tenthBipsOfValue_le_share ov bips r hovN hov0 hr
    refine ⟨hrN, hr0, ?_⟩
    have hbq : (bips.toNat : ℚ) / 100000 ≤ 1 := by
      rw [div_le_one (by norm_num)]; exact_mod_cast hb
    calc r.toRat ≤ ov.toRat * (bips.toNat / 100000) * (1 + ε) ^ 2 := hrle
      _ ≤ ov.toRat * 1 * (1 + 1 / 10 ^ 17) := by gcongr
      _ ≤ ov.toRat + 1 := by nlinarith
  have hov190 : |ov.toRat| < 10 ^ 190 := by
    rw [abs_of_nonneg hov0]; linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 190 by norm_num]

  -- the overpayment fee, rounded to the asset
  obtain ⟨fee, hfee, -, -⟩ := tenthBipsOfValue_ok_of_abs ov l.rates.overpaymentFee hovN hov190
  obtain ⟨hfeeN, hfee0, hfeele⟩ := hshare _ fee l.exact.overpaymentFee_cap hfee
  obtain ⟨fee', hfee', hfee'N, hfee'l⟩ := STAmount.roundToNumericType_asset_ok _ fee .to_nearest l.loanScale hasset
    hs hfeeN (by rw [abs_of_nonneg hfee0]; linarith [show (10 : ℚ) ^ 16 + 2 < 10 ^ 90 by norm_num])
    (fun hint => by rw [abs_of_nonneg hfee0]; linarith [hmaxge hint])
  have hfee'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfeeN hfee0 (Or.inl rfl) ⟨hs.1, by omega⟩ hfee'
  rw [abs_of_nonneg hfee0, abs_of_nonneg hfee'0] at hfee'l
  obtain ⟨vd, hvd, -, -⟩ := Number.reamSub ov fee' (10 ^ 17) (10 ^ 17) hovN hfee'N
    (by rw [abs_of_nonneg hov0]; linarith) (by rw [abs_of_nonneg hfee'0]; linarith) (by norm_num)

  -- the interest, rounded and split into net interest and its management fee
  obtain ⟨int, hint', -, -⟩ := tenthBipsOfValue_ok_of_abs ov l.rates.overpaymentInterestRate hovN hov190
  obtain ⟨hintN, hint0, hintle⟩ := hshare _ int l.exact.overpaymentInterestRate_cap hint'
  obtain ⟨lr, hlr, hlrN, hlrl⟩ := STAmount.roundToNumericType_asset_ok _ int .to_nearest l.loanScale hasset
    hs hintN (by rw [abs_of_nonneg hint0]; linarith [show (10 : ℚ) ^ 16 + 2 < 10 ^ 90 by norm_num])
    (fun hint => by rw [abs_of_nonneg hint0]; linarith [hmaxge hint])
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hintN hint0 (Or.inl rfl) ⟨hs.1, by omega⟩ hlr
  rw [abs_of_nonneg hint0, abs_of_nonneg hlr0] at hlrl
  have hfit : l.broker.numericType.Fits lr.toRat := by
    rcases hasset with h | h | h
    · exact Or.inl ⟨h, by linarith [show (10 : ℚ) ^ 17 < 10 ^ 90 by norm_num]⟩
    · exact Or.inr ⟨Or.inl h, by have := hmaxge (by rw [h]; rfl); linarith⟩
    · exact Or.inr ⟨Or.inr h, by have := hmaxge (by rw [h]; rfl); linarith⟩
  obtain ⟨split, hsplit, hspN, hsp0, hsple⟩ := computeManagementFee_ok _ lr l.broker.managementFeeRate
    l.loanScale hlrN hlr0 hfit l.broker.managementFeeRate_le ⟨hs.1, by omega⟩
  obtain ⟨net, hnet, hnetN, hnetl⟩ := Number.reamSub lr split (3 * 10 ^ 16) (3 * 10 ^ 16) hlrN hspN
    (by rw [abs_of_nonneg hlr0]; linarith) (by rw [abs_of_nonneg hsp0]; linarith) (by norm_num)
  have hnet0 : 0 ≤ net.toRat :=
    rn_nonneg (Number.operator_sub_rounded_to_nearest _ _ _ hlrN hspN hnet) (by linarith)
  have hrs : roundAndSplitInterest int l.broker.managementFeeRate .to_nearest l.broker.numericType
      l.loanScale = .ok (net, split) := by
    unfold roundAndSplitInterest
    simp only [hlr, hsplit, hnet, bind, Except.bind, pure, Except.pure]

  -- the principal: the overpayment less the net interest, its fee and the overpayment fee
  obtain ⟨p1, hp1, hp1N, hp1l⟩ := Number.reamSub ov net (10 ^ 17) (7 * 10 ^ 16) hovN hnetN
    (by rw [abs_of_nonneg hov0]; linarith) (by linarith) (by norm_num)
  have hp1le : p1.toRat ≤ ov.toRat * (1 + ε) :=
    le_trans (Number.sub_near _ _ _ hovN hnetN hp1).le_max
      (mul_le_mul_of_nonneg_right (max_le (by linarith) hov0) (by linarith))
  obtain ⟨p2, hp2, hp2N, hp2l⟩ := Number.reamSub p1 split (18 * 10 ^ 16) (3 * 10 ^ 16) hp1N hspN
    (by linarith) (by rw [abs_of_nonneg hsp0]; linarith) (by norm_num)
  have hp2le : p2.toRat ≤ ov.toRat * (1 + ε) ^ 2 := by
    calc p2.toRat ≤ max (p1.toRat - split.toRat) 0 * (1 + ε) := (Number.sub_near _ _ _ hp1N hspN hp2).le_max
      _ ≤ ov.toRat * (1 + ε) * (1 + ε) := by
          gcongr
          exact max_le (by linarith) (by positivity)
      _ = ov.toRat * (1 + ε) ^ 2 := by ring
  obtain ⟨pd, hpd, hpdN, hpdl⟩ := Number.reamSub p2 fee' (22 * 10 ^ 16) (3 * 10 ^ 16) hp2N hfee'N
    (by linarith) (by rw [abs_of_nonneg hfee'0]; linarith) (by norm_num)
  have hpdle : pd.toRat ≤ ov.toRat + 1 := by
    have h3 : (1 + ε) ^ 3 ≤ 1 + 1 / 10 ^ 17 := by
      have := one_add_pow_le_lin ε 3 he.le (by push_cast; linarith)
      push_cast at this; linarith
    calc pd.toRat ≤ max (p2.toRat - fee'.toRat) 0 * (1 + ε) := (Number.sub_near _ _ _ hp2N hfee'N hpd).le_max
      _ ≤ ov.toRat * (1 + ε) ^ 2 * (1 + ε) := by
          gcongr
          exact max_le (by linarith) (by positivity)
      _ = ov.toRat * (1 + ε) ^ 3 := by ring
      _ ≤ ov.toRat * (1 + 1 / 10 ^ 17) := by gcongr
      _ ≤ ov.toRat + 1 := by nlinarith
  refine ⟨{ totalValueDelta := vd, principalDelta := pd, managementFeeDelta := split, isFinal := false,
            untrackedInterest := net, untrackedManagementFee := fee' }, ?_, hpdN, hpdle, by linarith, hspN,
    by rw [abs_of_nonneg hsp0]; linarith, hnetN, by linarith, hfee'N, by rw [abs_of_nonneg hfee'0]; linarith⟩
  unfold Loan.overpaymentComponents
  simp only [hfee, hfee', hvd, hint', hrs, hp1, hp2, hpd, bind, Except.bind, pure, Except.pure]

/-- The value and the principal of a theoretical state with payments left. -/
private lemma LoanState.buildTheoretical_parts (pp rate : Number) (k : UInt32) (m : TenthBips16) (ts : LoanState)
    (hk0 : k ≠ 0) (h : LoanState.buildTheoretical pp rate k m = .ok ts) :
    pp.operator_mul (Number.ofInt64 k.toInt64) .to_nearest = .ok ts.valueOutstanding ∧
      loanPrincipalFromPeriodicPayment pp rate k = .ok ts.principalOutstanding := by
  have hk0' : (k == 0) = false := by simpa using hk0
  unfold LoanState.buildTheoretical at h
  simp only [hk0', Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨vo, hvo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tpo, htpo, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨ig, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨mf, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨i, -, h⟩ := bind_ok_peel _ _ _ h
  have h' : (Except.ok _ : Except Error LoanState) = .ok ts := h
  injection h' with h'
  rw [← h']
  exact ⟨hvo, htpo⟩

/-- A value clamped between zero and a cap of zero or more lies between them. -/
private lemma Number.clamp_zero_bounds (x cap : Number) (hx : x.isNormalized) (hcap : cap.isNormalized)
    (hc0 : 0 ≤ cap.toRat) :
    0 ≤ (Number.clamp x Number.zero cap).toRat ∧ (Number.clamp x Number.zero cap).toRat ≤ cap.toRat := by
  rcases Number.clamp_zero_cases x cap hx hcap with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨h0, hle, h⟩ <;> rw [h]
  · rw [Number.toRat_zero]; exact ⟨le_rfl, hc0⟩
  · exact ⟨hc0, le_rfl⟩
  · exact ⟨h0, hle⟩

/-- Rounding a value the asset holds and clamping it under a cap on the grid computes. The result is on the grid,
between zero and the cap. -/
private lemma roundAndClamp_computes (value cap : Number) (mode : rounding_mode) (nt : NumericType) (s : Int)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hs : -81 ≤ s ∧ s ≤ 0)
    (hvN : value.isNormalized) (hv90 : |value.toRat| < 10 ^ 90)
    (hfit : nt.isIntegral = true → |value.toRat| + 1 ≤ nt.maxValue.toNat) (hc0 : 0 ≤ cap.toRat)
    (hcapG : Number.OnGrid s cap) :
    ∃ r, roundAndClamp value cap mode nt s = .ok r ∧ r.isNormalized ∧ 0 ≤ r.toRat ∧ r.toRat ≤ cap.toRat ∧
      Number.OnGrid s r := by
  obtain ⟨y, hy, hyN, -⟩ := STAmount.roundToNumericType_asset_ok nt value mode s hasset hs hvN hv90 hfit
  have hyG : Number.OnGrid s y := STAmount.roundToNumericType_onGrid nt value y mode s ⟨hs.1, by omega⟩
    (fun _ => hs.2) hy
  obtain ⟨hr0, hrle⟩ := Number.clamp_zero_bounds y cap hyN hcapG.1 hc0
  refine ⟨Number.clamp y Number.zero cap, ?_, Number.clamp_isNormalized hyN Number.zero_isNormalized hcapG.1, hr0,
    hrle, ?_⟩
  · unfold roundAndClamp
    rw [hy, ok_bind]
    rfl
  · rcases Number.clamp_zero_cases y cap hyN hcapG.1 with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
    · exact Number.OnGrid.zero s
    · exact hcapG
    · exact hyG

set_option maxHeartbeats 1600000 in
-- one proof walks every step of the re-amortization with its bound
/-- The re-amortization after an overpayment computes on a loan with the loop's room and payments left. `hxrp` -
on XRP the rebuilt total value is an XRP amount, from a bound on the payments left and the value owed. -/
lemma Loan.tryOverpayment_computes_room (l : Loan) (hroom : l.PayRoom) (hpr : l.paymentRemaining ≠ 0)
    (hlo : -10 ≤ l.loanScale) (hint0 : l.broker.numericType.isIntegral = true → l.loanScale = 0)
    (hB : (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1))
    (opc : PaymentComponents) (hpdN : opc.principalDelta.isNormalized) (hpd0 : 0 < opc.principalDelta.toRat)
    (hpdle : opc.principalDelta.toRat ≤ l.totalValueOutstanding.toRat + 1)
    (hmdN : opc.managementFeeDelta.isNormalized) (hmdl : |opc.managementFeeDelta.toRat| ≤ 10 ^ 17)
    (huiN : opc.untrackedInterest.isNormalized) (huil : |opc.untrackedInterest.toRat| ≤ 10 ^ 17)
    (humN : opc.untrackedManagementFee.isNormalized) (huml : |opc.untrackedManagementFee.toRat| ≤ 10 ^ 17)
    (hxrp : l.broker.numericType = .native →
      20 * ((l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat) + 16 * l.totalValueOutstanding.toRat + 100 ≤
        10 ^ 17) :
    ∃ r, Loan.tryOverpayment l opc = .ok r ∧ ∀ re, r = some re → re.amounts.Norm ∧
      |re.amounts.principalPaid.toRat| ≤ 10 ^ 18 ∧ |re.amounts.interestPaid.toRat| ≤ 10 ^ 18 ∧
      |re.amounts.feePaid.toRat| ≤ 10 ^ 18 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have hasset := hroom.asset
  have hmaxge := NumericType.maxValue_ge l.broker.numericType hasset
  have hs0 := hroom.scale
  have hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0 := ⟨by omega, hs0⟩
  have hsc := hroom.computes
  have hk := hroom.clock
  have hn1 : (1 : ℚ) ≤ l.paymentRemaining.toNat := by
    have : l.paymentRemaining.toNat ≠ 0 := fun h0 => hpr (UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hir : l.rates.interestRate.toNat ≤ 100000 := by
    have := l.valid.interestRate_cap
    unfold maxLoanRate kTenthBipsPerUnity at this
    exact UInt32.le_iff_toNat_le.mp this
  have hiv : 60 ≤ l.schedule.paymentInterval.toNat := UInt32.le_iff_toNat_le.mp l.valid.paymentInterval_min
  have hmgmt := l.broker.managementFeeRate_le
  have hppN := l.wf.periodicPayment_norm
  have hpp0 : 0 ≤ l.periodicPayment.toRat := l.exact.periodicPayment_pos.le
  obtain ⟨gT, gP, gM, -, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hTle := hroom.value
  have hi3 : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat -
      l.managementFeeOutstanding.toRat := hroom.shape.3
  set B := (l.paymentRemaining.toNat : ℚ) * l.periodicPayment.toRat with hBdef
  set T := l.totalValueOutstanding.toRat with hTdef
  have hB0 : 0 ≤ B := by positivity
  have hPT : l.principalOutstanding.toRat ≤ T := by linarith
  have hMT : l.managementFeeOutstanding.toRat ≤ T := by linarith
  have habsP : |l.principalOutstanding.toRat| ≤ T := by rw [abs_of_nonneg hP0]; exact hPT
  have habsM : |l.managementFeeOutstanding.toRat| ≤ T := by rw [abs_of_nonneg hM0]; exact hMT
  have h2e : (1 + ε) ^ 2 ≤ 1 + 1 / 10 ^ 17 := by
    have := one_add_pow_le_lin ε 2 he.le (by push_cast; linarith)
    push_cast at this; linarith

  -- the rate and the state of the loan
  obtain ⟨rate, hrate⟩ := hsc.rate
  have hrate' : loanPeriodicRate l.rates.interestRate l.schedule.paymentInterval = .ok rate := hrate
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrate'
  have hr0 := loanPeriodicRate_nonneg _ _ rate hrate'
  obtain ⟨i, hi⟩ := Loan.interestDue_ok l
  have hstate := Loan.state_of_interestDue l i hi
  have hiN := RawLoan.interestDue_isNormalized l i hi
  have hiv' : i.toRat = T - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat := by
    rw [Loan.interestDue_toExact l i hi]; rfl
  have habsI : |i.toRat| ≤ T := by rw [hiv', abs_of_nonneg hi3]; linarith

  -- the theoretical state and what the loan differs from it
  obtain ⟨ts, hts, htpN, htp0, htpB, htiN, htiB, htmN, htmB⟩ := LoanState.buildTheoretical_tight
    l.periodicPayment rate l.rates.interestRate l.schedule.paymentInterval l.paymentRemaining
    l.broker.managementFeeRate hrate' hir hiv hk hpr hppN hpp0 (by linarith) hmgmt
  obtain ⟨-, htpoeq⟩ := LoanState.buildTheoretical_parts _ _ _ _ ts hpr hts
  have habstp : |ts.principalOutstanding.toRat| ≤ 49 / 10 * B := by rw [abs_of_nonneg htp0]; exact htpB
  obtain ⟨dP, hdP, hdPN, hdPl⟩ := Number.reamSub l.principalOutstanding ts.principalOutstanding T (49 / 10 * B)
    l.wf.principalOutstanding_norm htpN habsP habstp (by linarith)
  obtain ⟨dI, hdI, hdIN, hdIl⟩ := Number.reamSub i ts.interestDue T (49 / 10 * B) hiN htiN habsI htiB
    (by linarith)
  obtain ⟨dM, hdM, hdMN, hdMl⟩ := Number.reamSub l.managementFeeOutstanding ts.managementFeeDue T (49 / 10 * B)
    l.wf.managementFeeOutstanding_norm htmN habsM htmB (by linarith)
  have hdeltas : LoanState.calculateDeltas
      ⟨l.totalValueOutstanding, l.principalOutstanding, i, l.managementFeeOutstanding⟩ ts =
        .ok ⟨dP, dI, dM⟩ := by
    unfold LoanState.calculateDeltas
    simp only [hdP, hdI, hdM, bind, Except.bind, pure, Except.pure]

  -- the reduced principal, at most the theoretical one
  have habspd : |opc.principalDelta.toRat| ≤ T + 1 := by rw [abs_of_nonneg hpd0.le]; exact hpdle
  obtain ⟨x, hx, hxN, -⟩ := Number.reamSub ts.principalOutstanding opc.principalDelta (49 / 10 * B) (T + 1)
    htpN hpdN habstp habspd (by linarith)
  have hxle : x.toRat ≤ ts.principalOutstanding.toRat :=
    (Number.operator_sub_rounded_to_nearest _ _ _ htpN hpdN hx).le_of_ge (Or.inl rfl) _ htpN (by linarith)
  have hrpN : (Number.max x Number.zero).isNormalized := Number.max_isNormalized hxN Number.zero_isNormalized
  obtain ⟨hrp0, hrple⟩ : 0 ≤ (Number.max x Number.zero).toRat ∧
      (Number.max x Number.zero).toRat ≤ ts.principalOutstanding.toRat := by
    unfold Number.max
    by_cases hlt : x.operator_lt Number.zero = true
    · rw [if_pos hlt, Number.toRat_zero]; exact ⟨le_rfl, htp0⟩
    · rw [if_neg hlt]
      have := mt (Number.operator_lt_iff x Number.zero hxN Number.zero_isNormalized).mpr hlt
      rw [Number.toRat_zero] at this
      exact ⟨by linarith, hxle⟩

  -- the re-amortized loan values: the new payments are at most the old ones
  have hvalue : ∀ pp' : Number, loanPeriodicPayment (Number.max x Number.zero) rate l.paymentRemaining = .ok pp' →
      pp'.toRat * l.paymentRemaining.toNat ≤ B + 1 := by
    intro pp' hpp'
    have hle := loanPeriodicPayment_le_of_principal_le l.periodicPayment rate _ l.paymentRemaining _ pp' hppN hpp0
      hrN hr0 hrpN hrp0 htpoeq hrple hpp'
    calc pp'.toRat * l.paymentRemaining.toNat ≤ l.periodicPayment.toRat * (1 + ε) ^ 2 * l.paymentRemaining.toNat := by
          gcongr
      _ = B * (1 + ε) ^ 2 := by rw [hBdef]; ring
      _ ≤ B * (1 + 1 / 10 ^ 17) := by gcongr
      _ ≤ B + 1 := by nlinarith
  obtain ⟨props, hprops, hsz, hppeq⟩ := computeLoanPropertiesFromPeriodicRate_computes (Number.max x Number.zero) rate
    l.rates.interestRate l.schedule.paymentInterval l.paymentRemaining l.broker.managementFeeRate
    l.broker.numericType l.loanScale hrate' hrpN hrp0 (by linarith) hir hiv hpr hk hmgmt hasset ⟨hlo, hs0⟩
    (fun hint => by have := hmaxge hint; linarith) (B + 1) (by linarith)
    (fun hint => by have := hmaxge hint; linarith) hvalue
  have hpp'N := hsz.periodicPayment_norm
  have hpp'0 := hsz.periodicPayment_nonneg
  have hB' : (l.paymentRemaining.toNat : ℚ) * props.periodicPayment.toRat ≤ B + 1 := by
    rw [mul_comm]; exact hvalue _ hppeq

  -- the theoretical state of the new payment, with the differences added back
  obtain ⟨ts', hts', htp'N, htp'0, htp'B, hti'N, hti'B, htm'N, htm'B⟩ := LoanState.buildTheoretical_tight
    props.periodicPayment rate l.rates.interestRate l.schedule.paymentInterval l.paymentRemaining
    l.broker.managementFeeRate hrate' hir hiv hk hpr hpp'N hpp'0 (by linarith) hmgmt
  obtain ⟨hvo', -⟩ := LoanState.buildTheoretical_parts _ _ _ _ ts' hpr hts'
  have hNN := Number.ofInt64_isNormalized l.paymentRemaining.toInt64
  have hNv := Number.ofInt64_count l.paymentRemaining
  have hvo'N := Number.operator_mul_isNormalized _ _ _ _ hpp'N hNN hvo'
  have hvo'l : |ts'.valueOutstanding.toRat| ≤ B + 2 := by
    have h1 := (Number.mul_near _ _ _ hpp'N hNN hvo').abs_le
    have hq0 : 0 ≤ props.periodicPayment.toRat * l.paymentRemaining.toNat := mul_nonneg hpp'0 (by positivity)
    have hqle : props.periodicPayment.toRat * l.paymentRemaining.toNat ≤ B + 1 := by
      rw [mul_comm]; exact hB'
    rw [hNv, abs_of_nonneg hq0] at h1
    have h2 : props.periodicPayment.toRat * l.paymentRemaining.toNat * ε ≤ 1 := by
      calc props.periodicPayment.toRat * l.paymentRemaining.toNat * ε ≤ 10 ^ 18 * (1 / 10 ^ 18) := by
            gcongr
            linarith
        _ = 1 := by norm_num
    linarith
  have habstp' : |ts'.principalOutstanding.toRat| ≤ 49 / 10 * (B + 1) := by
    rw [abs_of_nonneg htp'0]; linarith
  have hti'B' : |ts'.interestDue.toRat| ≤ 49 / 10 * (B + 1) := by linarith
  have htm'B' : |ts'.managementFeeDue.toRat| ≤ 49 / 10 * (B + 1) := by linarith
  obtain ⟨t1, ht1, ht1N, ht1l⟩ := Number.reamAdd dP dI (T + 49 / 10 * B + 1) (T + 49 / 10 * B + 1) hdPN hdIN hdPl
    hdIl (by linarith)
  obtain ⟨tot, htot, htotN, htotl⟩ := Number.reamAdd t1 dM (2 * T + 98 / 10 * B + 3) (T + 49 / 10 * B + 1) ht1N
    hdMN (by linarith) hdMl (by linarith)
  obtain ⟨vo2, hvo2, hvo2N, hvo2l⟩ := Number.reamAdd ts'.valueOutstanding tot (B + 2) (3 * T + 147 / 10 * B + 5)
    hvo'N htotN hvo'l (by linarith) (by linarith)
  obtain ⟨po2, hpo2, -, -⟩ := Number.reamAdd ts'.principalOutstanding dP (49 / 10 * (B + 1))
    (T + 49 / 10 * B + 1) htp'N hdPN habstp' hdPl (by linarith)
  obtain ⟨i2, hi2, -, -⟩ := Number.reamAdd ts'.interestDue dI (49 / 10 * (B + 1)) (T + 49 / 10 * B + 1) hti'N hdIN
    hti'B' hdIl (by linarith)
  obtain ⟨m2, hm2, -, -⟩ := Number.reamAdd ts'.managementFeeDue dM (49 / 10 * (B + 1)) (T + 49 / 10 * B + 1)
    htm'N hdMN htm'B' hdMl (by linarith)
  have hadd : ts'.addDeltas ⟨dP, dI, dM⟩ = .ok ⟨vo2, po2, i2, m2⟩ := by
    unfold LoanState.addDeltas LoanStateDeltas.total
    simp only [ht1, htot, hvo2, hpo2, hi2, hm2, bind, Except.bind, pure, Except.pure]

  -- principal and fee pinned to the values after the overpayment
  obtain ⟨pin, hpin, hpinN, hpinl⟩ := Number.reamSub l.principalOutstanding opc.principalDelta T (T + 1)
    l.wf.principalOutstanding_norm hpdN habsP habspd (by linarith)
  obtain ⟨gi, hgi, hgiN, hgil⟩ := Number.reamSub vo2 pin (157 / 10 * B + 3 * T + 8) (2 * T + 2) hvo2N hpinN
    (by linarith) (by linarith) (by linarith)
  have hgil' : |gi.toRat| ≤ 157 / 10 * B + 5 * T + 11 := by linarith
  obtain ⟨pm, hpm, hpmN, hpml⟩ := tenthBipsOfValue_ok_of_abs gi l.broker.managementFeeRate.toTenthBips32 hgiN
    (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 190 by norm_num])
  have hpml' : |pm.toRat| ≤ |gi.toRat| / 10 + 1 := by
    have hq := mgmt_toNat_le l.broker.managementFeeRate hmgmt
    have hg0 := abs_nonneg gi.toRat
    calc |pm.toRat| ≤ |gi.toRat| * l.broker.managementFeeRate.toTenthBips32.toNat / 100000 * (1 + ε) ^ 2 := hpml
      _ ≤ |gi.toRat| * 10000 / 100000 * (1 + 1 / 10 ^ 17) := by gcongr
      _ ≤ |gi.toRat| / 10 + 1 := by nlinarith
  obtain ⟨id3, hid3, hid3N, hid3l⟩ := Number.reamSub gi pm (157 / 10 * B + 5 * T + 11)
    ((157 / 10 * B + 5 * T + 11) / 10 + 1) hgiN hpmN hgil' (by linarith) (by linarith)
  have hbuild3 : LoanState.build vo2 pin pm = .ok ⟨vo2, pin, id3, pm⟩ := by
    unfold LoanState.build
    rw [hgi, ok_bind, hid3, ok_bind]
    rfl

  -- the committed state: each value rounded to the asset and kept under the value before
  obtain ⟨po, hpo, hpoN, hpo0, hpole, -⟩ := roundAndClamp_computes pin l.principalOutstanding .upward
    l.broker.numericType l.loanScale hasset hs hpinN (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 90 by norm_num])
    (fun hint => by have := hmaxge hint; linarith) hP0 gP
  obtain ⟨int3, hint3, hint3N, hint3l⟩ := Number.reamAdd id3 pm
    (157 / 10 * B + 5 * T + 11 + ((157 / 10 * B + 5 * T + 11) / 10 + 1) + 1)
    ((157 / 10 * B + 5 * T + 11) / 10 + 1) hid3N hpmN hid3l (by linarith) (by linarith)
  have hgross3 : (⟨vo2, pin, id3, pm⟩ : LoanState).grossInterestOutstanding = .ok int3 := hint3
  have habspo : |po.toRat| ≤ T := by rw [abs_of_nonneg hpo0]; linarith
  obtain ⟨tvo, htvo, htvoN, htvol⟩ := Number.reamAdd po int3 T
    (157 / 10 * B + 5 * T + 11 + ((157 / 10 * B + 5 * T + 11) / 10 + 1) + 1 +
      ((157 / 10 * B + 5 * T + 11) / 10 + 1) + 1) hpoN hint3N habspo hint3l (by linarith)
  have htvol' : |tvo.toRat| ≤ 19 * B + 7 * T + 20 := by linarith
  obtain ⟨tvo', htvo', htvo'N, htvo'0, htvo'le, htvo'G⟩ := roundAndClamp_computes tvo l.totalValueOutstanding
    .upward l.broker.numericType l.loanScale hasset hs htvoN
    (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 90 by norm_num])
    (fun hint => by
      rcases hasset with h | h | h
      · rw [h] at hint; cases hint
      · have hmaxN : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
        rw [h, hmaxN]
        linarith [hxrp h]
      · have hmaxM : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
        rw [h, hmaxM]
        linarith) hT0 gT
  obtain ⟨mfo, hmfo, hmfoN, hmfo0, hmfole, -⟩ := roundAndClamp_computes pm l.managementFeeOutstanding
    .to_nearest l.broker.numericType l.loanScale hasset hs hpmN
    (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 90 by norm_num])
    (fun hint => by have := hmaxge hint; linarith) hM0 gM
  have habst' : |tvo'.toRat| ≤ T := by rw [abs_of_nonneg htvo'0]; exact htvo'le
  have habsm' : |mfo.toRat| ≤ T := by rw [abs_of_nonneg hmfo0]; linarith
  obtain ⟨v4, hv4, hv4N, hv4l⟩ := Number.reamSub tvo' po T T htvo'N hpoN habst' habspo (by linarith)
  obtain ⟨id4, hid4, hid4N, hid4l⟩ := Number.reamSub v4 mfo (T + T + 1) T hv4N hmfoN hv4l habsm' (by linarith)
  have hbuild4 : LoanState.build tvo' po mfo = .ok ⟨tvo', po, id4, mfo⟩ := by
    unfold LoanState.build
    rw [hv4, ok_bind, hid4, ok_bind]
    rfl
  obtain ⟨d4P, hd4P, hd4PN, hd4Pl⟩ := Number.reamSub l.principalOutstanding po T T
    l.wf.principalOutstanding_norm hpoN habsP habspo (by linarith)
  obtain ⟨d4I, hd4I, -, -⟩ := Number.reamSub i id4 T (T + T + 1 + T + 1) hiN hid4N habsI hid4l (by linarith)
  obtain ⟨d4M, hd4M, -, -⟩ := Number.reamSub l.managementFeeOutstanding mfo T T
    l.wf.managementFeeOutstanding_norm hmfoN habsM habsm' (by linarith)
  have hdeltas4 : LoanState.calculateDeltas
      ⟨l.totalValueOutstanding, l.principalOutstanding, i, l.managementFeeOutstanding⟩ ⟨tvo', po, id4, mfo⟩ =
        .ok ⟨d4P, d4I, d4M⟩ := by
    unfold LoanState.calculateDeltas
    simp only [hd4P, hd4I, hd4M, bind, Except.bind, pure, Except.pure]
  obtain ⟨io, hio, -, -⟩ := Number.reamAdd id4 mfo (T + T + 1 + T + 1) T hid4N hmfoN hid4l habsm' (by linarith)
  have hgross4 : (⟨tvo', po, id4, mfo⟩ : LoanState).grossInterestOutstanding = .ok io := hio

  -- the amortization guards on the committed values
  have hp10 : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨k, hk'⟩ := htvo'G.nat htvo'0
  have hk63 : k < 2 ^ 63 := by
    have hlt := (Loan.outstanding_grid l).2.2.2.1
    have : (k : ℚ) * 10 ^ l.loanScale < 2 ^ 63 * 10 ^ l.loanScale := by rw [← hk']; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  have hsz' : ({ props with
      totalValueOutstanding := tvo', principalOutstanding := po, managementFeeOutstanding := mfo,
      loanScale := l.loanScale } : LoanProperties).SetSizes l.broker.numericType :=
    { periodicPayment_norm := hsz.periodicPayment_norm
      periodicPayment_nonneg := hsz.periodicPayment_nonneg
      periodicPayment_lt := hsz.periodicPayment_lt
      periodicPayment_max := hsz.periodicPayment_max
      totalValue_norm := htvo'N
      totalValue_nonneg := htvo'0
      totalValue_units := ⟨k, hk63, hk'⟩
      managementFee_norm := hmfoN
      managementFee_abs := by linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 100 by norm_num]
      loanScale_range := ⟨hlo, le_trans hs0 (by norm_num)⟩
      loanScale_integral := hint0 }
  obtain ⟨g, hg⟩ := LoanProperties.amortizationGuards_computes _ l.broker.numericType hasset hsz' po hpoN
    (by linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 200 by norm_num]) (io.operator_ne Number.zero) l.paymentRemaining
  obtain ⟨fp, hfp, hfpN, hfpl⟩ := Number.reamAdd opc.managementFeeDelta opc.untrackedManagementFee (10 ^ 17)
    (10 ^ 17) hmdN humN hmdl huml (by norm_num)

  unfold Loan.tryOverpayment
  simp only [show l.periodicRate = .ok rate from hrate, hstate, hts, hdeltas, hx, hprops, hts', hadd, hpin, hgi,
    hpm, hbuild3, hpo, hgross3, htvo, htvo', hmfo, hbuild4, hdeltas4, hgross4, hg, hfp, bind, Except.bind, pure,
    Except.pure]
  split_ifs
  all_goals first
    | (refine ⟨_, rfl, fun re h => ?_⟩
       cases h
       done)
    | (refine ⟨_, rfl, fun re h => ?_⟩
       obtain rfl := (Option.some.inj h).symm
       refine ⟨⟨hd4PN, huiN, hfpN⟩, ?_, ?_, ?_⟩
       · show |d4P.toRat| ≤ 10 ^ 18
         linarith
       · show |opc.untrackedInterest.toRat| ≤ 10 ^ 18
         linarith
       · show |fp.toRat| ≤ 10 ^ 18
         linarith)

/-- A loan re-check fails only as not lawful. -/
private lemma RawLoan.to_lawful_error_notLawful {rl : RawLoan} {e : Error} (h : rl.to_lawful = .error e) :
    e = .notLawful := by
  unfold RawLoan.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

set_option maxHeartbeats 800000 in
-- one proof walks the overpayment tail step by step
/-- The overpayment tail after the instalment loop ends in a payment or fails its loan re-check. The loan it starts
from has the loop's room while payments are left, and `hxrp` is the XRP bound of the re-amortization. -/
lemma UnsettledPayment.applyOverpayment_error (q : UnsettledPayment Vault) (amount : Number)
    (hN : amount.isNormalized) (h0 : 0 ≤ amount.toRat) (hamt : amount.toRat < 10 ^ 97)
    (hrep : STAmount.isRounded q.loan.broker.numericType amount = false)
    (hasset : q.loan.broker.numericType = .fractional ∨ q.loan.broker.numericType = .native ∨
      q.loan.broker.numericType = .int64)
    (hlo : -10 ≤ q.loan.loanScale) (hs0 : q.loan.loanScale ≤ 0)
    (hint0 : q.loan.broker.numericType.isIntegral = true → q.loan.loanScale = 0)
    (hTle : q.loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1)
    (hroom : q.loan.paymentRemaining ≠ 0 → q.loan.PayRoom)
    (hB : q.loan.paymentRemaining ≠ 0 →
      (q.loan.paymentRemaining.toNat : ℚ) * q.loan.periodicPayment.toRat ≤ 2 * (10 ^ 16 + 1))
    (htN : q.totalPaid.isNormalized) (ht0 : 0 ≤ q.totalPaid.toRat) (hqN : q.amounts.Norm)
    (hqP : |q.amounts.principalPaid.toRat| ≤ 10 ^ 102) (hqI : |q.amounts.interestPaid.toRat| ≤ 10 ^ 102)
    (hqF : |q.amounts.feePaid.toRat| ≤ 10 ^ 102)
    (hxrp : q.loan.broker.numericType = .native → q.loan.paymentRemaining ≠ 0 →
      20 * ((q.loan.paymentRemaining.toNat : ℚ) * q.loan.periodicPayment.toRat) +
        16 * q.loan.totalValueOutstanding.toRat + 100 ≤ 10 ^ 17)
    (e : Error) (herr : UnsettledPayment.applyOverpayment q amount = .error e) : e = .notLawful := by
  have hs : -81 ≤ q.loan.loanScale ∧ q.loan.loanScale ≤ 0 := ⟨by omega, hs0⟩
  have hmaxge := NumericType.maxValue_ge q.loan.broker.numericType hasset
  have hTN := q.loan.wf.totalValueOutstanding_norm
  have hT0 : 0 ≤ q.loan.totalValueOutstanding.toRat := q.loan.exact.totalValueOutstanding_nonneg
  obtain ⟨c, hc⟩ := STAmount.roundToNumericType_towards_zero_ok _ amount _ hN h0 hrep hasset hs
  have hcN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hc
  obtain ⟨hc0, hcle⟩ := STAmount.roundToNumericType_towards_zero_some_le _ amount c _ hN h0
    ⟨by omega, by omega⟩ hc
  unfold UnsettledPayment.applyOverpayment at herr
  simp only [hc, bind, Except.bind, pure, Except.pure] at herr
  split at herr
  · cases herr
  rename_i hguard
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hguard
  obtain ⟨⟨⟨-, hpr⟩, hlt⟩, -⟩ := hguard
  have htc : q.totalPaid.toRat < c.toRat := (Number.operator_lt_iff _ _ htN hcN).mp hlt

  -- what is left of the amount, capped at the value owed and rounded down
  obtain ⟨un, hun⟩ := Number.operator_sub_ok_of_abs c q.totalPaid .to_nearest hcN htN
    (by rw [abs_of_nonneg hc0]; linarith [show (10 : ℚ) ^ 97 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg ht0]; linarith [show (10 : ℚ) ^ 97 < 10 ^ 200 by norm_num])
  have hunN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hcN htN hun
  have hun0 : 0 ≤ un.toRat :=
    rn_nonneg (Number.operator_sub_rounded_to_nearest _ _ _ hcN htN hun) (by linarith)
  obtain ⟨hcapv, hcapN⟩ := Number.min_toRat un q.loan.totalValueOutstanding hunN hTN
  have hcap0 : 0 ≤ (Number.min un q.loan.totalValueOutstanding).toRat := by rw [hcapv]; exact le_min hun0 hT0
  have hcaple : (Number.min un q.loan.totalValueOutstanding).toRat ≤ q.loan.totalValueOutstanding.toRat := by
    rw [hcapv]; exact min_le_right _ _
  obtain ⟨ov, hov, hovN, -⟩ := STAmount.roundToNumericType_asset_ok _ (Number.min un q.loan.totalValueOutstanding)
    .downward q.loan.loanScale hasset hs hcapN
    (by rw [abs_of_nonneg hcap0]; linarith [show (10 : ℚ) ^ 16 + 1 < 10 ^ 90 by norm_num])
    (fun hint => by rw [abs_of_nonneg hcap0]; linarith [hmaxge hint])
  have hov0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hcapN hcap0 (Or.inr (Or.inr rfl))
    ⟨hs.1, by omega⟩ hov
  have hovle := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hcapN hcap0 ⟨hs.1, by omega⟩ hov
  simp only [hun, hov] at herr
  split at herr
  · cases herr

  -- the split of the overpayment
  obtain ⟨opc, hopc, hpdN, hpdle, -, hmdN, hmdl, huiN, huil, humN, huml⟩ :=
    Loan.overpaymentComponents_computes q.loan ov hovN hov0 (by linarith) hasset hs
  simp only [hopc] at herr
  split at herr
  · cases herr
  rename_i hpdg
  have hpd0 : 0 < opc.principalDelta.toRat := by
    have hgt : opc.principalDelta.operator_gt Number.zero = true := by simpa using hpdg
    have := (Number.operator_lt_iff Number.zero opc.principalDelta Number.zero_isNormalized hpdN).mp hgt
    rwa [Number.toRat_zero] at this

  -- the re-amortization
  obtain ⟨r, hr, hre⟩ := Loan.tryOverpayment_computes_room q.loan (hroom hpr) hpr hlo hint0 (hB hpr) opc hpdN hpd0
    (by linarith) hmdN hmdl huiN huil humN huml (fun hn => hxrp hn hpr)
  simp only [hr] at herr
  cases r with
  | none => cases herr
  | some re =>
    obtain ⟨hreN, hreP, hreI, hreF⟩ := hre re rfl
    have h200 : (10 : ℚ) ^ 102 < 10 ^ 200 := by norm_num
    obtain ⟨a1, ha1⟩ := Number.operator_add_ok_of_abs q.amounts.principalPaid re.amounts.principalPaid .to_nearest
      hqN.1 hreN.1 (by linarith) (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    obtain ⟨a2, ha2⟩ := Number.operator_add_ok_of_abs q.amounts.interestPaid re.amounts.interestPaid .to_nearest
      hqN.2.1 hreN.2.1 (by linarith) (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    obtain ⟨a3, ha3⟩ := Number.operator_add_ok_of_abs q.amounts.feePaid re.amounts.feePaid .to_nearest
      hqN.2.2 hreN.2.2 (by linarith) (by linarith [show (10 : ℚ) ^ 18 < 10 ^ 200 by norm_num])
    simp only [PaymentAmounts.add, ha1, ha2, ha3, bind, Except.bind, pure, Except.pure] at herr
    split at herr
    · rename_i ev hev
      obtain rfl : ev = e := by injection herr
      exact RawLoan.to_lawful_error_notLawful hev
    · cases herr

end XRPL.Model.Lending
