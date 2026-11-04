import XRPL.Properties.Lending.Loan.Common.SetScale

/-! # What a new loan moves in the vault and the broker

The principal leaves AssetsAvailable for AssetsDeployed and DebtTotal, a pending loan also reserves it,
an active loan adds its interest to YieldUnrealized. On the base grid each update is exact. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- AssetsAvailable, AssetsDeployed, AssetsReserved, YieldUnrealized and the broker's DebtTotal are whole numbers
of base units below `10^16`, the amounts an STAmount holds at the base scale. -/
structure Loan.CreateGrid (broker : LoanBroker) (v : Vault) : Prop where
  assetsAvailable : Number.AtExponent v.assetsAvailable.toRat v.baseExponent (10 ^ 16)
  assetsDeployed : Number.AtExponent v.assetsDeployed.toRat v.baseExponent (10 ^ 16)
  assetsReserved : Number.AtExponent v.assetsReserved.toRat v.baseExponent (10 ^ 16)
  yieldUnrealized : Number.AtExponent v.yieldUnrealized.toRat v.baseExponent (10 ^ 16)
  debtTotal : Number.AtExponent broker.debtTotal.toRat v.baseExponent (10 ^ 16)

/-- A successful vault update computed its five new balances and wrote them. -/
private lemma Vault.adjustBalances_ok_sums (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    ∃ aa' ad' lu' ar' yu', Vault.AdjustSums v c aa' ad' lu' ar' yu' ∧
      raw = { v.toRawVault with
        assetsAvailable := aa'
        assetsDeployed := ad'
        assetsReserved := ar'
        lossUnrealized := lu'
        yieldUnrealized := yu' } := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  exact ⟨_, _, _, _, _, ⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, rfl⟩

/-- What a successful create moves. The vault's new balances are the old ones updated by the
create's change, the new DebtTotal is the old one plus PrincipalRequested, and the loan is the built one. -/
lemma Loan.create_pool_sums (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ props loanState debtTotal' principal' broker' aa' ad' lu' ar' yu',
      Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal' ∧
      STAmount.roundToNumericType broker.numericType principal .to_nearest = .ok principal' ∧
      Vault.AdjustSums v (Loan.createChange principal principal' loanState.interestDue pending)
        aa' ad' lu' ar' yu' ∧
      r.pool'.toRawVault = { v.toRawVault with
        assetsAvailable := aa'
        assetsDeployed := ad'
        assetsReserved := ar'
        lossUnrealized := lu'
        yieldUnrealized := yu' } ∧
      r.loan'.toRawLoan = RawLoan.build props rates fees schedule broker' allowsOverpayment pending ∧
      broker'.toRawLoanBroker =
        { broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 } := by
  obtain ⟨props, loanState, debtTotal', principal', broker', hchecks, hround, hpool, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ r.pool' hpool
  obtain ⟨aa', ad', lu', ar', yu', hsums, hraw⟩ := Vault.adjustBalances_ok_sums v _ raw hadj
  refine ⟨props, loanState, debtTotal', principal', broker', aa', ad', lu', ar', yu', hchecks, hround, hsums, ?_,
    (RawLoan.to_lawful_ok hloan).1, (RawLoanBroker.to_lawful_ok hbroker).1⟩
  rw [(RawVault.to_lawful_ok hv').1, hraw]

/-- The exact new balances of a create. On the base grid the principal moves from AssetsAvailable to
AssetsDeployed and DebtTotal, a pending loan reserves it, an active loan adds its interest to the yield. -/
lemma Loan.create_balances (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat - principal.toRat ∧
      r.pool'.assetsDeployed.toRat = v.assetsDeployed.toRat + principal.toRat ∧
      r.pool'.lossUnrealized.toRat = v.lossUnrealized.toRat ∧
      r.pool'.assetsReserved.toRat = v.assetsReserved.toRat + (if pending then principal.toRat else 0) ∧
      r.pool'.yieldUnrealized.toRat =
        v.yieldUnrealized.toRat + (if pending then 0 else r.loan'.toExact.interestDue) ∧
      r.loan'.broker.debtTotal.toRat = broker.debtTotal.toRat + principal.toRat := by
  have hPT := Loan.create_principal_le_value broker v principal rates fees schedule allowsOverpayment pending r hp hst
    hok
  obtain ⟨props, loanState, debtTotal', principal', broker', aa', ad', lu', ar', yu', hchecks, hround, hsums, hpool,
    hl, hb⟩ := Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, amount, amountSt, ti, -, -, -, -, -, -, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hDT : r.loan'.broker.debtTotal = debtTotal' := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.debtTotal = _; rw [hl]
    show broker'.toRawLoanBroker.debtTotal = _; rw [hb]
  set b := v.baseExponent with hbdef
  have hbase := Vault.baseExponent_scale_range v
  have hb10 : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  -- PrincipalRequested is `j` units of the LoanScale and `jb` base units, no more than AssetsAvailable
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨-, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  have hbls := (computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2).1
  set ls := props.loanScale with hlsdef
  have hls10 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _
  have hsl : minExponent + 18 ≤ ls ∧ ls ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal ls hp hpos.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
  set jb := j * 10 ^ (ls - b).toNat with hjbdef
  have hjb : principal.toRat = (jb : ℚ) * 10 ^ b := by rw [hj]; exact grid_point_fine j ls b hbls
  have hjjb : j ≤ jb := Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  obtain ⟨a, ha, hav⟩ := hgrid.assetsAvailable
  obtain ⟨d, hd, hdv⟩ := hgrid.assetsDeployed
  obtain ⟨ar, har, harv⟩ := hgrid.assetsReserved
  obtain ⟨y, hy, hyv⟩ := hgrid.yieldUnrealized
  obtain ⟨dt, hdt, hdtv⟩ := hgrid.debtTotal
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h1 := hchecks.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)
  have hja : jb ≤ a := by
    have : (jb : ℚ) * 10 ^ b ≤ (a : ℚ) * 10 ^ b := by rw [← hjb, ← hav]; exact hfunds
    exact_mod_cast le_of_mul_le_mul_right this hb10
  have hpN' := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have hp' : principal'.toRat = principal.toRat :=
    STAmount.roundToNumericType_of_isRounded_false _ _ _ hp hst hround
  -- AssetsAvailable: the principal leaves, and the 16-digit result stores the difference exactly
  have haa : aa'.toRat = v.assetsAvailable.toRat - principal.toRat := by
    obtain ⟨aa, hadd, hrnd⟩ := hsums.cash
    have hcash : (Loan.createChange principal principal' loanState.interestDue pending).cash =
        principal'.operator_neg := rfl
    rw [hcash] at hadd
    have haav := Number.operator_add_toRat_of_grid _ _ aa a (-(jb : ℤ)) b v.wf.assetsAvailable_norm
      (Number.operator_neg_isNormalized _ hpN') (by rw [hav]; norm_cast)
      (by rw [Number.toRat_neg, hp', hjb]; push_cast; ring) (by omega) hs hadd
    have haaN : aa.isNormalized := by
      have := Number.operator_neg_isNormalized _ hpN'
      exact operator_add_isNormalized_to_nearest_sz _ _ aa v.wf.assetsAvailable_norm this hadd
    have haav' : aa.toRat = ((a - jb : ℕ) : ℚ) * 10 ^ b := by
      rw [haav]; push_cast [Nat.cast_sub hja]; ring
    have haa0 : 0 ≤ aa.toRat := by rw [haav']; positivity
    have : aa'.toRat = aa.toRat := by
      cases hvt : v.numericType with
      | integral mv mo ms msh =>
        rw [hvt] at hrnd
        have hb0 : b = 0 := Vault.baseExponent_integral v (by rw [hvt]; rfl)
        rw [hb0, zpow_zero, mul_one] at haav'
        obtain ⟨hgf, -⟩ := STAmount.roundToNumericType_int_grid _ rfl aa _ .to_nearest _ haaN haa0 (Or.inl rfl) hrnd
        have h1 := hgf.lower (a - jb) (by rw [haav', zpow_zero, mul_one])
        have h2 := hgf.upper (a - jb) (by rw [haav', zpow_zero, mul_one])
        rw [zpow_zero, mul_one] at h1 h2
        rw [haav']; linarith
      | fractional =>
        rw [hvt] at hrnd
        have hrep : STAmount.isRounded .fractional aa = false :=
          (STAmount.isRounded_eq_false_iff _ aa haaN haa0).mpr (by
            rw [haav']; exact STAmount.representable_fractional_of_units _ b (by omega) (by omega) (by omega))
        exact STAmount.roundToNumericType_of_isRounded_false _ _ _ haaN hrep hrnd
    rw [this, haav', hav, hjb]; push_cast [Nat.cast_sub hja]; ring
  have had : ad'.toRat = v.assetsDeployed.toRat + principal.toRat := by
    have h := Number.operator_add_toRat_of_grid _ _ ad' d jb b v.wf.assetsDeployed_norm hp
      (by rw [hdv]; norm_cast) (by rw [hjb]; norm_cast) (by omega) hs hsums.deployed
    rw [h, hdv, hjb]; push_cast; ring
  have hlu : lu' = v.lossUnrealized := by
    have h := hsums.loss
    rw [show (Loan.createChange principal principal' loanState.interestDue pending).loss = Number.zero from rfl,
      Number.operator_add_zero_right, Except.ok.injEq] at h
    exact h.symm
  have har' : ar'.toRat = v.assetsReserved.toRat + (if pending then principal.toRat else 0) := by
    have h := hsums.reserved
    cases pending with
    | true =>
      have h' : v.assetsReserved.operator_add principal' .to_nearest = .ok ar' := h
      have := Number.operator_add_toRat_of_grid _ _ ar' ar jb b v.wf.assetsReserved_norm hpN'
        (by rw [harv]; norm_cast) (by rw [hp', hjb]; norm_cast) (by omega) hs h'
      rw [this, harv, hjb, if_pos rfl]; push_cast; ring
    | false =>
      have h' : v.assetsReserved.operator_add Number.zero .to_nearest = .ok ar' := h
      rw [Number.operator_add_zero_right, Except.ok.injEq] at h'
      rw [← h', if_neg Bool.false_ne_true, add_zero]
  have hdebt : debtTotal'.toRat = broker.debtTotal.toRat + principal.toRat := by
    have h := Number.operator_add_toRat_of_grid _ _ debtTotal' dt jb b broker.wf.debtTotal_norm hp
      (by rw [hdtv]; norm_cast) (by rw [hjb]; norm_cast) (by omega) hs hchecks.debt
    rw [h, hdtv, hjb]; push_cast; ring
  -- the interest of the new loan, on the LoanScale grid
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  have hmfN : props.managementFeeOutstanding.isNormalized := hMF ▸ hwf.managementFeeOutstanding_norm
  obtain ⟨aT, haT, haTv⟩ := hexg.totalValueOutstanding_atExponent
  obtain ⟨mm, hmm, hmmv⟩ := hexg.managementFeeOutstanding_atExponent
  simp only [RawLoan.toExact] at haT haTv hmm hmmv
  rw [hTV, hLS] at haTv
  rw [hMF, hLS] at hmmv
  have hbound := NumericType.mantissaBound_le r.loan'.broker.numericType
  have hjaT : j ≤ aT := by
    have : (j : ℚ) * 10 ^ ls ≤ (aT : ℚ) * 10 ^ ls := by
      rw [← hj, ← haTv]; simp only [RawLoan.toExact] at hPT; rw [hTV] at hPT; exact hPT
    exact_mod_cast le_of_mul_le_mul_right this hls10
  have hiv := LoanState.build_interestDue_grid _ _ _ ls aT j mm loanState htvN hp hmfN haTv hj hmmv (by omega) hjaT
    (by omega) hsl hchecks.state
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest props.loanScale hp
      hpos.le (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj (fun _ => by omega) hpo
  -- the fee is at most the interest `aT - j`, so the interest is `aT - j - mm ≥ 0` units
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j ls htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hsl hti]
    push_cast [Nat.cast_sub hjaT]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := by
    intro hf
    rw [hNT, hf] at haT
    exact lt_of_le_of_lt (Nat.sub_le _ _) haT
  obtain ⟨-, hmf_hi, -, -⟩ := computeManagementFee_bounds broker.numericType ti _ (aT - j)
    broker.managementFeeRate ls (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) htiv
    (by omega) hR10 ⟨by omega, hhi⟩ hint hfr hmfo
  have hmmK : mm ≤ aT - j := by
    have hC : ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 ≤ aT - j := by
      have : (aT - j) * broker.managementFeeRate.toNat ≤ (aT - j) * 10000 := Nat.mul_le_mul_left _ hR10
      omega
    have h1 : (mm : ℚ) * 10 ^ ls ≤
        ((((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) : ℚ) * 10 ^ ls := by
      rw [← hmmv]; exact hmf_hi
    have h2 : mm ≤ ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 := by
      exact_mod_cast le_of_mul_le_mul_right h1 hls10
    omega
  have h10 : (10 : ℚ) ^ ls = (10 : ℚ) ^ (ls - b).toNat * 10 ^ b := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
      sub_add_cancel]
  set ib : ℤ := ((aT : ℤ) - j - mm) * 10 ^ (ls - b).toNat with hibdef
  have hib0 : 0 ≤ ib := mul_nonneg (by omega) (by positivity)
  have hiunits : loanState.interestDue.toRat = (ib : ℚ) * 10 ^ b := by
    rw [hiv.2, haTv, hj, hmmv, hibdef, h10]; push_cast; ring
  have hiD : r.loan'.toExact.interestDue = loanState.interestDue.toRat := by
    show r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat -
      r.loan'.managementFeeOutstanding.toRat = _
    rw [hTV, hPO, hMF, hpov, hiv.2]
  -- YieldUnrealized: an active loan adds its interest, which stays inside the Open limit
  have hyu : yu'.toRat = v.yieldUnrealized.toRat + (if pending then 0 else r.loan'.toExact.interestDue) := by
    have h := hsums.yield
    cases pending with
    | true =>
      have h' : v.yieldUnrealized.operator_add Number.zero .to_nearest = .ok yu' := h
      rw [Number.operator_add_zero_right, Except.ok.injEq] at h'
      rw [← h', if_pos rfl, add_zero]
    | false =>
      have h' : v.yieldUnrealized.operator_add loanState.interestDue .to_nearest = .ok yu' := h
      have hopen := (Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiv.1 hchecks.open_zone).2.1
      have hlt : (y : ℤ) + ib < 2 ^ 63 := by
        have hsum : v.yieldUnrealized.toRat + loanState.interestDue.toRat =
            (((y : ℤ) + ib : ℤ) : ℚ) * 10 ^ b := by
          rw [hyv, hiunits]; push_cast; ring
        rw [hsum] at hopen
        have h2 : (10 : ℚ) ^ (b - 1) = 10 ^ b / 10 := by
          rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
        rw [h2, show ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * (10 ^ b / 10) = ((9 * 10 ^ 16 + 5 : ℕ) / 10 : ℚ) * 10 ^ b by
          ring] at hopen
        have h3 := lt_of_mul_lt_mul_right hopen hb10.le
        have h4 : (((y : ℤ) + ib : ℤ) : ℚ) < 2 ^ 63 := by
          refine lt_of_lt_of_le h3 ?_; norm_num
        exact_mod_cast h4
      have := Number.operator_add_toRat_of_grid _ _ yu' y ib b v.wf.yieldUnrealized_norm hiv.1
        (by rw [hyv]; norm_cast) hiunits ⟨by omega, hlt⟩ hs h'
      rw [this, if_neg Bool.false_ne_true, hiD, hyv, hiunits]; push_cast; ring
  have hpool' : ∀ f : RawVault → Number, f r.pool'.toRawVault = f { v.toRawVault with
      assetsAvailable := aa', assetsDeployed := ad', assetsReserved := ar', lossUnrealized := lu',
      yieldUnrealized := yu' } := fun f => by rw [hpool]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r.pool'.toRawVault.assetsAvailable.toRat = _; rw [hpool' RawVault.assetsAvailable]; exact haa
  · show r.pool'.toRawVault.assetsDeployed.toRat = _; rw [hpool' RawVault.assetsDeployed]; exact had
  · show r.pool'.toRawVault.lossUnrealized.toRat = _; rw [hpool' RawVault.lossUnrealized]; show lu'.toRat = _
    rw [hlu]
  · show r.pool'.toRawVault.assetsReserved.toRat = _; rw [hpool' RawVault.assetsReserved]; exact har'
  · show r.pool'.toRawVault.yieldUnrealized.toRat = _; rw [hpool' RawVault.yieldUnrealized]; exact hyu
  · rw [hDT]; exact hdebt

/-- Proof body of the AssetsTotal line of `Lending.create_updates`. -/
lemma Loan.create_assetsTotal_unchanged_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.toExact.assetsTotal = v.toExact.assetsTotal ∧
      r.pool'.toExact.lossUnrealized = v.toExact.lossUnrealized := by
  obtain ⟨haa, had, hlu, -, -, -⟩ := Loan.create_balances broker v principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hgrid hok
  refine ⟨?_, hlu⟩
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
    v.assetsAvailable.toRat + v.assetsDeployed.toRat
  rw [haa, had]; ring

/-- Proof body of the PrincipalRequested line of `Lending.create_updates`. -/
lemma Loan.create_principal_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    v.toExact.assetsAvailable - r.pool'.toExact.assetsAvailable = principal.toRat ∧
      r.pool'.toExact.assetsDeployed - v.toExact.assetsDeployed = principal.toRat ∧
      r.loan'.broker.toExact.debtTotal - broker.toExact.debtTotal = principal.toRat ∧
      r.pool'.toExact.assetsReserved - v.toExact.assetsReserved = if pending then principal.toRat else 0 := by
  obtain ⟨haa, had, -, har, -, hdt⟩ := Loan.create_balances broker v principal rates fees schedule
    allowsOverpayment pending r hp hpos hst hgrid hok
  refine ⟨?_, ?_, ?_, ?_⟩
  · show v.assetsAvailable.toRat - r.pool'.assetsAvailable.toRat = _; rw [haa]; ring
  · show r.pool'.assetsDeployed.toRat - v.assetsDeployed.toRat = _; rw [had]; ring
  · show r.loan'.broker.debtTotal.toRat - broker.debtTotal.toRat = _; rw [hdt]; ring
  · show r.pool'.assetsReserved.toRat - v.assetsReserved.toRat = _; rw [har]; ring

/-- A new loan -> YieldUnrealized' = YieldUnrealized + interestDue when it is active, unchanged when it is
pending. -/
lemma Loan.create_yield_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithPool Vault) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.toExact.yieldUnrealized =
      v.toExact.yieldUnrealized + if pending then 0 else r.loan'.toExact.interestDue :=
  (Loan.create_balances broker v principal rates fees schedule allowsOverpayment pending r hp hpos hst hgrid
    hok).2.2.2.2.1

end XRPL.Model.Lending
