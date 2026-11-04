import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Loan.Common.BrokerDebt
import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.SetLawful
import XRPL.Properties.Lending.Loan.Common.SetVault

/-! # What a new loan books in the vault

A new loan was made inside the Open zone, and on the base grid a pending loan adds its principal to
AssetsReserved exactly. An accept or a pending delete takes it out, nothing else changes the pending flag. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- The interest a new loan books, read by the Open-limit check, is at least zero. -/
lemma Loan.create_checkedInterest_nonneg (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (props : LoanProperties) (loanState : LoanState) (debtTotal' : Number) (broker' : LoanBroker)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal')
    (hl : r.loan'.toRawLoan = RawLoan.build props rates fees schedule broker' allowsOverpayment pending)
    (hb : broker'.toRawLoanBroker =
      { broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }) :
    loanState.interestDue.isNormalized ∧ 0 ≤ loanState.interestDue.toRat := by
  have hPT := Loan.create_principal_le_value broker v principal rates fees schedule allowsOverpayment pending r hp hst
    hok
  have hex := r.loan'.exact
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨rate, amount, amountSt, ti, -, -, -, -, -, -, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hbase := Vault.baseExponent_scale_range v
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees schedule props loanState
    debtTotal' hchecks hrange.2
  set ls := props.loanScale with hlsdef
  have hls10 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _
  have hsl : minExponent + 18 ≤ ls ∧ ls ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  -- PrincipalRequested, the total value and the fee are whole numbers of LoanScale units
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal ls hp hpos.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
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
  have haT16 : broker.numericType = .fractional → aT < 10 ^ 16 := by
    intro hf
    rw [hNT, hf] at haT
    exact haT
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := fun hf =>
    lt_of_le_of_lt (Nat.sub_le _ _) (haT16 hf)
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest ls hp hpos.le
      (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj (fun hf => lt_of_le_of_lt hjaT (haT16 hf)) hpo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  -- the interest before the fee is `aT - j` units, and the fee takes at most all of it
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j ls htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hsl hti]
    push_cast [Nat.cast_sub hjaT]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
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
  refine ⟨hiv.1, ?_⟩
  rw [hiv.2, haTv, hj, hmmv]
  have : (j : ℚ) + mm ≤ aT := by exact_mod_cast (by omega : j + mm ≤ aT)
  nlinarith

/-- A new loan was made inside the Open zone. AssetsAvailable plus AssetsDeployed was below the
limit, `9·10^15` base units plus half a unit, and the principal came out of AssetsAvailable. -/
lemma Loan.create_inside_open_zone (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat <
        (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) ∧
      principal.toRat ≤ v.assetsAvailable.toRat := by
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨hiN, hi0⟩ := Loan.create_checkedInterest_nonneg broker v principal rates fees schedule allowsOverpayment
    pending r props loanState debtTotal' broker' hp hpos hst hok hchecks hl hb
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨atot, hat⟩ := Vault.assetsTotal_of_exceedsOpenLimit v _ _ hchecks.open_zone
  have hopen := (Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiN hchecks.open_zone).2.2 atot hat
  refine ⟨?_, ?_⟩
  · -- a sum at the limit would give a total at the limit
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 16 + 5) (v.baseExponent - 1)
      (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
    have hle := Vault.assetsTotal_ge_of_le v atot hat w hw (by rw [hwv]; push_cast at hge ⊢; linarith)
    rw [hwv] at hle
    push_cast at hle hopen
    linarith
  · have h1 := hchecks.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)

/-- What a new loan reserves. On the base grid a pending loan adds PrincipalRequested to AssetsReserved
exactly and an active one keeps it. The loan stores PrincipalRequested and is not impaired. -/
lemma Loan.create_reserved (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.assetsReserved.toRat = v.assetsReserved.toRat + (if pending then principal.toRat else 0) ∧
      v.assetsReserved.toRat + principal.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent ∧
      r.loan'.principalOutstanding.toRat = principal.toRat ∧ r.loan'.isPending = pending ∧
      r.loan'.isImpaired = false := by
  obtain ⟨hzone, hfunds⟩ := Loan.create_inside_open_zone broker v principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hok
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule allowsOverpayment pending r hp hpos
    hst hnt hok
  obtain ⟨props, loanState, debtTotal', principal', broker', aa', ad', lu', ar', yu', hchecks, hround, hsums, hpool,
    hl, -⟩ := Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  set b := v.baseExponent with hbdef
  have hbase := Vault.baseExponent_scale_range v
  have hb10 : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hlsb : props.loanScale = b := by rw [← hLS, hls]
  have hint := (computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2).2
  -- PrincipalRequested is `j` base units, and AssetsReserved plus it stays inside the Open zone
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hpos.le hst
    ⟨by omega, by omega⟩ hint (hchecks.exact principal List.mem_cons_self)
  rw [hlsb] at hj
  obtain ⟨n, hn⟩ := har
  have hARD : v.assetsReserved.toRat ≤ v.assetsDeployed.toRat := v.exact.assetsReserved_le
  have hlt : v.assetsReserved.toRat + principal.toRat < 10 ^ 16 * (10 : ℚ) ^ b := by
    have h2 : (10 : ℚ) ^ (b - 1) = 10 ^ b / 10 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    rw [h2] at hzone
    push_cast at hzone
    nlinarith
  have hnj : n + j < 10 ^ 16 := by
    have : ((n + j : ℕ) : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by
      push_cast; rw [add_mul, ← hn, ← hj]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hb10.le
  have hpN' := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have hp' : principal'.toRat = principal.toRat :=
    STAmount.roundToNumericType_of_isRounded_false _ _ _ hp hst hround
  have har' : ar'.toRat = v.assetsReserved.toRat + (if pending then principal.toRat else 0) := by
    have h := hsums.reserved
    cases pending with
    | true =>
      have h' : v.assetsReserved.operator_add principal' .to_nearest = .ok ar' := h
      have := Number.operator_add_toRat_of_grid _ _ ar' n j b v.wf.assetsReserved_norm hpN'
        (by rw [hn]; norm_cast) (by rw [hp', hj]; norm_cast) ⟨by omega, by omega⟩ hs h'
      rw [this, hn, hj, if_pos rfl]; push_cast; ring
    | false =>
      have h' : v.assetsReserved.operator_add Number.zero .to_nearest = .ok ar' := h
      rw [Number.operator_add_zero_right, Except.ok.injEq] at h'
      rw [← h', if_neg Bool.false_ne_true, add_zero]
  obtain ⟨_, _, _, _, -, -, -, -, -, -, hpo, -, -⟩ := computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest props.loanScale hp
      hpos.le (Or.inl rfl) ⟨by omega, by omega⟩ hint hst j (by rw [hlsb]; exact hj) (fun _ => by omega) hpo
  refine ⟨?_, hlt, by rw [hPO, hpov], ?_, ?_⟩
  · show r.pool'.toRawVault.assetsReserved.toRat = _
    rw [hpool]; exact har'
  · show r.loan'.toRawLoan.isPending = _; rw [hl]; rfl
  · show r.loan'.toRawLoan.isImpaired = _; rw [hl]; rfl

/-- An accept takes PrincipalOutstanding out of AssetsReserved and marks the loan active. -/
lemma Loan.accept_reserved (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) :
    v.assetsReserved.operator_add loan.principalOutstanding.operator_neg .to_nearest = .ok r.pool'.assetsReserved ∧
      r.loan'.isPending = false ∧ r.loan'.principalOutstanding = loan.principalOutstanding ∧
      r.loan'.isImpaired = loan.isImpaired := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
  exact ⟨(Vault.poolAdjust_adjustSums v _ _ ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›).reserved,
    (congrArg RawLoan.isPending hl :), (congrArg RawLoan.principalOutstanding hl :),
    (congrArg RawLoan.isImpaired hl :)⟩

/-- A pending delete returns PrincipalOutstanding, rounded to the asset, out of AssetsReserved. -/
lemma Loan.delete_pending_reserved (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = true) (h : (loan.delete v).run = .ok (.ok r)) :
    ∃ principal', STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal' ∧
      v.assetsReserved.operator_add principal'.operator_neg .to_nearest = .ok r.pool'.assetsReserved := by
  obtain ⟨principal', raw, _, hround, hadj, hv', -, -⟩ := Loan.delete_pending_ok_inv loan v r hp h
  obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  refine ⟨principal', hround, ?_⟩
  rw [show r.pool'.assetsReserved = r.pool'.toRawVault.assetsReserved from rfl,
    (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1, heq]
  exact hs.reserved

/-- Deleting an active loan leaves the vault as it was. -/
lemma Loan.delete_active_vault (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = false) (h : (loan.delete v).run = .ok (.ok r)) : r.pool' = v := by
  simp only [Loan.delete] at h
  rw [hp] at h
  unfold_ter at h
  walk_ok
  rfl

/-- Setting or clearing the impaired flag keeps the pending flag. -/
private lemma Loan.changeImpairment_isPending {α : Type} [AssetPool α] (loan : Loan) (pool : α) (b : Bool)
    (r : LoanWithPool α) (h : (Loan.changeImpairment loan pool b).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok'
  all_goals exact (congrArg RawLoan.isPending (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :)

/-- An impair keeps the pending flag. -/
lemma Loan.manageImpair_isPending (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : r.loan'.isPending = loan.isPending := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_isPending loan v true r ‹_›

/-- An unimpair keeps the pending flag. -/
lemma Loan.manageUnimpair_isPending (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) : r.loan'.isPending = loan.isPending :=
  Loan.changeImpairment_isPending loan v false r h

/-- A default keeps the pending flag. -/
lemma Loan.manageDefault_isPending (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : r.loan'.isPending = loan.isPending := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  show r.loan'.toRawLoan.isPending = _
  rw [hloan]
  rfl

/-- An instalment keeps the pending flag. -/
private lemma Loan.doPayment_isPending (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (h : Loan.doPayment loan pc = .ok loan') : loan'.isPending = loan.isPending := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [(congrArg RawLoan.isPending (RawLoan.to_lawful_ok hl).1 :)]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    rw [(congrArg RawLoan.isPending (RawLoan.to_lawful_ok h).1 :)]

/-- The settlement keeps the pending flag. -/
private lemma Loan.settlePayment_isPending {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amounts : PaymentAmounts)
    (si : Number) (r : LoanWithAmounts α) (h : (Loan.settlePayment loan pool amounts si).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok'
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    rw [(congrArg RawLoan.isPending (RawLoan.to_lawful_ok hl).1 :)]

/-- The scheduled instalments keep the pending flag. -/
private lemma UnsettledPayment.payInstalments_isPending {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      p.loan.isPending = payment.loan.isPending := by
  intro n
  induction n with
  | zero =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [h]
  | succ k ih =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | rfl
      | exact Loan.doPayment_isPending _ _ _ ‹Loan.doPayment _ _ = _›
      | (rename_i hrec
         rw [ih _ _ hrec]
         exact Loan.doPayment_isPending _ _ _ ‹Loan.doPayment _ _ = _›)

/-- The re-amortization keeps the pending flag. -/
private lemma UnsettledPayment.applyOverpayment_isPending {α : Type} (payment p : UnsettledPayment α) (amount : Number)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p) : p.loan.isPending = payment.loan.isPending := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok'
  all_goals first
    | rfl
    | (have hl := ‹RawLoan.to_lawful _ = Except.ok _›
       rw [(congrArg RawLoan.isPending (RawLoan.to_lawful_ok hl).1 :)])

/-- Clearing the impaired flag keeps the pending flag. -/
private lemma Loan.unimpairIfImpaired_isPending {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (r : LoanWithPool α) (h : (Loan.unimpairIfImpaired loan pool).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · simp only [Loan.manageUnimpair, Loan.changeImpairment] at h
    unfold_ter at h
    walk_ok'
    all_goals exact (congrArg RawLoan.isPending (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :)
  · unfold_ter at h
    walk_ok'
    rfl

/-- The scheduled part of a payment keeps the pending flag. -/
private lemma Loan.payScheduledInstalments_isPending {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (p : UnsettledPayment α)
    (h : (Loan.payScheduledInstalments loan pool amount now).run = .ok (.ok p)) :
    p.loan.isPending = loan.isPending := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok'
  all_goals
    have hu := Loan.unimpairIfImpaired_isPending _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    have hi := ‹UnsettledPayment.payInstalments _ _ _ = _›
    rw [UnsettledPayment.payInstalments_isPending amount _ _ _ hi]
    exact hu

/-- A single settled instalment keeps the pending flag. -/
private lemma Loan.paySingleInstalment_isPending {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (pc : PaymentComponents) (amount : Number) (r : LoanWithAmounts α)
    (h : (Loan.paySingleInstalment loan pool pc amount).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok'
  all_goals
    rw [Loan.settlePayment_isPending _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›]
    exact Loan.doPayment_isPending _ _ _ ‹Loan.doPayment _ _ = _›

/-- A payment of any type keeps the pending flag. -/
lemma Loan.pay_isPending (loan : Loan) (v : Vault) (paymentType : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  cases paymentType <;>
    simp only [Loan.pay, Loan.regularPayment, Loan.latePayment, Loan.fullPayment, Loan.overpayment] at h <;>
    unfold_ter at h <;> walk_ok'
  all_goals first
    | (rw [Loan.settlePayment_isPending _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›]
       first
       | exact Loan.payScheduledInstalments_isPending _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
       | (rw [UnsettledPayment.applyOverpayment_isPending _ _ _ ‹UnsettledPayment.applyOverpayment _ _ = _›]
          exact Loan.payScheduledInstalments_isPending _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›))
    | (rw [Loan.paySingleInstalment_isPending _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›]
       exact Loan.unimpairIfImpaired_isPending _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›)

/-- An accept that passed its check was on a pending loan. -/
lemma Loan.canAccept_pending (loan : Loan) (v : Vault) (t : UInt32)
    (h : loan.canAccept v t = .ok .tesSUCCESS) : loan.isPending = true := by
  unfold Loan.canAccept at h
  cases hp : loan.isPending
  · rw [hp] at h; cases h
  · rfl

/-- A management action that passed its check was on an active loan. -/
lemma Loan.canManage_not_pending (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (h : loan.canManage action now = .tesSUCCESS) : loan.isPending = false := by
  unfold Loan.canManage at h
  cases hp : loan.isPending
  · rfl
  · rw [if_pos hp] at h; cases h

/-- A payment that passed its check was on an active loan. -/
lemma Loan.canPay_not_pending (loan : Loan) (paymentType : LoanPaymentType)
    (h : loan.canPay paymentType = .tesSUCCESS) : loan.isPending = false := by
  unfold Loan.canPay at h
  cases hp : loan.isPending
  · rfl
  · rw [if_pos hp] at h; cases h

end XRPL.Model.Lending
