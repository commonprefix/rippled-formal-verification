import XRPL.Properties.Lending.Loan.Common.SetInterest
import XRPL.Properties.Lending.Loan.Common.SetVault
import XRPL.Properties.Protocol.Number.ToRep.ToRep

/-! # How much a new loan owes

The amortization guards fit the rounded periodic payment `n − 1` times below TotalValueOutstanding, and the
Open-limit check of LoanSet keeps a new loan at most `10^16 + 1` LoanScale units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private UInt32.toUInt64_toInt64_toInt from XRPL.Properties.Lending.Loan.Common.SetValue
open private STAmount.isNormalized_of_isRounded_false Loan.create_principal_pos Loan.canCreate_principal_exact
  from XRPL.Properties.Lending.Loan.Common.SetInterest

/-- The amortization guards pass only when the rounded periodic payment fits `n − 1` times below
TotalValueOutstanding. The fourth guard rounds TotalValueOutstanding over that payment up to `n`. -/
lemma LoanProperties.amortizationGuards_room (props : LoanProperties) (principal : Number) (expect : Bool)
    (n : UInt32) (nt : NumericType) (hn : n ≠ 0)
    (h : props.amortizationGuards principal expect n nt = .ok .tesSUCCESS)
    (htv : props.totalValueOutstanding.isNormalized) (hpp : props.periodicPayment.isNormalized)
    (hpp0 : 0 ≤ props.periodicPayment.toRat) (hs : -81 ≤ props.loanScale ∧ props.loanScale ≤ 80) :
    ∃ rp : Number, STAmount.roundToNumericType nt props.periodicPayment .upward (some props.loanScale) = .ok rp ∧
      0 < rp.toRat ∧ ((n.toNat : ℚ) - 1) * rp.toRat < props.totalValueOutstanding.toRat := by
  unfold LoanProperties.amortizationGuards at h
  obtain ⟨ti, -, h⟩ := bind_ok_peel _ _ _ h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  cases hrp : STAmount.roundToNumericType nt props.periodicPayment .upward (some props.loanScale) with
  | error e => rw [hrp] at h; exact absurd h (by simp)
  | ok rp =>
  rw [hrp] at h
  dsimp only at h
  split at h
  · exact absurd h (by decide)
  rename_i hz
  have hrpN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrp
  have hrp_ne : rp.toRat ≠ 0 := by
    intro h0
    apply hz
    have := Number.eq_zero_of_mantissa_zero rp hrpN (Number.toRat_eq_zero_iff.mp h0)
    rw [this]; decide
  have hrp0 : 0 ≤ rp.toRat :=
    STAmount.roundToNumericType_some_nonneg nt _ _ .upward props.loanScale hpp hpp0 (Or.inr (Or.inl rfl)) hs hrp
  have hrp_pos : 0 < rp.toRat := lt_of_le_of_ne hrp0 (Ne.symm hrp_ne)
  refine ⟨rp, rfl, hrp_pos, ?_⟩
  cases hratio : props.totalValueOutstanding.operator_div rp .upward with
  | error e => rw [hratio] at h; exact absurd h (by simp)
  | ok ratio =>
    rw [hratio] at h
    dsimp only at h
    cases hcp : ratio.to_rep .upward with
    | error e => rw [hcp] at h; exact absurd h (by simp)
    | ok cp =>
      rw [hcp] at h
      dsimp only at h
      split at h
      · exact absurd h (by decide)
      rename_i hne
      have hcpn : cp = n.toInt64 := by simpa using hne
      have hratioN := Number.operator_div_isNormalized _ _ _ _ htv hrpN hratio
      have hwithin := to_rep_within_one ratio .upward cp hratioN hcp
      rw [hcpn, UInt32.toUInt64_toInt64_toInt] at hwithin
      have hn1 : (1 : ℚ) ≤ n.toNat := by
        have : n.toNat ≠ 0 := fun h0 => hn (UInt32.toNat_inj.mp (by simpa using h0))
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      have hgt : (n.toNat : ℚ) - 1 < ratio.toRat := by
        have := (abs_lt.mp hwithin).2
        push_cast at this
        linarith
      -- a ratio at most `n − 1` rounds up to at most `n − 1`
      by_contra hle
      push Not at hle
      have hq : props.totalValueOutstanding.toRat / rp.toRat ≤ (n.toNat : ℚ) - 1 := by
        rw [div_le_iff₀ hrp_pos]; exact hle
      have hratio_ne : ratio.mantissa_ ≠ 0 := by
        intro h0
        rw [Number.toRat_eq_zero_of_mantissa_zero _ h0] at hgt
        linarith
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((n.toNat : ℤ) - 1) 0
        (by have := n.toNat_lt; constructor <;> omega) (by unfold minExponent maxExponent; omega)
      have hR := operator_div_rounded_upward _ _ _ htv hrpN hratio hratio_ne
      have := hR.le_of_ge (Or.inr (Or.inl rfl)) w hw (by rw [hwv]; push_cast; simpa using hq)
      rw [hwv] at this
      push_cast at this
      linarith

/-- A loan a LoanSet creates owes at most `10^16 + 1` LoanScale units, below `9·10^15 + 1` of them principal.
PrincipalRequested comes out of AssetsAvailable, the Open limit caps it plus the interest. -/
private lemma Loan.Created.size {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ start.loanScale ∧
      start.principalOutstanding.toRat < (9 * 10 ^ 15 + 1) * 10 ^ start.loanScale := by
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, hcan, hok, rfl⟩ := h
  have hst := Loan.canCreate_principal_exact broker v principal fees _ t₀ twoStep hcan
  have hp := STAmount.isNormalized_of_isRounded_false _ _ hst
  have hpos := Loan.create_principal_pos broker v principal rates fees _ allowsOverpayment twoStep r hp hok
  have hPT := Loan.create_principal_le_value broker v principal rates fees _ allowsOverpayment twoStep r hp hst hok
  obtain ⟨props, loanState, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  obtain ⟨_, _, _, ti, -, -, -, -, -, -, hpo, hti, hmfo⟩ :=
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
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees _ props _
    _ hchecks hrange.2
  set ls := props.loanScale with hlsdef
  have hls10 : (0 : ℚ) < 10 ^ ls := zpow_pos (by norm_num) _
  have hsl : minExponent + 18 ≤ ls ∧ ls ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal ls hp hpos.le hst ⟨by omega, hhi⟩ hint
    (hchecks.exact principal List.mem_cons_self)
  -- the total value is `aT` units, at least the `j` units of principal and below the asset's bound
  have htvN : props.totalValueOutstanding.isNormalized := hTV ▸ hwf.totalValueOutstanding_norm
  have hmfN : props.managementFeeOutstanding.isNormalized := hMF ▸ hwf.managementFeeOutstanding_norm
  obtain ⟨aT, haT, haTv⟩ := hexg.totalValueOutstanding_atExponent
  simp only [RawLoan.toExact] at haT haTv
  rw [hTV, hLS] at haTv
  rw [hNT] at haT
  have hbound := NumericType.mantissaBound_le broker.numericType
  have hjaT : j ≤ aT := by
    have : (j : ℚ) * 10 ^ ls ≤ (aT : ℚ) * 10 ^ ls := by
      rw [← hj, ← haTv]; simp only [RawLoan.toExact] at hPT; rw [hTV] at hPT; exact hPT
    exact_mod_cast le_of_mul_le_mul_right this hls10
  -- the stored principal is PrincipalRequested, so the interest is `aT − j` units
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest ls hp
      hpos.le (Or.inl rfl) ⟨by omega, hhi⟩ hint hst j hj
      (fun hf => by rw [hf] at haT; exact lt_of_le_of_lt hjaT haT) hpo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j ls htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hsl hti]
    push_cast [Nat.cast_sub hjaT]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := by
    intro hf
    rw [hf] at haT
    exact lt_of_le_of_lt (Nat.sub_le _ _) haT
  obtain ⟨-, hmf_hi, -, m, hmv⟩ := computeManagementFee_bounds broker.numericType ti _ (aT - j)
    broker.managementFeeRate ls (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) htiv
    (by omega) hR10 ⟨hlo, hhi⟩ hint hfr hmfo
  -- the fee is at most a tenth of the interest plus one unit
  have hmf10 : props.managementFeeOutstanding.toRat ≤ (((aT - j : ℕ) : ℚ) / 10 + 1) * 10 ^ ls := by
    refine hmf_hi.trans (mul_le_mul_of_nonneg_right ?_ hls10.le)
    have h1 : (((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) ≤
        ((aT - j) * 10000 + 99999) / 100000 :=
      Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ hR10) _)
    have h2 : ((((aT - j) * 10000 + 99999) / 100000 : ℕ) : ℚ) ≤ (((aT - j) * 10000 + 99999 : ℕ) : ℚ) / 100000 :=
      Nat.cast_div_le
    calc ((((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) : ℚ)
        ≤ ((((aT - j) * 10000 + 99999) / 100000 : ℕ) : ℚ) := by exact_mod_cast h1
      _ ≤ (((aT - j) * 10000 + 99999 : ℕ) : ℚ) / 100000 := h2
      _ ≤ ((aT - j : ℕ) : ℚ) / 10 + 1 := by push_cast; linarith
  -- the interest the Open-limit check saw is the loan's interest, exactly
  have hm_le : m ≤ aT - j := by
    have hC : ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 ≤ aT - j := by
      have : (aT - j) * broker.managementFeeRate.toNat ≤ (aT - j) * 10000 := Nat.mul_le_mul_left _ hR10
      omega
    have : (m : ℚ) * 10 ^ ls ≤ ((((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) : ℚ) * 10 ^ ls :=
      by rw [← hmv]; exact hmf_hi
    have := le_of_mul_le_mul_right this hls10
    have : m ≤ ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 := by exact_mod_cast this
    omega
  have hstate := hchecks.state
  unfold LoanState.build at hstate
  obtain ⟨d1, hd1, hstate⟩ := bind_ok_peel _ _ _ hstate
  obtain ⟨d2, hd2, hstate⟩ := bind_ok_peel _ _ _ hstate
  have hxe : loanState.interestDue = d2 := by
    simp only [pure, Except.pure, Except.ok.injEq] at hstate
    rw [← hstate]
  have hd1v : d1.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ d1 aT j ls htvN hp (by rw [haTv]; norm_cast)
      (by rw [hj]; norm_cast) (by omega) hsl hd1]
    push_cast [Nat.cast_sub hjaT]; ring
  have hd1N := operator_sub_isNormalized_to_nearest_sz _ _ d1 htvN hp hd1
  have hd2v : d2.toRat = ((aT - j - m : ℕ) : ℚ) * 10 ^ ls := by
    rw [Number.operator_sub_toRat_of_grid _ _ d2 (aT - j) m ls hd1N hmfN (by rw [hd1v]; norm_cast)
      (by rw [hmv]; norm_cast) (by omega) hsl hd2]
    push_cast [Nat.cast_sub hjaT, Nat.cast_sub hm_le]; ring
  have hxN : loanState.interestDue.isNormalized := by
    rw [hxe]; exact operator_sub_isNormalized_to_nearest_sz _ _ d2 hd1N hmfN hd2
  -- AssetsAvailable is at least PrincipalRequested, and both with the interest stay below the limit
  have hopen := (Vault.exceedsOpenLimit_false_bound v _ hxN hchecks.open_zone).1
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat :=
    (operator_lt_eq_false_iff _ _ v.wf.assetsAvailable_norm hp).mp hchecks.funds
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨hls1, -⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2
  have hpow : (10 : ℚ) ^ (v.baseExponent - 1) ≤ 10 ^ ls / 10 := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
    exact div_le_div_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) hls1) (by norm_num)
  rw [hxe, hd2v] at hopen
  have hcast : ((aT - j - m : ℕ) : ℚ) = aT - j - m := by push_cast [Nat.cast_sub hjaT, Nat.cast_sub hm_le]; ring
  rw [hcast] at hopen
  have hjv : principal.toRat = (j : ℚ) * 10 ^ ls := hj
  rw [hjv] at hfunds
  have hmv' : (m : ℚ) * 10 ^ ls ≤ (((aT - j : ℕ) : ℚ) / 10 + 1) * 10 ^ ls := by rw [← hmv]; exact hmf10
  have hm' : (m : ℚ) ≤ ((aT - j : ℕ) : ℚ) / 10 + 1 := le_of_mul_le_mul_right hmv' hls10
  push_cast [Nat.cast_sub hjaT] at hm'
  have hlim : ((aT : ℚ) - m) * 10 ^ ls < (9 * 10 ^ 16 + 5 : ℕ) * (10 ^ ls / 10) := by
    calc ((aT : ℚ) - m) * 10 ^ ls = (j : ℚ) * 10 ^ ls + ((aT : ℚ) - j - m) * 10 ^ ls := by ring
      _ ≤ v.assetsAvailable.toRat + ((aT : ℚ) - j - m) * 10 ^ ls := by linarith
      _ < (9 * 10 ^ 16 + 5 : ℕ) * (10 : ℚ) ^ (v.baseExponent - 1) := hopen
      _ ≤ (9 * 10 ^ 16 + 5 : ℕ) * (10 ^ ls / 10) := by gcongr
  have hlim' : (aT : ℚ) - m < (9 * 10 ^ 16 + 5) / 10 := by
    have : ((aT : ℚ) - m) * 10 ^ ls < ((9 * 10 ^ 16 + 5) / 10) * 10 ^ ls := by
      calc ((aT : ℚ) - m) * 10 ^ ls < (9 * 10 ^ 16 + 5 : ℕ) * (10 ^ ls / 10) := hlim
        _ = ((9 * 10 ^ 16 + 5) / 10) * 10 ^ ls := by push_cast; ring
    exact lt_of_mul_lt_mul_right this hls10.le
  have hjnn : (0 : ℚ) ≤ j := by positivity
  have haT2 : (aT : ℚ) < 10 ^ 16 + 2 := by linarith
  have haT2' : aT < 10 ^ 16 + 2 := by exact_mod_cast haT2
  have haT' : (aT : ℚ) ≤ 10 ^ 16 + 1 := by exact_mod_cast (by omega : aT ≤ 10 ^ 16 + 1)
  -- PrincipalRequested is the total less the interest and the fee
  have hPO : r.loan'.principalOutstanding = props.principalOutstanding := by
    show r.loan'.toRawLoan.principalOutstanding = _; rw [hl]; rfl
  have hjm : (j : ℚ) ≤ aT - m := by
    have : ((j + m : ℕ) : ℚ) ≤ aT := by exact_mod_cast (by omega : j + m ≤ aT)
    push_cast at this
    linarith
  refine ⟨?_, ?_⟩
  · show r.loan'.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ r.loan'.loanScale
    rw [hTV, hLS, haTv]
    exact mul_le_mul_of_nonneg_right haT' hls10.le
  · show r.loan'.principalOutstanding.toRat < (9 * 10 ^ 15 + 1) * 10 ^ r.loan'.loanScale
    rw [hPO, hpov, hjv, hLS]
    exact mul_lt_mul_of_pos_right (by linarith) hls10

/-- A loan a LoanSet creates owes at most `10^16 + 1` LoanScale units. PrincipalRequested comes out of
AssetsAvailable, the Open limit caps it plus the interest, and the fee is at most a tenth of the interest. -/
lemma Loan.Created.totalValue_le {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ start.loanScale :=
  (Loan.Created.size h).1

/-- A loan a LoanSet creates lends less than `9·10^15 + 1` LoanScale units. The Open limit caps
PrincipalRequested plus the interest. -/
lemma Loan.Created.principal_lt {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.principalOutstanding.toRat < (9 * 10 ^ 15 + 1) * 10 ^ start.loanScale :=
  (Loan.Created.size h).2

end XRPL.Model.Lending
