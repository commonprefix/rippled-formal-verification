import XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal
import XRPL.Properties.Lending.Loan.Common.ManageCoverBase
import XRPL.Properties.Lending.Loan.Common.ManageTotal
import XRPL.Properties.Lending.Loan.Common.PayDefs

/-! # A default succeeds on the base grid

When the vault and the broker hold whole base units below `10^16`, a default only moves whole base units, and
the vault, the broker and the loan pass their re-checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- AssetsAvailable, AssetsDeployed, LossUnrealized, YieldUnrealized and DebtTotal are whole base units below `10^16`,
the loan is at the base scale, AssetsAvailable has room for its principal, and CoverAvailable is below `10^96`. -/
structure Loan.DefaultGrid (loan : Loan) (v : Vault) : Prop where
  numericType : loan.broker.numericType = v.numericType
  loanScale : loan.loanScale = v.baseExponent
  assetsAvailable : Number.AtExponent v.assetsAvailable.toRat v.baseExponent (10 ^ 16)
  room : v.assetsAvailable.toRat + loan.principalOutstanding.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent
  assetsDeployed : Number.AtExponent v.assetsDeployed.toRat v.baseExponent (10 ^ 16)
  lossUnrealized : Number.AtExponent v.lossUnrealized.toRat v.baseExponent (10 ^ 16)
  yieldUnrealized : Number.AtExponent v.yieldUnrealized.toRat v.baseExponent (10 ^ 16)
  debtTotal : Number.AtExponent loan.broker.debtTotal.toRat v.baseExponent (10 ^ 16)
  coverAvailable : loan.broker.coverAvailable.toRat < 10 ^ 96

/-- A normalized value below `10^96` in size leaves the headroom `operator_add` needs. -/
private lemma exponent_headroom_of_abs (n : Number) (hn : n.isNormalized) (hlo : -10 ^ 96 < n.toRat)
    (hhi : n.toRat < 10 ^ 96) : n.exponent_ + 22 ≤ maxExponent := by
  by_cases h0 : 0 ≤ n.toRat
  · exact Number.exponent_headroom_of_lt n hn h0 hhi
  · push Not at h0
    have hm : n.mantissa_ ≠ 0 := by
      intro hm
      rw [Number.toRat_eq_zero_of_mantissa_zero n hm] at h0
      exact lt_irrefl _ h0
    have hneg := Number.exponent_headroom_of_lt n.operator_neg (Number.operator_neg_isNormalized n hn)
      (by rw [Number.toRat_neg]; linarith) (by rw [Number.toRat_neg]; linarith)
    rwa [Number.operator_neg_exponent n hm] at hneg

/-- A whole number of units below `2^63` is below `10^96` at a scale at most `10^0`. -/
private lemma units_lt_pow (k : ℕ) (s : ℤ) (hk : k < 2 ^ 63) (hs : s ≤ 0) : (k : ℚ) * 10 ^ s < 10 ^ 96 := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hs1 : (10 : ℚ) ^ s ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hs
  have hk' : (k : ℚ) < 2 ^ 63 := by exact_mod_cast hk
  have hk0 : (0 : ℚ) ≤ k := by positivity
  calc (k : ℚ) * 10 ^ s ≤ k := by nlinarith
    _ < 10 ^ 96 := by linarith [show (2 : ℚ) ^ 63 < 10 ^ 96 by norm_num]

/-- A normalized value at least zero passes the `Number` check `0 ≤ x`. -/
private lemma zero_le_of_toRat (x : Number) (hx : x.isNormalized) (h : 0 ≤ x.toRat) :
    Number.zero.operator_le x = true :=
  (operator_le_iff _ _ Number.zero_isNormalized hx).mpr (by rw [Number.toRat_zero]; exact h)

variable (loan : Loan) (v : Vault)

/-- A default on the base grid succeeds. The asset is XRP, an MPT or an IOU, and AssetsDeployed, LossUnrealized,
DebtTotal and YieldUnrealized hold what the loan takes out. -/
lemma Loan.manageDefault_ok_of_grid (hg : Loan.DefaultGrid loan v) (hasset : Vault.HoldsAsset v)
    (hdeployed : (if loan.isImpaired then 0 else v.lossUnrealized.toRat) + loan.principalOutstanding.toRat ≤
      v.assetsDeployed.toRat)
    (hreserved : v.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat)
    (hloss : loan.isImpaired = true → loan.principalOutstanding.toRat ≤ v.lossUnrealized.toRat)
    (hdebt : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat)
    (hyield : loan.toExact.interestDue ≤ v.yieldUnrealized.toRat) :
    ∃ r, (loan.manageDefault v).run = .ok (.ok r) := by
  set b := v.baseExponent with hbdef
  have hbase := Vault.baseExponent_scale_range v
  have hp10 : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hsc : cMinOffset ≤ b ∧ b ≤ cMaxOffset := by unfold cMinOffset cMaxOffset; omega
  have hpow16 : (10 : ℚ) ^ (16 + b) = 10 ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num

  obtain ⟨a, -, hav⟩ := hg.assetsAvailable
  obtain ⟨d, hd, hdv⟩ := hg.assetsDeployed
  obtain ⟨l, hl, hlv⟩ := hg.lossUnrealized
  obtain ⟨y, hy, hyv⟩ := hg.yieldUnrealized
  obtain ⟨t, ht, htv⟩ := hg.debtTotal

  have hex := loan.exact
  have hexg := loan.grid
  obtain ⟨tv, htvlt, htvv⟩ := hexg.totalValueOutstanding_atExponent
  obtain ⟨p, -, hpv⟩ := hexg.principalOutstanding_atExponent
  obtain ⟨mf, hmflt, hmfv⟩ := hexg.managementFeeOutstanding_atExponent
  have htol := hex.interest_nonneg
  simp only [RawLoan.toExact] at htvv hpv hmfv htvlt hmflt
  have hbound := NumericType.mantissaBound_le loan.broker.numericType
  rw [hg.loanScale] at htvv hpv hmfv
  have hap : a + p < 10 ^ 16 := by
    have h1 : ((a + p : ℕ) : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by
      push_cast; rw [add_mul, ← hav, ← hpv]; exact hg.room
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
  have hpd : p ≤ d := by
    have h1 : (p : ℚ) * 10 ^ b ≤ (d : ℚ) * 10 ^ b := by
      rw [← hpv, ← hdv]
      have : 0 ≤ (if loan.isImpaired then 0 else v.lossUnrealized.toRat) := by
        split
        · exact le_refl _
        · exact v.exact.lossUnrealized_nonneg
      linarith
    exact_mod_cast le_of_mul_le_mul_right h1 hp10
  have hpt : p ≤ t := by
    have h1 : (p : ℚ) * 10 ^ b ≤ (t : ℚ) * 10 ^ b := by rw [← hpv, ← htv]; exact hdebt
    exact_mod_cast le_of_mul_le_mul_right h1 hp10

  -- the interest is exact and at least minus one unit
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  have hi' : loan.interestDue = (loan.totalValueOutstanding.operator_sub loan.principalOutstanding .to_nearest >>=
      fun x => x.operator_sub loan.managementFeeOutstanding .to_nearest) := rfl
  have hib := hi
  rw [hi'] at hib
  obtain ⟨x, hx, hix⟩ := bind_ok_peel _ _ _ hib
  have hxv := Number.operator_sub_toRat_of_grid _ _ x tv p b loan.wf.totalValueOutstanding_norm
    loan.wf.principalOutstanding_norm (by rw [htvv]; norm_cast) (by rw [hpv]; norm_cast) (by omega) hs hx
  have hxn := operator_sub_isNormalized_to_nearest_sz _ _ _ loan.wf.totalValueOutstanding_norm
    loan.wf.principalOutstanding_norm hx
  have hiDue : loan.toExact.interestDue = (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b := by
    show loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat = _
    rw [htvv, hpv, hmfv]; push_cast; ring
  have hi1 : -1 ≤ (tv : ℤ) - p - mf := by
    have h1 : -(10 : ℚ) ^ b ≤ (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b := by
      rw [← hiDue]
      linarith
    have h2 : ((-1 : ℤ) : ℚ) * 10 ^ b ≤ (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b := by
      rw [show ((-1 : ℤ) : ℚ) = -1 by norm_num]; linarith
    exact_mod_cast le_of_mul_le_mul_right h2 hp10
  have hiv := Number.operator_sub_toRat_of_grid _ _ i ((tv : ℤ) - p) mf b hxn loan.wf.managementFeeOutstanding_norm
    hxv (by rw [hmfv]; norm_cast) (by omega) hs hix
  have hin := operator_sub_isNormalized_to_nearest_sz _ _ _ hxn loan.wf.managementFeeOutstanding_norm hix

  -- the cover is `k` whole base units, at most the principal and the cover
  obtain ⟨dc, hdc⟩ := Loan.defaultCover_ok loan v hasset hg.numericType hg.loanScale hg.assetsAvailable hg.room
    hg.debtTotal
  obtain ⟨mc, liq, cov, st, hmc, hliq, -, -, -⟩ := Loan.defaultCover_parts loan v dc hdc
  have hcap0 := Loan.cappedCover_nonneg loan mc liq hmc hliq
  set capped := min (min liq.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat
    with hcapdef
  have hcapPO : capped ≤ loan.principalOutstanding.toRat := min_le_of_left_le (min_le_right _ _)
  have hcapCA : capped ≤ loan.broker.coverAvailable.toRat := min_le_right _ _
  have hdcv := Loan.defaultCover_at_base loan v dc mc liq a hdc hmc hliq hg.numericType hav (by
    rw [hpow16]
    have h1 : v.assetsAvailable.toRat + loan.principalOutstanding.toRat = ((a + p : ℕ) : ℚ) * 10 ^ b := by
      rw [hav, hpv]; push_cast; ring
    have h2 : ((a + p : ℕ) : ℚ) ≤ 10 ^ 16 - 1 := by
      have : a + p ≤ 10 ^ 16 - 1 := by omega
      have h3 : ((10 ^ 16 - 1 : ℕ) : ℚ) = 10 ^ 16 - 1 := by norm_num
      rw [← h3]; exact_mod_cast this
    nlinarith)
  rw [← hcapdef] at hdcv
  have hk0 : 0 ≤ ⌊capped / 10 ^ b⌋ := Int.floor_nonneg.mpr (div_nonneg hcap0 hp10.le)
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, (k : ℤ) = ⌊capped / 10 ^ b⌋ := ⟨_, Int.toNat_of_nonneg hk0⟩
  have hdck : dc.toRat = (k : ℚ) * 10 ^ b := by rw [hdcv, ← hkdef]; norm_cast
  have hkcap : (k : ℚ) * 10 ^ b ≤ capped := by
    have := Int.floor_le (capped / 10 ^ b)
    rw [← hkdef, le_div_iff₀ hp10] at this
    exact_mod_cast this
  have hkp : k ≤ p := by
    have h1 : (k : ℚ) * 10 ^ b ≤ (p : ℚ) * 10 ^ b := by rw [← hpv]; linarith
    exact_mod_cast le_of_mul_le_mul_right h1 hp10
  have hdcn := Loan.defaultCover_isNormalized loan v dc hdc

  -- AssetsAvailable takes the cover exactly, and the asset stores the sum
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_lt v.assetsAvailable dc .to_nearest v.wf.assetsAvailable_norm hdcn
    hAA0 (by rw [hav]; exact units_lt_pow a b (by omega) hbase.2) (by rw [hdck]; positivity)
    (by rw [hdck]; exact units_lt_pow k b (by omega) hbase.2)
  have haav : aa.toRat = ((a + k : ℕ) : ℚ) * 10 ^ b := by
    rw [Number.operator_add_toRat_of_grid _ _ aa a k b v.wf.assetsAvailable_norm hdcn (by rw [hav]; norm_cast)
      (by rw [hdck]; norm_cast) (by omega) hs haa]
    push_cast; ring
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hdcn haa
  have haar : STAmount.isRounded v.numericType aa = false := hasset.isRounded_units aa (a + k) haan (by omega) haav
  obtain ⟨aa', hround⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ haar
  have haa'v : aa'.toRat = aa.toRat := STAmount.roundToNumericType_of_isRounded_false _ _ _ haan haar hround
  have haa'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround

  obtain ⟨ad', had⟩ := Number.operator_sub_ok_of_grid v.assetsDeployed loan.principalOutstanding d p b
    v.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm hdv hpv (by omega) (by omega) hsc
  have hadv : ad'.toRat = ((d - p : ℕ) : ℚ) * 10 ^ b := by
    rw [Number.operator_sub_toRat_of_grid _ _ ad' d p b v.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm
      (by rw [hdv]; norm_cast) (by rw [hpv]; norm_cast) (by omega) hs had]
    push_cast [Nat.cast_sub hpd]; ring
  have hadn := operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsDeployed_norm
    loan.wf.principalOutstanding_norm had

  have hlad : l ≤ d := by
    have h1 : (l : ℚ) * 10 ^ b ≤ (d : ℚ) * 10 ^ b := by rw [← hlv, ← hdv]; exact v.exact.lossUnrealized_le
    exact_mod_cast le_of_mul_le_mul_right h1 hp10
  obtain ⟨lu', hlu', hluv, hlun, hlu0⟩ : ∃ lu',
      v.lossUnrealized.operator_add (loan.defaultChange i dc).loss .to_nearest = .ok lu' ∧
        lu'.toRat ≤ ((d - p : ℕ) : ℚ) * 10 ^ b ∧ lu'.isNormalized ∧ 0 ≤ lu'.toRat := by
    cases himp : loan.isImpaired
    · have hlpd : l + p ≤ d := by
        rw [himp] at hdeployed
        simp only [Bool.false_eq_true, ↓reduceIte] at hdeployed
        have h1 : ((l + p : ℕ) : ℚ) * 10 ^ b ≤ (d : ℚ) * 10 ^ b := by
          push_cast; rw [add_mul, ← hlv, ← hpv, ← hdv]; exact hdeployed
        exact_mod_cast le_of_mul_le_mul_right h1 hp10
      refine ⟨v.lossUnrealized, ?_, ?_, v.wf.lossUnrealized_norm, v.exact.lossUnrealized_nonneg⟩
      · simp only [Loan.defaultChange, himp, Bool.false_eq_true, ↓reduceIte]
        exact Number.operator_add_zero_right _ _
      · rw [hlv]
        apply mul_le_mul_of_nonneg_right _ hp10.le
        exact_mod_cast (by omega : l ≤ d - p)
    · have hpl : p ≤ l := by
        have h1 : (p : ℚ) * 10 ^ b ≤ (l : ℚ) * 10 ^ b := by rw [← hpv, ← hlv]; exact hloss himp
        exact_mod_cast le_of_mul_le_mul_right h1 hp10
      obtain ⟨lu', hsub⟩ := Number.operator_sub_ok_of_grid v.lossUnrealized loan.principalOutstanding l p b
        v.wf.lossUnrealized_norm loan.wf.principalOutstanding_norm hlv hpv (by omega) (by omega) hsc
      have hv' := Number.operator_sub_toRat_of_grid _ _ lu' l p b v.wf.lossUnrealized_norm
        loan.wf.principalOutstanding_norm (by rw [hlv]; norm_cast) (by rw [hpv]; norm_cast) (by omega) hs hsub
      have hlp : (((l : ℤ) - p : ℤ) : ℚ) = ((l - p : ℕ) : ℚ) := by push_cast [Nat.cast_sub hpl]; ring
      refine ⟨lu', ?_, ?_, operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm
        loan.wf.principalOutstanding_norm hsub, ?_⟩
      · simp only [Loan.defaultChange, himp, ↓reduceIte]
        exact hsub
      · rw [hv', hlp]
        apply mul_le_mul_of_nonneg_right _ hp10.le
        exact_mod_cast (by omega : l - p ≤ d - p)
      · rw [hv', hlp]; positivity

  have hyi : (tv : ℤ) - p - mf ≤ y := by
    have h1 : (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b ≤ ((y : ℤ) : ℚ) * 10 ^ b := by
      rw [← hiDue]; push_cast; rw [← hyv]; exact hyield
    exact_mod_cast le_of_mul_le_mul_right h1 hp10
  have hiv' : i.toRat = (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b := by rw [hiv]
  have hYU0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hYUlt : v.yieldUnrealized.toRat < 10 ^ 96 := by rw [hyv]; exact units_lt_pow y b (by omega) hbase.2
  have hilo : -10 ^ 96 < i.operator_neg.toRat ∧ i.operator_neg.toRat < 10 ^ 96 := by
    rw [Number.toRat_neg, hiv']
    have hz1 : (-1 : ℚ) ≤ (((tv : ℤ) - p - mf : ℤ) : ℚ) := by exact_mod_cast hi1
    have hz2 : (((tv : ℤ) - p - mf : ℤ) : ℚ) ≤ y := by exact_mod_cast hyi
    have hy' : (y : ℚ) < 10 ^ 16 := by exact_mod_cast hy
    have hs1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
    have hy0 : (0 : ℚ) ≤ y := by positivity
    have hzb1 : (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b ≤ y :=
      calc (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b ≤ (y : ℚ) * 10 ^ b := mul_le_mul_of_nonneg_right hz2 hp10.le
        _ ≤ y := mul_le_of_le_one_right hy0 hs1
    have hzb2 : (-1 : ℚ) ≤ (((tv : ℤ) - p - mf : ℤ) : ℚ) * 10 ^ b :=
      calc (-1 : ℚ) ≤ (-1) * 10 ^ b := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hz1 hp10.le
    constructor <;> linarith [show (10 : ℚ) ^ 16 < 10 ^ 96 by norm_num]
  obtain ⟨yu', hyu'⟩ := Number.operator_add_ok_of_exp v.yieldUnrealized i.operator_neg .to_nearest
    v.wf.yieldUnrealized_norm (Number.operator_neg_isNormalized i hin)
    (Number.exponent_headroom_of_lt _ v.wf.yieldUnrealized_norm hYU0 hYUlt)
    (exponent_headroom_of_abs _ (Number.operator_neg_isNormalized i hin) hilo.1 hilo.2)
  have hyuv : yu'.toRat = (((y : ℤ) - ((tv : ℤ) - p - mf) : ℤ) : ℚ) * 10 ^ b :=
    Number.operator_sub_toRat_of_grid _ _ yu' y ((tv : ℤ) - p - mf) b v.wf.yieldUnrealized_norm hin
      (by rw [hyv]; norm_cast) hiv' (by omega) hs hyu'
  have hyun := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.yieldUnrealized_norm
    (Number.operator_neg_isNormalized i hin) hyu'
  have hyu0 : 0 ≤ yu'.toRat := by
    rw [hyuv]
    have : (0 : ℤ) ≤ (y : ℤ) - ((tv : ℤ) - p - mf) := by omega
    have : (0 : ℚ) ≤ (((y : ℤ) - ((tv : ℤ) - p - mf) : ℤ) : ℚ) := by exact_mod_cast this
    positivity

  have hs' : Vault.AdjustSums v (loan.defaultChange i dc) aa' ad' lu' v.assetsReserved yu' :=
    ⟨⟨aa, haa, hround⟩, had, hlu', Number.operator_add_zero_right _ _, hyu'⟩
  have haa'0 : 0 ≤ aa'.toRat := by rw [haa'v, haav]; positivity
  have had0 : 0 ≤ ad'.toRat := by rw [hadv]; positivity
  have hlule : lu'.toRat ≤ ad'.toRat := by rw [hadv]; exact hluv
  have harle : v.assetsReserved.toRat ≤ ad'.toRat := by
    rw [hadv]; push_cast [Nat.cast_sub hpd]; rw [hdv, hpv] at hreserved; linarith
  have hle : lu'.operator_gt ad' = false := by
    unfold Number.operator_gt
    exact (operator_lt_eq_false_iff _ _ hadn hlun).mpr hlule
  have hadj := Vault.adjustBalances_ok v _ _ _ _ _ _ hs'
    ⟨Number.signum_nonneg_of_toRat _ haa'n haa'0, Number.signum_nonneg_of_toRat _ hadn had0,
      Number.signum_nonneg_of_toRat _ hlun hlu0, Number.signum_nonneg_of_toRat _ hyun hyu0,
      Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm v.exact.assetsReserved_nonneg⟩ hle
  obtain ⟨v', hv', -⟩ := Vault.balances_lawful v aa' ad' v.assetsReserved lu' yu'
    ⟨haa'n, hadn, v.wf.assetsReserved_norm, hlun, hyun⟩
    ⟨haa'0, had0, v.exact.assetsReserved_nonneg, hlu0, hyu0⟩ hlule harle
    (hasset.isRounded_units ad' (d - p) hadn (by omega) hadv)
    (hasset.isRounded_units aa' (a + k) haa'n (by omega) (by rw [haa'v, haav]))
    ⟨((a + k : ℕ) : ℤ), by rw [haa'v, haav]; push_cast; ring⟩ (by
      intro h0
      obtain ⟨ha0, hd0⟩ := v.valid.empty_shares h0
      have ha0' : a = 0 := by
        have h1 : (a : ℚ) * 10 ^ b = 0 := by rw [← hav, ha0, Number.toRat_zero]
        exact_mod_cast (mul_eq_zero.mp h1).resolve_right hp10.ne'
      have hd0' : d = 0 := by
        have h1 : (d : ℚ) * 10 ^ b = 0 := by rw [← hdv, hd0, Number.toRat_zero]
        exact_mod_cast (mul_eq_zero.mp h1).resolve_right hp10.ne'
      have hk0' : k = 0 := by omega
      refine ⟨by rw [haa'v, haav, ha0', hk0']; simp, by rw [hadv, hd0']; simp⟩)

  obtain ⟨dt', hdt'⟩ := Number.operator_sub_ok_of_grid loan.broker.debtTotal loan.principalOutstanding t p b
    loan.broker.wf.debtTotal_norm loan.wf.principalOutstanding_norm htv hpv (by omega) (by omega) hsc
  have hdt'v : dt'.toRat = ((t - p : ℕ) : ℚ) * 10 ^ b := by
    rw [Number.operator_sub_toRat_of_grid _ _ dt' t p b loan.broker.wf.debtTotal_norm
      loan.wf.principalOutstanding_norm (by rw [htv]; norm_cast) (by rw [hpv]; norm_cast) (by omega) hs hdt']
    push_cast [Nat.cast_sub hpt]; ring
  have hdt'n := operator_sub_isNormalized_to_nearest_sz _ _ _ loan.broker.wf.debtTotal_norm
    loan.wf.principalOutstanding_norm hdt'
  have hCA0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  obtain ⟨ca', hca'⟩ := Number.operator_sub_ok_of_lt loan.broker.coverAvailable dc .to_nearest
    loan.broker.wf.coverAvailable_norm hdcn hCA0 hg.coverAvailable (by rw [hdck]; positivity)
    (by rw [hdck]; exact units_lt_pow k b (by omega) hbase.2)
  have hca'n := operator_sub_isNormalized_to_nearest_sz _ _ _ loan.broker.wf.coverAvailable_norm hdcn hca'
  have hca'0 : 0 ≤ ca'.toRat :=
    operator_add_nonneg _ _ _ loan.broker.wf.coverAvailable_norm (Number.operator_neg_isNormalized _ hdcn) hca'
      (by rw [Number.toRat_neg, hdck]; linarith)
  have hdtle : dt'.toRat ≤ loan.broker.debtTotal.toRat := by
    rw [hdt'v, htv]
    apply mul_le_mul_of_nonneg_right _ hp10.le
    exact_mod_cast Nat.sub_le t p
  have hbwf : (loan.defaultedBroker dt' ca').WF :=
    { loan.broker.wf with debtTotal_norm := hdt'n, coverAvailable_norm := hca'n }
  have hbvalid : (loan.defaultedBroker dt' ca').Valid :=
    { loan.broker.valid with
      debtTotal_nonneg := zero_le_of_toRat dt' hdt'n (by rw [hdt'v]; positivity)
      coverAvailable_nonneg := zero_le_of_toRat ca' hca'n hca'0
      debt_within_cap := fun hdm => by
        have h1 := (operator_le_iff _ _ loan.broker.wf.debtTotal_norm loan.broker.wf.debtMaximum_norm).mp
          (loan.broker.valid.debt_within_cap hdm)
        exact (operator_le_iff _ _ hdt'n loan.broker.wf.debtMaximum_norm).mpr (le_trans hdtle h1)
      empty_broker := fun hlc => by
        have h0 := loan.broker.valid.empty_broker hlc
        have ht0 : t = 0 := by
          have h1 : (t : ℚ) * 10 ^ b = 0 := by rw [← htv, h0, Number.toRat_zero]
          exact_mod_cast (mul_eq_zero.mp h1).resolve_right hp10.ne'
        exact (Number.toRat_eq_zero_iff_eq_zero hdt'n).mp (by rw [hdt'v, ht0]; simp) }
  obtain ⟨broker', hb', -⟩ := RawLoanBroker.to_lawful_ok_of hbwf hbvalid
  obtain ⟨loan', hok, -⟩ := Loan.manageDefault_success_proof loan v i dc dt' ca' _ v' broker' hi hdc hadj hv' hdt'
    hca' hb'
  exact ⟨_, hok⟩

end XRPL.Model.Lending
