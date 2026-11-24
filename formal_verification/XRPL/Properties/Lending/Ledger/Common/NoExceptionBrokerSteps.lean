import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerSet
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.LoanBroker.Common.CoverDebit
import XRPL.Properties.Lending.Loan.Common.NextInstalment
import XRPL.Properties.Protocol.Common.TenthBipsTotality
import XRPL.Properties.Protocol.STAmount.Range.Success

/-! # The steps of the cover transactions never throw within the asset's range

Each Number operation of a cover transaction succeeds far below the largest Number, and each conversion succeeds
within the asset's maximum (XRP, MPT) or `iouProofCap` (IOU). -/

namespace XRPL.Model.Protocol

open private exponent_headroom_of_abs from XRPL.Properties.Lending.Loan.Common.DefaultTotal

/-- The IOU size the cover proofs follow, `10^89`. The largest IOU amount is just below `10^96`. -/
def iouProofCap : ℚ := 10 ^ 89

/-- A value below `10^96` in size leaves the exponent room an addition needs. -/
private lemma abs_headroom (n : Number) (hn : n.isNormalized) (h : |n.toRat| < 10 ^ 96) :
    n.exponent_ + 22 ≤ maxExponent :=
  exponent_headroom_of_abs n hn (by linarith [(abs_lt.mp h).1]) (abs_lt.mp h).2

/-- Adding two values below `10^96` in size never throws, in every mode. -/
lemma Number.operator_add_total_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 96) (hyl : |y.toRat| < 10 ^ 96) :
    ∃ r, x.operator_add y mode = .ok r ∧ r.isNormalized := by
  obtain ⟨r, hr⟩ := Number.operator_add_ok_of_exp x y mode hx hy (abs_headroom x hx hxl) (abs_headroom y hy hyl)
  exact ⟨r, hr, Number.operator_add_isNormalized_any x y r mode hx hy hr⟩

/-- Subtracting two values below `10^96` in size never throws, in every mode. -/
lemma Number.operator_sub_total_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 96) (hyl : |y.toRat| < 10 ^ 96) :
    ∃ r, x.operator_sub y mode = .ok r ∧ r.isNormalized := by
  obtain ⟨r, hr⟩ := Number.operator_sub_ok_of_exp x y mode hx hy (abs_headroom x hx hxl) (abs_headroom y hy hyl)
  exact ⟨r, hr, Number.operator_sub_isNormalized_any x y r mode hx hy hr⟩

/-- A sum stays between two Numbers that enclose the exact sum and zero, in every mode. -/
lemma Number.operator_add_between (x y r lo hi : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : x.operator_add y mode = .ok r) (hlo : lo.isNormalized) (hhi : hi.isNormalized)
    (hlo0 : lo.toRat ≤ 0) (hhi0 : 0 ≤ hi.toRat) (h1 : lo.toRat ≤ x.toRat + y.toRat)
    (h2 : x.toRat + y.toRat ≤ hi.toRat) : lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat := by
  by_cases hr0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r hr0]; exact ⟨hlo0, hhi0⟩
  have hlower : ∀ n, Number.lower (x.toRat + y.toRat) = some n → lo.toRat ≤ n.toRat ∧ n.toRat ≤ hi.toRat :=
    fun n hn => ⟨Number.lower_tight _ n hn lo hlo h1, le_trans (Number.lower_le _ n hn) h2⟩
  have hupper : ∀ n, Number.upper (x.toRat + y.toRat) = some n → lo.toRat ≤ n.toRat ∧ n.toRat ≤ hi.toRat :=
    fun n hn => ⟨le_trans h1 (Number.le_upper _ n hn), Number.upper_tight _ n hn hi hhi h2⟩
  cases mode with
  | to_nearest =>
    rcases Number.operator_add_rounded_to_nearest x y r hx hy hok with ⟨n, hn, hv⟩ | ⟨n, hn, hv⟩
    · rw [hv]; exact hlower n hn
    · rw [hv]; exact hupper n hn
  | upward =>
    obtain ⟨n, hn, hv⟩ := Number.operator_add_rounded_upward x y r hx hy hok hr0
    rw [hv]; exact hupper n hn
  | downward =>
    obtain ⟨n, hn, hv⟩ := Number.operator_add_rounded_downward x y r hx hy hok hr0
    rw [hv]; exact hlower n hn
  | towards_zero =>
    obtain ⟨n, hn, hv⟩ := Number.operator_add_rounded_towards_zero x y r hx hy hok
    rw [hv]
    split_ifs at hn
    · exact hlower n hn
    · exact hupper n hn

/-- A difference stays between two Numbers that enclose the exact difference and zero, in every mode. -/
lemma Number.operator_sub_between (x y r lo hi : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : x.operator_sub y mode = .ok r) (hlo : lo.isNormalized) (hhi : hi.isNormalized)
    (hlo0 : lo.toRat ≤ 0) (hhi0 : 0 ≤ hi.toRat) (h1 : lo.toRat ≤ x.toRat - y.toRat)
    (h2 : x.toRat - y.toRat ≤ hi.toRat) : lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat :=
  Number.operator_add_between x y.operator_neg r lo hi mode hx (Number.operator_neg_isNormalized y hy) hok hlo hhi
    hlo0 hhi0 (by rw [Number.toRat_neg]; linarith) (by rw [Number.toRat_neg]; linarith)

/-- The asset's maximum is the value of a normalized Number. -/
lemma NumericType.maxAmount_number (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = nt.maxAmount := by
  rcases hasset with rfl | rfl | rfl
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16 - 1) 80 (by constructor <;> norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    refine ⟨w, hw, ?_⟩
    rw [hwv, NumericType.maxAmount_fractional]
    push_cast
    norm_num
  · obtain ⟨w, hw, -, hwv⟩ := Number.exists_normalized_of_pos_nat (100000000000000000) (by norm_num) (by norm_num)
    exact ⟨w, hw, by rw [hwv]; rfl⟩
  · obtain ⟨w, hw, -, hwv⟩ := Number.exists_normalized_of_pos_nat (9223372036854775807) (by norm_num)
      (by norm_num)
    exact ⟨w, hw, by rw [hwv]; rfl⟩

/-- `10^89` and its negative are values of normalized Numbers. -/
lemma iouProofCap_number : ∃ lo hi : Number, lo.isNormalized ∧ hi.isNormalized ∧
    lo.toRat = -iouProofCap ∧ hi.toRat = iouProofCap := by
  obtain ⟨hi, hhi, hhiv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 18) 71 (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  obtain ⟨lo, hlo, hlov⟩ := Number.exists_normalized_int_mul_pow (-10 ^ 18) 71 (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  refine ⟨lo, hi, hlo, hhi, ?_, ?_⟩
  · rw [hlov]; unfold iouProofCap; push_cast; norm_num
  · rw [hhiv]; unfold iouProofCap; push_cast; norm_num

/-- `2 * 10^89` and its negative are values of normalized Numbers. -/
lemma iouProofCap_two_number : ∃ lo hi : Number, lo.isNormalized ∧ hi.isNormalized ∧
    lo.toRat = -(2 * iouProofCap) ∧ hi.toRat = 2 * iouProofCap := by
  obtain ⟨hi, hhi, hhiv⟩ := Number.exists_normalized_int_mul_pow (2 * 10 ^ 18) 71 (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  obtain ⟨lo, hlo, hlov⟩ := Number.exists_normalized_int_mul_pow (-(2 * 10 ^ 18)) 71
    (by constructor <;> norm_num) ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  refine ⟨lo, hi, hlo, hhi, ?_, ?_⟩
  · rw [hlov]; unfold iouProofCap; push_cast; norm_num
  · rw [hhiv]; unfold iouProofCap; push_cast; norm_num

/-- A value at least zero converts to the asset when it is within the maximum of XRP or an MPT, or below `10^90`
for an IOU. -/
lemma STAmount.ofNumber_ok_of_asset_cap (nt : NumericType) (n : Number) (mode : rounding_mode)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hint : nt.isIntegral = true → n.toRat ≤ nt.maxValue.toNat)
    (hfrac : nt.isIntegral = false → n.toRat < 10 ^ 90) : ∃ st, STAmount.ofNumber nt n mode = .ok st := by
  have hrange : ∀ M : ℕ, n.toRat ≤ M → RoundsWithinUnits mode M 1 n.toRat := by
    intro M hM
    cases mode <;> simp only [RoundsWithinUnits, mul_one]
    · exact Or.inl (by rw [abs_of_nonneg h0]; linarith)
    · rw [abs_of_nonneg h0]; linarith
    · exact ⟨by linarith [show (0 : ℚ) ≤ M by positivity], by linarith⟩
    · exact ⟨by linarith [show (0 : ℚ) ≤ M by positivity], hM⟩
  rcases hasset with rfl | rfl | rfl
  · obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr n mode hn
      (by rw [abs_of_nonneg h0]; exact hfrac rfl)
    exact ⟨st, hst⟩
  · refine (STAmount.ofNumber_ok_iff_proof _ n mode hn (Or.inr (Or.inl rfl)) (Or.inl h0)).mpr ?_
    rw [STAmount.roundsInRange_native_iff]
    exact hrange _ (hint rfl)
  · refine (STAmount.ofNumber_ok_iff_proof _ n mode hn (Or.inr (Or.inr rfl)) (Or.inl h0)).mpr ?_
    rw [STAmount.roundsInRange_int64_iff]
    exact hrange _ (hint rfl)

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private STAmount.roundToNumericType_asset_ok from XRPL.Properties.Lending.Loan.Common.NextInstalment

/-- The Open limit of a vault always computes. -/
lemma Vault.pool_openLimit_ok (v : Vault) : ∃ L : Number, AssetPool.openLimit v = .ok L ∧ L.isNormalized := by
  obtain ⟨L, hL, hLn, -⟩ := Vault.openLimit_value v
  exact ⟨L, hL, hLn⟩

/-- A cover credit or debit of an amount of the asset fails only the broker re-check. Reading the amount and
moving CoverAvailable by it never throw below `10^96`. -/
lemma LoanBroker.applyCoverTransaction_error (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (ha : a.CanonicalOrZero) (hal : |a.toRat| < 10 ^ 96) (hcl : lb.coverAvailable.toRat < 10 ^ 96) {e : Error}
    (h : lb.applyCoverTransaction d a = .error e) : e = .notLawful := by
  obtain ⟨aN, haN⟩ := ha.toNumber_ok
  obtain ⟨haNv, haNn⟩ := ha.toNumber_exact aN haN
  have hcn := lb.wf.coverAvailable_norm
  have hc0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hcl' : |lb.coverAvailable.toRat| < 10 ^ 96 := by rw [abs_of_nonneg hc0]; exact hcl
  unfold LoanBroker.applyCoverTransaction at h
  rw [haN, ok_bind] at h
  cases d with
  | credit =>
    obtain ⟨c', hc', -⟩ := Number.operator_add_total_of_abs lb.coverAvailable aN .to_nearest hcn haNn hcl'
      (by rw [haNv]; exact hal)
    simp only [hc', ok_bind] at h
    unfold RawLoanBroker.to_lawful at h
    split at h
    · cases h
    · cases h; rfl
  | debit =>
    obtain ⟨c', hc', -⟩ := Number.operator_sub_total_of_abs lb.coverAvailable aN .to_nearest hcn haNn hcl'
      (by rw [haNv]; exact hal)
    simp only [hc', ok_bind] at h
    unfold RawLoanBroker.to_lawful at h
    split at h
    · cases h
    · cases h; rfl

/-- The minimum cover of a DebtTotal of at most `10^16` whole base units always computes. -/
lemma minimumBrokerCover_ok_of_units (nt : NumericType) (d : Number) (rate : TenthBips32) (b : Int)
    (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hb : -10 ≤ b ∧ b ≤ 0) (hd : d.isNormalized)
    (t : ℕ) (ht : t ≤ 10 ^ 16) (hdv : d.toRat = (t : ℚ) * 10 ^ b) (hrate : rate.toNat ≤ 100000) :
    ∃ m, minimumBrokerCover nt d rate b = .ok m ∧ m.isNormalized ∧ |m.toRat| ≤ 2 * 10 ^ 16 + 1 := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hb.2
  have ht' : (t : ℚ) ≤ 10 ^ 16 := by exact_mod_cast ht
  have hd0 : 0 ≤ d.toRat := by rw [hdv]; positivity
  have hd16 : d.toRat ≤ 10 ^ 16 := by rw [hdv]; nlinarith
  obtain ⟨r, hr, hrn, hr0, hrle, -⟩ := tenthBipsOfValue_upward_ok d rate b hd hd0 (by linarith) (by omega)
    (fun hm => by
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · exfalso
          rw [h] at hdv
          simp only [Nat.cast_zero, zero_mul] at hdv
          exact hm ((Number.toRat_eq_zero_iff).mp hdv)
        · exact h
      rw [hdv]
      have : (1 : ℚ) ≤ t := by exact_mod_cast ht1
      nlinarith) hrate
  have hrabs : |r.toRat| ≤ 10 ^ 16 := by rw [abs_of_nonneg hr0]; linarith
  obtain ⟨y, hy, hyn, hyl⟩ := STAmount.roundToNumericType_asset_ok nt r .upward b hasset ⟨by omega, hb.2⟩ hrn
    (by linarith [show (10 : ℚ) ^ 16 < 10 ^ 90 by norm_num]) (fun hint => by
      rcases hasset with rfl | rfl | rfl
      · cases hint
      · show |r.toRat| + 1 ≤ ((100000000000000000 : ℕ) : ℚ)
        push_cast; linarith
      · show |r.toRat| + 1 ≤ ((9223372036854775807 : ℕ) : ℚ)
        push_cast; linarith)
  refine ⟨y, ?_, hyn, by linarith⟩
  unfold minimumBrokerCover
  rw [hr, ok_bind]
  exact hy

end XRPL.Model.Lending
