import XRPL.Properties.Vault.Proofs.WithdrawMono.Zero
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.VaultValid

/-! # The `isFractionalNonPositive` guard and the cap bound -/

namespace XRPL.Model.SingleAssetVault.ExitsC

open XRPL.Model.Protocol

lemma frac_of_not_integral (s : STAmount) (h : s.integral = false) :
    s.mNumericType = .fractional := by
  cases hnt : s.mNumericType with
  | fractional => rfl
  | integral mv mo ms msh =>
    exfalso
    have : s.integral = true := by
      show s.mNumericType.isIntegral = true; rw [hnt]; rfl
    rw [this] at h; exact absurd h (by decide)

/-- A vanished fractional amount trips the guard. -/
lemma fnp_true (s : STAmount) (h : s.integral = false ∧ s.toRat ≤ 0) :
    s.isFractionalNonPositive = .ok true := by
  refine WdMono.fnp_nonpos s (frac_of_not_integral s h.1) ?_
  by_contra hc
  push Not at hc
  obtain ⟨hz, hn⟩ := hc
  have := WdMono.pos_of_nonneg s (STAmount.toRat_nonneg_of s (by simpa using hn)) hz
  linarith [h.2]

/-- An integral or positive amount passes the guard. -/
lemma fnp_false (s : STAmount) (h : s.integral = true ∨ 0 < s.toRat) :
    s.isFractionalNonPositive = .ok false := by
  unfold STAmount.isFractionalNonPositive
  rcases h with h | h
  · rw [if_pos h]
  by_cases hi : s.integral = true
  · rw [if_pos hi]
  rw [if_neg hi]
  have hneg := STAmount.mIsNegative_false_of_pos s h
  have hz : s.mValue ≠ 0 := fun hz => by
    rw [STAmount.toRat_eq_zero_of_mValue_zero s hz] at h; exact lt_irrefl _ h
  unfold STAmount.operator_le STAmount.operator_lt STAmount.areComparable
  simp [STAmount.zero_mValue, STAmount.zero_mIsNegative, STAmount.zero_mNumericType,
    STAmount.numericType, hneg, hz]

/-- A total that did not grow cannot exceed a respected cap. -/
lemma not_over_cap (v : Vault) (at' : Number) (hat_norm : at'.isNormalized)
    (hle : at'.toRat ≤ v.assetsTotal.toRat)
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) : False := by
  cases hm : v.assetsMaximum with
  | none =>
    have h0 : Number.zero.operator_ne Number.zero = false := by decide
    rw [hm, Option.getD_none, h0, Bool.false_and] at hmax
    exact absurd hmax (by decide)
  | some m =>
    rw [hm] at hmax
    simp only [Option.getD_some, Bool.and_eq_true] at hmax
    have hmn : m.isNormalized := v.wf.assetsMaximum_norm m hm
    have hgt := (operator_gt_iff at' m hat_norm hmn).mp hmax.2
    have hcap := v.exact.cap m.toRat (Option.mem_map_of_mem _ hm)
    have : at'.toRat ≤ m.toRat := le_trans hle hcap
    exact absurd hgt (not_lt.mpr this)

end XRPL.Model.SingleAssetVault.ExitsC
