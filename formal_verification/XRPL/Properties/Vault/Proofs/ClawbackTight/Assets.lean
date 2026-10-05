import XRPL.Properties.Vault.Proofs.ClawbackTight.Clamp
import XRPL.Properties.Vault.Proofs.ClawbackTight.Reduce
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Clamp
import XRPL.Properties.Vault.Proofs.ClawbackAccuracy
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Protocol.STAmount.Mul.Common.Integral

/-! # Recovered-asset facts of a successful clawback -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

lemma numExact_of_zero (s : STAmount) (hz : s.mValue = 0) : NumExact s := by
  intro n hn
  rw [STAmount.toNumber_zero_eq s _ n hz hn, Number.toRat_zero, (STAmount.toRat_eq_zero_iff s).mpr hz]
  exact ⟨Or.inl rfl, rfl⟩

lemma price_type (v : Vault) (sd p : STAmount) (h : v.sharesToAssetsWithdraw sd false = .ok p) :
    p.mNumericType = v.numericType := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  · exact STAmount.zero_mNumericType _
  · exact STAmount.ofNumber_mNumericType _ _ _ _ ‹_›

/-- A fractional clamp of a zero priced amount never passes the `tecPRECISION_LOSS` guard. -/
lemma frac_zero_contra (A : Number) (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (p rec : STAmount)
    (hz : p.mValue = 0) (hfr : p.mNumericType = .fractional)
    (hcl : clampToSumExponent A p.operator_neg = .ok rec)
    (hfnp : rec.isFractionalNonPositive = .ok false) : False := by
  have hfc : STAmount.FracCanonZero p := ⟨hfr, Or.inr hz⟩
  have hrc := WdAcc.clamp_frac_shape A p.operator_neg rec (STAmount.operator_neg_fczr p hfc) hcl
  have hrint : rec.integral = false := by
    show rec.mNumericType.isIntegral = false; rw [hrc.1]; rfl
  obtain ⟨hrm, hrn⟩ := STAmount.fnp_false_pos rec hrint hfnp
  have hid : p.operator_neg = p := by unfold STAmount.operator_neg; simp [hz]
  have hpint : p.integral = false := by show p.mNumericType.isIntegral = false; rw [hfr]; rfl
  rcases hn : p.mIsNegative with _ | _
  · rw [hid] at hcl
    have h1 := clampToSumExponent_sum_zero_nonpos A p rec hA hA0 hz hpint hn hcl
    have h2 : 0 < rec.toRat := by
      rw [STAmount.toRat_of_nonneg rec hrn]
      have : (0 : ℚ) < rec.mValue.toNat := by
        have : rec.mValue.toNat ≠ 0 := fun h0 => hrm (by
          apply UInt64.toNat_inj.mp; rw [h0]; rfl)
        exact_mod_cast Nat.pos_of_ne_zero this
      positivity
    linarith
  · exact hrm (clampToSumExponent_neg_zero A p rec hz (by rw [hid]; exact hn) hcl)

lemma sign_false_of_nonneg (s : STAmount) (h0 : 0 ≤ s.toRat) (hm : s.mValue ≠ 0) :
    s.mIsNegative = false := by
  rcases h : s.mIsNegative with _ | _
  · rfl
  · exfalso
    have h1 := STAmount.toRat_nonpos_of s h
    have h2 : s.toRat ≠ 0 := fun h' => hm ((STAmount.toRat_eq_zero_iff s).mp h')
    exact h2 (le_antisymm h1 h0)

/-- On an integral vault the clamp leaves a nonnegative priced amount unchanged. -/
lemma integral_clamp_eq (v : Vault) (hint : v.numericType.isIntegral = true) (sd p rec : STAmount)
    (hpr : v.sharesToAssetsWithdraw sd false = .ok p) (hp0 : 0 ≤ p.toRat)
    (hcl : clampToSumExponent v.assetsTotal p.operator_neg = .ok rec) :
    rec.toRat = p.toRat ∧ rec.exponent = 0 ∧ p.exponent = 0 ∧ rec.mValue = p.mValue := by
  obtain ⟨hnt, hoff, -⟩ := WdAcc.price_integral_shape v sd p false hint hpr
  obtain ⟨-, hroff, hrval, hrv, -⟩ :=
    ClwAcc.clamp_neg_integral v.assetsTotal p rec (hnt ▸ hint) hoff hcl
  refine ⟨?_, hroff, hoff, hrval⟩
  rw [hrv]
  by_cases hm : p.mValue = 0
  · rw [(STAmount.toRat_eq_zero_iff p).mpr hm, hm]; rfl
  · rw [STAmount.toRat_of_nonneg_offset_zero p (sign_false_of_nonneg p hp0 hm) hoff]

end XRPL.Model.SingleAssetVault.ClwTight
