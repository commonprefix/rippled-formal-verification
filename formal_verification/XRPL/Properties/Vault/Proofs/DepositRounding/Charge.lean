import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Proofs.Support.DepositPricing

/-! # Deposit charge

The rounded deposit amount is canonical and positive, and the recorded charge sits between zero and
the priced one. -/

namespace XRPL.Model.SingleAssetVault.DepRnd

open XRPL.Model.Protocol

/-- A canonical request that rounds (rather than being rejected) rounds to a canonical positive
amount: a successful rounding is never zero. -/
lemma Vault.roundedDepositAmount_canonical_pos (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.Canonical)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount)) :
    roundedAmount.Canonical ∧ 0 < roundedAmount.toRat := by
  obtain ⟨assetsTotal, -, hcl, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  obtain ⟨hc, -, hnn⟩ := clampToSumExponent_canonicalOrZero assetsTotal amountDeposit roundedAmount
    v.baseExponent (Or.inl hcanon) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hmv : roundedAmount.mValue ≠ 0 := (STAmount.isZero_eq_false_iff _).mp hnz
  exact ⟨hc.resolve_right (by simp [hnz]),
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero roundedAmount hmv))⟩

/-- The recorded deposit charge is nonnegative and never exceeds the priced one. On an integral
vault the clamp is the identity. On a fractional one it snaps the charge down onto the post-sum grid. -/
lemma Vault.deposit_charge_bounds (v : Vault) (shares priced c : STAmount) (navN : Number)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent navN priced v.baseExponent = .ok c) :
    0 ≤ c.toRat ∧ c.toRat ≤ priced.toRat := by
  have hpnn : 0 ≤ priced.toRat := sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v shares priced hsad
  by_cases hint : v.numericType.isIntegral = true
  · rw [clampToSumExponent_integral_nonneg navN priced c v.baseExponent
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl]
    exact ⟨hpnn, le_refl _⟩
  have hpfrac : priced.integral = false := by
    show priced.mNumericType.isIntegral = false; rw [hpnt]; simpa using hint
  have hpc : priced.CanonicalOrZero := by
    rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares priced hshc hshnt hsad with h | h
    · exact Or.inl ⟨fun hi => absurd (hpfrac.symm.trans hi) (by decide), fun _ => h.iouCanonical hpfrac⟩
    · exact Or.inr (by simp [STAmount.isZero, h])
  have hle := clampToSumExponent_le_abs navN priced c v.baseExponent hpc v.baseExponent_range.1
    v.baseExponent_range.2 hcl
  rw [abs_of_nonneg hpnn] at hle
  exact ⟨(clampToSumExponent_canonicalOrZero navN priced c v.baseExponent hpc v.baseExponent_range.1
    v.baseExponent_range.2 hcl).2.2, hle⟩

/-- The recorded deposit charge never exceeds the priced one. -/
lemma Vault.deposit_charge_le (v : Vault) (shares priced c : STAmount) (navN : Number)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent navN priced v.baseExponent = .ok c) :
    c.toRat ≤ priced.toRat :=
  (Vault.deposit_charge_bounds v shares priced c navN hshc hshnt hshpos hsad hcl).2

end XRPL.Model.SingleAssetVault.DepRnd
