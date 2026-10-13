import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Proofs.Support.DepositPricing
import XRPL.Properties.Vault.Proofs.Support.RoundToVaultExponent

/-! # Deposit charge

The rounded deposit amount is canonical, the recorded charge never exceeds the priced one, and the
`assetsMaximum` guard stays silent under the cap. -/

set_option maxRecDepth 4000

namespace XRPL.Model.SingleAssetVault.DepRnd

open XRPL.Model.Protocol

/-- The rounded deposit amount from `roundedDepositAmount` is stored canonically
whenever the raw `amountDeposit` is: the `.rounded` outcome forbids the zero case. -/
lemma Vault.roundedDepositAmount_canonical (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.Canonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    roundedAmount.Canonical := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  rcases roundToVaultExponent_canonical_or_isZero amountDeposit roundedAmount v.assetsTotal
    hcanon hround with hc | hz
  · exact hc
  · rw [hz] at hnz; exact absurd hnz (by decide)

/-- A canonical positive request that rounds (rather than being rejected) rounds to a
canonical positive amount. -/
lemma Vault.roundedDepositAmount_canonical_pos (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    roundedAmount.Canonical ∧ 0 < roundedAmount.toRat := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hnn := RawVault.roundToVaultExponent_nonneg amountDeposit roundedAmount v.assetsTotal
    hcanon hpos.le hround
  have hmv : roundedAmount.mValue ≠ 0 := by
    intro h0; unfold STAmount.isZero at hnz; rw [h0] at hnz; exact absurd hnz (by decide)
  exact ⟨Vault.roundedDepositAmount_canonical v amountDeposit roundedAmount hcanon hrounded,
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero roundedAmount hmv))⟩

/-- **The `assetsMaximum` guard never fires when the exact sum stays under the
maximum.** The stored total rounds `assetsTotal + charge` to nearest, and a
normalized maximum the exact sum is under is never crossed by the rounding, so the
`operator_gt` guard reads `false`. -/
lemma deposit_maximum_guard_false (v : Vault) (cN at' : Number)
    (hcNnorm : cN.isNormalized)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hbound : ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + cN.toRat ≤ m.toRat) :
    ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false := by
  have hatnorm : at'.isNormalized := by
    by_cases h0 : at'.mantissa_ = 0
    · rw [Number.operator_add_zero_shape_sz v.assetsTotal cN at' v.wf.assetsTotal_norm hcNnorm hat h0]
      exact Or.inl rfl
    · exact operator_add_isNormalized_to_nearest v.assetsTotal cN at'
        v.wf.assetsTotal_norm hcNnorm hat h0
  cases hm : v.assetsMaximum with
  | none =>
    simp only [Option.getD_none]
    rw [show Number.zero.operator_ne Number.zero = false from by decide, Bool.false_and]
  | some m =>
    have hmem : m ∈ v.assetsMaximum := by rw [hm]; exact Option.mem_some_self m
    have hmnorm : m.isNormalized := v.wf.assetsMaximum_norm m hmem
    have hle : v.assetsTotal.toRat + cN.toRat ≤ m.toRat := hbound m hmem
    have hat_le : at'.toRat ≤ m.toRat :=
      operator_add_le_of_le_normalized v.assetsTotal cN at' m v.wf.assetsTotal_norm hcNnorm hat hmnorm hle
    have hgt_false : at'.operator_gt m = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      have := (operator_gt_iff at' m hatnorm hmnorm).mp h
      linarith
    simp only [Option.getD_some]
    rw [hgt_false, Bool.and_false]

/-- **The recorded deposit charge never exceeds the priced one.** On an integral
vault the clamp is the identity; on a fractional one it snaps the charge to the
post-sum total's grid, and every step of that snap rounds downward. -/
lemma Vault.deposit_charge_le (v : Vault) (shares priced c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent v.assetsTotal priced = .ok c) :
    c.toRat ≤ priced.toRat := by
  have hpnn : 0 ≤ priced.toRat := sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v shares priced hsad
  by_cases hint : v.numericType.isIntegral = true
  · rw [clampToSumExponent_integral_nonneg v.assetsTotal priced c
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl]
  have hpfrac : priced.integral = false := by
    show priced.mNumericType.isIntegral = false; rw [hpnt]; simpa using hint
  by_cases hbr : priced.negative = true
  · -- a set sign bit on a non-negative charge forces a zero, where the clamp is the identity
    have hpz : priced.mValue = 0 := by
      by_contra hz
      have := STAmount.toRat_neg_of priced hbr hz
      linarith
    have hid : priced.operator_neg = priced := by unfold STAmount.operator_neg; simp [hpz]
    have hcz : c.mValue = 0 :=
      clampToSumExponent_neg_zero v.assetsTotal priced c hpz (by rw [hid]; exact hbr)
        (by rw [hid]; exact hcl)
    rw [(STAmount.toRat_eq_zero_iff c).mpr hcz]; exact hpnn
  · refine clampToSumExponent_sum_le v.assetsTotal priced c v.wf.assetsTotal_norm
      v.exact.assetsTotal_nonneg ?_ hpnn hpfrac (by simpa using hbr) hcl
    by_cases hpz : priced.mValue = 0
    · exact Or.inr hpz
    · rcases sharesToAssetsDeposit_disj_canonical v shares priced hshc hshnt hsad hpz with h | h
      · exact Or.inl h
      · exfalso
        have := h.is_integral
        rw [hpnt] at this
        exact hint this

/-- **Charge-side bound for the limit guard.** On a real deposit the RECORDED
charge's `Number` never pushes `assetsTotal + charge` over a maximum the rounded
deposit already fits under. The clamp only ever lowers the charge
(`deposit_charge_le`), and the priced charge is itself at most the rounded amount;
an underflowed (zero) charge leaves the total at `assetsTotal`, which a lawful
vault keeps under its own maximum. -/
lemma deposit_real_charge_bound (v : Vault)
    (amount roundedAmount a sh rc : STAmount) (cN : Number)
    (hcanonR : roundedAmount.Canonical) (hnzR : roundedAmount.isZero = false)
    (hposR : 0 < roundedAmount.toRat)
    (hameq : amount = roundedAmount)
    (hcd : computeDeposit v amount = .ok (.success a sh))
    (hclamp : clampToSumExponent v.assetsTotal a = .ok rc)
    (hcN : rc.toNumber .to_nearest = .ok cN)
    (hmargin : ∀ m ∈ v.assetsMaximum, v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + cN.toRat ≤ m.toRat := by
  intro m hm
  obtain ⟨shares, hats, hshz, hsad, hgt, hseq⟩ := computeDeposit_success_reduces v amount a sh hcd
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amount shares (by rw [hameq]; exact hcanonR)
      (by rw [hameq]; exact hposR) hats hshz
  obtain ⟨hcNval, -⟩ :=
    Vault.deposit_charge_toNumber_facts v shares a rc cN hshc hshnt hshpos hsad hclamp hcN
  have hrc_le : rc.toRat ≤ a.toRat :=
    Vault.deposit_charge_le v shares a rc hshc hshnt hshpos hsad hclamp
  have hAeq : v.assetsTotal.toRat = v.toExact.assetsTotal := rfl
  -- the PRICED charge never exceeds the rounded deposit
  have ha_le : a.toRat ≤ roundedAmount.toRat := by
    by_cases ha0 : a.mValue = 0
    · rw [(STAmount.toRat_eq_zero_iff a).mpr ha0]; linarith
    have hcmp_ba : STAmount.areComparable amount a = true := by
      rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
      split at hgt
      · exact absurd hgt (by simp)
      · rename_i hcond; simpa using hcond
    have hcmp_ab : STAmount.areComparable a amount = true := by
      rw [STAmount.areComparable_comm]; exact hcmp_ba
    have hexact : a.ExactCanonical := by
      rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares a hshc hshnt hsad with h | h0
      · exact h
      · exact absurd h0 ha0
    have hexactAmt : amount.ExactCanonical := by
      rw [hameq]; exact STAmount.Canonical.exactCanonical roundedAmount hcanonR
    have hamt0 : amount.mValue ≠ 0 := by
      rw [hameq]; intro h; rw [STAmount.isZero, h] at hnzR; simp at hnzR
    have hcmpF : STAmount.CmpFaithful a amount :=
      STAmount.CmpFaithful.ofExactCanonical a amount hexact hexactAmt hcmp_ab
        (fun h => absurd h ha0) (fun h => absurd h hamt0)
    have hcharge_le : a.toRat ≤ amount.toRat :=
      computeDeposit_success_charge_le v amount a sh hcmpF hcd
    rw [hameq] at hcharge_le; exact hcharge_le
  rw [hcNval, hAeq]
  have := hmargin m hm
  linarith

end XRPL.Model.SingleAssetVault.DepRnd
