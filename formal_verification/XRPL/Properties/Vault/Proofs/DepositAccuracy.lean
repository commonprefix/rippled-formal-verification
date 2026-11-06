import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Proofs.DepositRounding

/-! # `Vault.deposit` accuracy proofs -/

namespace XRPL.Model.SingleAssetVault.DepAcc

open XRPL.Model.Protocol

/-- A successful deposit, step by step. The amount rounds to a canonical positive amount, the shares are
priced from it as a positive `int64` count, and the charge is those shares re-priced and clamped to the total's grid. -/
lemma Vault.deposit_success_reduces (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    ∃ (roundedAmount priced : STAmount) (navN : Number),
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      roundedAmount.Canonical ∧ 0 < roundedAmount.toRat ∧
      assetsToSharesDeposit v roundedAmount = .ok r.shares ∧ r.shares.isZero = false ∧
      r.shares.IntegralCanonical ∧ r.shares.mNumericType = .int64 ∧ 0 < r.shares.toRat ∧
      sharesToAssetsDeposit v r.shares = .ok priced ∧ priced.operator_gt roundedAmount = .ok false ∧
      v.assetsTotal = .ok navN ∧
      clampToSumExponent navN priced v.baseExponent = .ok r.assets ∧
      r.assets.isFractionalNonPositive = .ok false := by
  obtain ⟨ra, amounts, -, hra, hcd, -, -, -, hassets, hshares⟩ :=
    Vault.deposit_ok_reduces v amountDeposit false t hpos r hok
  obtain ⟨priced, navN, hats, hz, hsad, hgt, hat, hcl, hfnp⟩ := computeDeposit_success_reduces v ra amounts hcd
  obtain ⟨hrc, hrp⟩ := DepRnd.Vault.roundedDepositAmount_canonical_pos v amountDeposit ra hcanon hra
  rw [← hshares] at hats hz hsad
  rw [← hassets] at hcl hfnp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v ra r.shares hats
  exact ⟨ra, priced, navN, hra, hrc, hrp, hats, hz, hshc, hshnt,
    assetsToSharesDeposit_pos v ra r.shares hrc hrp hats hz, hsad, hgt, hat, hcl, hfnp⟩

/-- The priced charge never exceeds the rounded amount. The deposit computation rejects a
charge above it, and comparing two canonical amounts of one asset compares their values. -/
lemma Vault.deposit_priced_le (v : Vault) (shares priced roundedAmount : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hrc : roundedAmount.Canonical) (hrp : 0 < roundedAmount.toRat)
    (hgt : priced.operator_gt roundedAmount = .ok false) :
    priced.toRat ≤ roundedAmount.toRat ∧ priced.mNumericType = roundedAmount.mNumericType := by
  have hcmp : STAmount.areComparable priced roundedAmount = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; rw [STAmount.areComparable_comm]; simpa using hcond
  have hty : priced.mNumericType = roundedAmount.mNumericType := by
    unfold STAmount.areComparable at hcmp; exact beq_iff_eq.mp hcmp
  refine ⟨?_, hty⟩
  have hrmv : roundedAmount.mValue ≠ 0 := fun h =>
    absurd ((STAmount.toRat_eq_zero_iff _).mpr h) (ne_of_gt hrp)
  rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares priced hshc hshnt hsad with hexact | h0
  · have hpmv : priced.mValue ≠ 0 ∨ priced.mValue = 0 := ne_or_eq _ _
    rcases hpmv with hpmv | hpmv
    · exact STAmount.operator_gt_false_le priced roundedAmount
        (STAmount.CmpFaithful.ofExactCanonical priced roundedAmount hexact
          (STAmount.Canonical.exactCanonical roundedAmount hrc) hcmp (fun h => absurd h hpmv)
          (fun h => absurd h hrmv)) hgt
    · rw [(STAmount.toRat_eq_zero_iff _).mpr hpmv]; exact hrp.le
  · rw [(STAmount.toRat_eq_zero_iff _).mpr h0]; exact hrp.le

end XRPL.Model.SingleAssetVault.DepAcc

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- Deposit shares are monotone in the rounded amount. The exact `⌊amount · 10^scale⌋` map of an empty
vault and the pricing chain, truncation and integral conversion of a nonempty one are each monotone. -/
lemma Vault.deposit_shares_monotone_proof (v : Vault)
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount) (t₁ t₂ : UInt32)
    (hcanon₁ : amountDeposit₁.Canonical) (hcanon₂ : amountDeposit₂.Canonical)
    (hpos₁ : 0 < amountDeposit₁.toRat) (hpos₂ : 0 < amountDeposit₂.toRat)
    (hrounded₁ : (v.roundedDepositAmount amountDeposit₁).run = .ok (.ok roundedAmount₁))
    (hrounded₂ : (v.roundedDepositAmount amountDeposit₂).run = .ok (.ok roundedAmount₂))
    (r₁ r₂ : VaultWithAmounts)
    (hok₁ : (v.deposit amountDeposit₁ false t₁ hpos₁).run = .ok (.ok r₁))
    (hok₂ : (v.deposit amountDeposit₂ false t₂ hpos₂).run = .ok (.ok r₂))
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    r₁.shares.toRat ≤ r₂.shares.toRat := by
  obtain ⟨ra₁, -, -, hra₁, hc₁, hp₁, hats₁, hz₁, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit₁ t₁ hpos₁ hcanon₁ r₁ hok₁
  obtain ⟨ra₂, -, -, hra₂, hc₂, hp₂, hats₂, hz₂, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit₂ t₂ hpos₂ hcanon₂ r₂ hok₂
  rw [hrounded₁, Except.ok.injEq, Except.ok.injEq] at hra₁
  rw [hrounded₂, Except.ok.injEq, Except.ok.injEq] at hra₂
  subst hra₁ hra₂
  exact assetsToSharesDeposit_mono v roundedAmount₁ roundedAmount₂ r₁.shares r₂.shares hc₁ hp₁ hc₂ hp₂
    hats₁ hz₁ hats₂ hz₂ hle

end XRPL.Model.SingleAssetVault
