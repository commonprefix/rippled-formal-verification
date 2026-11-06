import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout
import XRPL.Properties.Vault.Proofs.Support.WithdrawExchange
import XRPL.Properties.Vault.Common.ClawbackDefs

/-! # `computeClawback`

The shares a clawback destroys are a nonnegative canonical MPT amount, and the assets it recovers
are canonical or zero and covered by the cash, on every path of its pricing. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The shares a clawback request names are a nonnegative canonical MPT amount: the share total,
the holder's balance, or the shares the assets are worth. -/
private lemma assetsToSharesClawback_form (v : Vault) (assets holderShares shares : STAmount) (waive : Bool)
    (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat) (hhs : holderShares.ShareBalance)
    (hok : assetsToSharesClawback v assets holderShares waive = .ok shares) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 ∧ 0 ≤ shares.toRat := by
  simp only [assetsToSharesClawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  -- the share total
  · obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) ‹_›
    exact ⟨hic, hty, STAmount.ofNumber_nonneg _ _ _ _ v.wf.sharesTotal_norm
      (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) ‹_›⟩
  -- the holder's balance
  · exact ⟨(hhs.canonical.1 (by simp only [STAmount.integral, hhs.int64]; decide)).1, hhs.int64,
      STAmount.toRat_nonneg_of _ hhs.nonneg⟩
  -- the shares the assets are worth
  · obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ‹_›
    exact ⟨hic, hty, assetsToSharesWithdraw_nonneg v _ _ waive hc hnn ‹_›⟩

/-- The pricing of a clawback destroys a nonnegative canonical MPT amount of shares and
recovers a canonical-or-zero amount between zero and the cash. -/
lemma Vault.ClawbackPriced.form {v : Vault} {assets holderShares : STAmount} {waive : Bool}
    {shares recovered : STAmount}
    (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 ∧ 0 ≤ shares.toRat ∧
      recovered.CanonicalOrZero ∧ 0 ≤ recovered.toRat ∧ recovered.toRat ≤ v.assetsAvailable.toRat := by
  -- the shares' price stays within the cash once compared with it
  have hcap : ∀ (sd ar : STAmount) (n : Number), sd.IntegralCanonical → sd.mNumericType = .int64 →
      0 ≤ sd.toRat → v.sharesToAssetsWithdraw sd waive = .ok ar → ar.toNumber .to_nearest = .ok n →
      n.operator_gt v.assetsAvailable = false →
      ar.CanonicalOrZero ∧ 0 ≤ ar.toRat ∧ ar.toRat ≤ v.assetsAvailable.toRat := by
    intro sd ar n hic hty h0 hs2a hn hgt
    have har := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
    have hsdc : sd.CanonicalOrZero := Or.inl (hic.canonical (by rw [hty]; decide))
    obtain ⟨hv, hnorm⟩ := har.toNumber_exact n hn
    have hle : ¬ v.assetsAvailable.toRat < n.toRat := by
      rw [← operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm]
      simpa [Number.operator_gt] using hgt
    exact ⟨har, Vault.sharesToAssetsWithdraw_nonneg v _ _ waive hsdc h0 hs2a, by rw [← hv]; linarith⟩
  cases hpr with
  | direct _ _ n ha2s hs2a hn hgt =>
    obtain ⟨hic, hty, h0⟩ := assetsToSharesClawback_form v _ _ _ waive hc hnn hhs ha2s
    exact ⟨hic, hty, h0, hcap _ _ n hic hty h0 hs2a hn hgt⟩
  | capped _ _ cash _ _ _ n _ _ _ _ hcash ha2s hs2a hn hgt =>
    have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
    have hc0 := STAmount.ofNumber_nonneg _ _ _ _ v.wf.assetsAvailable_norm
      (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg) hcash
    obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ha2s
    have h0 := assetsToSharesWithdraw_nonneg v _ _ waive hcc hc0 ha2s
    exact ⟨hic, hty, h0, hcap _ _ n hic hty h0 hs2a hn hgt⟩

/-- A successful clawback pricing, read off the code: the priced shares and recovery, the
obligations check passed, and the recovery clamped onto the grid of the cash unless it is zero. -/
lemma computeClawback_success_reduces (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (amounts : VaultAmounts)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts)) :
    ∃ recovered sharesTotalAmount : STAmount,
      v.ClawbackPriced assets holderShares waive amounts.shares recovered ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      (amounts.shares.operator_eq sharesTotalAmount && v.assetsDeployed.operator_ne Number.zero) = false ∧
      ((recovered.isZero = true ∧ amounts.assets = recovered) ∨
        (recovered.isZero = false ∧
          clampToSumExponent v.assetsAvailable recovered.operator_neg v.baseExponent = .ok amounts.assets ∧
          amounts.assets.isFractionalNonPositive = .ok false)) := by
  simp only [computeClawback] at hcomp
  unfold_ter at hcomp
  walk_ok
  all_goals simp only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false] at *
  all_goals subst_vars
  all_goals first
    | exact ⟨_, _, .capped _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›, ‹_›, ‹_›,
        Or.inr ⟨‹_›, ‹_›, ‹_›⟩⟩
    | exact ⟨_, _, .capped _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›, ‹_›, ‹_›,
        Or.inl ⟨‹_›, rfl⟩⟩
    | exact ⟨_, _, .direct _ _ _ ‹_› ‹_› ‹_› ‹_›, ‹_›, ‹_›,
        Or.inr ⟨‹_›, ‹_›, ‹_›⟩⟩
    | exact ⟨_, _, .direct _ _ _ ‹_› ‹_› ‹_› ‹_›, ‹_›, ‹_›, Or.inl ⟨‹_›, rfl⟩⟩

/-- What a clawback destroys and recovers: a nonnegative canonical MPT amount of shares, and a
canonical-or-zero recovery the cash covers. -/
lemma computeClawback_amounts_form (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (amounts : VaultAmounts)
    (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts)) :
    amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧ 0 ≤ amounts.shares.toRat ∧
      amounts.assets.CanonicalOrZero ∧ 0 ≤ v.assetsAvailable.toRat + amounts.assets.operator_neg.toRat := by
  obtain ⟨_, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  obtain ⟨hic, hty, h0, hrc, hr0, hrle⟩ := hpr.form hc hnn hhs hmax
  refine ⟨hic, hty, h0, ?_⟩
  rcases hrec with ⟨-, heq⟩ | ⟨-, hcl, -⟩
  · rw [heq, STAmount.operator_neg_toRat]
    exact ⟨hrc, by linarith⟩
  · have hcf := clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    have hle := clampToSumExponent_le_abs _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0] at hle
    rw [STAmount.operator_neg_toRat]
    exact ⟨hcf.1, by linarith⟩

/-- The clawback pricing rejects with `tecINTERNAL`, `tecHAS_OBLIGATIONS`, `tecPRECISION_LOSS`, or
`tecPATH_DRY` for an overflow. -/
lemma computeClawback_codes (v : Vault) (assets holderShares : STAmount) (waive : Bool) (ter : TER)
    (h : (computeClawback v assets holderShares waive).run = .ok (.error ter)) :
    ter = .tecINTERNAL ∨ ter = .tecHAS_OBLIGATIONS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY := by
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals simp

end XRPL.Model.SingleAssetVault
