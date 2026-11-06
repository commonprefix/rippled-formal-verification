import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Protocol.STAmount.Compare.Common.Proofs
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.Support.Basic
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.VaultBalances

/-! # `Vault.canBurnShares` / `Vault.burnShares` proofs

Proof bodies behind `VaultBurn.lean` and `VaultBurnReturn.lean`. Burning reads and
writes only `sharesTotal`, so nothing here prices, rounds an asset amount or
clamps. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A burn the vault allows, read off the code: the vault is insolvent, the amount names the
holder's whole balance or nothing, and the result is the share total as an MPT amount. -/
lemma Vault.canBurnShares_ok_reduces (v : Vault) (amount holderShares sharesTotalAmount : STAmount)
    (hok : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) :
    v.isInsolvent = true ∧ (!amount.isZero && !(amount.operator_eq holderShares)) = false ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount := by
  simp only [Vault.canBurnShares] at hok
  unfold_ter at hok
  walk_ok
  exact ⟨by simpa using (‹¬ (!v.isInsolvent) = true›), Bool.eq_false_iff.mpr ‹_›, ‹_›⟩

/-- A successful burn, read off the code: it destroys a nonzero amount and stores the share
total less that amount, re-checked by `to_lawful`. -/
lemma Vault.burnShares_ok_reduces (v : Vault) (sharesDestroyed : STAmount) (v' : Vault)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v')) :
    sharesDestroyed.isZero = false ∧ ∃ sharesDestroyedNumber st' : Number,
      sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber ∧
      v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } := by
  simp only [Vault.burnShares] at hok
  unfold_ter at hok
  walk_ok
  exact ⟨Bool.eq_false_iff.mpr ‹_›, _, _, ‹_›, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩

/-- The burn subtracts exactly: a canonical nonnegative amount of shares up to the share total
leaves the exact whole-number difference. -/
private lemma Vault.burn_sub_exact (v : Vault) (sharesDestroyed : STAmount) (sharesDestroyedNumber st' : Number)
    (hcanon : sharesDestroyed.IntegralCanonical) (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ v.sharesTotal.toRat)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st') :
    st'.toRat = v.sharesTotal.toRat - sharesDestroyed.toRat ∧ st'.toRat.den = 1 ∧ st'.isNormalized := by
  have hfit := v.sharesTotal_le_maxRep
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hsd_val : sharesDestroyed.toRat = ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) := by
      rw [STAmount.IntegralCanonical.toRat_eq_signedDrops sharesDestroyed hcanon]
      unfold STAmount.signedDrops
      rw [show sharesDestroyed.mIsNegative = false from hnn]
      simp only [Bool.false_eq_true, if_false]
      norm_cast
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [← hsd_val]
      exact le_trans hle (le_trans hfit (by norm_num))
    exact_mod_cast h1
  obtain ⟨sdn, hsdn_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  obtain rfl : sdn = sharesDestroyedNumber := Except.ok.inj (hsdn_ok.symm.trans hnum)
  -- the subtraction of two whole numbers below `2^63`
  have hxq := Rat.coe_int_num_of_den_eq_one v.wf.sharesTotal_int
  have hyq := Rat.coe_int_num_of_den_eq_one (q := sdn.toRat) (by rw [hsdn_val]; exact hsd_den)
  have hdiff : v.sharesTotal.toRat - sdn.toRat
      = ((v.sharesTotal.toRat.num - sdn.toRat.num : ℤ) : ℚ) := by
    conv_lhs => rw [← hxq, ← hyq]
    push_cast; ring
  have hdiff_den : (v.sharesTotal.toRat - sdn.toRat).den = 1 := by
    rw [hdiff]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn.toRat := by rw [hsdn_val]; linarith
  have hdiff_le : v.sharesTotal.toRat - sdn.toRat ≤ 2 ^ 63 - 1 := by
    rw [hsdn_val]; linarith [STAmount.toRat_nonneg_of sharesDestroyed hnn]
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn st'
    v.wf.sharesTotal_norm hsdn_norm v.wf.sharesTotal_int
    (by rw [hsdn_val]; exact hsd_den)
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  exact ⟨by rw [hst_val, hsdn_val], hst_den,
    operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm hsdn_norm hst⟩

/-- The share total is a whole number below `2^63`, so its `int64` conversion is exact. -/
lemma Vault.canBurnShares_assets_exact_proof (v : Vault) (amount holderShares sharesTotalAmount : STAmount)
    (hok : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) :
    sharesTotalAmount.toRat = (v.toExact.sharesTotal : ℚ) := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨-, -, hofn⟩ := Vault.canBurnShares_ok_reduces v amount holderShares sharesTotalAmount hok
  obtain ⟨_, _, _, _, hval⟩ := STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest sharesTotalAmount
    v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg v.wf.sharesTotal_int v.sharesTotal_le_maxRep hofn
  rw [hval, ← hST]

/-- The burn subtracts two whole numbers below `2^63`, which `Number` does exactly. -/
lemma Vault.burnShares_sharesTotal_exact_proof (v : Vault) (sharesDestroyed : STAmount) (v' : Vault)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v'))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ)) :
    (v'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) - sharesDestroyed.toRat := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨-, n, st', hnum, hst, hv'⟩ := Vault.burnShares_ok_reduces v sharesDestroyed v' hok
  obtain ⟨hst_val, hst_den, -⟩ :=
    Vault.burn_sub_exact v sharesDestroyed n st' hcanon hnn (by rw [← hST]; exact hle) hnum hst
  have hst_nn : 0 ≤ st'.toRat := by
    rw [hst_val, ← hST]; linarith
  have hproj : (v'.toExact.sharesTotal : ℚ) = ((st'.toRat.num.toNat : ℕ) : ℚ) := by
    rw [hv']; rfl
  rw [hproj, rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn, hst_val, ← hST]

lemma Vault.canBurnShares_error_codes_proof (v : Vault) (amount holderShares : STAmount) (ter : TER)
    (hok : (v.canBurnShares amount holderShares).run = .ok (.error ter)) :
    ter = .tecNO_PERMISSION ∨ ter = .tecLIMIT_EXCEEDED := by
  simp only [Vault.canBurnShares] at hok
  unfold_ter at hok
  walk_ok
  all_goals simp

lemma Vault.canBurnShares_no_permission_proof (v : Vault) (amount holderShares : STAmount)
    (hsolvent : v.isInsolvent = false) :
    (v.canBurnShares amount holderShares).run = .ok (.error .tecNO_PERMISSION) := by
  simp only [Vault.canBurnShares]
  unfold_ter
  simp [hsolvent]

lemma Vault.canBurnShares_limit_exceeded_proof (v : Vault) (amount holderShares : STAmount)
    (hins : v.isInsolvent = true) (hpart : (!amount.isZero && !(amount.operator_eq holderShares)) = true) :
    (v.canBurnShares amount holderShares).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  simp only [Vault.canBurnShares]
  unfold_ter
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpart
  simp [hins, hpart]

lemma Vault.canBurnShares_ok_proof (v : Vault) (amount holderShares sharesTotalAmount : STAmount)
    (hins : v.isInsolvent = true) (hall : (!amount.isZero && !(amount.operator_eq holderShares)) = false)
    (hshares : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) := by
  have h : ¬ (amount.isZero = false ∧ amount.operator_eq holderShares = false) := by simpa using hall
  simp only [Vault.canBurnShares]
  unfold_ter
  simp [hins, h, hshares]

lemma Vault.burnShares_zero_shares_proof (v : Vault) (sharesDestroyed : STAmount)
    (hz : sharesDestroyed.isZero = true) :
    (v.burnShares sharesDestroyed).run = .ok (.error .tecPRECISION_LOSS) := by
  simp only [Vault.burnShares]
  unfold_ter
  simp [hz]

lemma Vault.burnShares_ok_proof (v : Vault) (amount holderShares sharesDestroyed sharesTotalAmount : STAmount)
    (sharesDestroyedNumber st' : Number)
    (hcan : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical) (hnn : sharesDestroyed.negative = false)
    (hnz : sharesDestroyed.isZero = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st') :
    ∃ v' : Vault, (v.burnShares sharesDestroyed).run = .ok (.ok v') ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨hins, -, -⟩ := Vault.canBurnShares_ok_reduces v amount holderShares sharesTotalAmount hcan
  have hle' : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by
    rw [← hST, ← Vault.canBurnShares_assets_exact_proof v amount holderShares sharesTotalAmount hcan]
    exact hle
  obtain ⟨hst_val, hst_den, hstn⟩ :=
    Vault.burn_sub_exact v sharesDestroyed sharesDestroyedNumber st' hcanon hnn hle' hnum hst
  have hsd0 := STAmount.toRat_nonneg_of sharesDestroyed hnn
  -- an insolvent vault holds no assets, so it stays lawful whatever shares remain
  have hm : (v.assetsAvailable.mantissa_ = 0 ∧ v.assetsDeployed.mantissa_ = 0) ∧ v.sharesTotal.signum = 1 := by
    simpa [Vault.isInsolvent] using hins
  have hAA : v.assetsAvailable = Number.zero :=
    Number.eq_zero_of_mantissa_zero _ v.wf.assetsAvailable_norm hm.1.1
  have hAD : v.assetsDeployed = Number.zero :=
    Number.eq_zero_of_mantissa_zero _ v.wf.assetsDeployed_norm hm.1.2
  have hlaw := Vault.cash_shares_update_lawful v v.assetsAvailable st' v.wf.assetsAvailable_norm
    v.exact.assetsAvailable_nonneg v.valid.assetsAvailable_representable v.valid.assetsAvailable_onGrid hstn
    (by rw [hst_val]; linarith) hst_den
    (by rw [hst_val]; linarith [v.sharesTotal_le_maxRep]) (fun _ => ⟨hAA, hAD⟩)
  obtain ⟨v', hl, hv'⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
  refine ⟨v', ?_, hv'⟩
  simp only [Vault.burnShares]
  unfold_ter
  simp [hnz, hnum, hst, hl]

end XRPL.Model.SingleAssetVault
