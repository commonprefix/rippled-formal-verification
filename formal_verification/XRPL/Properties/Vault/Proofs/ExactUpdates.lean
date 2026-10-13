import XRPL.Properties.Vault.Proofs.ExactUpdates.Steps
import XRPL.Properties.Vault.Proofs.ExactUpdates.ClawbackWalk
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Reduce
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Burn
import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Proofs.ClawbackAccuracy

/-! # Exact stored-total updates of `Vault.withdraw` and `Vault.clawback`

The clamp puts the payout on a grid of the post-subtraction total, so both stored
asset fields decrease by exactly the reported amount. -/

namespace XRPL.Model.SingleAssetVault.Exact

open XRPL.Model.Protocol

/-- The clamped payout of a nonnegative priced amount `p ≤ assetsTotal`: nonnegative,
at most `p`, and gridded near the post-subtraction total. -/
lemma clamp_payout (v : Vault) (p a : STAmount)
    (hp0 : 0 ≤ p.toRat) (hpnt : p.mNumericType = v.numericType)
    (hpc : v.numericType.isIntegral = false → p.mValue ≠ 0 → p.IOUCanonical)
    (hpoff : v.numericType.isIntegral = true → p.mOffset = 0)
    (hpT : p.toRat ≤ v.assetsTotal.toRat)
    (hTfit : v.numericType.isIntegral = true → v.assetsTotal.toRat < 2 ^ 63)
    (hcl : clampToSumExponent v.assetsTotal p.operator_neg = .ok a)
    (hfnp : a.isFractionalNonPositive = .ok false) :
    0 ≤ a.toRat ∧ a.toRat ≤ p.toRat ∧ GridNear v.assetsTotal a.toRat := by
  have hT := v.wf.assetsTotal_norm
  have hT0 : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨ha, hg⟩ := clamp_grid_int v.assetsTotal p a
      (show p.mNumericType.isIntegral = true by rw [hpnt]; exact hint) (hpoff hint) hp0
      (hTfit hint) hcl
    exact ⟨ha ▸ hp0, ha.le, hg⟩
  have hint' : v.numericType.isIntegral = false := by simpa using hint
  have hpfr : p.mNumericType = .fractional := by
    rw [hpnt]; cases h : v.numericType with
    | fractional => rfl
    | integral => rw [h] at hint'; simp [NumericType.isIntegral] at hint'
  have hpf : STAmount.FracCanonZero p := ⟨hpfr, by
    by_cases hz : p.mValue = 0
    · exact Or.inr hz
    · exact Or.inl (hpc hint' hz)⟩
  have haf := WdAcc.clamp_frac_shape _ _ _ (STAmount.operator_neg_fczr _ hpf) hcl
  have haint : a.integral = false := by
    show a.mNumericType.isIntegral = false; rw [haf.1]; rfl
  obtain ⟨ham, haneg⟩ := STAmount.fnp_false_pos a haint hfnp
  have hapos : 0 < a.toRat := WdMono.pos_of_nonneg a (STAmount.toRat_nonneg_of a haneg) ham
  have hpz : p.mValue ≠ 0 := by
    intro hz
    have hid : p.operator_neg = p := by unfold STAmount.operator_neg; simp [hz]
    cases hn : p.mIsNegative
    · have hpint : p.operator_neg.integral = false := by
        rw [hid]; show p.mNumericType.isIntegral = false; rw [hpfr]; rfl
      have := clampToSumExponent_sum_zero_nonpos v.assetsTotal p.operator_neg a hT hT0
        (by rw [hid]; exact hz) hpint (by rw [hid]; exact hn) hcl
      linarith
    · exact ham (clampToSumExponent_neg_zero v.assetsTotal p a hz
        (by rw [hid]; exact hn) hcl)
  exact clamp_grid_frac v.assetsTotal p a hT (hpc hint' hpz)
    (WdMono.pos_of_nonneg p hp0 hpz) hpT ham hcl

/-- An offset-`0` `int64` amount within `maxRep` is canonical. -/
lemma int64_canonical (s : STAmount) (hnt : s.mNumericType = .int64) (hoff : s.mOffset = 0)
    (hval : s.mValue.toNat ≤ maxRep.toNat) : s.Canonical := by
  have hint : s.mNumericType.isIntegral = true := by rw [hnt]; rfl
  have hmax : NumericType.int64.maxValue.toNat = maxRep.toNat := by decide
  refine ⟨fun _ => ⟨⟨hint, hoff, by rw [hnt, hmax]; exact hval⟩, by rw [hnt, hmax]⟩, fun h => ?_⟩
  exact absurd hint (by rw [show s.mNumericType.isIntegral = s.integral from rfl, h]; decide)

end XRPL.Model.SingleAssetVault.Exact

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Both stored asset fields of a non-final withdrawal are the old value minus the
recorded payout, exactly; the share total likewise when it fits `int64`. -/
lemma Vault.withdraw_vault_updates_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat)
    (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assets'.toRat ∧
    ((v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      r.vault'.sharesTotal.toRat = (v.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat) := by
  obtain ⟨cw, an, sta, hcomp, hcerr, han, hlt, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hpos hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rcases hcase with ⟨hf, -⟩ | ⟨-, an', sbn, at', atr, -, av', st', hcl, hfnp, han', hsbn, hat,
    hatr, -, -, hav, hsub, hrv⟩
  · rw [hsb, hf] at hfin; exact absurd hfin (by decide)
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp hcerr
  rw [hsb] at hnn hc hSnt
  rw [hsb]
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  obtain ⟨hp0, hpnt, hpc, hpx⟩ := Exact.price_facts v waiveUnrealizedLoss _ _
    (fun sn' h => by obtain rfl := Except.ok.inj (hsn.symm.trans h); exact ⟨hsnn, hsnv⟩) hnn hp
  obtain ⟨hann, hanv⟩ := hpx an han
  have hvx := v.exact
  have hpA : cw.assets'.toRat ≤ v.assetsAvailable.toRat := by
    rw [← hanv]
    by_contra h
    rw [not_le] at h
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hann).mpr h] at hlt
    exact absurd hlt (by decide)
  have hAT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := hvx.assetsAvailable_le
  have hT0 : 0 ≤ v.assetsTotal.toRat := hvx.assetsTotal_nonneg
  obtain ⟨ha0, hap, hg⟩ := Exact.clamp_payout v cw.assets' r.assets' hp0 hpnt hpc
    (fun hint => (WdAcc.price_integral_shape v _ _ _ hint hp).2.1) (le_trans hpA hAT)
    (fun hint => Exact.total_fit _ hint _ atr v.wf.assetsTotal_norm hT0 hatr) hcl hfnp
  obtain ⟨hann', hanv'⟩ := WdAcc.payout_toNumber v _ _ _ waiveUnrealizedLoss an' hc hp hcl han'
  obtain ⟨h1, h2⟩ := Exact.updates_exact _ _ _ _ _ r.assets'.toRat v.wf.assetsTotal_norm
    v.wf.assetsAvailable_norm hAT hann' hanv' ha0 (le_trans hap hpA) hg hat hav
  have hTeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  have hAeq : r.vault'.assetsAvailable = av' := congrArg RawVault.assetsAvailable hrv
  have hSeq : r.vault'.sharesTotal = st' := congrArg RawVault.sharesTotal hrv
  refine ⟨by rw [hTeq]; exact h1, by rw [hAeq]; exact h2, fun hfit => ?_⟩
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal _ v.wf
  rw [hSeq, hST]
  exact WdAcc.sub_burn_exact v.sharesTotal sbn st' _ v.wf.sharesTotal_norm
    v.wf.sharesTotal_nonneg v.wf.sharesTotal_int (by rw [← hST]; exact hfit) hnn hc hSnt hsbn hsub

/-- Both stored asset fields of a successful clawback are the old value minus the
recorded recovery, exactly; the share total likewise when it fits `int64`. -/
lemma Vault.clawback_vault_updates_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat ∧
    (r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) ∧
        (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) := by
  obtain ⟨cr, sdn, arn, at', atr, av', st', hcomp, hcerr, hra, hsd, hsdn, harn, hat, hatr, hav,
    hsub, hvt, hva, hvs⟩ := Exact.clawback_ok_cases v assets holderShares r hnn hok herr
  obtain ⟨X, priced, prn, hX, hsh, hpr, hprn, hgt, hcl, hfnp⟩ :=
    Exact.computeClawback_facts v assets holderShares cr hznz hcomp hcerr
  rw [hra, hsd]
  have hvx := v.exact
  have hA0 : 0 ≤ v.assetsAvailable.toRat := hvx.assetsAvailable_nonneg
  have hAT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := hvx.assetsAvailable_le
  have hT0 : 0 ≤ v.assetsTotal.toRat := hvx.assetsTotal_nonneg
  obtain ⟨hsnt, hsoff, hsval⟩ := ClwAcc.shares_shape v X _ hsh
  have hsc := Exact.int64_canonical _ hsnt hsoff hsval
  have hsd0 : 0 ≤ cr.sharesDestroyed.toRat := by
    refine Exact.shares_nonneg v X _ false (fun xn hxn => ?_) hsh
    rcases hX with rfl | hX
    · obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
        (STAmount.Canonical.exactCanonical _ hc)
      obtain rfl := Except.ok.inj (hsn.symm.trans hxn)
      exact ⟨hsnn, by rw [hsnv]; exact hnn⟩
    · obtain ⟨hX0, -, -, hXx⟩ := WdMono.ofNumber_facts v.numericType _ X
        v.wf.assetsAvailable_norm hA0 hX
      obtain ⟨hxnn, hxnv⟩ := hXx xn hxn
      exact ⟨hxnn, by rw [hxnv]; exact hX0⟩
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
    (STAmount.Canonical.exactCanonical _ hsc)
  obtain ⟨hp0, hpnt, hpc, hpx⟩ := Exact.price_facts v false _ _
    (fun sn' h => by obtain rfl := Except.ok.inj (hsn.symm.trans h); exact ⟨hsnn, hsnv⟩) hsd0 hpr
  obtain ⟨hprnn, hprnv⟩ := hpx prn hprn
  have hpA : priced.toRat ≤ v.assetsAvailable.toRat := by
    rw [← hprnv]
    by_contra h
    rw [not_le] at h
    rw [(operator_gt_iff _ _ hprnn v.wf.assetsAvailable_norm).mpr h] at hgt
    exact absurd hgt (by decide)
  obtain ⟨ha0, hap, hg⟩ := Exact.clamp_payout v priced cr.assetsRecovered hp0 hpnt hpc
    (fun hint => (WdAcc.price_integral_shape v _ _ _ hint hpr).2.1) (le_trans hpA hAT)
    (fun hint => Exact.total_fit _ hint _ atr v.wf.assetsTotal_norm hT0 hatr) hcl hfnp
  obtain ⟨hann', hanv'⟩ := WdAcc.payout_toNumber v _ _ _ false arn hsc hpr hcl harn
  obtain ⟨h1, h2⟩ := Exact.updates_exact _ _ _ _ _ cr.assetsRecovered.toRat v.wf.assetsTotal_norm
    v.wf.assetsAvailable_norm hAT hann' hanv' ha0 (le_trans hap hpA) hg hat hav
  refine ⟨by rw [hvt]; exact h1, by rw [hva]; exact h2, fun hfit => ?_⟩
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal _ v.wf
  rw [RawVault.WF.toExact_sharesTotal _ r.vault'.wf, hvs, hST]
  exact WdAcc.sub_burn_exact v.sharesTotal sdn st' _ v.wf.sharesTotal_norm
    v.wf.sharesTotal_nonneg v.wf.sharesTotal_int (by rw [← hST]; exact hfit.2) hsd0 hsc hsnt hsdn hsub

end XRPL.Model.SingleAssetVault
