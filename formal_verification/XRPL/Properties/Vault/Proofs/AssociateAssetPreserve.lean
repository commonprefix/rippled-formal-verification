import XRPL.Properties.Vault.Proofs.AssociateAssetGrid
import XRPL.Properties.Vault.Proofs.ExactUpdates
import XRPL.Properties.Vault.Proofs.ClawbackTight.Reduce

/-! # Withdraw and clawback keep a fractional vault on the grid

Absent underflow of the stored asset fields below `10⁻⁸¹`. -/

namespace XRPL.Model.SingleAssetVault.CatHI

open XRPL.Model.Protocol

lemma clamp_sum_branch_zero (priced : STAmount) (hnn : 0 ≤ priced.toRat)
    (hbr : (priced.operator_neg).negative = false) : priced.mValue = 0 := by
  by_contra hz
  have hflip : (priced.operator_neg).mIsNegative = !priced.mIsNegative := by
    unfold STAmount.operator_neg; simp [hz]
  have : priced.mIsNegative = true := by
    unfold STAmount.negative at hbr; rw [hflip] at hbr; simpa using hbr
  have := STAmount.toRat_neg_of priced this hz
  linarith

/-- The clamp's negative branch really ran, and the priced payout is a positive
canonical IOU: the `tecPRECISION_LOSS` guard on the reported amount rules out both the
sum branch and a zero pricing. -/
lemma priced_pos_canonical (T : Number) (priced reported : STAmount)
    (hTnorm : T.isNormalized) (hTnn : 0 ≤ T.toRat)
    (hpfrac : priced.mNumericType = .fractional)
    (hpnn : 0 ≤ priced.toRat)
    (hdisj : priced.mValue ≠ 0 → priced.IOUCanonical)
    (hcl : clampToSumExponent T priced.operator_neg = .ok reported)
    (hfnp : reported.isFractionalNonPositive = .ok false) :
    priced.IOUCanonical ∧ priced.mIsNegative = false ∧ reported.mValue ≠ 0 := by
  have hpfcz : STAmount.FracCanonZero priced := ⟨hpfrac, by
    by_cases h : priced.mValue = 0
    · exact Or.inr h
    · exact Or.inl (hdisj h)⟩
  have hnegfrac : (priced.operator_neg).mNumericType = .fractional :=
    (STAmount.operator_neg_fczr priced hpfcz).1
  have hrfrac : reported.mNumericType = .fractional :=
    (WdAcc.clamp_frac_shape T hTnorm _ _ (STAmount.operator_neg_fczr priced hpfcz) hcl).1
  have hrint : reported.integral = false := by
    show reported.mNumericType.isIntegral = false; rw [hrfrac]; rfl
  obtain ⟨hrne, hrsgn⟩ := STAmount.fnp_false_pos reported hrint hfnp
  by_cases hbr : (priced.operator_neg).negative = true
  · have hpne : priced.mValue ≠ 0 := by
      intro hz
      exact hrne (clampToSumExponent_neg_zero T priced reported hz hbr hcl)
    have hflip : (priced.operator_neg).mIsNegative = !priced.mIsNegative := by
      unfold STAmount.operator_neg; simp [hpne]
    have hsgn : priced.mIsNegative = false := by
      unfold STAmount.negative at hbr; rw [hflip] at hbr; simpa using hbr
    exact ⟨hdisj hpne, hsgn, hrne⟩
  · exfalso
    rw [Bool.not_eq_true] at hbr
    have hpz : priced.mValue = 0 := clamp_sum_branch_zero priced hpnn hbr
    have hdz : (priced.operator_neg).mValue = 0 := by
      unfold STAmount.operator_neg; simp [hpz]
    have hdfrac : (priced.operator_neg).integral = false := by
      show (priced.operator_neg).mNumericType.isIntegral = false; rw [hnegfrac]; rfl
    have hnonpos := clampToSumExponent_sum_zero_nonpos T priced.operator_neg reported
      hTnorm hTnn hdz hdfrac hbr hcl
    have hpos : 0 < reported.toRat := by
      rw [STAmount.toRat_of_nonneg reported hrsgn]
      have : 0 < reported.mValue.toNat := by
        rcases Nat.eq_zero_or_pos reported.mValue.toNat with h | h
        · exact absurd (by exact UInt64.toNat_inj.mp (by simpa using h)) hrne
        · exact h
      have hq : (0 : ℚ) < (reported.mValue.toNat : ℚ) := by exact_mod_cast this
      positivity
    linarith

lemma Vault.not_assetsRounded_iff (v : Vault) :
    ¬ v.assetsRounded ↔
      STAmount.isRounded v.numericType v.assetsTotal = false ∧
      STAmount.isRounded v.numericType v.assetsAvailable = false ∧
      STAmount.isRounded v.numericType v.assetsReserved = false ∧
      STAmount.isRounded v.numericType v.lossUnrealized = false ∧
      ∀ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m = false := by
  unfold Vault.assetsRounded
  simp only [not_or, Bool.not_eq_true, not_exists, not_and]

/-- Nonnegative shares with exact `toNumber`, passing the funds guard, price to a positive
canonical fractional payout at most `assetsAvailable` whose clamp keeps the stored field on
the grid. -/
lemma field_on_grid (v : Vault) (hfr : v.numericType = .fractional) (w : Bool)
    (sd priced rep : STAmount) (prn repN X res : Number)
    (hs : ∀ sn, sd.toNumber .to_nearest = .ok sn → sn.isNormalized ∧ sn.toRat = sd.toRat)
    (hsnn : 0 ≤ sd.toRat)
    (hpr : v.sharesToAssetsWithdraw sd w = .ok priced)
    (hprn : priced.toNumber .to_nearest = .ok prn)
    (hle : prn.toRat ≤ v.assetsAvailable.toRat)
    (hcl : clampToSumExponent v.assetsTotal priced.operator_neg = .ok rep)
    (hfnp : rep.isFractionalNonPositive = .ok false)
    (hrepN : rep.toNumber .to_nearest = .ok repN)
    (hX : X = v.assetsTotal ∨ X = v.assetsAvailable)
    (hTgrid : STAmount.isRounded v.numericType v.assetsTotal = false)
    (hXgrid : STAmount.isRounded v.numericType X = false)
    (hresnorm : res.isNormalized)
    (hsub : X.operator_sub repN .to_nearest = .ok res)
    (hnf : res.mantissa_ = 0 ∨ (10 : ℚ) ^ (-81 : ℤ) ≤ res.toRat) :
    STAmount.isRounded .fractional res = false := by
  obtain ⟨hp0, hpnt, hpc, hpx⟩ := Exact.price_facts v w sd priced hs hsnn hpr
  obtain ⟨-, hprv⟩ := hpx prn hprn
  have hTnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hTnn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAle : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
  have hpfrac : priced.mNumericType = .fractional := by rw [hpnt, hfr]
  obtain ⟨hpcan, hpsgn, hrepne⟩ := priced_pos_canonical v.assetsTotal priced rep hTnorm hTnn
    hpfrac hp0 (hpc (by rw [hfr]; rfl)) hcl hfnp
  have hpleA : priced.toRat ≤ v.assetsAvailable.toRat := by rw [← hprv]; exact hle
  have hTneg : v.assetsTotal.negative_ = false :=
    Number.negative_false_of_norm_nonneg _ hTnorm hTnn
  rw [hfr] at hTgrid hXgrid
  have hXf : X.isNormalized ∧ X.negative_ = false ∧ X.toRat ≤ v.assetsTotal.toRat ∧
      priced.toRat ≤ X.toRat := by
    rcases hX with rfl | rfl
    · exact ⟨hTnorm, hTneg, le_rfl, le_trans hpleA hAle⟩
    · exact ⟨v.wf.assetsAvailable_norm, Number.negative_false_of_norm_nonneg _
        v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg, hAle, hpleA⟩
  obtain ⟨hXnorm, hXneg, hXle, hpX⟩ := hXf
  exact clamped_field_on_grid v.assetsTotal X priced rep repN res hTnorm hTneg hTgrid hXnorm
    hXneg hXgrid hXle hpcan hpsgn hpX hcl hrepne hrepN hresnorm hsub hnf

lemma computeClawback_zero_facts (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hz : assets.isZero = true)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ priced prn,
      (cr.sharesDestroyed = holderShares ∨ ∃ X,
        STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X ∧
        assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed) ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      priced.toNumber .to_nearest = .ok prn ∧
      prn.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.isFractionalNonPositive = .ok false := by
  simp only [computeClawback, assetsToSharesClawback, hz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd trivial ‹¬ True›
    | (dsimp only; exact ⟨_, _, Or.inl rfl, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all⟩)
    | (dsimp only; exact ⟨_, _, Or.inr ⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all⟩)
/-- The final pricing chain of a successful `computeClawback`, and where its shares came
from. -/
lemma computeClawback_all_facts (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ priced prn,
      (cr.sharesDestroyed = holderShares ∨ ∃ X,
        (X = assets ∨ STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) ∧
        assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed) ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      priced.toNumber .to_nearest = .ok prn ∧
      prn.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.isFractionalNonPositive = .ok false := by
  by_cases hz : assets.isZero = true
  · obtain ⟨priced, prn, hsrc, h⟩ := computeClawback_zero_facts v assets holderShares cr hz hok herr
    refine ⟨priced, prn, ?_, h⟩
    rcases hsrc with h1 | ⟨X, hX, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨X, Or.inr hX, h2⟩
  · obtain ⟨X, priced, prn, hX, hsh, h⟩ :=
      Exact.computeClawback_facts v assets holderShares cr (by simpa using hz) hok herr
    exact ⟨priced, prn, Or.inr ⟨X, hX, hsh⟩, h⟩

end XRPL.Model.SingleAssetVault.CatHI

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol CatHI

lemma Vault.withdraw_assetsRounded_preserved_proof (v : Vault) (amount : WithdrawAmount)
    (waive : Bool) (r : WithdrawResult)
    (hfr : v.numericType = .fractional)
    (hpre : ¬ v.assetsRounded)
    (hsbc : r.sharesBurned.Canonical)
    (hsbnn : 0 ≤ r.sharesBurned.toRat)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waive hpos = .ok r) (herr : r.error = none)
    (hnf₁ : r.vault'.assetsTotal.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsTotal.toRat)
    (hnf₂ : r.vault'.assetsAvailable.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsAvailable.toRat) :
    ¬ r.vault'.assetsRounded := by
  rw [CatHI.Vault.not_assetsRounded_iff] at hpre ⊢
  obtain ⟨hpT, hpA, hpR, hpL, hpM⟩ := hpre
  obtain ⟨cw, an, sta, hcomp, hcerr, han, hlt, hsta, hsb, -, hdisj⟩ :=
    WdAcc.withdraw_ok_cases v amount waive r hpos hok herr
  rcases hdisj with ⟨-, -, -, hrec⟩ |
      ⟨-, an', sbn, at', atr, atr', av', st', hcl, hfnp, han', -, hsubT, -, -, -, hsubA, -, hrec⟩
  · have hnt : r.vault'.numericType = v.numericType := by
      show r.vault'.toRawVault.numericType = _; rw [hrec]
    have hT : r.vault'.assetsTotal = Number.zero := by
      show r.vault'.toRawVault.assetsTotal = _; rw [hrec]
    have hA : r.vault'.assetsAvailable = Number.zero := by
      show r.vault'.toRawVault.assetsAvailable = _; rw [hrec]
    have hR : r.vault'.assetsReserved = v.assetsReserved := by
      show r.vault'.toRawVault.assetsReserved = _; rw [hrec]
    have hL : r.vault'.lossUnrealized = v.lossUnrealized := by
      show r.vault'.toRawVault.lossUnrealized = _; rw [hrec]
    have hM : r.vault'.assetsMaximum = v.assetsMaximum := by
      show r.vault'.toRawVault.assetsMaximum = _; rw [hrec]
    rw [hnt, hT, hA, hR, hL, hM]
    exact ⟨STAmount.isRounded_zero _, STAmount.isRounded_zero _, hpR, hpL, hpM⟩
  · have hnt : r.vault'.numericType = v.numericType := by
      show r.vault'.toRawVault.numericType = _; rw [hrec]
    have hT : r.vault'.assetsTotal = at' := by
      show r.vault'.toRawVault.assetsTotal = _; rw [hrec]
    have hA : r.vault'.assetsAvailable = av' := by
      show r.vault'.toRawVault.assetsAvailable = _; rw [hrec]
    have hR : r.vault'.assetsReserved = v.assetsReserved := by
      show r.vault'.toRawVault.assetsReserved = _; rw [hrec]
    have hL : r.vault'.lossUnrealized = v.lossUnrealized := by
      show r.vault'.toRawVault.lossUnrealized = _; rw [hrec]
    have hM : r.vault'.assetsMaximum = v.assetsMaximum := by
      show r.vault'.toRawVault.assetsMaximum = _; rw [hrec]
    have hpr := computeWithdraw_ok_priced v amount waive cw hcomp hcerr
    rw [← hsb] at hpr
    have hs : ∀ sn, r.sharesBurned.toNumber .to_nearest = .ok sn →
        sn.isNormalized ∧ sn.toRat = r.sharesBurned.toRat := by
      intro sn hsn
      obtain ⟨sn0, hsn0, hv, hn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
        (STAmount.Canonical.exactCanonical _ hsbc)
      obtain rfl := Except.ok.inj (hsn.symm.trans hsn0)
      exact ⟨hn, hv⟩
    obtain ⟨-, -, -, hpx⟩ := Exact.price_facts v waive _ _ hs hsbnn hpr
    obtain ⟨hann, -⟩ := hpx an han
    have hle : an.toRat ≤ v.assetsAvailable.toRat := by
      by_contra h
      rw [not_le] at h
      rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hann).mpr h] at hlt
      exact absurd hlt (by decide)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hnt, hT, hfr]
      exact field_on_grid v hfr waive _ _ _ an an' _ at' hs hsbnn hpr han hle hcl hfnp han'
        (Or.inl rfl) hpT hpT (by rw [← hT]; exact r.vault'.wf.assetsTotal_norm) hsubT
        (by rw [← hT]; exact hnf₁)
    · rw [hnt, hA, hfr]
      exact field_on_grid v hfr waive _ _ _ an an' _ av' hs hsbnn hpr han hle hcl hfnp han'
        (Or.inr rfl) hpT hpA (by rw [← hA]; exact r.vault'.wf.assetsAvailable_norm) hsubA
        (by rw [← hA]; exact hnf₂)
    · rw [hnt, hR]; exact hpR
    · rw [hnt, hL]; exact hpL
    · rw [hnt, hM]; exact hpM

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol CatHI

lemma Vault.clawback_assetsRounded_preserved_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hfr : v.numericType = .fractional)
    (hpre : ¬ v.assetsRounded)
    (hac : assets.Canonical) (hSc : holderShares.Canonical) (hSnn : holderShares.negative = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none)
    (hnf₁ : r.vault'.assetsTotal.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsTotal.toRat)
    (hnf₂ : r.vault'.assetsAvailable.mantissa_ = 0 ∨
            (10 : ℚ) ^ (-81 : ℤ) ≤ r.vault'.assetsAvailable.toRat) :
    ¬ r.vault'.assetsRounded := by
  rw [CatHI.Vault.not_assetsRounded_iff] at hpre ⊢
  obtain ⟨hpT, hpA, hpR, hpL, hpM⟩ := hpre
  obtain ⟨cr, -, arn, at', -, av', -, hcomp, hcerr, -, -, -, harn, hat, -, hav, -, hvt, hva, -⟩ :=
    Exact.clawback_ok_cases v assets holderShares r hnn hok herr
  obtain ⟨priced, prn, hsrc, hpr, hprn, hgt, hcl, hfnp⟩ :=
    computeClawback_all_facts v assets holderShares cr hcomp hcerr
  have hsdf : cr.sharesDestroyed.Canonical ∧ 0 ≤ cr.sharesDestroyed.toRat := by
    rcases hsrc with h | ⟨X, hX, hsh⟩
    · rw [h]
      exact ⟨hSc, STAmount.toRat_nonneg_of _ hSnn⟩
    · obtain ⟨hsnt, hsoff, hsval⟩ := ClwAcc.shares_shape v X _ hsh
      refine ⟨Exact.int64_canonical _ hsnt hsoff hsval, ?_⟩
      refine Exact.shares_nonneg v X _ false (fun xn hxn => ?_) hsh
      rcases hX with rfl | hX
      · obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
          (STAmount.Canonical.exactCanonical _ hac)
        obtain rfl := Except.ok.inj (hsn.symm.trans hxn)
        exact ⟨hsnn, by rw [hsnv]; exact hnn⟩
      · obtain ⟨hX0, -, -, hXx⟩ := WdMono.ofNumber_facts v.numericType _ X
          v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg hX
        obtain ⟨hxnn, hxnv⟩ := hXx xn hxn
        exact ⟨hxnn, by rw [hxnv]; exact hX0⟩
  obtain ⟨hsdc, hsdnn⟩ := hsdf
  have hs : ∀ sn, cr.sharesDestroyed.toNumber .to_nearest = .ok sn →
      sn.isNormalized ∧ sn.toRat = cr.sharesDestroyed.toRat := by
    intro sn hsn
    obtain ⟨sn0, hsn0, hv, hn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
      (STAmount.Canonical.exactCanonical _ hsdc)
    obtain rfl := Except.ok.inj (hsn.symm.trans hsn0)
    exact ⟨hn, hv⟩
  obtain ⟨-, -, -, hpx⟩ := Exact.price_facts v false _ _ hs hsdnn hpr
  obtain ⟨hprnn, -⟩ := hpx prn hprn
  have hle : prn.toRat ≤ v.assetsAvailable.toRat := by
    by_contra h
    rw [not_le] at h
    rw [(operator_gt_iff _ _ hprnn v.wf.assetsAvailable_norm).mpr h] at hgt
    exact absurd hgt (by decide)
  have hrec : r.vault'.toRawVault.numericType = v.numericType ∧
      r.vault'.assetsReserved = v.assetsReserved ∧
      r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.assetsMaximum = v.assetsMaximum := by
    simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
    walk_ok
    all_goals first
      | (simp [ClawbackResult.rejected] at herr; done)
      | (simp only at herr; simp [herr] at *; done)
      | skip
    have hl := (RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1
    exact ⟨by dsimp only; rw [hl], by dsimp only; rw [hl], by dsimp only; rw [hl],
      by dsimp only; rw [hl]⟩
  obtain ⟨hnt, hR, hL, hM⟩ := hrec
  have hnt' : r.vault'.numericType = v.numericType := hnt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hnt', hvt, hfr]
    exact field_on_grid v hfr false _ _ _ prn arn _ at' hs hsdnn hpr hprn hle hcl hfnp harn
      (Or.inl rfl) hpT hpT (by rw [← hvt]; exact r.vault'.wf.assetsTotal_norm) hat
      (by rw [← hvt]; exact hnf₁)
  · rw [hnt', hva, hfr]
    exact field_on_grid v hfr false _ _ _ prn arn _ av' hs hsdnn hpr hprn hle hcl hfnp harn
      (Or.inr rfl) hpT hpA (by rw [← hva]; exact r.vault'.wf.assetsAvailable_norm) hav
      (by rw [← hva]; exact hnf₂)
  · rw [hnt', hR]; exact hpR
  · rw [hnt', hL]; exact hpL
  · rw [hnt', hM]; exact hpM

end XRPL.Model.SingleAssetVault
