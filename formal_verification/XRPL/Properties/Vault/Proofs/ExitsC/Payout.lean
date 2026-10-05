import XRPL.Properties.Vault.Proofs.ExactUpdates
import XRPL.Properties.Vault.Proofs.WithdrawMono
import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Vault.Proofs.ExitsC.Basic
import XRPL.Properties.Vault.Proofs.ExitsC.Total

/-! # A payout too small for the stored total

The clamped payout `a` lies in `[0, p]` for the priced payout `p`. Either it
vanishes, or the precision guard on `assetsTotal - a` agrees with the guard on
`assetsTotal - p`. -/

namespace XRPL.Model.SingleAssetVault.ExitsC

open XRPL.Model.Protocol

/-- Shares priced by the truncating `assetsToSharesWithdraw` convert exactly. -/
lemma shares_exact (v : Vault) (X sd : STAmount) (w : Bool)
    (hX : ∀ xn, X.toNumber .to_nearest = .ok xn → xn.isNormalized ∧ 0 ≤ xn.toRat)
    (h : assetsToSharesWithdraw v X true w = .ok sd) :
    ∀ sn, sd.toNumber .to_nearest = .ok sn → sn.isNormalized ∧ sn.toRat = sd.toRat := by
  cases w <;> simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at h <;>
    walk_ok
  all_goals first
    | (intro sn hsn
       obtain ⟨h1, h2⟩ := STAmount.toNumber_zero_facts _ _ sn (STAmount.zero_mValue _) hsn
       exact ⟨h2, h1⟩)
    | skip
  all_goals
    have hN := ‹v.assetsTotal.operator_sub _ .to_nearest = .ok _›
    obtain ⟨hnavn, hnav0⟩ := Exact.nav_nonneg' v _ _
      (by first | exact Or.inl rfl | exact Or.inr rfl) hN
    obtain ⟨hxn, hx0⟩ := hX _ ‹X.toNumber _ = _›
    have hmul := ‹Number.operator_mul v.sharesTotal _ _ = _›
    have hdiv := ‹Number.operator_div _ _ _ = _›
    have hMn := WdMono.mul_norm _ _ _ v.wf.sharesTotal_norm hxn hmul
    have hM0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_mul_rounded_to_nearest _ _ _ v.wf.sharesTotal_norm hxn hmul)
      (mul_nonneg v.wf.sharesTotal_nonneg hx0)
    have hDn := WdMono.div_norm _ _ _ hMn hnavn hdiv
    have hD0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_div_rounded_to_nearest _ _ _ hMn hnavn hdiv) (div_nonneg hM0 hnav0)
    obtain ⟨htv, htn⟩ := Number.truncate_floor _ _ hDn
      (Number.negative_false_of_nonneg _ hDn hD0) ‹Number.truncate _ = _›
    rename_i t _ _
    have hof := ‹STAmount.ofNumber _ t _ = _›
    by_cases htm : t.mantissa_ = 0
    · intro sn hsn
      have hz := WdMono.ofNumber_mant0 _ _ _ _ htm hof
      obtain ⟨h1, h2⟩ := STAmount.toNumber_zero_facts _ _ sn hz hsn
      exact ⟨h2, h1⟩
    · have ht0 : 0 ≤ t.toRat := by rw [htv]; exact_mod_cast Int.floor_nonneg.mpr hD0
      exact (WdMono.ofNumber_facts _ t sd (htn htm) ht0 hof).2.2.2

/-- The redeemed shares of a canonical positive request convert exactly and are
nonnegative. -/
lemma redeemed_facts (v : Vault) (amount : WithdrawAmount) (w : Bool) (cw : ComputeWithdrawResult)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw)
    (herr : cw.error = none)
    (hcanon : amount.amount.Canonical) (hpos : 0 < amount.amount.toRat) :
    (∀ sn, cw.sharesRedeemed.toNumber .to_nearest = .ok sn →
      sn.isNormalized ∧ sn.toRat = cw.sharesRedeemed.toRat) ∧ 0 ≤ cw.sharesRedeemed.toRat := by
  cases amount with
  | vaultShares s =>
    simp only [computeWithdrawByShares, bind, Except.bind, pure, Except.pure, tryCatch,
      tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hcomp
    walk_ok
    all_goals try (simp at herr; done)
    obtain ⟨sn0, hsn0, hv0, hn0⟩ := STAmount.toNumber_exact_canonical s .to_nearest
      (STAmount.Canonical.exactCanonical s hcanon)
    refine ⟨fun sn h => ?_, le_of_lt hpos⟩
    obtain rfl := Except.ok.inj (hsn0.symm.trans h)
    exact ⟨hn0, hv0⟩
  | vaultAssets X =>
    simp only [computeWithdrawByAssets, bind, Except.bind, pure, Except.pure, tryCatch,
      tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hcomp
    walk_ok
    all_goals try (simp at herr; done)
    obtain ⟨xn0, hxn0, hxv0, hxnn0⟩ := STAmount.toNumber_exact_canonical X .to_nearest
      (STAmount.Canonical.exactCanonical X hcanon)
    have hX : ∀ xn, X.toNumber .to_nearest = .ok xn → xn.isNormalized ∧ 0 ≤ xn.toRat := by
      intro xn h
      obtain rfl := Except.ok.inj (hxn0.symm.trans h)
      exact ⟨hxnn0, by rw [hxv0]; exact le_of_lt hpos⟩
    have hsh := ‹assetsToSharesWithdraw v X true w = .ok _›
    exact ⟨shares_exact v X _ w hX hsh, Exact.shares_nonneg v X _ w hX hsh⟩

lemma exit_guard (v : Vault) (amount : WithdrawAmount) (w : Bool) (hpos : 0 < amount.amount.toRat)
    (cw : ComputeWithdrawResult) (pN an sbn at'' : Number) (sta a atr atr'' : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok pN)
    (hins : v.assetsAvailable.operator_lt pN = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta)
    (hfin : cw.sharesRedeemed.operator_eq sta = false)
    (hcl : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok a)
    (hfnp : a.isFractionalNonPositive = .ok false)
    (han : a.toNumber .to_nearest = .ok an)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sbn)
    (hat : v.assetsTotal.operator_sub an .to_nearest = .ok at'')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr)
    (hrt'' : STAmount.ofNumber v.numericType at'' .to_nearest = .ok atr'')
    (hg : (an.mantissa_ != 0 && atr.operator_eq atr'') = true) :
    v.withdraw amount w hpos = .ok (.rejected v .tecPRECISION_LOSS) := by
  cases amount <;> simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

lemma exit_fnp (v : Vault) (amount : WithdrawAmount) (w : Bool) (hpos : 0 < amount.amount.toRat)
    (cw : ComputeWithdrawResult) (pN : Number) (sta a : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok pN)
    (hins : v.assetsAvailable.operator_lt pN = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta)
    (hfin : cw.sharesRedeemed.operator_eq sta = false)
    (hcl : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok a)
    (hfnp : a.isFractionalNonPositive = .ok true) :
    v.withdraw amount w hpos = .ok (.rejected v .tecPRECISION_LOSS) := by
  cases amount <;> simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

/-- The exponent of a total whose fractional pack succeeds is small. -/
lemma total_exp (T : Number) (r : STAmount) (hT : T.isNormalized) (hT0 : 0 ≤ T.toRat)
    (hok : STAmount.ofNumber .fractional T .to_nearest = .ok r) : T.exponent_ ≤ 100 := by
  by_cases hm : T.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero T hT hm]; decide
  have hneg := Number.negative_false_of_nonneg T hT hT0
  obtain ⟨exp, hexp, hres⟩ := WdMono.ofNumber_frac_tn_exp T r hT hneg hm hok
  have h80 := WdMono.exp_cases T r hok
  rcases hexp with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hres with ⟨h2, _, _⟩ | ⟨_, _, h3⟩ <;> omega

lemma neg_neg_of_ne (s : STAmount) (h : s.mValue ≠ 0) : s.operator_neg.operator_neg = s := by
  rw [STAmount.operator_neg_of_ne s h,
    STAmount.operator_neg_of_ne { s with mIsNegative := !s.mIsNegative } h]
  cases s; simp

/-- `operator_eq` on amounts identifies all four fields. -/
lemma eq_of_operator_eq (x y : STAmount) (h : x.operator_eq y = true) : x = y := by
  unfold STAmount.operator_eq STAmount.areComparable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x; cases y
  simp_all

lemma payout_too_small (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true)
    (hpos : 0 < amount.amount.toRat)
    (hcanon : amount.amount.Canonical) :
    v.withdraw amount waiveUnrealizedLoss hpos =
      .ok (.rejected v .tecPRECISION_LOSS) := by
  set p := cw.assets' with hp_def
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp herr
  obtain ⟨hsx, hsnn⟩ := redeemed_facts v amount waiveUnrealizedLoss cw hcomp herr hcanon hpos
  obtain ⟨hp0, hpnt, hpc, hpx⟩ := Exact.price_facts v waiveUnrealizedLoss _ _ hsx hsnn hp
  obtain ⟨hpNn, hpNv⟩ := hpx _ haN
  have hg' := hguard
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg'
  obtain ⟨hpNm, hReq⟩ := hg'
  have hpz : p.mValue ≠ 0 := fun h => hpNm (by
    rw [STAmount.toNumber_zero_eq p _ _ h haN]; rfl)
  have hppos : 0 < p.toRat := WdMono.pos_of_nonneg _ hp0 hpz
  have hpneg : p.mIsNegative = false := STAmount.mIsNegative_false_of_pos _ hppos
  have hT := v.wf.assetsTotal_norm
  have hT0 : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hpA : p.toRat ≤ v.assetsAvailable.toRat := by
    rw [← hpNv]
    by_contra h
    rw [not_le] at h
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hpNn).mpr h] at hins
    exact absurd hins (by decide)
  have hAT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
  have hpneg' : p.operator_neg = { p with mIsNegative := true } := by
    rw [STAmount.operator_neg_of_ne p hpz, hpneg]; rfl
  have hnn : p.operator_neg.operator_neg = p := neg_neg_of_ne p hpz
  have hnegneg : p.operator_neg.negative = true := by rw [hpneg']; rfl
  by_cases hint : v.numericType.isIntegral = true
  · -- integral: the clamp hands the price back
    have hpi : p.integral = true := by
      show p.mNumericType.isIntegral = true; rw [hpnt]; exact hint
    have hpi' : p.operator_neg.integral = true := by
      show p.operator_neg.mNumericType.isIntegral = true
      rw [STAmount.operator_neg_mNumericType]; exact hpi
    have hcl : clampToSumExponent v.assetsTotal p.operator_neg = .ok p := by
      rw [clampToSumExponent_integral _ _ hpi', if_pos hnegneg, hnn]
    exact exit_guard v amount waiveUnrealizedLoss hpos cw assetsNumber' assetsNumber'
      sharesBurnedNumber assetsTotal' sharesTotalAmount p assetsTotalRounded assetsTotalRounded'
      hcomp herr haN hins hst hfin hcl (fnp_false p (Or.inl hpi)) haN hsN hat hrt hrt' hguard
  have hint' : v.numericType.isIntegral = false := by simpa using hint
  have hnt : v.numericType = .fractional := by
    cases h : v.numericType with
    | fractional => rfl
    | integral => rw [h] at hint'; simp [NumericType.isIntegral] at hint'
  have hpc' : p.IOUCanonical := hpc hint' hpz
  have hrtF : STAmount.ofNumber .fractional v.assetsTotal .to_nearest = .ok assetsTotalRounded := by
    rw [← hnt]; exact hrt
  have hrt'F : STAmount.ofNumber .fractional assetsTotal' .to_nearest = .ok assetsTotalRounded' := by
    rw [← hnt]; exact hrt'
  have hpN_eq : assetsNumber' = ⟨false, p.mValue * 10 * 10 * 10, p.mOffset - 3⟩ := by
    have h := STAmount.toNumber_iou_canonical p .to_nearest hpc'
    rw [hpneg] at h
    exact Except.ok.inj (haN.symm.trans h)
  have hdn : p.operator_neg.toNumber .to_nearest = .ok assetsNumber'.operator_neg := by
    rw [STAmount.toNumber_iou_canonical _ _ hpc'.operator_neg]
    have hm : (assetsNumber'.mantissa_ == 0) = false := by simpa using hpNm
    unfold Number.operator_neg
    rw [hm, hpneg']
    simp only [Bool.false_eq_true, if_false, hpN_eq, Bool.not_false]
  have hpse : postSumExponent v.assetsTotal p.operator_neg = .ok assetsTotalRounded'.exponent := by
    have hsub : v.assetsTotal.operator_add assetsNumber'.operator_neg .to_nearest
        = .ok assetsTotal' := hat
    have hnt' : p.operator_neg.numericType = .fractional := by
      show p.operator_neg.mNumericType = _
      rw [STAmount.operator_neg_mNumericType, hpnt, hnt]
    simp only [postSumExponent, numberExponent, bind, Except.bind, pure, Except.pure, hdn, hsub,
      hnt', hrt'F]
  have hfr : p.operator_neg.integral = false := by
    show p.operator_neg.mNumericType.isIntegral = false
    rw [STAmount.operator_neg_mNumericType, hpnt]; exact hint'
  have hcl_eq : clampToSumExponent v.assetsTotal p.operator_neg =
      STAmount.roundToExponent p assetsTotalRounded'.exponent .downward := by
    unfold clampToSumExponent
    simp only [hfr, hnegneg, hpse, hnn, bind, Except.bind, pure, Except.pure, if_true,
      Bool.false_eq_true, if_false]
  have hpint : p.integral = false := by
    show p.mNumericType.isIntegral = false; rw [hpnt]; exact hint'
  have hpisz : p.isZero = false := by simpa [STAmount.isZero] using hpz
  by_cases hge : assetsTotalRounded'.exponent ≤ p.mOffset
  · have hrte : STAmount.roundToExponent p assetsTotalRounded'.exponent .downward = .ok p := by
      unfold STAmount.roundToExponent
      rw [if_neg (by rw [hpint]; decide), if_neg (by rw [hpisz]; decide),
        if_pos (show p.exponent ≥ _ from hge)]
    exact exit_guard v amount waiveUnrealizedLoss hpos cw assetsNumber' assetsNumber'
      sharesBurnedNumber assetsTotal' sharesTotalAmount p assetsTotalRounded assetsTotalRounded'
      hcomp herr haN hins hst hfin (hcl_eq.trans hrte) (fnp_false p (Or.inr hppos)) haN hsN hat
      hrt hrt' hguard
  have hlt : p.mOffset < assetsTotalRounded'.exponent := lt_of_not_ge hge
  have hplo := hpc'.exp_lo
  have hpe := WdMono.exp_cases assetsTotal' _ hrt'F
  have hpe_lo : (-96 : ℤ) ≤ assetsTotalRounded'.exponent := by omega
  have hpe_hi : assetsTotalRounded'.exponent ≤ 80 := by omega
  obtain ⟨a, hrte⟩ := rte_ok p hpc' hpneg _ hpe_lo hpe_hi hlt
  have hcl := hcl_eq.trans hrte
  have hpf : STAmount.FracCanonZero p := ⟨by rw [hpnt, hnt], Or.inl hpc'⟩
  have haf := WdAcc.clamp_frac_shape _ _ _ (STAmount.operator_neg_fczr _ hpf) hcl
  have haint : a.integral = false := by
    show a.mNumericType.isIntegral = false; rw [haf.1]; rfl
  by_cases hapos : 0 < a.toRat
  swap
  · exact exit_fnp v amount waiveUnrealizedLoss hpos cw assetsNumber' sharesTotalAmount a
      hcomp herr haN hins hst hfin hcl (fnp_true a ⟨haint, not_lt.mp hapos⟩)
  have hfnp := fnp_false a (Or.inr hapos)
  obtain ⟨ha0, hap, hgrid⟩ := Exact.clamp_payout v p a hp0 hpnt hpc
    (fun h => absurd h (by rw [hint']; decide)) (le_trans hpA hAT)
    (fun h => absurd h (by rw [hint']; decide)) hcl hfnp
  have haC : a.IOUCanonical := haf.2.resolve_right (fun hz => by
    rw [STAmount.toRat_eq_zero_of_mValue_zero a hz] at hapos; exact lt_irrefl _ hapos)
  obtain ⟨an, han, hanv, hann⟩ := STAmount.toNumber_iou_exact a .to_nearest haC
  have hanm : an.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hanv; linarith
  by_cases heq : a.toRat = p.toRat
  · obtain rfl : an = assetsNumber' :=
      Number.isNormalized.toRat_inj hann hpNn (by rw [hanv, heq, hpNv])
    exact exit_guard v amount waiveUnrealizedLoss hpos cw an an sharesBurnedNumber assetsTotal'
      sharesTotalAmount a assetsTotalRounded assetsTotalRounded' hcomp herr haN hins hst hfin hcl
      hfnp han hsN hat hrt hrt' hguard
  -- a strictly smaller clamped payout: the subtraction is exact and lands on `assetsTotal'`
  have hTe := total_exp v.assetsTotal _ hT hT0 hrtF
  have hane : an.exponent_ ≤ 100 := by
    have h := STAmount.toNumber_iou_canonical a .to_nearest haC
    obtain rfl := Except.ok.inj (han.symm.trans h)
    show a.mOffset - 3 ≤ 100
    have := haC.exp_hi; omega
  obtain ⟨at'', hat''⟩ := sub_ok _ _ hT hann hTe hane
  have hat''v := (Exact.updates_exact _ _ _ _ _ a.toRat hT hT le_rfl hann hanv ha0
    (le_trans hap (le_trans hpA hAT)) hgrid hat'' hat'').1
  have hat''n := operator_sub_isNormalized_to_nearest_sz _ _ _ hT hann hat''
  have hat'n := operator_sub_isNormalized_to_nearest_sz _ _ _ hT hpNn hat
  have hr := operator_sub_rounded_to_nearest _ _ _ hT hpNn hat
  have h1 : assetsTotal'.toRat ≤ at''.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized _ _ hr at'' hat''n
      (by rw [hat''v, hpNv]; linarith)
  have hat'0 : 0 ≤ assetsTotal'.toRat :=
    Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hr (by rw [hpNv]; linarith)
  have hReq' : assetsTotalRounded = assetsTotalRounded' := eq_of_operator_eq _ _ hReq
  have hzero : STAmount.ofNumber .fractional Number.zero .to_nearest
      = .ok ⟨.fractional, 0, -100, false⟩ := by rfl
  have hAT'm : assetsTotal'.mantissa_ ≠ 0 := by
    intro h
    rw [Number.eq_zero_of_mantissa_zero _ hat'n h, hzero] at hrt'F
    obtain rfl := Except.ok.inj hrt'F
    exact absurd hlt (by show ¬ p.mOffset < -100; omega)
  have hR'nz : assetsTotalRounded'.mValue ≠ 0 := by
    obtain ⟨exp, -, hres⟩ := WdMono.ofNumber_frac_tn_exp assetsTotal' _ hat'n
      (Number.negative_false_of_nonneg _ hat'n hat'0) hAT'm hrt'F
    rcases hres with ⟨-, -, he⟩ | ⟨-, hnz, -⟩
    · exact absurd hlt (by rw [he]; omega)
    · exact hnz
  have hATm : v.assetsTotal.mantissa_ ≠ 0 := by
    intro h
    rw [Number.eq_zero_of_mantissa_zero _ hT h, hzero, hReq'] at hrtF
    obtain rfl := Except.ok.inj hrtF
    exact hR'nz rfl
  obtain ⟨-, -, hc1, -, -⟩ := WdMono.frac_pack v.assetsTotal _ hT
    (Number.negative_false_of_nonneg _ hT hT0) hATm hrtF (by rw [hReq']; exact hR'nz)
  obtain ⟨-, -, hc2, -, -⟩ := WdMono.frac_pack assetsTotal' _ hat'n
    (Number.negative_false_of_nonneg _ hat'n hat'0) hAT'm hrt'F hR'nz
  rw [hReq'] at hc1
  obtain ⟨-, -, hgr, -⟩ := WdMono.rte_facts p a _ hpc' hppos hpe_hi hrte
  obtain ⟨z, hz⟩ := hgr _ le_rfl
  have hu : (0 : ℚ) < 10 ^ assetsTotalRounded'.exponent := zpow_pos (by norm_num) _
  have hz1 : (1 : ℚ) ≤ z := by
    have : (0 : ℤ) < z := by
      by_contra hc
      have hz0 : (z : ℚ) ≤ 0 := by exact_mod_cast not_lt.mp hc
      have : a.toRat ≤ 0 := by rw [hz]; exact mul_nonpos_of_nonpos_of_nonneg hz0 hu.le
      linarith
    exact_mod_cast this
  have hage : (10 : ℚ) ^ assetsTotalRounded'.exponent ≤ a.toRat := by
    rw [hz]; nlinarith
  have h2 : at''.toRat ≤ assetsTotal'.toRat := by
    rw [hat''v]
    have := abs_le.mp hc1
    have := abs_le.mp hc2
    linarith
  obtain rfl : at'' = assetsTotal' :=
    Number.isNormalized.toRat_inj hat''n hat'n (le_antisymm h2 h1)
  exact exit_guard v amount waiveUnrealizedLoss hpos cw assetsNumber' an sharesBurnedNumber at''
    sharesTotalAmount a assetsTotalRounded assetsTotalRounded' hcomp herr haN hins hst hfin hcl
    hfnp han hsN hat'' hrt hrt' (by simp [hanm, hReq])

end XRPL.Model.SingleAssetVault.ExitsC
