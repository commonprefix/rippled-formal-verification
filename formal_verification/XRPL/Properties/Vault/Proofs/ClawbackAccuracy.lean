import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.ClampFacts

/-! # `Vault.clawback` integral accuracy

Proof bodies of `clawback_vault_updates_integral` and
`clawback_assetsRecovered_integral`. -/

namespace XRPL.Model.SingleAssetVault.ClwAcc

open XRPL.Model.Protocol

/-- The pricing steps behind a successful `computeClawback` on a nonzero amount. -/
lemma computeClawback_priced (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hznz : assets.isZero = false)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ X priced, assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered := by
  simp only [computeClawback, assetsToSharesClawback, hznz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd ‹false = true› (by decide)
    | (dsimp only; exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩)

/-- The stored-total updates of a successful `Vault.clawback`. -/
lemma clawback_updates (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    ∃ cr arn at' av', computeClawback v assets holderShares = .ok cr ∧ cr.error = none ∧
      r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
      cr.assetsRecovered.toNumber .to_nearest = .ok arn ∧
      v.assetsTotal.operator_sub arn .to_nearest = .ok at' ∧
      v.assetsAvailable.operator_sub arn .to_nearest = .ok av' ∧
      r.vault'.assetsTotal = at' ∧ r.vault'.assetsAvailable = av' := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp [ClawbackResult.rejected] at herr; done)
    | (simp only at herr; simp [herr] at *; done)
    | skip
  have hl := (RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1
  refine ⟨_, _, _, _, ‹computeClawback _ _ _ = _›, ?_, rfl, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · simpa using ‹¬ (Option.isSome _) = true›
  · dsimp only; rw [hl]
  · dsimp only; rw [hl]

lemma clamp_neg_integral (a : Number) (p rec : STAmount) (hi : p.mNumericType.isIntegral = true)
    (hoff : p.mOffset = 0) (h : clampToSumExponent a p.operator_neg = .ok rec) :
    rec.mNumericType = p.mNumericType ∧ rec.mOffset = 0 ∧ rec.mValue = p.mValue ∧
      rec.toRat = (p.mValue.toNat : ℚ) ∧ p.toRat ≤ rec.toRat := by
  have hni : p.operator_neg.integral = true := by
    unfold STAmount.operator_neg STAmount.integral; split <;> exact hi
  unfold clampToSumExponent at h
  simp only [hni, if_true, pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [STAmount.toRat_signed, STAmount.toRat_signed]
  unfold STAmount.operator_neg STAmount.negative
  by_cases hm : p.mValue = 0
  · simp [hm, hoff]
  · cases p.mIsNegative <;> simp [hm, hoff]

lemma zero_integral_shape (nt : NumericType) (hnt : nt.isIntegral = true) :
    (STAmount.zero nt).mNumericType = nt ∧ (STAmount.zero nt).mOffset = 0 ∧
      (STAmount.zero nt).mValue = 0 := by
  cases nt with
  | fractional => simp [NumericType.isIntegral] at hnt
  | integral a b c d =>
    simp [STAmount.zero, STAmount.checked, STAmount.canonicalize, STAmount.unchecked,
      STAmount.integral, NumericType.isIntegral]

lemma integral_shape_facts (nt : NumericType) (s : STAmount) (hnt : nt.isIntegral = true)
    (h : s = STAmount.zero nt ∨ ∃ n, STAmount.ofNumber nt n .to_nearest = .ok s) :
    s.mNumericType = nt ∧ s.mOffset = 0 ∧ s.mValue.toNat ≤ maxRep.toNat := by
  rcases h with h | ⟨n, h⟩
  · subst h
    obtain ⟨h1, h2, h3⟩ := zero_integral_shape nt hnt
    exact ⟨h1, h2, by rw [h3]; exact Nat.zero_le _⟩
  · exact STAmount.ofNumber_integral_facts nt n .to_nearest s hnt h

lemma priced_cases (v : Vault) (sh priced : STAmount)
    (h : v.sharesToAssetsWithdraw sh false = .ok priced) :
    ∃ nav, v.assetsTotal.operator_sub v.lossUnrealized .to_nearest = .ok nav ∧
      ((nav.mantissa_ = 0 ∧ priced = STAmount.zero v.numericType) ∨
       (nav.mantissa_ ≠ 0 ∧ ∃ sn nv an, sh.toNumber .to_nearest = .ok sn ∧
          nav.operator_mul sn .to_nearest = .ok nv ∧
          nv.operator_div v.sharesTotal .to_nearest = .ok an ∧
          STAmount.ofNumber v.numericType an .to_nearest = .ok priced)) := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  · exact ⟨_, ‹_›, Or.inl ⟨beq_iff_eq.mp ‹(_ == _) = true›, rfl⟩⟩
  · exact ⟨_, ‹_›, Or.inr ⟨fun h0 => by simp [h0] at *, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩

lemma shares_shape (v : Vault) (X sd : STAmount)
    (h : assetsToSharesWithdraw v X true false = .ok sd) :
    sd.mNumericType = .int64 ∧ sd.mOffset = 0 ∧ sd.mValue.toNat ≤ maxRep.toNat := by
  simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact integral_shape_facts _ _ rfl (Or.inl rfl)
    | exact integral_shape_facts _ _ rfl (Or.inr ⟨_, ‹_›⟩)

lemma neg_pow_witness (e : ℤ) (hlo : minExponent + 18 ≤ e) (hhi : e ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = -(10 : ℚ) ^ e := by
  refine ⟨⟨true, 1000000000000000000, e - 18⟩, ?_, ?_⟩
  · refine Or.inr ⟨show largeRange.min ≤ (1000000000000000000 : UInt64) by decide,
      show (1000000000000000000 : UInt64) ≤ largeRange.max by decide,
      Or.inl (show (1000000000000000000 : UInt64) ≤ maxRep by decide), ?_, ?_⟩
    · show minExponent ≤ e - 18; omega
    · show e - 18 ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_neg _ rfl]
    show -(((1000000000000000000 : UInt64).toNat : ℚ) * (10 : ℚ) ^ (e - 18)) = -(10 : ℚ) ^ e
    rw [show ((1000000000000000000 : UInt64).toNat : ℚ) = (10 : ℚ) ^ (18 : ℤ) by
      rw [show (1000000000000000000 : UInt64).toNat = 1000000000000000000 from rfl]; norm_num,
      ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    ring_nf

lemma neg_half_witness : ∃ w : Number, w.isNormalized ∧ w.toRat = -(1 / 2 : ℚ) := by
  refine ⟨⟨true, 5000000000000000000, -19⟩, ?_, ?_⟩
  · exact Or.inr ⟨by decide, by decide, Or.inr (by decide), by decide, by decide⟩
  · rw [Number.toRat_of_neg _ rfl]
    show -(((5000000000000000000 : UInt64).toNat : ℚ) * (10 : ℚ) ^ (-19 : ℤ)) = -(1 / 2 : ℚ)
    rw [show (5000000000000000000 : UInt64).toNat = 5000000000000000000 from rfl]
    norm_num

/-- Below a non-negative stored value, the gap to an integer above it contains a
negative grid point. -/
lemma neg_gap_witness (x : Number) (k : ℚ) (hx : x.isNormalized) (hx0 : 0 ≤ x.toRat)
    (hk : k.den = 1) (hkx : x.toRat < k) :
    ∃ w : Number, w.isNormalized ∧ x.toRat - k ≤ w.toRat ∧ w.toRat < 0 := by
  by_cases hden : x.toRat.den = 1
  · obtain ⟨w, hw, hwv⟩ := neg_pow_witness 0 (by unfold minExponent; omega) le_rfl
    have := rat_one_le_sub_of_lt k x.toRat hk hden hkx
    refine ⟨w, hw, ?_, ?_⟩ <;> rw [hwv] <;> norm_num; linarith
  have hm : x.mantissa_ ≠ 0 := by
    intro h0; apply hden
    rw [Number.toRat_eq_zero_of_mantissa_zero x h0]; rfl
  have hneg : x.negative_ = false := Number.negative_false_of_normalized_nonneg x hx hx0
  have hxv := Number.toRat_of_nonneg x hneg
  obtain ⟨hMlo, hMhi⟩ := hx.mantissaBounds_nat hm
  have he : x.exponent_ < 0 := by
    by_contra hge; push Not at hge
    apply hden
    rw [hxv, show x.exponent_ = ((x.exponent_.toNat : ℕ) : ℤ) by omega, zpow_natCast]
    exact_mod_cast Rat.den_natCast (x.mantissa_.toNat * 10 ^ x.exponent_.toNat)
  have hk1 : 1 ≤ k := by
    have := rat_one_le_sub_of_lt k 0 hk rfl (lt_of_le_of_lt hx0 hkx); linarith
  by_cases hhalf : x.toRat ≤ 1 / 2
  · obtain ⟨w, hw, hwv⟩ := neg_half_witness
    exact ⟨w, hw, by rw [hwv]; linarith, by rw [hwv]; norm_num⟩
  push Not at hhalf
  obtain ⟨j, hj⟩ : ∃ j : ℕ, x.exponent_ = -(j : ℤ) := ⟨(-x.exponent_).toNat, by omega⟩
  have hpow : (10 : ℚ) ^ x.exponent_ = 1 / 10 ^ j := by
    rw [hj, zpow_neg, zpow_natCast]; ring
  have hj19 : j ≤ 19 := by
    by_contra hj'; push Not at hj'
    have h20 : (10 : ℚ) ^ 20 ≤ 10 ^ j := pow_le_pow_right₀ (by norm_num) hj'
    have hMq : (x.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hMhi
    rw [hxv, hpow] at hhalf
    have hpos : (0 : ℚ) < 10 ^ j := by positivity
    rw [mul_one_div, lt_div_iff₀ hpos] at hhalf
    nlinarith
  obtain ⟨w, hw, hwv⟩ := neg_pow_witness x.exponent_ (by unfold minExponent; omega) he.le
  refine ⟨w, hw, ?_, by rw [hwv]; exact neg_neg_of_pos (zpow_pos (by norm_num) _)⟩
  rw [hwv, hpow, hxv, hpow]
  have hkN : k = (k.num : ℚ) := (rat_eq_num_cast_of_den_one k hk).symm
  have hpos : (0 : ℚ) < 10 ^ j := by positivity
  have hlt : (x.mantissa_.toNat : ℤ) < k.num * 10 ^ j := by
    have : (x.mantissa_.toNat : ℚ) < (k.num : ℚ) * 10 ^ j := by
      rw [hxv, hpow, mul_one_div, div_lt_iff₀ hpos] at hkx; rw [← hkN]; exact hkx
    exact_mod_cast this
  have hge : (x.mantissa_.toNat : ℤ) + 1 ≤ k.num * 10 ^ j := hlt
  have hge' : (x.mantissa_.toNat : ℚ) + 1 ≤ (k.num : ℚ) * 10 ^ j := by exact_mod_cast hge
  rw [hkN]
  have : (x.mantissa_.toNat : ℚ) * (1 / 10 ^ j) - (k.num : ℚ) + 1 / 10 ^ j
      = ((x.mantissa_.toNat : ℚ) + 1 - (k.num : ℚ) * 10 ^ j) / 10 ^ j := by
    field_simp; ring
  have hnp : ((x.mantissa_.toNat : ℚ) + 1 - (k.num : ℚ) * 10 ^ j) / 10 ^ j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  linarith

/-- Subtracting a non-negative integer from an in-range non-negative stored value
is exact whenever the rounded result is non-negative. -/
lemma sub_exact_of_nonneg (x y res : Number) (k : ℚ) (hx : x.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hxle : x.toRat ≤ 2 ^ 63 - 1) (hy : y.isNormalized)
    (hyv : y.toRat = k) (hk : k.den = 1) (hk0 : 0 ≤ k)
    (hok : x.operator_sub y .to_nearest = .ok res) (hres : 0 ≤ res.toRat) :
    res.toRat = x.toRat - k := by
  by_cases hkx : k ≤ x.toRat
  · exact operator_sub_exact_int_le x y res k hx hxle hy hyv hk hk0 hkx hok
  push Not at hkx
  have hrtr := operator_sub_rounded_to_nearest x y res hx hy hok
  rw [hyv] at hrtr
  obtain ⟨w, hw, h1, h2⟩ := neg_gap_witness x k hx hx0 hk hkx
  have := Number.RoundsToRepresentable.le_of_le_normalized res _ hrtr w hw h1
  linarith

lemma pos_witness_one : ∃ w : Number, w.isNormalized ∧ w.toRat = 1 := by
  obtain ⟨w, hw, -, hv⟩ := Number.exists_normalized_of_pos_nat 1 le_rfl (by norm_num)
  exact ⟨w, hw, by rw [hv]; norm_num⟩

lemma pos_half_witness : ∃ w : Number, w.isNormalized ∧ w.toRat = 1 / 2 := by
  refine ⟨⟨false, 5000000000000000000, -19⟩, ?_, ?_⟩
  · exact Or.inr ⟨by decide, by decide, Or.inr (by decide), by decide, by decide⟩
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((5000000000000000000 : UInt64).toNat : ℚ) * (10 : ℚ) ^ (-19 : ℤ) = 1 / 2
    rw [show (5000000000000000000 : UInt64).toNat = 5000000000000000000 from rfl]
    norm_num

lemma mantissa_ne_zero_of_toRat_ne {n : Number} (h : n.toRat ≠ 0) : n.mantissa_ ≠ 0 :=
  fun h0 => h (Number.toRat_eq_zero_of_mantissa_zero n h0)

/-- An integral vault prices a share amount above one whole unit to within
`depositε` relative plus one unit. -/
lemma priced_lower (v : Vault) (hnav : v.WithdrawNavExact false)
    (hint : v.numericType.isIntegral = true) (sd priced : STAmount)
    (hsd : sd.mNumericType.isIntegral = true ∧ sd.mOffset = 0 ∧ sd.mValue.toNat ≤ maxRep.toNat)
    (hpr : v.sharesToAssetsWithdraw sd false = .ok priced)
    (h1 : 1 < v.idealAssetsClawback sd.toRat) :
    v.idealAssetsClawback sd.toRat * (1 - depositε) - 1 ≤ priced.toRat := by
  obtain ⟨nav, hnavok, hcase⟩ := priced_cases v sd priced hpr
  obtain ⟨nav', hnav', hnavv⟩ := hnav
  have hnn : nav' = nav := Except.ok.inj (hnav'.symm.trans hnavok)
  subst hnn
  simp only [Bool.false_eq_true, if_false] at hnavv
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  unfold RawVault.idealAssetsClawback at h1 ⊢
  rw [hST, ← hnavv] at h1 ⊢
  rcases hcase with ⟨hm0, -⟩ | ⟨hm, sn, nv, an, hsn, hnv, han, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm0] at h1; norm_num at h1
  obtain ⟨sn0, hsn0, hsnv, hsnn, -⟩ :=
    STAmount.toNumber_integral_exact' sd .to_nearest hsd.1 hsd.2.1 hsd.2.2
  have hss : sn = sn0 := Except.ok.inj (hsn.symm.trans hsn0)
  subst hss
  have hnavn : nav'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hnavok
  have hSTn := v.wf.sharesTotal_norm
  set W := nav'.toRat with hW
  set T := v.sharesTotal.toRat with hT
  set I := W * sd.toRat / T with hI
  have hT0 : 0 ≤ T := v.wf.sharesTotal_nonneg
  have hTpos : 0 < T := by
    rcases lt_or_eq_of_le hT0 with h | h
    · exact h
    · rw [hI, ← h, div_zero] at h1; norm_num at h1
  have hT1 : 1 ≤ T := by
    have := rat_one_le_sub_of_lt T 0 v.wf.sharesTotal_int rfl hTpos; linarith
  have hWs : W * sd.toRat = I * T := by rw [hI]; field_simp
  have hWs1 : 1 ≤ W * sd.toRat := by rw [hWs]; nlinarith
  obtain ⟨w1, hw1, hw1v⟩ := pos_witness_one
  obtain ⟨wh, hwh, hwhv⟩ := pos_half_witness
  have hr1 := operator_mul_rounded_to_nearest nav' sn nv hnavn hsnn hnv
  rw [hsnv] at hr1
  have hnv1 : 1 ≤ nv.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized nv _ hr1 w1 hw1 (by rw [hw1v]; exact hWs1)
    rwa [hw1v] at this
  have hsnm : sn.mantissa_ ≠ 0 := mantissa_ne_zero_of_toRat_ne (by
    rw [hsnv]; intro h0; rw [h0, mul_zero] at hWs1; norm_num at hWs1)
  have hnvm : nv.mantissa_ ≠ 0 := mantissa_ne_zero_of_toRat_ne (by linarith)
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := mantissa_ne_zero_of_toRat_ne (by rw [← hT]; linarith)
  have hnvn : nv.isNormalized := operator_mul_result_isNormalized _ _ _ _ hnavn hsnn hm hsnm hnv hnvm
  have hw1 := operator_mul_rounds_to_nearest nav' sn nv hnavn hsnn hnv hnvm
  simp only [RoundsWithin, RatValued.toRat, hsnv] at hw1
  change |nv.toRat - W * sd.toRat| ≤ |W * sd.toRat| * (5 / (2 ^ 63 + 7)) at hw1
  rw [abs_of_pos (by linarith : (0 : ℚ) < W * sd.toRat)] at hw1
  have hu1 : (0 : ℚ) ≤ 5 / (2 ^ 63 + 7) ∧ (5 / (2 ^ 63 + 7) : ℚ) ≤ 1 / 4 := by norm_num
  have hu2 : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3) ∧ (6 / (2 ^ 63 - 3) : ℚ) ≤ 1 / 4 := by norm_num
  have hnvlo : W * sd.toRat * (1 - 5 / (2 ^ 63 + 7)) ≤ nv.toRat := by
    have := (abs_le.mp hw1).1; nlinarith
  have hq : I * (1 - 5 / (2 ^ 63 + 7)) ≤ nv.toRat / T := by
    rw [le_div_iff₀ hTpos]; nlinarith
  have hq2 : 1 / 2 ≤ nv.toRat / T := by nlinarith
  have hr2 := operator_div_rounded_to_nearest nv v.sharesTotal an hnvn hSTn han
  have han1 : 1 / 2 ≤ an.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized an _ hr2 wh hwh
      (by rw [hwhv]; exact hq2)
    rwa [hwhv] at this
  have hanm : an.mantissa_ ≠ 0 := mantissa_ne_zero_of_toRat_ne (by linarith)
  have hann : an.isNormalized :=
    operator_div_result_isNormalized _ _ _ _ hnvn hSTn hnvm hSTm han hanm
  have hw2 := operator_div_rounds_to_nearest nv v.sharesTotal an hnvn hSTn han hanm
  simp only [RoundsWithin, RatValued.toRat] at hw2
  change |an.toRat - nv.toRat / T| ≤ |nv.toRat / T| * (6 / (2 ^ 63 - 3)) at hw2
  rw [abs_of_pos (by linarith : (0 : ℚ) < nv.toRat / T)] at hw2
  have hanlo : nv.toRat / T * (1 - 6 / (2 ^ 63 - 3)) ≤ an.toRat := by
    have := (abs_le.mp hw2).1; nlinarith
  have hanneg : an.negative_ = false :=
    Number.negative_false_of_normalized_nonneg an hann (by linarith)
  have hwo := STAmount.ofNumber_integral_within_one v.numericType an _ priced hint hann hanneg hof
  have hpr1 := (abs_lt.mp hwo).1
  have hchain : I * (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) ≤ an.toRat :=
    le_trans (mul_le_mul_of_nonneg_right hq (by linarith)) hanlo
  have hnum : (1 : ℚ) - depositε ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
    unfold depositε; norm_num
  have : I * (1 - depositε) ≤ I * ((1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3))) :=
    mul_le_mul_of_nonneg_left hnum (by linarith)
  nlinarith

end XRPL.Model.SingleAssetVault.ClwAcc

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.clawback_vault_updates_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hint : v.numericType.isIntegral = true)
    (hznz : assets.isZero = false)
    (hnnA : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnnA = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat := by
  obtain ⟨cr, arn, at', av', hcomp, hcerr, hra, -, harn, hat, hav, hvt, hva⟩ :=
    ClwAcc.clawback_updates v assets holderShares r hnnA hok herr
  obtain ⟨-, priced, -, hpr, hcl⟩ :=
    ClwAcc.computeClawback_priced v assets holderShares cr hznz hcomp hcerr
  obtain ⟨nav, -, hcase⟩ := ClwAcc.priced_cases v _ priced hpr
  obtain ⟨hnt, hoff, hval⟩ := ClwAcc.integral_shape_facts v.numericType priced hint (by
    rcases hcase with ⟨-, h⟩ | ⟨-, _, _, an, -, -, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨an, h⟩)
  obtain ⟨hrnt, hroff, hrval, -, -⟩ :=
    ClwAcc.clamp_neg_integral v.assetsTotal priced cr.assetsRecovered (hnt ▸ hint) hoff hcl
  obtain ⟨sn, hsn, hsnv, hsnn, hden⟩ :=
    STAmount.toNumber_integral_exact' cr.assetsRecovered .to_nearest
      (by rw [hrnt, hnt]; exact hint) hroff (by rw [hrval]; exact hval)
  have hsa : arn = sn := Except.ok.inj (harn.symm.trans hsn)
  subst hsa
  rw [hra] at hnn ⊢
  have hA := v.exact.assetsTotal_nonneg
  have hAA := v.exact.assetsAvailable_nonneg
  have hAle := v.exact.assetsAvailable_le
  have h1 := r.vault'.exact.assetsTotal_nonneg
  have h2 := r.vault'.exact.assetsAvailable_nonneg
  simp only [RawVault.toExact] at hA hAA hAle h1 h2 hsz ⊢
  rw [hvt] at h1 ⊢
  rw [hva] at h2 ⊢
  exact ⟨ClwAcc.sub_exact_of_nonneg _ _ _ _ v.wf.assetsTotal_norm hA hsz hsnn hsnv hden hnn hat h1,
    ClwAcc.sub_exact_of_nonneg _ _ _ _ v.wf.assetsAvailable_norm hAA (le_trans hAle hsz) hsnn hsnv
      hden hnn hav h2⟩

lemma Vault.clawback_assetsRecovered_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hint : v.numericType.isIntegral = true)
    (_hc : assets.Canonical) (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
      1 + v.idealAssetsClawback r.sharesDestroyed.toRat * depositε := by
  obtain ⟨cr, -, -, -, hcomp, hcerr, hra, hsd, -⟩ :=
    ClwAcc.clawback_updates v assets holderShares r hnn hok herr
  obtain ⟨X, priced, hsh, hpr, hcl⟩ :=
    ClwAcc.computeClawback_priced v assets holderShares cr hznz hcomp hcerr
  obtain ⟨hsnt, hsoff, hsval⟩ := ClwAcc.shares_shape v X _ hsh
  obtain ⟨nav, -, hcase⟩ := ClwAcc.priced_cases v _ priced hpr
  obtain ⟨hnt, hoff, -⟩ := ClwAcc.integral_shape_facts v.numericType priced hint (by
    rcases hcase with ⟨-, h⟩ | ⟨-, _, _, an, -, -, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨an, h⟩)
  obtain ⟨-, -, -, hrv, hle⟩ :=
    ClwAcc.clamp_neg_integral v.assetsTotal priced cr.assetsRecovered (hnt ▸ hint) hoff hcl
  rw [hra, hsd]
  have hrec0 : 0 ≤ cr.assetsRecovered.toRat := by rw [hrv]; positivity
  have hε : (0 : ℚ) ≤ depositε ∧ depositε ≤ 1 / 2 := by unfold depositε; norm_num
  set I := v.idealAssetsClawback cr.sharesDestroyed.toRat with hI
  by_cases h1 : 1 < I
  · have := ClwAcc.priced_lower v hnav hint cr.sharesDestroyed priced
      ⟨by rw [hsnt]; rfl, hsoff, hsval⟩ hpr h1
    linarith
  · push Not at h1
    rcases le_or_gt 0 I with h0 | h0
    · nlinarith
    · nlinarith

end XRPL.Model.SingleAssetVault
