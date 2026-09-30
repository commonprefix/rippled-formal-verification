import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Proofs.WithdrawMono.OfNumber
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.ClampFacts

/-! # Withdraw pricing is monotone in the burned shares

`sharesToAssetsWithdraw` is `nav·shares/sharesTotal` rounded `.to_nearest` at each
stage and packed `.to_nearest`; each stage is monotone. A nonzero smaller payout
anchors the smaller quotient far above the `Number` underflow, so the larger run's
stages cannot flush to zero. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- A zero-mantissa source packs to zero. -/
lemma ofNumber_mant0 (nt : NumericType) (n : Number) (mode : rounding_mode) (r : STAmount)
    (hz : n.mantissa_ = 0) (hok : STAmount.ofNumber nt n mode = .ok r) : r.mValue = 0 := by
  unfold STAmount.ofNumber at hok
  dsimp only at hok
  set neg := decide (n.signum < 0) with hneg
  set w := (if neg = true then n.operator_neg else n) with hw
  have hwz : w.mantissa_ = 0 := by
    rw [hw]; split
    · unfold Number.operator_neg; rw [if_pos (by simp [hz])]; rfl
    · exact hz
  have hchk : ∀ (m : UInt64) (e : Int), m = 0 →
      STAmount.checked nt m e neg mode = .ok r → r.mValue = 0 := by
    intro m e hm h
    subst hm
    unfold STAmount.checked STAmount.canonicalize at h
    split at h
    · split at h
      · rw [← Except.ok.inj h]
      · simp [STAmount.unchecked] at *
    · have hiou : (STAmount.unchecked nt 0 e neg).iou mode = .ok IOUAmount.zero := by
        unfold STAmount.iou IOUAmount.ofMantissaExp IOUAmount.normalize
        rw [if_neg (by assumption)]
        have : (STAmount.unchecked nt 0 e neg).signedDrops.toInt64 = 0 := by
          unfold STAmount.signedDrops STAmount.unchecked; split <;> rfl
        rw [this]; rfl
      rw [hiou] at h
      rw [← Except.ok.inj h]
      rfl
  split at hok
  · cases hr : w.to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok iv =>
      rw [hr] at hok
      simp only [] at hok
      have hiv : iv = 0 := by
        unfold Number.to_rep at hr
        have hm : w.mantissa = 0 := by
          unfold Number.mantissa; rw [hwz]; simp
        simp only [hm] at hr
        exact (Except.ok.inj hr).symm
      exact hchk _ 0 (by rw [hiv]; rfl) hok
  · cases hr : w.normalizeToRange kMinValue kMaxValue mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok me =>
      obtain ⟨mant, exp⟩ := me
      rw [hr] at hok
      simp only [] at hok
      have hmant : mant = 0 := by
        unfold Number.normalizeToRange doNormalize at hr
        rw [if_pos (by simp [hwz])] at hr
        have := congrArg Prod.fst (Except.ok.inj hr)
        simp only at this
        rw [← this]; rfl
      exact hchk _ exp (by rw [hmant]; rfl) hok

/-- The pricing steps of `sharesToAssetsWithdraw`. -/
lemma price_reduces (v : Vault) (s p : STAmount) (w : Bool)
    (hok : v.sharesToAssetsWithdraw s w = .ok p) :
    ∃ nav, v.assetsTotal.operator_sub (match w with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok nav ∧
      ((nav.mantissa_ = 0 ∧ p = STAmount.zero v.numericType) ∨
       (nav.mantissa_ ≠ 0 ∧ ∃ sn NV aN, s.toNumber .to_nearest = .ok sn ∧
          nav.operator_mul sn .to_nearest = .ok NV ∧
          NV.operator_div v.sharesTotal .to_nearest = .ok aN ∧
          STAmount.ofNumber v.numericType aN .to_nearest = .ok p)) := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact ⟨_, ‹_›, Or.inl ⟨beq_iff_eq.mp ‹_›, rfl⟩⟩
    | exact ⟨_, ‹_›, Or.inr ⟨fun h => ‹¬ _› (beq_iff_eq.mpr h), _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩

private lemma doNormalize_zero_shape (neg : Bool) (m : UInt64) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize neg m e minM maxM mode = .ok result) (h0 : result.mantissa_ = 0) :
    result = Number.zero := by
  unfold doNormalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok; exact (Except.ok.inj hok).symm
  rw [if_neg hm] at hok
  simp only [] at hok
  rcases hsu : doNormalize_scaleUp minM m e with ⟨m₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
  cases hsd : doNormalize_scaleDown maxM m₁ e₁
      (if neg then Guard.new.set_negative else Guard.new) with
  | error err => rw [hsd] at hok; simp at hok
  | ok sd =>
    obtain ⟨m₂, e₂, g₂⟩ := sd
    rw [hsd] at hok
    simp only [] at hok
    by_cases hund : (e₂ < minExponent || m₂ < minM) = true
    · rw [if_pos hund] at hok; exact (Except.ok.inj hok).symm
    · rw [if_neg hund] at hok
      cases hcap : doNormalize_capAtMaxRep m₂ e₂ g₂ with
      | error err => rw [hcap] at hok; simp at hok
      | ok cp =>
        obtain ⟨m₃, e₃, g₃⟩ := cp
        rw [hcap] at hok
        simp only [] at hok
        cases hru : g₃.doRoundUp neg m₃ e₃ minM maxM mode .normalize2 with
        | error err => rw [hru] at hok; simp at hok
        | ok res =>
          rw [hru] at hok
          simp only [] at hok
          have hres : result = res.toNumber := (Except.ok.inj hok).symm
          rw [hres] at h0 ⊢
          exact Guard.doRoundUp_zero_shape g₃ neg m₃ e₃ minM maxM mode .normalize2 res hru h0

/-- A zero-mantissa product of normalized operands is the literal zero. -/
lemma mul_zero_shape (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y mode = .ok result) (h0 : result.mantissa_ = 0) :
    result = Number.zero := by
  unfold Number.operator_mul at hok
  by_cases hxz : x.operator_eq Number.zero = true
  · rw [if_pos hxz] at hok
    have := (Except.ok.inj hok).symm; subst this
    exact Number.eq_zero_of_mantissa_zero result hx h0
  rw [if_neg hxz] at hok
  by_cases hyz : y.operator_eq Number.zero = true
  · rw [if_pos hyz] at hok
    have := (Except.ok.inj hok).symm; subst this
    exact Number.eq_zero_of_mantissa_zero result hy h0
  rw [if_neg hyz] at hok
  simp only [] at hok
  split at hok
  · simp at hok
  · rename_i res _
    unfold Number.normalize at hok
    exact doNormalize_zero_shape res.toNumber.negative_ res.toNumber.mantissa_
      res.toNumber.exponent_ _ _ _ result hok h0

/-- A zero-mantissa quotient of normalized operands is the literal zero. -/
lemma div_zero_shape (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y mode = .ok result) (h0 : result.mantissa_ = 0) :
    result = Number.zero := by
  have hym : y.mantissa_ ≠ 0 := operator_div_divisor_ne_zero x y result _ hy hok
  by_cases hxm : x.mantissa_ = 0
  · have hxz := Number.eq_zero_of_mantissa_zero x hx hxm
    unfold Number.operator_div at hok
    rw [if_neg (by
      intro h
      exact hym (Number.mantissa_eq_zero_of_operator_eq_zero h)),
      if_pos (by rw [hxz]; decide)] at hok
    rw [← hxz]; exact (Except.ok.inj hok).symm
  obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _, _, _⟩ :=
    operator_div_algorithmic_facts_represents x y result mode hx hy hxm hym hok
  exact doNormalize128_zero_shape _ _ _ _ _ result hok128 h0

lemma mul_norm (x y result : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .to_nearest = .ok result) : result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [mul_zero_shape x y result .to_nearest hx hy hok h0]; exact Or.inl rfl
  · obtain ⟨hxm, hym⟩ := operator_mul_operands_ne_zero hx hy hok h0
    exact operator_mul_result_isNormalized x y result .to_nearest hx hy hxm hym hok h0

lemma div_norm (x y result : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok result) : result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [div_zero_shape x y result .to_nearest hx hy hok h0]; exact Or.inl rfl
  · obtain ⟨hxm, hym⟩ := operator_div_operands_ne_zero hx hy hok h0
    exact operator_div_result_isNormalized x y result .to_nearest hx hy hxm hym hok h0

/-- The withdraw net asset value: normalized, non-negative, and exact. -/
lemma nav_facts (v : Vault) (w : Bool) (nav : Number)
    (hsub : v.assetsTotal.operator_sub (match w with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok nav) (hnav : v.WithdrawNavExact w) :
    nav.isNormalized ∧ 0 ≤ nav.toRat ∧
      nav.toRat = (if w then v.depositNav else v.withdrawNav) := by
  obtain ⟨nv, he, hval⟩ := hnav
  have hnv : nav = nv := Except.ok.inj (hsub.symm.trans he)
  subst hnv
  refine ⟨?_, ?_, hval⟩
  · cases w
    · exact operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub
    · exact operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub
  · rw [hval]
    cases w
    · exact v.exact.withdraw_nav_nonneg
    · exact v.exact.assetsTotal_nonneg

private lemma zero_amount_toNumber (r : STAmount) (hz : r.mValue = 0)
    (hoff : r.mNumericType.isIntegral = true → r.mOffset = 0) :
    ∀ pn, r.toNumber .to_nearest = .ok pn → pn.isNormalized ∧ pn.toRat = r.toRat := by
  intro pn hpn
  by_cases hint : r.mNumericType.isIntegral = true
  · obtain ⟨sn, hsn, hval, hnorm, _⟩ := STAmount.toNumber_integral_exact' r .to_nearest hint
      (hoff hint) (by rw [hz]; exact Nat.zero_le _)
    rw [Except.ok.inj (hpn.symm.trans hsn)]; exact ⟨hnorm, hval⟩
  · rw [STAmount.toNumber_zero_fractional r .to_nearest (by simpa using hint : r.mNumericType.isIntegral = false) hz] at hpn
    rw [← Except.ok.inj hpn, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hz]
    exact ⟨Or.inl rfl, rfl⟩

/-- The priced payout: non-negative, of the vault's type, canonical when fractional
and nonzero, and exactly convertible to a `Number`. -/
lemma price_facts (v : Vault) (w : Bool) (s p : STAmount) (hc : s.Canonical)
    (hnn : 0 ≤ s.toRat) (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw s w = .ok p) :
    0 ≤ p.toRat ∧ p.mNumericType = v.numericType ∧
    (v.numericType.isIntegral = false → p.mValue ≠ 0 → p.IOUCanonical) ∧
    (∀ pn, p.toNumber .to_nearest = .ok pn → pn.isNormalized ∧ pn.toRat = p.toRat) := by
  obtain ⟨nav, hsub, hcase⟩ := price_reduces v s p w hok
  obtain ⟨hnavn, hnav0, _⟩ := nav_facts v w nav hsub hnav
  rcases hcase with ⟨_, rfl⟩ | ⟨_, sn, NV, aN, hsn, hmul, hdiv, hof⟩
  · have hz : (STAmount.zero v.numericType).mValue = 0 := by cases v.numericType <;> rfl
    have hnt : (STAmount.zero v.numericType).mNumericType = v.numericType := by
      cases v.numericType <;> rfl
    refine ⟨by rw [STAmount.toRat_eq_zero_of_mValue_zero _ hz], hnt, fun _ h => absurd hz h,
      zero_amount_toNumber _ hz ?_⟩
    rw [hnt]; intro hi
    cases h : v.numericType with
    | fractional => rw [h] at hi; exact absurd hi (by decide)
    | integral => rfl
  · obtain ⟨sn', hsn', hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical s .to_nearest
      (STAmount.Canonical.exactCanonical s hc)
    have hs : sn = sn' := Except.ok.inj (hsn.symm.trans hsn')
    subst hs
    have hNVn := mul_norm nav sn NV hnavn hsnn hmul
    have hNV0 : 0 ≤ NV.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg NV _
      (operator_mul_rounded_to_nearest nav sn NV hnavn hsnn hmul)
      (mul_nonneg hnav0 (by rw [hsnv]; exact hnn))
    have haNn := div_norm NV v.sharesTotal aN hNVn v.wf.sharesTotal_norm hdiv
    have haN0 : 0 ≤ aN.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg aN _
      (operator_div_rounded_to_nearest NV v.sharesTotal aN hNVn v.wf.sharesTotal_norm hdiv)
      (div_nonneg hNV0 v.wf.sharesTotal_nonneg)
    exact ofNumber_facts v.numericType aN p haNn haN0 hof

private lemma sigma_le : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-90 : ℤ) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
  exact zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; norm_num)

set_option maxHeartbeats 1000000 in
-- high budget: the underflow chain is closed by several nonlinear steps
/-- **`sharesToAssetsWithdraw` is monotone in the shares** (given the smaller price
is nonzero). -/
lemma price_mono (v : Vault) (w : Bool) (s₁ s₂ p₁ p₂ : STAmount)
    (hc₁ : s₁.Canonical) (hc₂ : s₂.Canonical) (hnn₁ : 0 ≤ s₁.toRat) (_hnn₂ : 0 ≤ s₂.toRat)
    (hnav : v.WithdrawNavExact w)
    (hok₁ : v.sharesToAssetsWithdraw s₁ w = .ok p₁) (hok₂ : v.sharesToAssetsWithdraw s₂ w = .ok p₂)
    (hle : s₁.toRat ≤ s₂.toRat) (hz : p₁.mValue ≠ 0) : p₁.toRat ≤ p₂.toRat := by
  obtain ⟨nav, hsub, hcase₁⟩ := price_reduces v s₁ p₁ w hok₁
  obtain ⟨nav', hsub', hcase₂⟩ := price_reduces v s₂ p₂ w hok₂
  have hnn' : nav' = nav := Except.ok.inj (hsub'.symm.trans hsub)
  subst hnn'
  obtain ⟨hnavn, hnav0, _⟩ := nav_facts v w nav' hsub hnav
  have hz0 : (STAmount.zero v.numericType).mValue = 0 := by cases v.numericType <;> rfl
  rcases hcase₁ with ⟨_, rfl⟩ | ⟨hnavm, sn₁, NV₁, aN₁, hsn₁, hmul₁, hdiv₁, hof₁⟩
  · exact absurd hz0 hz
  rcases hcase₂ with ⟨h, _⟩ | ⟨_, sn₂, NV₂, aN₂, hsn₂, hmul₂, hdiv₂, hof₂⟩
  · exact absurd h hnavm
  set nav := nav'
  obtain ⟨sn₁', h1', hsnv₁, hsnn₁⟩ := STAmount.toNumber_exact_canonical s₁ .to_nearest
    (STAmount.Canonical.exactCanonical s₁ hc₁)
  have e1 : sn₁ = sn₁' := Except.ok.inj (hsn₁.symm.trans h1')
  subst e1
  obtain ⟨sn₂', h2', hsnv₂, hsnn₂⟩ := STAmount.toNumber_exact_canonical s₂ .to_nearest
    (STAmount.Canonical.exactCanonical s₂ hc₂)
  have e2 : sn₂ = sn₂' := Except.ok.inj (hsn₂.symm.trans h2')
  subst e2
  have hnavp : 0 < nav.toRat :=
    lt_of_le_of_ne hnav0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero nav hnavm))
  -- run 1: every stage is nonzero
  have haN₁m : aN₁.mantissa_ ≠ 0 := fun h => hz (ofNumber_mant0 _ _ _ _ h hof₁)
  have hNV₁n := mul_norm nav sn₁ NV₁ hnavn hsnn₁ hmul₁
  obtain ⟨hNV₁m, hSTm⟩ := operator_div_operands_ne_zero hNV₁n v.wf.sharesTotal_norm hdiv₁ haN₁m
  obtain ⟨_, hsn₁m⟩ := operator_mul_operands_ne_zero hnavn hsnn₁ hmul₁ hNV₁m
  have hANn₁ := div_norm NV₁ v.sharesTotal aN₁ hNV₁n v.wf.sharesTotal_norm hdiv₁
  have hNV₁0 : 0 ≤ NV₁.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg NV₁ _
    (operator_mul_rounded_to_nearest nav sn₁ NV₁ hnavn hsnn₁ hmul₁)
    (mul_nonneg hnav0 (by rw [hsnv₁]; exact hnn₁))
  have haN₁0 : 0 ≤ aN₁.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg aN₁ _
    (operator_div_rounded_to_nearest NV₁ v.sharesTotal aN₁ hNV₁n v.wf.sharesTotal_norm hdiv₁)
    (div_nonneg hNV₁0 v.wf.sharesTotal_nonneg)
  have hanchor : (10 : ℚ) ^ (-82 : ℤ) ≤ aN₁.toRat :=
    ofNumber_anchor v.numericType aN₁ p₁ hANn₁ haN₁0 hof₁ hz
  set ST : ℚ := v.sharesTotal.toRat with hST_def
  have hSTp : 0 < ST :=
    lt_of_le_of_ne v.wf.sharesTotal_nonneg
      (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.sharesTotal hSTm))
  have hST1 : 1 ≤ ST := by
    have hden : v.sharesTotal.toRat.den = 1 := v.wf.sharesTotal_int
    have heq : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      rw [← Rat.num_div_den v.sharesTotal.toRat, hden]; simp
    rw [hST_def, heq]
    have hpos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hSTp
    exact_mod_cast (by omega : (1 : ℤ) ≤ v.sharesTotal.toRat.num)
  have hsnp₁ : 0 < sn₁.toRat :=
    lt_of_le_of_ne (hsnv₁ ▸ hnn₁) (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero sn₁ hsn₁m))
  have hsn₂pos : 0 < sn₂.toRat := by rw [hsnv₂]; exact lt_of_lt_of_le (by rw [← hsnv₁]; exact hsnp₁) hle
  have hsn₂m : sn₂.mantissa_ ≠ 0 :=
    fun h => (ne_of_gt hsn₂pos) (Number.toRat_eq_zero_of_mantissa_zero sn₂ h)
  have hsnle : sn₁.toRat ≤ sn₂.toRat := by rw [hsnv₁, hsnv₂]; exact hle
  set Q : ℚ := nav.toRat * sn₁.toRat with hQ_def
  set R : ℚ := nav.toRat * sn₂.toRat with hR_def
  have hQpos : 0 < Q := mul_pos hnavp hsnp₁
  have hRpos : 0 < R := mul_pos hnavp hsn₂pos
  have hQR : Q ≤ R := mul_le_mul_of_nonneg_left hsnle (le_of_lt hnavp)
  have hε₂le : (5 : ℚ) / (2 ^ 63 + 7) ≤ 1 := by norm_num
  have hε₂half : (5 : ℚ) / (2 ^ 63 + 7) ≤ 1 / 2 := by norm_num
  have hε₃le : (6 : ℚ) / (2 ^ 63 - 3) ≤ 1 := by norm_num
  have hmul1b : |NV₁.toRat - Q| ≤ Q * (5 / (2 ^ 63 + 7)) := by
    have h : |NV₁.toRat - Q| ≤ |Q| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest nav sn₁ NV₁ hnavn hsnn₁ hmul₁ hNV₁m
    rwa [abs_of_pos hQpos] at h
  have hNV1pos : 0 < NV₁.toRat := by
    have := abs_le.mp hmul1b; nlinarith [hQpos, hε₂le, this.1]
  have hdiv_cl : |aN₁.toRat * ST - NV₁.toRat| ≤ NV₁.toRat * (6 / (2 ^ 63 - 3)) := by
    have hb : |aN₁.toRat - NV₁.toRat / ST| ≤ NV₁.toRat / ST * (6 / (2 ^ 63 - 3)) := by
      have h : |aN₁.toRat - NV₁.toRat / v.sharesTotal.toRat|
          ≤ |NV₁.toRat / v.sharesTotal.toRat| * (6 / (2 ^ 63 - 3)) :=
        operator_div_rounds_to_nearest NV₁ v.sharesTotal aN₁ hNV₁n
          v.wf.sharesTotal_norm hdiv₁ haN₁m
      rwa [← hST_def, abs_of_pos (by positivity : (0 : ℚ) < NV₁.toRat / ST)] at h
    have hrw : aN₁.toRat * ST - NV₁.toRat = (aN₁.toRat - NV₁.toRat / ST) * ST := by field_simp
    rw [hrw, abs_mul, abs_of_pos hSTp]
    calc |aN₁.toRat - NV₁.toRat / ST| * ST
        ≤ (NV₁.toRat / ST * (6 / (2 ^ 63 - 3))) * ST :=
          mul_le_mul_of_nonneg_right hb (le_of_lt hSTp)
      _ = NV₁.toRat * (6 / (2 ^ 63 - 3)) := by
            rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hSTp)]
  have hσ82 := sigma_le
  have h82_8 : (10 : ℚ) ^ (-90 : ℤ) * 8 ≤ 10 ^ (-82 : ℤ) := by
    have he : (10 : ℚ) ^ (-82 : ℤ) = 10 ^ (-90 : ℤ) * 10 ^ (8 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    have hp : (0 : ℚ) < (10 : ℚ) ^ (-90 : ℤ) := zpow_pos (by norm_num) _
    have h8 : (10 : ℚ) ^ (8 : ℤ) = 100000000 := by norm_num
    rw [he, h8]; nlinarith [hp]
  have h2NV1 : aN₁.toRat * ST ≤ 2 * NV₁.toRat := by
    have := abs_le.mp hdiv_cl; nlinarith [hNV1pos, hε₃le, this.2]
  have h2Q : NV₁.toRat ≤ 2 * Q := by
    have := abs_le.mp hmul1b; nlinarith [hQpos, hε₂le, this.1]
  have hanchor_ST : (10 : ℚ) ^ (-82 : ℤ) * ST ≤ aN₁.toRat * ST :=
    mul_le_mul_of_nonneg_right hanchor (le_of_lt hSTp)
  have h4Q_ST : (10 : ℚ) ^ (-82 : ℤ) * ST ≤ 4 * Q := by
    have h4 : aN₁.toRat * ST ≤ 4 * Q := by linarith [h2NV1, h2Q]
    linarith [hanchor_ST, h4]
  have hR_ge : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ R := by
    have hQ1 : (10 : ℚ) ^ (-82 : ℤ) ≤ 4 * Q := by
      calc (10 : ℚ) ^ (-82 : ℤ) = (10 : ℚ) ^ (-82 : ℤ) * 1 := (mul_one _).symm
        _ ≤ (10 : ℚ) ^ (-82 : ℤ) * ST := mul_le_mul_of_nonneg_left hST1 (by positivity)
        _ ≤ 4 * Q := h4Q_ST
    nlinarith [hQR, hQ1, hσ82, h82_8]
  have hNVm₂ : NV₂.mantissa_ ≠ 0 := by
    intro h0
    have hRlt := operator_mul_underflow_truth_small nav sn₂ NV₂ .to_nearest hnavn hsnn₂
      hnavm hsn₂m hmul₂ h0
    rw [← hR_def, abs_of_pos hRpos] at hRlt
    linarith [hR_ge, hRlt]
  have hNVn₂ := mul_norm nav sn₂ NV₂ hnavn hsnn₂ hmul₂
  have hmul2b : |NV₂.toRat - R| ≤ R * (5 / (2 ^ 63 + 7)) := by
    have h : |NV₂.toRat - R| ≤ |R| * (5 / (2 ^ 63 + 7)) :=
      operator_mul_rounds_to_nearest nav sn₂ NV₂ hnavn hsnn₂ hmul₂ hNVm₂
    rwa [abs_of_pos hRpos] at h
  have hR2NV2 : R ≤ 2 * NV₂.toRat := by
    have := abs_le.mp hmul2b; nlinarith [hRpos, hε₂half, this.1]
  have hσST : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) * ST ≤ NV₂.toRat := by
    have h8NV2 : (10 : ℚ) ^ (-82 : ℤ) * ST ≤ 8 * NV₂.toRat := by
      nlinarith [hQR, hR2NV2, h4Q_ST]
    nlinarith [h8NV2, hσ82, h82_8, hSTp]
  have hNV2pos : 0 < NV₂.toRat := by linarith [hR2NV2, hRpos]
  have haNm₂ : aN₂.mantissa_ ≠ 0 := by
    intro h0
    have hlt := operator_div_underflow_truth_small NV₂ v.sharesTotal aN₂ .to_nearest hNVn₂
      v.wf.sharesTotal_norm hNVm₂ hSTm hdiv₂ h0
    rw [← hST_def, abs_of_pos (div_pos hNV2pos hSTp)] at hlt
    rw [div_lt_iff₀ hSTp] at hlt
    linarith [hσST, hlt]
  have hANn₂ := div_norm NV₂ v.sharesTotal aN₂ hNVn₂ v.wf.sharesTotal_norm hdiv₂
  have hneg : ∀ n : Number, n.isNormalized → 0 ≤ n.toRat → n.negative_ = false :=
    fun n hn h0 => Number.negative_false_of_normalized_nonneg n hn h0
  have haNle : aN₁.toRat ≤ aN₂.toRat :=
    Number.mul_div_num_mono nav v.sharesTotal sn₁ sn₂ NV₁ NV₂ aN₁ aN₂
      hnavn hnavm (hneg nav hnavn hnav0) v.wf.sharesTotal_norm hSTm
      (hneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg)
      hsnn₁ hsn₁m (hneg _ hsnn₁ (le_of_lt hsnp₁)) hsnn₂ hsn₂m (hneg _ hsnn₂ (le_of_lt hsn₂pos))
      hmul₁ hNV₁m hmul₂ hNVm₂ hdiv₁ haN₁m hdiv₂ haNm₂ hsnle
  exact ofNumber_mono v.numericType aN₁ aN₂ p₁ p₂ hANn₁ hANn₂ haN₁0 haNle hof₁ hof₂

end XRPL.Model.SingleAssetVault.WdMono
