import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Proofs.DepositTight.Shares
import XRPL.Properties.Vault.Common.Reduction

/-! # Tight accuracy bounds of `Vault.deposit` -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- The largest 16-digit mantissa at exponent `k`, as a canonical amount. -/
lemma top_canon (k : ℤ) (h1 : -96 ≤ k) (h2 : k ≤ 80) :
    (⟨.fractional, 9999999999999999, k, false⟩ : STAmount).IOUCanonical :=
  ⟨rfl, by show 10 ^ 15 ≤ (9999999999999999 : UInt64).toNat; decide,
    by show (9999999999999999 : UInt64).toNat < 10 ^ 16; decide, h1, h2⟩

/-- Arithmetic core of the lower charge bound: the three shortfalls add up. -/
lemma lower_combine (I Q p c ε g gx half : ℚ)
    (hQ : |Q - I| ≤ I * ε) (hp : |p - Q| ≤ half) (hc : p - g ≤ c)
    (hhalf : half ≤ 1 / 2 * gx) (hg : g ≤ gx) :
    I * (1 - ε) - 3 / 2 * gx ≤ c := by
  have := (abs_le.mp hQ).1
  have := (abs_le.mp hp).1
  linarith

end XRPL.Model.SingleAssetVault.DepTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- **Tight deposit charge bound.** The taken amount never exceeds the request; it
is at most `depositε` relatively plus `3/2` steps of the post-deposit grid
`10^e` below the issued shares' exact worth (half a step from the `to_nearest`
pricing, one from the sum clamp); a zero taken amount forces a sub-unit ideal;
and it overpays by at most `depositε` relatively plus half a unit of its own last
digit. -/
lemma Vault.deposit_charge_proof (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat ≤ amountDeposit.toRat ∧
    (∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) - 3 / 2 * (10 : ℚ) ^ e ≤
        r.amountDeposit'.toRat) ∧
    (r.amountDeposit'.isZero = true →
      v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) <
        if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      v.idealChargeDeposit r.sharesIssued.toRat * depositε +
        1 / 2 * (10 : ℚ) ^ r.amountDeposit'.exponent := by
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, hanz, _, _, _, hcd, _, _, _, _, _, _,
    hamt, hshr, _⟩ := DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
  obtain ⟨p, hcdp, hclamp, hfnp⟩ := hcd rfl
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount p sh hcdp
  have hamt_canon : amount.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit amount v.assetsTotal hcanon hround
      with h | h
    · exact h
    · rw [h] at hanz; exact absurd hanz (by decide)
  have hamt_nn : 0 ≤ amount.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
  have hamt_mv : amount.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hanz; exact hanz)
  have hamt_pos : 0 < amount.toRat :=
    lt_of_le_of_ne hamt_nn (Ne.symm (fun h => hamt_mv ((STAmount.toRat_eq_zero_iff amount).mp h)))
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amount shares hamt_canon hamt_pos hats hsz
  have hcr : r.amountDeposit' = c := hamt
  have hsr : r.sharesIssued = shares := by rw [hshr]; exact hsheq
  rw [hcr, hsr]
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hATnn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hpnn : 0 ≤ p.toRat := sharesToAssetsDeposit_nonneg v shares p hshc hshnt hshpos hsad
  have hrle : c.toRat ≤ p.toRat := DepRnd.Vault.deposit_charge_le v shares p c hshc hshnt hshpos hsad hclamp
  have hrnn : 0 ≤ c.toRat :=
    Vault.deposit_charge_nonneg v shares p c hshc hshnt hshpos hsad hclamp hfnp
  have hle_amt : amount.toRat ≤ amountDeposit.toRat :=
    rtve_le amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
  have hcmp_ty : STAmount.areComparable p amount = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; rw [STAmount.areComparable_comm]; simpa using hcond
  have hpriced_le : p.toRat ≤ amount.toRat := by
    by_cases hc0 : p.mValue = 0
    · rw [(STAmount.toRat_eq_zero_iff _).mpr hc0]; exact hamt_nn
    · have hexact : p.ExactCanonical := by
        rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares p hshc hshnt hsad with h | h0
        · exact h
        · exact absurd h0 hc0
      have hcmpF : STAmount.CmpFaithful p amount :=
        STAmount.CmpFaithful.ofExactCanonical p amount hexact
          (STAmount.Canonical.exactCanonical amount hamt_canon) hcmp_ty
          (fun h => absurd h hc0) (fun h => absurd h hamt_mv)
      exact computeDeposit_success_charge_le v amount p sh hcmpF hcdp
  have hcty : p.mNumericType = v.numericType := sharesToAssetsDeposit_mNumericType v shares p hsad
  have hamt_ty : amount.mNumericType = v.numericType := by
    have hb := hcmp_ty; unfold STAmount.areComparable at hb
    exact (beq_iff_eq.mp hb).symm.trans hcty
  have hx_ty : amountDeposit.mNumericType = v.numericType := by
    rw [← hamt_ty]
    exact (roundToVaultExponent_mNumericType amountDeposit v.assetsTotal amount hcanon hround).symm
  refine ⟨by linarith, ?_⟩
  by_cases hint : v.numericType.isIntegral = true
  · ------------------------------------------------------------------ integral vault
    have hid : c = p :=
      clampToSumExponent_integral_nonneg v.assetsTotal p c
        (by show p.mNumericType.isIntegral = true; rw [hcty]; exact hint) hpnn hclamp
    subst hid
    have hxint : amountDeposit.integral = true := by
      show amountDeposit.mNumericType.isIntegral = true; rw [hx_ty]; exact hint
    by_cases hmz : v.assetsTotal.mantissa_ = 0
    · obtain ⟨hex, hexs⟩ := charge_empty_integral v shares c hint hshc hshnt hshpos hmz hsad
      refine ⟨fun e _ => ?_, fun hz => ?_, ?_⟩
      · rw [hex]
        have : (0 : ℚ) ≤ 10 ^ e := le_of_lt (zpow_pos (by norm_num) _)
        nlinarith [mul_nonneg (le_of_lt hshpos) hεnn]
      · exfalso
        have hz' : c.toRat = 0 := by
          rw [STAmount.isZero] at hz
          exact (STAmount.toRat_eq_zero_iff c).mpr (beq_iff_eq.mp hz)
        linarith
      · rw [hex, sub_self]
        have : (0 : ℚ) < 10 ^ c.exponent := zpow_pos (by norm_num) _
        have : 0 ≤ v.idealChargeDeposit shares.toRat := by rw [← hex]; exact hpnn
        nlinarith [mul_nonneg this hεnn]
    · obtain ⟨Q, hQc, hIpos, hQcases⟩ := charge_nonempty v shares c hshc hshnt hshpos hmz hsad
      set I := v.idealChargeDeposit shares.toRat with hI
      have hc_exp0 : ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → e = 0 :=
        fun e he => post_exp_integral v.assetsTotal amountDeposit e hxint he
      rcases hQcases with ⟨hm, hn, hneg, hb⟩ | ⟨hm, hb⟩
      · obtain ⟨z, hz, -, hzQ, hoff, -, -⟩ :=
          WdMono.int_pack v.numericType hint Q c hn (Number.toRat_nonneg_of_nonnegative Q hneg) hQc
        have hb' := abs_le.mp hb
        have hzQ' := abs_le.mp hzQ
        refine ⟨fun e he => ?_, fun hzr => ?_, ?_⟩
        · rw [hc_exp0 e he, hz]; norm_num; linarith
        · have hz0 : c.toRat = 0 := by
            rw [STAmount.isZero] at hzr
            exact (STAmount.toRat_eq_zero_iff c).mpr (beq_iff_eq.mp hzr)
          rw [if_pos hint]
          rw [hz] at hz0
          rw [hz0] at hzQ'
          linarith
        · have : c.exponent = 0 := hoff
          rw [this, hz]; norm_num; linarith
      · have hc0 : c.mValue = 0 := by
          by_contra hne
          exact (STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest c hint hQc hne) hm
        have hcz : c.toRat = 0 := (STAmount.toRat_eq_zero_iff c).mpr hc0
        have htiny : (10 : ℚ) ^ (-32700 : ℤ) ≤ 1 / 2 :=
          le_trans (zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10)
            (show (-32700 : ℤ) ≤ -1 by norm_num)) (by norm_num)
        refine ⟨fun e he => ?_, fun _ => ?_, ?_⟩
        · rw [hc_exp0 e he, hcz]; norm_num; nlinarith [mul_nonneg (le_of_lt hIpos) hεnn]
        · rw [if_pos hint]; nlinarith [mul_nonneg (le_of_lt hIpos) hεnn]
        · rw [hcz]
          have : (0 : ℚ) < 10 ^ c.exponent := zpow_pos (by norm_num) _
          nlinarith [mul_nonneg (le_of_lt hIpos) hεnn]
  · ------------------------------------------------------------------ fractional vault
    have hintf : v.numericType.isIntegral = false := by simpa using hint
    have hvfrac : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral _ _ _ _ => rw [h] at hintf; simp [NumericType.isIntegral] at hintf
    have hpfrac : p.integral = false := by
      show p.mNumericType.isIntegral = false; rw [hcty]; exact hintf
    have hpcz : p.IOUCanonical ∨ p.mValue = 0 := by
      by_cases h0 : p.mValue = 0
      · exact Or.inr h0
      · rcases sharesToAssetsDeposit_disj_canonical v shares p hshc hshnt hsad h0 with h | h
        · exact Or.inl h
        · exfalso; have := h.is_integral; rw [hcty] at this; rw [this] at hintf; exact absurd hintf (by decide)
    have hpty : p.mNumericType = .fractional := by rw [hcty, hvfrac]
    have hcty' : c.mNumericType = .fractional := clamp_nt v.assetsTotal p c v.wf.assetsTotal_norm hpty hpcz hclamp
    have hcfrac : c.integral = false := by unfold STAmount.integral; rw [hcty']; rfl
    obtain ⟨hcm, hcneg⟩ := STAmount.fnp_false_pos c hcfrac hfnp
    have hc_pos : 0 < c.toRat := STAmount.toRat_pos_of c hcneg hcm
    have hp_pos : 0 < p.toRat := lt_of_lt_of_le hc_pos hrle
    have hpm : p.mValue ≠ 0 := fun h => by
      rw [(STAmount.toRat_eq_zero_iff p).mpr h] at hp_pos; exact lt_irrefl _ hp_pos
    have hpc : p.IOUCanonical := hpcz.resolve_right hpm
    have hpneg : p.mIsNegative = false := STAmount.mIsNegative_false_of_pos p hp_pos
    have hcc : c.IOUCanonical := by
      rcases (clampToSumExponent_sum_shape v.assetsTotal p c v.wf.assetsTotal_norm hpcz hpfrac
        hpneg hclamp).2 with h | h
      · exact h
      · exact absurd h hcm
    obtain ⟨ep, hep⟩ := clamp_post_exists v.assetsTotal p c hpfrac hpneg hclamp
    have hcl_ge := clamp_sum_ge v.assetsTotal p c ep v.wf.assetsTotal_norm hATnn hpc hpneg hep
      hclamp hc_pos
    obtain ⟨hpe_le, -, -, -, -⟩ := post_exp_facts v.assetsTotal p ep v.wf.assetsTotal_norm hATnn hpc
      hpneg hep
    have hxfrac : amountDeposit.integral = false := by
      unfold STAmount.integral; rw [hx_ty]; exact hintf
    have hxc : amountDeposit.IOUCanonical := hcanon.2 hxfrac
    have hxneg : amountDeposit.mIsNegative = false := STAmount.mIsNegative_false_of_pos _ hpos
    have hamtfrac : amount.mNumericType = .fractional := by rw [hamt_ty, hvfrac]
    set I := v.idealChargeDeposit shares.toRat with hI
    -- the pricing facts: an exact charge on an empty vault, a half-ULP pack otherwise
    obtain ⟨Q, hQI, hQp, hQle⟩ : ∃ Q : ℚ, |Q - I| ≤ I * depositε ∧
        |p.toRat - Q| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent ∧
        (c.exponent < p.exponent → c.toRat ≤ Q) := by
      by_cases hmz : v.assetsTotal.mantissa_ = 0
      · have hex : p.toRat = I :=
          empty_frac_charge_exact v amount shares p hintf hmz hamt_canon hamtfrac hats hsz hsad
        refine ⟨I, by rw [sub_self, abs_zero]; exact mul_nonneg (by rw [← hex]; exact hpnn) hεnn,
          by rw [hex, sub_self, abs_zero]; positivity, fun _ => by rw [← hex]; exact hrle⟩
      · obtain ⟨Qn, hQc, hIpos, hQcases⟩ := charge_nonempty v shares p hshc hshnt hshpos hmz hsad
        rw [hvfrac] at hQc
        rcases hQcases with ⟨hQm, hQn, hQneg, hb⟩ | ⟨hQm, -⟩
        swap
        · exact absurd (STAmount.ofNumber_source_ne_zero _ Qn .to_nearest p hQc hpm) (by simpa using hQm)
        obtain ⟨-, -, hhalf, -, -⟩ := WdMono.frac_pack Qn p hQn hQneg hQm hQc hpm
        refine ⟨Qn.toRat, hb, hhalf, fun hce => ?_⟩
        -- the recorded charge sits a decade below the priced one, under `Qn`
        have hce_lo : (-96 : ℤ) ≤ c.exponent := hcc.exp_lo
        have hGc := top_canon (p.exponent - 1)
          (by have := hcc.exp_lo; have : c.mOffset < p.mOffset := hce; show (-96 : ℤ) ≤ p.mOffset - 1; omega)
          (by have := hpc.exp_hi; show p.mOffset - 1 ≤ 80; omega)
        have hGv : (⟨.fractional, 9999999999999999, p.exponent - 1, false⟩ : STAmount).toRat
            = 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) := by
          have h9 : (9999999999999999 : UInt64).toNat = 9999999999999999 := by decide
          rw [STAmount.toRat_of_nonneg _ rfl]
          show ((9999999999999999 : UInt64).toNat : ℚ) * 10 ^ (p.exponent - 1) = _
          rw [h9]; push_cast; ring
        have hQG : 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) < Qn.toRat := by
          by_contra hle
          push_neg at hle
          have := STAmount.ofNumber_frac_le_canonical Qn _ p hQn hQneg hGc rfl (by rw [hGv]; exact hle) hQc
          rw [hGv] at this
          have h1 := (canon_band p hpc hpneg).1
          have h2 : (10 : ℚ) ^ (p.exponent + 15) = 10 ^ (p.exponent - 1) * 10 ^ 16 := by
            rw [show p.exponent + 15 = (p.exponent - 1) + ((16 : ℕ) : ℤ) by push_cast; ring, p10]
          have h3 : (0 : ℚ) < 10 ^ (p.exponent - 1) := zpow_pos (by norm_num) _
          nlinarith
        have hcG : c.toRat ≤ 9999999999999999 * (10 : ℚ) ^ (p.exponent - 1) := by
          rw [STAmount.toRat_of_nonneg c hcneg]
          have hm : (c.mValue.toNat : ℚ) ≤ 9999999999999999 := by
            have := hcc.mant_hi; exact_mod_cast (show c.mValue.toNat ≤ 9999999999999999 by omega)
          have he : (10 : ℚ) ^ c.mOffset ≤ 10 ^ (p.exponent - 1) :=
            zpow_le_zpow_right₀ (by norm_num)
              (by have : c.mOffset < p.mOffset := hce; show c.mOffset ≤ p.mOffset - 1; omega)
          have : (0 : ℚ) ≤ 10 ^ c.mOffset := le_of_lt (zpow_pos (by norm_num) _)
          calc (c.mValue.toNat : ℚ) * 10 ^ c.mOffset ≤ 9999999999999999 * 10 ^ c.mOffset :=
                mul_le_mul_of_nonneg_right hm this
            _ ≤ 9999999999999999 * 10 ^ (p.exponent - 1) := by linarith
        linarith
    have hpow_pe : (10 : ℚ) ^ p.exponent ≤ 10 ^ ep := zpow_le_zpow_right₀ (by norm_num) hpe_le
    refine ⟨fun e he => ?_, fun hz => ?_, ?_⟩
    · have hepe : ep ≤ e := postSumExponent_mono v.assetsTotal p amountDeposit ep e
        v.wf.assetsTotal_norm hATnn hpc hpneg hxc hxneg (by linarith) hep he
      have hg : (10 : ℚ) ^ ep ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) hepe
      exact lower_combine I Q p.toRat c.toRat depositε (10 ^ ep) (10 ^ e) (1 / 2 * 10 ^ p.exponent)
        hQI hQp hcl_ge (by linarith) hg
    · exfalso
      rw [STAmount.isZero] at hz
      exact hcm (beq_iff_eq.mp hz)
    · have hb := abs_le.mp hQI
      have hp' := abs_le.mp hQp
      by_cases hce : c.exponent < p.exponent
      · have := hQle hce
        have : (0 : ℚ) ≤ 10 ^ c.exponent := le_of_lt (zpow_pos (by norm_num) _)
        linarith
      · push_neg at hce
        have : (10 : ℚ) ^ p.exponent ≤ 10 ^ c.exponent := zpow_le_zpow_right₀ (by norm_num) hce
        linarith


/-- **Sharp share count bound.** The issued shares are a nonnegative integer within
`11·10⁻¹⁹` relatively of the ideal, less one whole share below (the truncation). -/
lemma Vault.deposit_sharesIssued_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (r : DepositResult)
    (hcanon : roundedAmount.Canonical) (hpos : 0 < roundedAmount.toRat)
    (hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hposA : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hposA = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - sharesε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + sharesε) := by
  obtain ⟨hround0, -⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, _, _, _, _, hcd, _, _, _, _, _, _, _, hshr, _⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hposA hok herr
  have hameq : amount = roundedAmount := by
    rw [hround0] at hround
    exact (Except.ok.inj hround).symm
  obtain ⟨p, hcdp, -, -⟩ := hcd rfl
  obtain ⟨shares, hats, hsz, _, _, hsheq⟩ := computeDeposit_success_reduces v amount p sh hcdp
  rw [hameq] at hats
  obtain ⟨q, hqval, hqbound, hqpos⟩ := shares_spec v roundedAmount shares hcanon hpos hnav hats hsz
  have hshare_eq : r.sharesIssued = shares := by rw [hshr, hsheq]
  rw [hshare_eq, hqval]
  have hfl := Int.floor_le q
  have hfl2 := Int.sub_one_lt_floor q
  obtain ⟨hlo, hhi⟩ := abs_le.mp hqbound
  refine ⟨Rat.den_intCast _, ?_, ?_, ?_⟩
  · have hε1 : sharesε < 1 := by unfold sharesε; norm_num
    have hqpos' : 0 < q := by nlinarith
    have h0 : (0 : ℤ) ≤ ⌊q⌋ := Int.floor_nonneg.mpr (le_of_lt hqpos')
    exact_mod_cast h0
  · linarith
  · linarith

end XRPL.Model.SingleAssetVault
