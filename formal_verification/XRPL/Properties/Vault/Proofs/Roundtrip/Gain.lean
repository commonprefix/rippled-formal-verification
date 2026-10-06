import XRPL.Properties.Vault.Proofs.Dilution.Charge
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.Roundtrip.Pack
import XRPL.Properties.Vault.Proofs.Roundtrip.GainArith
import XRPL.Properties.Vault.Proofs.Roundtrip.IntGlue

/-! # Deposit and redemption facts for the round-trip gain

On a fractional asset the deposit's priced charge `P` (the `.to_nearest` pack of a `Number`
within `2·10⁻¹⁸` of the ideal) bounds the clamped charge `c` within one post-sum grid step
below, and the redemption's payout is at most the pack of a `Number` within `depositε` of the
ideal. On an integral asset the charge carries the certificate of `charge_int_cert`. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight
open XRPL.Model.SingleAssetVault.DilG

lemma charge_facts (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    (v.numericType.isIntegral = true ∧
      (v.assetsTotal.mantissa_ ≠ 0 → ∃ (Y : ℚ) (z : ℤ), r.amountDeposit'.toRat = z ∧ 0 ≤ z ∧
        (z : ℚ) ≤ 9223372036854775807 ∧ r.amountDeposit'.exponent = 0 ∧
        |Y - v.idealChargeDeposit r.sharesIssued.toRat| ≤
          v.idealChargeDeposit r.sharesIssued.toRat * (5 / (2 ^ 63 + 7)) ∧
        (Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 69 / 125) ∧
        (925 * 10 ^ 15 ≤ Y → Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 1 / 2) ∧
        (9223372036854775807 ≤ Y → (z : ℚ) = 9223372036854775807) ∧
        (93 * 10 ^ 15 ≤ Y → Y < 922 * 10 ^ 15 → |(z : ℚ) - Y| ≤ 11 / 20)) ∧
      ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → 0 ≤ e) ∨
    (v.numericType.isIntegral = false ∧
      ∃ (P : STAmount) (Qd : ℚ) (ep : ℤ), P.IOUCanonical ∧ P.mIsNegative = false ∧
        |Qd - v.idealChargeDeposit r.sharesIssued.toRat| ≤
          v.idealChargeDeposit r.sharesIssued.toRat * (2 / 10 ^ 18) ∧
        |P.toRat - Qd| ≤ 1 / 2 * (10 : ℚ) ^ P.exponent ∧
        r.amountDeposit'.toRat ≤ P.toRat ∧ P.toRat - 10 ^ ep ≤ r.amountDeposit'.toRat ∧
        v.assetsTotal.toRat + P.toRat < 10 ^ 16 * 10 ^ ep ∧
        (10 : ℚ) ^ P.exponent ≤ 10 ^ ep ∧
        ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → ep ≤ e) := by
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
  have hδ : (0 : ℚ) ≤ 2 / 10 ^ 18 := by norm_num
  by_cases hint : v.numericType.isIntegral = true
  · have hid : c = p :=
      clampToSumExponent_integral_nonneg v.assetsTotal p c
        (by show p.mNumericType.isIntegral = true; rw [hcty]; exact hint) hpnn hclamp
    subst hid
    have hxint : amountDeposit.integral = true := by
      show amountDeposit.mNumericType.isIntegral = true; rw [hx_ty]; exact hint
    have hc_exp0 : ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → 0 ≤ e :=
      fun e he => le_of_eq (post_exp_integral v.assetsTotal amountDeposit e hxint he).symm
    left
    exact ⟨hint, fun hmz => charge_int_cert v shares c hint hshc hshnt hshpos hmz hsad, hc_exp0⟩
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
    obtain ⟨hpe_le, -, -, hsumhi, -⟩ := post_exp_facts v.assetsTotal p ep v.wf.assetsTotal_norm hATnn hpc
      hpneg hep
    have hxfrac : amountDeposit.integral = false := by
      unfold STAmount.integral; rw [hx_ty]; exact hintf
    have hxc : amountDeposit.IOUCanonical := hcanon.2 hxfrac
    have hxneg : amountDeposit.mIsNegative = false := STAmount.mIsNegative_false_of_pos _ hpos
    have hamtfrac : amount.mNumericType = .fractional := by rw [hamt_ty, hvfrac]
    set I := v.idealChargeDeposit shares.toRat with hI
    obtain ⟨Q, hQI, hQp, hQle, hI0⟩ : ∃ Q : ℚ, |Q - I| ≤ I * (2 / 10 ^ 18) ∧
        |p.toRat - Q| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent ∧
        (c.exponent < p.exponent → c.toRat ≤ Q) ∧ 0 ≤ I := by
      by_cases hmz : v.assetsTotal.mantissa_ = 0
      · have hex : p.toRat = I :=
          empty_frac_charge_exact v amount shares p hintf hmz hamt_canon hamtfrac hats hsz hsad
        refine ⟨I, by rw [sub_self, abs_zero]; exact mul_nonneg (by rw [← hex]; exact hpnn) hδ,
          by rw [hex, sub_self, abs_zero]; positivity, fun _ => by rw [← hex]; exact hrle,
          by rw [← hex]; exact hpnn⟩
      · obtain ⟨Qn, hQc, hIpos, hQcases⟩ := charge_nonempty_sharp v shares p hshc hshnt hshpos hmz hsad
        rw [hvfrac] at hQc
        rcases hQcases with ⟨hQm, hQn, hQneg, hb⟩ | ⟨hQm, -⟩
        swap
        · exact absurd (STAmount.ofNumber_source_ne_zero _ Qn .to_nearest p hQc hpm) (by simpa using hQm)
        obtain ⟨-, -, hhalf, -, -⟩ := WdMono.frac_pack Qn p hQn hQneg hQm hQc hpm
        refine ⟨Qn.toRat, hb, hhalf, fun hce => ?_, hIpos.le⟩
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
          replace hle := not_lt.mp hle
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
    have hb := abs_le.mp hQI
    have hsum16 : v.assetsTotal.toRat + p.toRat < 10 ^ 16 * 10 ^ ep := by
      have := p10 ep 16
      push_cast at this
      rw [mul_comm, ← this]; exact hsumhi
    right
    exact ⟨hintf, p, Q, ep, hpc, hpneg, hQI, hQp, hrle, hcl_ge,
      hsum16, zpow_le_zpow_right₀ (by norm_num) hpe_le,
      fun e he => postSumExponent_mono v.assetsTotal p amountDeposit ep e
        v.wf.assetsTotal_norm hATnn hpc hpneg hxc hxneg (by linarith) hep he⟩

lemma payout_le (v : Vault) (sh p a atr : STAmount)
    (hint : v.numericType.isIntegral = false)
    (hsc : sh.Canonical) (hnn : 0 ≤ sh.toRat) (hnav : v.WithdrawNavExact false)
    (hp : v.sharesToAssetsWithdraw sh false = .ok p)
    (hatr : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr)
    (hcl : clampToSumExponent v.assetsTotal p.operator_neg = .ok a)
    (hfnp : a.isFractionalNonPositive = .ok false) :
    ∃ (an : Number) (q : STAmount), an.isNormalized ∧
        0 ≤ an.toRat ∧ an.toRat ≤ v.idealAssetsWithdraw false sh.toRat * (1 + depositε) ∧
        STAmount.ofNumber .fractional an .to_nearest = .ok q ∧ a.toRat ≤ q.toRat := by
  obtain ⟨hp0, hpnt, hpc, -⟩ := WdMono.price_facts v false sh p hsc hnn hnav hp
  have hup := WdTight.price_an_upper v sh p false hnn hsc hnav hp
  have hnt : v.numericType = .fractional := by
    cases h : v.numericType with
    | fractional => rfl
    | integral _ _ _ _ => rw [h] at hint; simp [NumericType.isIntegral] at hint
  rw [hnt] at hatr
  have hTn : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hT0 : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hpz : p.mValue ≠ 0 := fun hz => by
    have := WdMono.clamp_zero_frac _ p _ atr hTn hT0 (hpnt.trans hnt) hz hatr hcl
    rw [hfnp] at this; exact absurd (Except.ok.inj this) (by decide)
  have hpcan := hpc hint hpz
  have hppos := WdMono.pos_of_nonneg p hp0 hpz
  obtain ⟨dn, s, pe, hdn, hs, hpe, hrte⟩ := WdMono.clamp_neg_frac _ _ _ hpcan hppos hcl
  have hale : a.toRat ≤ p.toRat :=
    (WdMono.rte_facts p _ pe hpcan hppos (WdMono.pe_le _ _ hpe) hrte).2.1
  rcases hup with hz | ⟨an0, hof0, hann0, han00, hanu⟩
  · exact absurd (by rw [hz]; exact STAmount.zero_mValue _) hpz
  · rw [hnt] at hof0
    exact ⟨an0, p, hann0, han00, hanu, hof0, hale⟩

end XRPL.Model.SingleAssetVault.RtT
