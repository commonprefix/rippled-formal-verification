import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares

/-! # Payout of a non-final withdrawal

The priced amount `p` is the `.to_nearest` pack of a `Number` within `depositε` of the
ideal, so within half a unit of its own grid of `ideal · (1 ± depositε)`. The recorded
payout is `p` itself on an integral asset or when `p` already sits on the grid of the
rounded post-withdrawal total; otherwise it is `p` floored onto that coarser grid,
losing less than one step of it. -/

namespace XRPL.Model.SingleAssetVault.WdTight

open XRPL.Model.Protocol

lemma nav_nonneg (v : Vault) (w : Bool) :
    0 ≤ (if w then v.depositNav else v.withdrawNav) := by
  cases w
  · exact v.exact.withdraw_nav_nonneg
  · exact v.exact.assetsTotal_nonneg

/-- The pre-packing price is non-negative and at most `depositε` above the ideal. -/
lemma price_an_upper (v : Vault) (sh p : STAmount) (w : Bool)
    (hnn : 0 ≤ sh.toRat) (hc : sh.Canonical) (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    p = STAmount.zero v.numericType ∨
    ∃ an : Number, STAmount.ofNumber v.numericType an .to_nearest = .ok p ∧ an.isNormalized ∧
      0 ≤ an.toRat ∧ an.toRat ≤ v.idealAssetsWithdraw w sh.toRat * (1 + depositε) := by
  obtain ⟨nav, hnavq, hnavn, hcase⟩ := WdAcc.price_cases v sh p w hnav hok
  rcases hcase with ⟨-, rfl⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · exact Or.inl rfl
  right
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  obtain rfl : sn = sn0 := Except.ok.inj (hsn.symm.trans hsn0)
  have hnav0 : 0 ≤ nav.toRat := by rw [hnavq]; exact nav_nonneg v w
  have hNSn := WdMono.mul_norm nav sn NS hnavn hsnn hmul
  have hT0 : 0 ≤ nav.toRat * sn.toRat := mul_nonneg hnav0 (by rw [hsnv]; exact hnn)
  have hNS0 : 0 ≤ NS.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg NS _
    (operator_mul_rounded_to_nearest nav sn NS hnavn hsnn hmul) hT0
  have hann := WdMono.div_norm NS v.sharesTotal an hNSn v.wf.sharesTotal_norm hdiv
  have han0 : 0 ≤ an.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg an _
    (operator_div_rounded_to_nearest NS v.sharesTotal an hNSn v.wf.sharesTotal_norm hdiv)
    (div_nonneg hNS0 v.wf.sharesTotal_nonneg)
  refine ⟨an, hof, hann, han0, ?_⟩
  have hε : (0 : ℚ) ≤ depositε := by rw [WdAcc.depositε_val]; norm_num
  by_cases hanm : an.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero an hanm]
    exact mul_nonneg (WdAcc.ideal_nonneg v w _ hnn) (by linarith)
  obtain ⟨hNSm, hSTm⟩ := operator_div_operands_ne_zero hNSn v.wf.sharesTotal_norm hdiv hanm
  set ST := v.sharesTotal.toRat with hST
  have hSTpos : 0 < ST := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  set T0 := nav.toRat * sn.toRat with hT0def
  have hideal : v.idealAssetsWithdraw w sh.toRat = T0 / ST := by
    unfold RawVault.idealAssetsWithdraw
    rw [hT0def, hsnv, hnavq, hST, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hmulb : |NS.toRat - T0| ≤ |T0| * (5 / (2 ^ 63 + 7)) :=
    operator_mul_rounds_to_nearest nav sn NS hnavn hsnn hmul hNSm
  rw [abs_of_nonneg hT0] at hmulb
  have hQ0 : 0 ≤ NS.toRat / ST := div_nonneg hNS0 hSTpos.le
  have hdivb : |an.toRat - NS.toRat / ST| ≤ |NS.toRat / ST| * (6 / (2 ^ 63 - 3)) :=
    operator_div_rounds_to_nearest NS v.sharesTotal an hNSn v.wf.sharesTotal_norm hdiv hanm
  rw [abs_of_nonneg hQ0] at hdivb
  have h1 := (abs_le.mp hmulb).2
  have h2 := (abs_le.mp hdivb).2
  have hq : NS.toRat / ST ≤ T0 / ST * (1 + 5 / (2 ^ 63 + 7)) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hSTpos]; linarith
  have hTS : 0 ≤ T0 / ST := div_nonneg hT0 hSTpos.le
  rw [hideal]
  calc an.toRat ≤ NS.toRat / ST * (1 + 6 / (2 ^ 63 - 3)) := by linarith
    _ ≤ T0 / ST * (1 + 5 / (2 ^ 63 + 7)) * (1 + 6 / (2 ^ 63 - 3)) :=
        mul_le_mul_of_nonneg_right hq (by norm_num)
    _ ≤ T0 / ST * (1 + depositε) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left pipe_up hTS

/-- `roundToExponent` onto a grid no coarser than the value's own returns the value. -/
lemma rte_ge (p a : STAmount) (s : ℤ) (hc : p.IOUCanonical) (hge : s ≤ p.exponent)
    (hok : STAmount.roundToExponent p s .downward = .ok a) : a = p := by
  have hint : ¬ p.integral = true := by
    unfold STAmount.integral; rw [hc.is_fractional]; decide
  have hnz : ¬ p.isZero = true := by
    unfold STAmount.isZero
    have := hc.mant_lo
    intro h
    rw [beq_iff_eq.mp h] at this; simp at this
  unfold STAmount.roundToExponent at hok
  rw [if_neg hint, if_neg hnz, if_pos hge] at hok
  exact (Except.ok.inj hok).symm

/-- Two points of the `10 ^ xp` grid less than `10 ^ s` apart, `xp < s`, are at most
`10 ^ s - 10 ^ xp` apart. -/
lemma grid_gap (p a : ℚ) (xp s : ℤ) (hs : xp < s) (zp za : ℤ)
    (hp : p = (zp : ℚ) * 10 ^ xp) (ha : a = (za : ℚ) * 10 ^ xp) (hlt : p - a < 10 ^ s) :
    p - a ≤ 10 ^ s - 10 ^ xp := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s = xp + k := ⟨(s - xp).toNat, by omega⟩
  have hx : (0 : ℚ) < 10 ^ xp := zpow_pos (by norm_num) _
  have hsk : (10 : ℚ) ^ s = 10 ^ xp * ((10 ^ k : ℤ) : ℚ) := by
    rw [hk, zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
  have hd : p - a = ((zp - za : ℤ) : ℚ) * 10 ^ xp := by rw [hp, ha]; push_cast; ring
  rw [hd, hsk] at hlt ⊢
  have h1 : ((zp - za : ℤ) : ℚ) < ((10 ^ k : ℤ) : ℚ) := by
    by_contra h
    replace h := not_lt.mp h
    have := mul_le_mul_of_nonneg_right h hx.le
    linarith
  have h2 : zp - za ≤ 10 ^ k - 1 := by
    have : zp - za < 10 ^ k := by exact_mod_cast h1
    omega
  have h3 : ((zp - za : ℤ) : ℚ) ≤ ((10 ^ k : ℤ) : ℚ) - 1 := by exact_mod_cast h2
  nlinarith

/-- The half-unit window of a nonzero fractional pack. -/
lemma frac_half (nt : NumericType) (hnt : nt = .fractional) (an : Number) (p : STAmount)
    (hann : an.isNormalized) (han0 : 0 ≤ an.toRat)
    (hof : STAmount.ofNumber nt an .to_nearest = .ok p) (hpz : p.mValue ≠ 0) :
    |p.toRat - an.toRat| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent := by
  subst hnt
  exact (WdMono.frac_pack an p hann (Number.negative_false_of_normalized_nonneg an hann han0)
    (STAmount.ofNumber_source_ne_zero _ _ _ _ hof hpz) hof hpz).2.2.1

set_option maxHeartbeats 1000000 in
-- one long case split over the three payout regimes
/-- Bounds of a non-final payout against the burned shares' worth. -/
lemma payout_bounds (v : Vault) (amount : WithdrawAmount) (w : Bool)
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact w) (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount w hpos = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    0 ≤ r.assets'.toRat ∧
    r.assets'.toRat ≤ v.idealAssetsWithdraw w r.sharesBurned.toRat * (1 + depositε) +
      1 / 2 * (10 : ℚ) ^ r.assets'.exponent ∧
    ∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
      v.idealAssetsWithdraw w r.sharesBurned.toRat - r.assets'.toRat ≤
        v.idealAssetsWithdraw w r.sharesBurned.toRat * depositε +
          max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) := by
  obtain ⟨cw, an, sta, hcomp, hcerr, han, hlt, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount w r hpos hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rcases hcase with ⟨hf, -⟩ | ⟨-, an', sbn, at', atr, atr', av', st', hcl, hfnp, han', -, hat,
    hatr, hatr', -, -, -, hrv⟩
  · rw [hsb, hf] at hfin; exact absurd hfin (by decide)
  have hp := computeWithdraw_ok_priced v amount w cw hcomp hcerr
  rw [← hsb] at hp
  set p := cw.assets' with hpdef
  have hATeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  rw [hATeq]
  obtain ⟨hp0, hpnt, hpc, hpn⟩ := WdMono.price_facts v w _ p hc hnn hnav hp
  have hI0 := WdAcc.ideal_nonneg v w _ hnn
  have hε : (0 : ℚ) ≤ depositε := by rw [WdAcc.depositε_val]; norm_num
  have hup := price_an_upper v _ p w hnn hc hnav hp
  have hlo := WdAcc.price_an_lower v _ p w hc hnav hp
  set I := v.idealAssetsWithdraw w r.sharesBurned.toRat with hIdef
  clear_value p I
  have hIε : 0 ≤ I * depositε := mul_nonneg hI0 hε
  have hsmall : (10 : ℚ) ^ (-82 : ℤ) < 10 ^ (-81 : ℤ) := zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  by_cases hint : v.numericType.isIntegral = true
  · have hpint : p.integral = true := by unfold STAmount.integral; rw [hpnt]; exact hint
    have hval : r.assets'.toRat = p.toRat :=
      WdMono.clampToSumExponent_neg_int_toRat _ _ _ hpint hp0 hcl
    obtain ⟨-, hoff, -, -⟩ := WdAcc.clamp_integral _ _ _ hpint hcl
    obtain ⟨-, hpoff, -⟩ := WdAcc.price_integral_shape v _ _ w hint hp
    have hx : r.assets'.exponent = 0 := by show r.assets'.mOffset = 0; rw [hoff, hpoff]
    obtain ⟨-, hoff', -⟩ := STAmount.ofNumber_integral_facts _ _ _ _ hint hatr'
    have hx' : atr'.exponent = 0 := hoff'
    refine ⟨by rw [hval]; exact hp0, ?_, atr', hatr', ?_⟩
    · rw [hx, hval, zpow_zero, mul_one]
      rcases hup with hz | ⟨an0, hof0, hann0, han00, hanu⟩
      · rw [hz, STAmount.toRat_eq_zero_of_mValue_zero _ (STAmount.zero_mValue _)]
        have : 0 ≤ I * (1 + depositε) := mul_nonneg hI0 (by linarith)
        linarith
      · obtain ⟨z, hz, -, hzh, -⟩ := WdMono.int_pack _ hint an0 p hann0 han00 hof0
        rw [hz]
        linarith [(abs_le.mp hzh).2]
    · rw [hx, hx', hval, zpow_zero, mul_one]
      refine le_trans ?_ (add_le_add le_rfl (le_max_left _ _))
      by_cases hI : (10 : ℚ) ^ (-82 : ℤ) ≤ I
      · obtain ⟨an0, hof0, hann0, -, han0, hanl⟩ := hlo hI
        obtain ⟨z, hz, -, hzh, -⟩ := WdMono.int_pack _ hint an0 p hann0 han0.le hof0
        rw [hz]
        linarith [(abs_le.mp hzh).1]
      · replace hI := not_le.mp hI
        have h1 : (10 : ℚ) ^ (-82 : ℤ) ≤ 1 / 2 := by norm_num
        have h2 : I - p.toRat ≤ I := by linarith
        have h3 : I ≤ 1 / 2 := le_trans hI.le h1
        have h4 : I - p.toRat ≤ 1 / 2 := le_trans h2 h3
        exact le_trans h4 (le_add_of_nonneg_left hIε)
  · have hnt : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rw [h] at hint; simp [NumericType.isIntegral] at hint
    have hint' : v.numericType.isIntegral = false := by simpa using hint
    rw [hnt] at hatr hatr'
    have hTn : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
    have hT0 : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
    have hpz : p.mValue ≠ 0 := fun hz => by
      have := WdMono.clamp_zero_frac _ p _ atr hTn hT0 (hpnt.trans hnt) hz hatr hcl
      rw [hfnp] at this; exact absurd (Except.ok.inj this) (by decide)
    have hpcan := hpc hint' hpz
    have hppos := WdMono.pos_of_nonneg p hp0 hpz
    obtain ⟨dn, s, pe, hdn, hs, hpe, hrte⟩ := WdMono.clamp_neg_frac _ _ _ hpcan hppos hcl
    have hpu : p.toRat ≤ I * (1 + depositε) + 1 / 2 * (10 : ℚ) ^ p.exponent := by
      rcases hup with hz | ⟨an0, hof0, hann0, han00, hanu⟩
      · exact absurd (by rw [hz]; exact STAmount.zero_mValue _) hpz
      · linarith [(abs_le.mp (frac_half _ hnt an0 p hann0 han00 hof0 hpz)).2]
    have hpl : (10 : ℚ) ^ (-82 : ℤ) ≤ I → I - p.toRat ≤ I * depositε + 1 / 2 * (10 : ℚ) ^ p.exponent := by
      intro hI
      obtain ⟨an0, hof0, hann0, -, han0, hanl⟩ := hlo hI
      linarith [(abs_le.mp (frac_half _ hnt an0 p hann0 han0.le hof0 hpz)).1]
    have hbig : ∀ a : STAmount, a.IOUCanonical → 0 < a.toRat → (10 : ℚ) ^ (-82 : ℤ) < a.toRat :=
      fun a ha ha0 => by
        have := WdAcc.iou_abs_ge a ha
        rw [abs_of_pos ha0] at this
        linarith
    have hx0 : ∀ x : ℤ, 0 < max (1 / 2 * (10 : ℚ) ^ x) ((10 : ℚ) ^ atr'.exponent - 1 / 2 * 10 ^ x) :=
      fun x => lt_of_lt_of_le (by positivity) (le_max_left _ _)
    by_cases hge : pe ≤ p.exponent
    · have ha := rte_ge p _ pe hpcan hge hrte
      rw [ha]
      refine ⟨hp0, hpu, atr', by rw [hnt]; exact hatr', ?_⟩
      by_cases hI : (10 : ℚ) ^ (-82 : ℤ) ≤ I
      · exact le_trans (hpl hI) (add_le_add le_rfl (le_max_left _ _))
      · replace hI := not_le.mp hI
        linarith [hbig p hpcan hppos, hx0 p.exponent]
    · replace hge := not_le.mp hge
      have hpe80 := WdMono.pe_le _ _ hpe
      obtain ⟨ha0, hale, hgrid, hmax⟩ := WdMono.rte_facts p _ pe hpcan hppos hpe80 hrte
      have hant := WdMono.roundToExponent_frac_nt _ _ _ _ hpcan.is_fractional hrte
      have haz : r.assets'.mValue ≠ 0 := fun h => by
        rw [WdMono.fnp_zero _ hant h] at hfnp; exact absurd (Except.ok.inj hfnp) (by decide)
      have hacan : r.assets'.IOUCanonical := by
        rcases (STAmount.roundToExponent_fczr p _ pe .downward
          ⟨hpcan.is_fractional, Or.inl hpcan⟩ hrte).2 with h | h
        · exact h
        · exact absurd h haz
      have hapos := WdMono.pos_of_nonneg _ ha0 haz
      have hxle : r.assets'.exponent ≤ p.exponent := WdAcc.iou_offset_le _ _ hacan hpcan ha0 hale
      obtain ⟨zp, hzp⟩ := STAmount.exists_int_grid p
      obtain ⟨za, hza⟩ := hgrid p.exponent hge.le
      have h10 : (0 : ℚ) < 10 ^ pe := zpow_pos (by norm_num) _
      have hlt' : p.toRat - r.assets'.toRat < 10 ^ pe := by
        have h1 : (⌊p.toRat / 10 ^ pe⌋ : ℚ) * 10 ^ pe ≤ p.toRat := by
          have := Int.floor_le (p.toRat / 10 ^ pe); rwa [le_div_iff₀ h10] at this
        have h2 := hmax haz _ h1
        have h3 : p.toRat < ((⌊p.toRat / 10 ^ pe⌋ : ℚ) + 1) * 10 ^ pe := by
          have := Int.lt_floor_add_one (p.toRat / 10 ^ pe); rwa [div_lt_iff₀ h10] at this
        linarith
      have hgap := grid_gap p.toRat r.assets'.toRat p.exponent pe hge zp za hzp hza hlt'
      have hxp : (10 : ℚ) ^ r.assets'.exponent ≤ 10 ^ p.exponent :=
        zpow_le_zpow_right₀ (by norm_num) hxle
      refine ⟨ha0, ?_, atr', by rw [hnt]; exact hatr', ?_⟩
      · by_cases heq : r.assets'.toRat = p.toRat
        · have hxe : r.assets'.exponent = p.exponent :=
            le_antisymm hxle (WdAcc.iou_offset_le _ _ hpcan hacan hp0 heq.ge)
          rw [heq, hxe]; exact hpu
        · have hlt2 : r.assets'.toRat < p.toRat := lt_of_le_of_ne hale heq
          have hd : p.toRat - r.assets'.toRat = ((zp - za : ℤ) : ℚ) * 10 ^ p.exponent := by
            rw [hzp, hza]; push_cast; ring
          have hpx : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
          have hz1 : (1 : ℚ) ≤ ((zp - za : ℤ) : ℚ) := by
            have : (0 : ℚ) < ((zp - za : ℤ) : ℚ) := by
              by_contra h; replace h := not_lt.mp h
              have := mul_nonpos_of_nonpos_of_nonneg h hpx.le
              linarith
            have : 0 < zp - za := by exact_mod_cast this
            exact_mod_cast (show 1 ≤ zp - za by omega)
          have : 10 ^ p.exponent ≤ p.toRat - r.assets'.toRat := by
            rw [hd]; nlinarith
          have : (0 : ℚ) ≤ 10 ^ r.assets'.exponent := by positivity
          linarith
      · have he1 : numberExponent at' .fractional = .ok atr'.exponent := by
          unfold numberExponent; rw [hatr']; rfl
        obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact r.assets' .to_nearest hacan
        obtain rfl : an' = sn := Except.ok.inj (han'.symm.trans hsn)
        have hanm' : an'.mantissa_ ≠ 0 :=
          Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnv]; exact hapos.ne')
        have hy1n := Number.operator_neg_isNormalized an' hsnn
        have hy1m : an'.operator_neg.mantissa_ ≠ 0 := by
          rw [Number.operator_neg_mantissa_of_ne _ hanm']; exact hanm'
        have hy1neg : an'.operator_neg.negative_ = true := by
          rw [Number.operator_neg_negative_of_ne _ hanm',
            Number.negative_false_of_pos an' (by rw [hsnv]; exact hapos)]; rfl
        have hy1v : an'.operator_neg.toRat = -r.assets'.toRat := by rw [Number.toRat_neg, hsnv]
        obtain ⟨hdnn, hdnv, hdnm, hdnneg⟩ := WdMono.neg_toNumber p hpcan hppos dn hdn
        obtain ⟨hpnn, hpnv⟩ := hpn an han
        have hav : an.toRat ≤ v.assetsAvailable.toRat := by
          by_contra h
          replace h := not_le.mp h
          have := (operator_lt_iff _ _ v.wf.assetsAvailable_norm hpnn).mpr h
          rw [hlt] at this; exact absurd this (by decide)
        have haT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
        have hTpos : 0 < v.assetsTotal.toRat := by linarith
        have hTm : v.assetsTotal.mantissa_ ≠ 0 := fun h => by
          rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hTpos; exact lt_irrefl _ hTpos
        have hTneg : v.assetsTotal.negative_ = false := Number.negative_false_of_pos _ hTpos
        have hpee : pe ≤ atr'.exponent :=
          WdMono.sum_exp_anti _ _ dn at' s hTn hy1n hdnn hTm hy1m hdnm hTneg hy1neg hdnneg
            (by rw [hy1v, hdnv]; linarith) (by rw [hdnv]; linarith) hat hs _ _ he1 hpe
        have hee : (10 : ℚ) ^ pe ≤ 10 ^ atr'.exponent := zpow_le_zpow_right₀ (by norm_num) hpee
        refine le_trans ?_ (add_le_add le_rfl (le_max_right _ _))
        by_cases hI : (10 : ℚ) ^ (-82 : ℤ) ≤ I
        · have := hpl hI
          linarith
        · replace hI := not_le.mp hI
          have := hbig _ hacan hapos
          have : (10 : ℚ) ^ r.assets'.exponent ≤ 10 ^ atr'.exponent := by
            have : (10 : ℚ) ^ p.exponent ≤ 10 ^ pe := zpow_le_zpow_right₀ (by norm_num) hge.le
            linarith
          have : (0 : ℚ) ≤ 10 ^ r.assets'.exponent := by positivity
          linarith

end XRPL.Model.SingleAssetVault.WdTight
