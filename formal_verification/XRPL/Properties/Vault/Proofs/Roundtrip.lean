import XRPL.Properties.Vault.Proofs.Dilution.Deposit
import XRPL.Properties.Vault.Proofs.Dilution.Withdraw
import XRPL.Properties.Vault.Proofs.Roundtrip.Arith
import XRPL.Properties.Vault.Proofs.Roundtrip.Gain
import XRPL.Properties.Vault.Proofs.Roundtrip.FracLoss

/-! # Deposit then redeem: the gain is one grid step, the loss grid-step sized

The relative term `depositε/8` is needed only on an integral asset; on a fractional one
the bounds hold without it. -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol

lemma add_zero_left (x y z : Number) (hx : x.isNormalized) (hx0 : x.toRat = 0)
    (h : x.operator_add y .to_nearest = .ok z) : z.toRat = y.toRat := by
  have hxz : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx (by
    by_contra hm; exact Number.toRat_ne_zero_of_mantissa_ne_zero x hm hx0)
  subst hxz
  unfold Number.operator_add at h
  by_cases hy : y.operator_eq Number.zero = true
  · rw [if_pos hy] at h
    obtain rfl := Except.ok.inj h
    have hyz : y = Number.zero := by
      simp only [Number.operator_eq, Bool.and_eq_true, beq_iff_eq] at hy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hy
      cases y; simp_all [Number.zero]
    rw [hyz]
  · rw [if_neg hy, if_pos (by decide)] at h
    obtain rfl := Except.ok.inj h
    rfl

lemma byShares_redeemed (v : Vault) (s : STAmount) (w : Bool) (cw : ComputeWithdrawResult)
    (h : computeWithdrawByShares v s w = .ok cw) (herr : cw.error = none) :
    cw.sharesRedeemed = s := by
  simp only [computeWithdrawByShares, bind, Except.bind, pure, Except.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  walk_ok
  all_goals first
    | (simp at herr; done)
    | rfl

lemma eq_of_operator_eq (x y : STAmount) (h : x.operator_eq y = true) : x = y := by
  unfold STAmount.operator_eq STAmount.areComparable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x; cases y
  simp_all

lemma int64_operator_eq (x y : STAmount) (hx : x.IntegralCanonical) (hxnt : x.mNumericType = .int64)
    (hxpos : 0 < x.toRat) (hynt : y.mNumericType = .int64) (hyoff : y.mOffset = 0)
    (hyneg : y.mIsNegative = false) (hv : (y.mValue.toNat : ℚ) = x.toRat) : x.operator_eq y = true := by
  have hxneg := STAmount.mIsNegative_false_of_pos x hxpos
  have hxv := STAmount.toRat_of_nonneg x hxneg
  rw [hx.offset_zero, zpow_zero, mul_one] at hxv
  have hm : y.mValue.toNat = x.mValue.toNat := by
    have : (y.mValue.toNat : ℚ) = x.mValue.toNat := by rw [hv, hxv]
    exact_mod_cast this
  have hm' : y.mValue = x.mValue := UInt64.toNat_inj.mp hm
  unfold STAmount.operator_eq STAmount.areComparable
  simp [hxnt, hynt, hxneg, hyneg, hx.offset_zero, hyoff, hm']

lemma ofNumber_zero_ok (nt : NumericType) :
    ∃ a, STAmount.ofNumber nt Number.zero .to_nearest = .ok a := by
  cases nt with
  | fractional => exact ⟨_, rfl⟩
  | integral a b c d => exact ⟨_, rfl⟩

/-- Packing a nonnegative exact charge back to an amount moves it by at most half a unit of
the result's last digit. -/
lemma repack_half (v : Vault) (n : Number) (c p : STAmount) (hn : n.isNormalized)
    (hnv : n.toRat = c.toRat) (hc0 : 0 ≤ c.toRat)
    (hfr : v.numericType.isIntegral = false → c.IOUCanonical ∧ 0 < c.toRat)
    (hok : STAmount.ofNumber v.numericType n .to_nearest = .ok p) :
    |p.toRat - c.toRat| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent := by
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨z, hz, -, hzn, hoff, -, -⟩ :=
      WdMono.int_pack v.numericType hint n p hn (by rw [hnv]; exact hc0) hok
    have : p.exponent = 0 := hoff
    rw [this, zpow_zero, mul_one, hz, ← hnv]; exact hzn
  · have hintf : v.numericType.isIntegral = false := by simpa using hint
    obtain ⟨hcc, hcpos⟩ := hfr hintf
    have hvfrac : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral _ _ _ _ => rw [h] at hintf; simp [NumericType.isIntegral] at hintf
    rw [hvfrac] at hok
    have hnpos : 0 < n.toRat := by rw [hnv]; exact hcpos
    have hnm : n.mantissa_ ≠ 0 := fun h => by
      rw [Number.toRat_eq_zero_of_mantissa_zero n h] at hnpos; exact lt_irrefl _ hnpos
    have hnneg : n.negative_ = false := Number.negative_false_of_pos n hnpos
    have hpm : p.mValue ≠ 0 := by
      intro hz
      have hlt := STAmount.ofNumber_fractional_zero_below_min .fractional n p .to_nearest rfl hn
        hnneg hnm hok hz
      have hband := (DepTight.canon_band c hcc (STAmount.mIsNegative_false_of_pos c hcpos)).1
      have hexp : (-81 : ℤ) ≤ c.exponent + 15 := by
        have := hcc.exp_lo; show (-81 : ℤ) ≤ c.mOffset + 15; omega
      have : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (c.exponent + 15) := zpow_le_zpow_right₀ (by norm_num) hexp
      rw [hnv] at hlt
      linarith
    obtain ⟨-, -, hh, -, -⟩ := WdMono.frac_pack n p hn hnneg hnm hok hpm
    rw [← hnv]; exact hh

end XRPL.Model.SingleAssetVault.DilG

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DilG
open XRPL.Model.SingleAssetVault.RtT

/-- **Round trip.** Redeeming the shares a deposit issued returns the charge up to
`depositε/8` relatively plus grid steps: the gain is at most one step of the deposit's
post-sum grid; the shortfall is at most half a unit of the charge plus the payout's pricing
and clamp error (half a unit of the payout, or one step of the post-withdrawal total's grid
less that). -/
lemma Vault.deposit_withdraw_roundtrip_proof (v : Vault) (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    (hL : v.toExact.lossUnrealized = 0)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false hpos = .ok r₁) (herr₁ : r₁.error = none)
    (hpos₂ : 0 < r₁.sharesIssued.toRat)
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂)
    (herr₂ : r₂.error = none) :
    (∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      r₂.assets'.toRat - r₁.amountDeposit'.toRat ≤
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) + (10 : ℚ) ^ e) ∧
    ∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' ∧
      r₁.amountDeposit'.toRat - r₂.assets'.toRat ≤
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) +
          1 / 2 * (10 : ℚ) ^ r₁.amountDeposit'.exponent +
          max (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent) := by
  obtain ⟨hA₁, hL₁, hnt₁, hins, hsic, hsnt, hspos, hS₁⟩ :=
    deposit_totals v amountDeposit r₁ hcanon hpos hok₁ herr₁
  obtain ⟨hc0, hI0, hfrac, hover, -⟩ :=
    charge_sharp v amountDeposit r₁ hcanon hpos hok₁ herr₁
  have hε : depositε = 1 / 10 ^ 17 := by rw [DepAcc.depositε_eq]; norm_num
  have hκ : 11 / 10 * sharesε = 121 / 10 ^ 20 := by unfold sharesε; norm_num
  set A := v.toExact.assetsTotal with hAdef
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hSdef
  set s := r₁.sharesIssued.toRat with hsdef
  set c := r₁.amountDeposit'.toRat with hcdef
  set I := v.idealChargeDeposit s with hIdef
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := v.exact.assetsTotal_nonneg
  have hSST : S = v.sharesTotal.toRat := RawVault.WF.toExact_sharesTotal _ v.wf
  have hSz_of : A = 0 → S = 0 := fun hAz => by
    by_contra hne
    have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hne)
    have hsig : v.sharesTotal.signum = 1 :=
      (signum_eq_one_iff _ v.wf.sharesTotal_norm).mpr (by rw [← hSST]; exact hSpos)
    have hm : v.assetsTotal.mantissa_ = 0 := by
      by_contra hm; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hm hAz
    simp [Vault.isInsolvent, hm, hsig] at hins
  have hAsI : A * s = S * I := by
    rcases lt_or_eq_of_le hA0 with hApos | hAz
    · have hSpos := shares_pos_of_total v hApos
      rw [hIdef]
      unfold RawVault.idealChargeDeposit
      rw [if_neg (ne_of_gt hApos)]
      show A * s = S * (v.toExact.assetsTotal * s / S)
      have hSne : S ≠ 0 := ne_of_gt hSpos
      rw [mul_div_assoc', mul_comm S, mul_div_assoc, div_self hSne, mul_one]
    · rw [hSz_of hAz.symm, ← hAz]; ring
  have hL₁0 : r₁.vault'.toExact.lossUnrealized = 0 := by rw [hL₁, hL]
  have hS₁' : (r₁.vault'.toExact.sharesTotal : ℚ) = S + s := hS₁ hSsz
  have hSs : 0 < S + s := by linarith
  set A₁ := r₁.vault'.toExact.assetsTotal with hA₁def
  have hI₂ : r₁.vault'.idealAssetsWithdraw false s = A₁ * s / (S + s) := by
    unfold RawVault.idealAssetsWithdraw
    rw [if_neg (by decide), hS₁']
    show (A₁ - r₁.vault'.toExact.lossUnrealized) * s / (S + s) = _
    rw [hL₁0, sub_zero]
  set J := (A + c) * s / (S + s) with hJdef
  have hJ : J * (S + s) = S * I + s * c := by
    rw [hJdef, div_mul_cancel₀ _ (ne_of_gt hSs)]; linarith [hAsI]
  obtain ⟨hA₁lo, hA₁hi⟩ := abs_le.mp hA₁
  have hsum : 0 ≤ A + c := by linarith
  have hdel : (6 : ℚ) / (2 ^ 63 - 3) ≤ 1 / 10 ^ 18 := by norm_num
  have hA₁up : A₁ ≤ (1 + 1 / 10 ^ 18) * (A + c) := by nlinarith
  have hA₁dn : (1 - 1 / 10 ^ 18) * (A + c) ≤ A₁ := by nlinarith
  have hsS : 0 ≤ s / (S + s) := div_nonneg hspos.le hSs.le
  have hI₂lo : (1 - 1 / 10 ^ 18) * J ≤ r₁.vault'.idealAssetsWithdraw false s := by
    rw [hI₂, hJdef]
    have := mul_le_mul_of_nonneg_right hA₁dn hsS
    calc (1 - 1 / 10 ^ 18) * ((A + c) * s / (S + s))
        = (1 - 1 / 10 ^ 18) * (A + c) * (s / (S + s)) := by ring
      _ ≤ A₁ * (s / (S + s)) := this
      _ = A₁ * s / (S + s) := by ring
  -- the redemption
  obtain ⟨cw, an, sta, hcomp, hcerr, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases r₁.vault' (.vaultShares r₁.sharesIssued) false r₂ hpos₂ hok₂ herr₂
  have hred : cw.sharesRedeemed = r₁.sharesIssued := byShares_redeemed _ _ _ _ hcomp hcerr
  have hsbs : r₂.sharesBurned = r₁.sharesIssued := hsb.trans hred
  have hsc : r₁.sharesIssued.Canonical := Exact.int64_canonical _ hsnt hsic.offset_zero (by
    have h := hsic.in_range; rw [hsnt] at h; exact h.trans (le_of_eq (by decide)))
  have hu0 : (0 : ℚ) ≤ 1 / 2 * 10 ^ r₂.assets'.exponent := by positivity
  have huc0 : (0 : ℚ) ≤ 1 / 2 * 10 ^ r₁.amountDeposit'.exponent := by positivity
  have hS₁n : 0 ≤ r₁.vault'.sharesTotal.toRat := r₁.vault'.wf.sharesTotal_nonneg
  have hS₁v : r₁.vault'.sharesTotal.toRat = S + s := by
    rw [← RawVault.WF.toExact_sharesTotal _ r₁.vault'.wf]; exact hS₁'
  have hcε : 0 ≤ c * (11 / 10 * sharesε) := by rw [hκ]; positivity
  rcases hcase with ⟨hfin, -, hpay, hrv⟩ | hcase
  · ------------------------------------------------------------------ final redemption
    rw [hred] at hfin
    have hseq := eq_of_operator_eq _ _ hfin
    obtain ⟨-, -, -, -, hstav⟩ := STAmount.ofNumber_int64_shape _ .to_nearest sta
      r₁.vault'.wf.sharesTotal_norm hS₁n r₁.vault'.wf.sharesTotal_int (by rw [hS₁v]; exact hSsz) hsta
    have hSz : S = 0 := by
      have : s = S + s := by
        calc s = sta.toRat := by show r₁.sharesIssued.toRat = sta.toRat; rw [hseq]
          _ = r₁.vault'.sharesTotal.toRat := hstav
          _ = S + s := hS₁v
      linarith
    have hAv0 : v.assetsAvailable.toRat = 0 :=
      (v.exact.empty_shares (by
        have : ((v.toExact.sharesTotal : ℕ) : ℚ) = 0 := hSz
        exact_mod_cast this)).2
    obtain ⟨cN, hcNv, hcNn, hadd⟩ := deposit_avail v amountDeposit r₁ hcanon hpos hok₁ herr₁
    have hAv₁ : r₁.vault'.assetsAvailable.toRat = c :=
      (add_zero_left _ _ _ v.wf.assetsAvailable_norm hAv0 hadd).trans hcNv
    have hnt' : r₁.vault'.numericType = v.numericType := hnt₁
    rw [hnt'] at hpay
    have hh := repack_half v _ r₁.amountDeposit' r₂.assets' r₁.vault'.wf.assetsAvailable_norm
      hAv₁ hc0 hfrac hpay
    obtain ⟨hh1, hh2⟩ := abs_le.mp hh
    have hT' : r₂.vault'.toRawVault.assetsTotal = Number.zero := by rw [hrv]
    obtain ⟨atr', hatr'⟩ := ofNumber_zero_ok v.numericType
    refine ⟨fun e he => ?_, atr', ?_, ?_⟩
    · rcases charge_facts v amountDeposit r₁ hcanon hpos hok₁ herr₁ with
        ⟨hint, -, he0⟩ | ⟨hint, -⟩
      · obtain ⟨z, hz, -, hzn, -, -, -⟩ := WdMono.int_pack v.numericType hint _ r₂.assets'
          r₁.vault'.wf.assetsAvailable_norm (by rw [hAv₁]; exact hc0) hpay
        have : (1 : ℚ) ≤ 10 ^ e := one_le_zpow₀ (by norm_num) (he0 e he)
        rw [hAv₁] at hzn
        rw [hz]; linarith [(abs_le.mp hzn).2]
      · have hvfrac : v.numericType = .fractional := by
          cases h : v.numericType with
          | fractional => rfl
          | integral _ _ _ _ => rw [h] at hint; simp [NumericType.isIntegral] at hint
        obtain ⟨hcc, hcpos⟩ := hfrac hint
        rw [hvfrac] at hpay
        have hu : (0 : ℚ) < 10 ^ r₁.amountDeposit'.exponent := zpow_pos (by norm_num) _
        have := pack_le _ r₁.amountDeposit' r₂.assets' r₁.vault'.wf.assetsAvailable_norm
          (by rw [hAv₁]; exact hc0) hcc (STAmount.mIsNegative_false_of_pos _ hcpos)
          (by rw [hAv₁]; linarith) hpay
        have : (0 : ℚ) ≤ 10 ^ e := by positivity
        linarith
    · show STAmount.ofNumber v.numericType r₂.vault'.toRawVault.assetsTotal .to_nearest = _
      rw [hT']; exact hatr'
    · have := le_max_left (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
        ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
      linarith
  · ------------------------------------------------------------------ partial redemption
    obtain ⟨hfin, -, -, -, atr, -, -, -, hcl, hfnp, -, -, -, hatr, -⟩ := hcase
    have hfin' : r₂.sharesBurned.operator_eq sta = false := by rw [hsb]; exact hfin
    have hnnb : 0 ≤ r₂.sharesBurned.toRat := by rw [hsbs]; exact hspos.le
    have hcb : r₂.sharesBurned.Canonical := by rw [hsbs]; exact hsc
    obtain ⟨-, -, atr', hatr', hlo⟩ := Vault.withdraw_payout_proof r₁.vault'
      (.vaultShares r₁.sharesIssued) false sta r₂ hnnb hcb (navExact_of_zero _ false hL₁0)
      hpos₂ hok₂ herr₂ hsta hfin'
    rw [hsbs] at hlo
    have hp := computeWithdraw_ok_priced r₁.vault' (.vaultShares r₁.sharesIssued) false cw
      hcomp hcerr
    rw [hred] at hp
    have hnt' : r₁.vault'.numericType = v.numericType := hnt₁
    have hatrv : STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' := by
      rw [← hnt']; exact hatr'
    -- a partial redemption leaves shares behind, so the vault held some
    have hSpos : 0 < S := by
      by_contra hS
      have hSz : S = 0 := le_antisymm (not_lt.mp hS) hS0
      obtain ⟨hstnt, hstoff, hstneg, hstm, -⟩ := STAmount.ofNumber_int64_shape _ .to_nearest sta
        r₁.vault'.wf.sharesTotal_norm hS₁n r₁.vault'.wf.sharesTotal_int
        (by rw [hS₁v]; exact hSsz) hsta
      have := int64_operator_eq r₁.sharesIssued sta hsic hsnt hspos hstnt hstoff hstneg
        (by rw [hstm, hS₁v, hSz, zero_add])
      rw [hred] at hfin; rw [hfin] at this; exact absurd this (by decide)
    have hApos : 0 < A := by
      rcases lt_or_eq_of_le hA0 with h | h
      · exact h
      · exact absurd (hSz_of h.symm) (ne_of_gt hSpos)
    by_cases hint : v.numericType.isIntegral = true
    · ---------------------------------------------------------------- integral asset
      have hint₁ : r₁.vault'.numericType.isIntegral = true := by rw [hnt']; exact hint
      have hmz : v.assetsTotal.mantissa_ ≠ 0 :=
        Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hApos)
      obtain ⟨Y, zc, hcz, hzc0, hzcM, hcexp, hY, hc1, hc2, hc3, hc4⟩ :
          ∃ (Y : ℚ) (z : ℤ), c = z ∧ 0 ≤ z ∧ (z : ℚ) ≤ 9223372036854775807 ∧
            r₁.amountDeposit'.exponent = 0 ∧ |Y - I| ≤ I * (5 / (2 ^ 63 + 7)) ∧
            (Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 69 / 125) ∧
            (925 * 10 ^ 15 ≤ Y → Y < 9223372036854775807 → |(z : ℚ) - Y| ≤ 1 / 2) ∧
            (9223372036854775807 ≤ Y → (z : ℚ) = 9223372036854775807) ∧
            (93 * 10 ^ 15 ≤ Y → Y < 922 * 10 ^ 15 → |(z : ℚ) - Y| ≤ 11 / 20) := by
        rcases charge_facts v amountDeposit r₁ hcanon hpos hok₁ herr₁ with
          ⟨-, hcert, -⟩ | ⟨hint', -⟩
        · exact hcert hmz
        · rw [hint] at hint'; exact absurd hint' (by decide)
      have he0 : ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e → 0 ≤ e := by
        rcases charge_facts v amountDeposit r₁ hcanon hpos hok₁ herr₁ with
          ⟨-, -, he0⟩ | ⟨hint', -⟩
        · exact he0
        · rw [hint] at hint'; exact absurd hint' (by decide)
      obtain ⟨cN, hcNv, hcNn, hadd⟩ := deposit_total_add v amountDeposit r₁ hcanon hpos hok₁ herr₁
      have hcap := int_cap _ hint₁ r₁.vault'.assetsTotal atr r₁.vault'.wf.assetsTotal_norm
        r₁.vault'.exact.assetsTotal_nonneg hatr
      obtain ⟨heu, hel, hel1⟩ := add_err v.assetsTotal cN r₁.vault'.assetsTotal v.wf.assetsTotal_norm
        hApos hcNn zc (by rw [hcNv]; exact hcz) hzc0 hadd hcap
      obtain ⟨X, zq, hqz, hzq0, hzqM, hX, hq1, hq2, hq3, hq4⟩ := payout_int_cert r₁.vault' r₁.sharesIssued
        cw.assets' hint₁ hsc hspos (navExact_of_zero _ false hL₁0) (by rw [hS₁v]; exact hSs) hp
      rw [hI₂] at hX
      have hp0 : 0 ≤ cw.assets'.toRat := by rw [hqz]; exact_mod_cast hzq0
      have hcwint : cw.assets'.integral = true := by
        obtain ⟨-, hpnt, -, -⟩ := WdMono.price_facts _ false _ _ hsc hspos.le
          (navExact_of_zero _ false hL₁0) hp
        unfold STAmount.integral; rw [hpnt]; exact hint₁
      have hval : r₂.assets'.toRat = cw.assets'.toRat :=
        WdMono.clampToSumExponent_neg_int_toRat _ _ _ hcwint hp0 hcl
      have hAv : A = v.assetsTotal.toRat := rfl
      have hJ0 : 0 ≤ A₁ * s / (S + s) := div_nonneg (mul_nonneg
        r₁.vault'.exact.assetsTotal_nonneg hspos.le) hSs.le
      obtain ⟨hg, hl⟩ := int_core A S s I zc zq Y (A₁ * s / (S + s)) X
        (A₁ - (A + zc)) (5 / (2 ^ 63 + 7)) (by norm_num) (by norm_num) hSpos hspos hAsI
        (by rw [div_mul_cancel₀ _ (ne_of_gt hSs)]; ring) hY hI0 (by exact_mod_cast hzc0) hc1 hc2 hc3
        hc4 hX hJ0 hq1 hq2 hq3 hq4 hzcM hzqM (by rw [hAv]; exact heu) (by rw [hAv]; exact hel)
        (by rw [hAv]; exact hel1) ⟨zc, rfl⟩ ⟨zq, rfl⟩
      rw [← hcz] at hg hl
      rw [← hqz, ← hval] at hg hl
      rw [← hκ] at hg hl
      refine ⟨fun e he => ?_, atr', hatrv, ?_⟩
      · have : (1 : ℚ) ≤ 10 ^ e := one_le_zpow₀ (by norm_num) (he0 e he)
        linarith
      · obtain ⟨-, hoff', -⟩ := STAmount.ofNumber_integral_facts _ _ _ _ hint hatrv
        have hx' : atr'.exponent = 0 := hoff'
        rw [hcexp, hx', zpow_zero]
        have := le_max_right (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
          (1 - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
        have := le_max_left (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
          (1 - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
        linarith
    · ---------------------------------------------------------------- fractional asset
      have hintf : v.numericType.isIntegral = false := by simpa using hint
      have hvfrac : v.numericType = .fractional := by
        cases h : v.numericType with
        | fractional => rfl
        | integral _ _ _ _ => rw [h] at hintf; simp [NumericType.isIntegral] at hintf
      rw [hε] at hlo
      have hloss := loss_arith S s c I J (r₁.vault'.idealAssetsWithdraw false s) r₂.assets'.toRat
        (1 / 2 * 10 ^ r₁.amountDeposit'.exponent) _ hS0 hspos hc0 hI0 huc0 hover hJ hI₂lo hlo
      refine ⟨fun e he => ?_, atr', hatrv, ?_⟩
      · have hpay := payout_le r₁.vault' r₁.sharesIssued cw.assets' r₂.assets' atr
          (by rw [hnt']; exact hintf) hsc hspos.le (navExact_of_zero _ false hL₁0) hp hatr hcl hfnp
        rw [hI₂, hε] at hpay
        have hAv : A = v.assetsTotal.toRat := rfl
        rcases charge_facts v amountDeposit r₁ hcanon hpos hok₁ herr₁ with
          ⟨hint', -⟩ | ⟨-, P, Qd, ep', hPc, hPn, hQd, hPQ, hcP, hPc', hsum, hug, hep'⟩
        · rw [hint'] at hintf; exact absurd hintf (by decide)
        obtain ⟨an, q, hann, han0, hanu, hof, hle⟩ := hpay
        have hu0 : (0 : ℚ) < 10 ^ P.exponent := zpow_pos (by norm_num) _
        obtain ⟨hblo, hbhi⟩ := DepTight.canon_band P hPc hPn
        have h15 : (10 : ℚ) ^ (P.exponent + 15) = 10 ^ 15 * 10 ^ P.exponent := by
          rw [zpow_add₀ (by norm_num)]; ring
        have h16 : (10 : ℚ) ^ (P.exponent + 16) = 10 ^ 16 * 10 ^ P.exponent := by
          rw [zpow_add₀ (by norm_num)]; ring
        rw [h15] at hblo
        rw [h16] at hbhi
        have hg : (10 : ℚ) ^ ep' ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) (hep' e he)
        rw [← hAv] at hsum
        rcases gain_frac_arith S s A c P.toRat (10 ^ P.exponent) (10 ^ ep') I Qd A₁ an.toRat
            hS0 hspos hA0 hAsI hQd hPQ hcP hc0 hA₁up hanu hsum hu0 hblo hbhi with h1 | ⟨h2, h3⟩
        · have := pack_le an P q hann han0 hPc hPn h1 hof
          linarith
        · have := pack_le_succ an P q hann han0 hPc hPn h2 hof
          linarith
      · -- the grids absorb the relative term
        obtain ⟨hcc, hcpos⟩ := hfrac hintf
        obtain ⟨hq0, hqnt, hqc, -⟩ := WdMono.price_facts _ false _ _ hsc hspos.le
          (navExact_of_zero _ false hL₁0) hp
        have hint₁ : r₁.vault'.numericType.isIntegral = false := by rw [hnt']; exact hintf
        have hTn := r₁.vault'.wf.assetsTotal_norm
        have hT0 : 0 ≤ r₁.vault'.assetsTotal.toRat := r₁.vault'.exact.assetsTotal_nonneg
        have hvfrac₁ : r₁.vault'.numericType = .fractional := by rw [hnt']; exact hvfrac
        have hqz : cw.assets'.mValue ≠ 0 := fun hz => by
          have := WdMono.clamp_zero_frac _ cw.assets' _ atr hTn hT0 (hqnt.trans hvfrac₁) hz
            (by rw [← hvfrac₁]; exact hatr) hcl
          rw [hfnp] at this; exact absurd (Except.ok.inj this) (by decide)
        have hqcan := hqc hint₁ hqz
        have hqpos := WdMono.pos_of_nonneg _ hq0 hqz
        obtain ⟨hacan, hapos, hqa⟩ := clamp_half _ cw.assets' r₂.assets' hqcan hqpos hcl hfnp
        have hI₂c : c * (98 / 100) ≤ r₁.vault'.idealAssetsWithdraw false s :=
          frac_worth r₁.amountDeposit' S s I J _ hcc hcpos hS0 hspos hI0 hover hJ hI₂lo
        have hcsmall : (10 : ℚ) ^ (-82 : ℤ) ≤ r₁.vault'.idealAssetsWithdraw false s := by
          have h0 : (10 : ℚ) ^ (-81 : ℤ) ≤ c := by
            have := WdAcc.iou_abs_ge _ hcc
            rwa [abs_of_pos hcpos] at this
          have h2 : (10 : ℚ) ^ (-82 : ℤ) ≤ 10 ^ (-81 : ℤ) * (98 / 100) := by norm_num
          have h3 : (10 : ℚ) ^ (-81 : ℤ) * (98 / 100) ≤ c * (98 / 100) :=
            mul_le_mul_of_nonneg_right h0 (by norm_num)
          exact le_trans h2 (le_trans h3 hI₂c)
        obtain ⟨an0, hof0, hann0, -, han0, hanl⟩ :=
          WdAcc.price_an_lower _ _ _ false hsc (navExact_of_zero _ false hL₁0) hp hcsmall
        rw [hvfrac₁] at hof0
        have hhalf := WdTight.frac_half _ rfl an0 cw.assets' hann0 han0.le hof0 hqz
        rw [hε] at hanl
        have := frac_loss_final r₁.amountDeposit' r₂.assets' cw.assets' atr'.exponent _ _ hcc hcpos
          hacan hapos hqcan hqpos hqa hI₂c hanl hhalf hloss
        linarith

end XRPL.Model.SingleAssetVault
