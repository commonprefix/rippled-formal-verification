import XRPL.Properties.Vault.Proofs.Dilution.Withdraw
import XRPL.Properties.Vault.Proofs.ClawbackTight

/-! # A clawback dilutes by at most `depositε` plus half a unit of the recovery -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol

lemma computeClawback_zero_facts (v : Vault) (assets holderShares : STAmount)
    (cr : ComputeClawbackResult) (hz : assets.isZero = true)
    (hok : computeClawback v assets holderShares = .ok cr) (herr : cr.error = none) :
    ∃ priced prn,
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
      priced.toNumber .to_nearest = .ok prn ∧
      prn.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.isFractionalNonPositive = .ok false ∧
      (cr.sharesDestroyed = holderShares ∨
        ∃ X, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X ∧
          assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed) := by
  simp only [computeClawback, assetsToSharesClawback, hz, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | (simp at herr; done)
    | exact absurd trivial ‹¬ True›
    | (dsimp only; exact ⟨_, _, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all, Or.inl rfl⟩)
    | (dsimp only; exact ⟨_, _, ‹_›, ‹_›, by simp_all, ‹_›, by simp_all, Or.inr ⟨_, ‹_›, ‹_›⟩⟩)

/-- The stored fields of a successful clawback: totals from the recorded amounts, the loss
untouched. -/
lemma clawback_fields (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error = none) :
    ∃ cr, computeClawback v assets holderShares = .ok cr ∧ cr.error = none ∧
      r.assetsRecovered = cr.assetsRecovered ∧ r.sharesDestroyed = cr.sharesDestroyed ∧
      r.vault'.toRawVault.lossUnrealized = v.toRawVault.lossUnrealized := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp [ClawbackResult.rejected] at herr; done)
    | (simp only at herr; simp [herr] at *; done)
    | skip
  have hl := (RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1
  refine ⟨_, ‹computeClawback _ _ _ = _›, ?_, rfl, rfl, ?_⟩
  · simpa using ‹¬ (Option.isSome _) = true›
  · dsimp only; rw [hl]

/-- The destroyed shares of a successful clawback: an exact, canonical, nonnegative
integer within `int64`. -/
lemma clawback_sd_facts (v : Vault) (assets holderShares sd : STAmount)
    (hc : assets.Canonical) (hnn : 0 ≤ assets.toRat)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hsd : sd = holderShares ∨ ∃ X, (X = assets ∨
        STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) ∧
      assetsToSharesWithdraw v X true false = .ok sd) :
    sd.Canonical ∧ 0 ≤ sd.toRat ∧ sd.toRat.den = 1 ∧ sd.toRat ≤ 2 ^ 63 - 1 := by
  rcases hsd with rfl | ⟨X, hX, hsh⟩
  · have h0 : 0 ≤ sd.toRat := STAmount.toRat_nonneg_of sd hSnn
    refine ⟨hSc, h0, STAmount.IntegralCanonical.den_eq_one sd hSic, ?_⟩
    rw [← STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sd hSic h0]
    have h1 := hSic.in_range
    have h2 := (hSc.1 hSic.is_integral).2
    have h3 : maxRep.toNat = 2 ^ 63 - 1 := by decide
    have h4 : sd.mValue.toNat + 1 ≤ 2 ^ 63 := by omega
    have h5 : ((sd.mValue.toNat + 1 : ℕ) : ℚ) ≤ ((2 ^ 63 : ℕ) : ℚ) := by exact_mod_cast h4
    push_cast at h5
    linarith
  · obtain ⟨hsnt, hsoff, hsval⟩ := ClwAcc.shares_shape v X sd hsh
    have hsc := Exact.int64_canonical _ hsnt hsoff hsval
    have hsd0 : 0 ≤ sd.toRat := by
      refine Exact.shares_nonneg v X _ false (fun xn hxn => ?_) hsh
      rcases hX with rfl | hX
      · obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
          (STAmount.Canonical.exactCanonical _ hc)
        obtain rfl := Except.ok.inj (hsn.symm.trans hxn)
        exact ⟨hsnn, by rw [hsnv]; exact hnn⟩
      · obtain ⟨hX0, -, -, hXx⟩ := WdMono.ofNumber_facts v.numericType _ X
          v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg hX
        obtain ⟨hxnn, hxnv⟩ := hXx xn hxn
        exact ⟨hxnn, by rw [hxnv]; exact hX0⟩
    obtain ⟨hden, hle⟩ := WdAcc.int64_bounds sd hsd0 hsc hsnt
    exact ⟨hsc, hsd0, hden, hle⟩

/-- The recovery of a priced share count, clamped: at most its ideal worth times
`1 + depositε` plus half a unit of its own last digit. -/
lemma claw_upper (v : Vault) (hnav : v.WithdrawNavExact false) (sd priced rec : STAmount)
    (prn : Number) (hsdE : ClwTight.NumExact sd) (hsd0 : 0 ≤ sd.toRat)
    (hpr : v.sharesToAssetsWithdraw sd false = .ok priced)
    (harn : priced.toNumber .to_nearest = .ok prn)
    (hle : prn.operator_gt v.assetsAvailable = false)
    (hcl : clampToSumExponent v.assetsTotal priced.operator_neg = .ok rec)
    (hfnp : rec.isFractionalNonPositive = .ok false) :
    rec.toRat ≤ v.idealAssetsClawback sd.toRat * (1 + depositε) +
      1 / 2 * (10 : ℚ) ^ rec.exponent := by
  have hAn := v.wf.assetsAvailable_norm
  have hTn := v.wf.assetsTotal_norm
  have hT0 := v.exact.assetsTotal_nonneg
  have hAle := v.exact.assetsAvailable_le
  have hε : (0 : ℚ) ≤ depositε ∧ depositε ≤ 1 / 2 := by unfold depositε; norm_num
  have hpc := ClwTight.price_core v hnav _ priced hsdE hsd0 hpr
  have hpE : ClwTight.NumExact priced := by
    rcases hpc with ⟨hz, -⟩ | ⟨an, hann, -, -, -, -, hof⟩
    · exact ClwTight.numExact_of_zero _ hz
    · exact ClwTight.numExact_of_ofNumber _ _ _ _ hof
  have hple : priced.toRat ≤ v.assetsAvailable.toRat := by
    obtain ⟨harnn, harnv⟩ := hpE prn harn
    rw [← harnv]
    by_contra hc'
    replace hc' := not_le.mp hc'
    rw [(operator_gt_iff _ _ harnn hAn).mpr hc'] at hle
    exact absurd hle (by decide)
  have hptype := ClwTight.price_type v _ priced hpr
  have hI0 : 0 ≤ v.idealAssetsClawback sd.toRat := by
    unfold RawVault.idealAssetsClawback
    exact div_nonneg (mul_nonneg v.exact.withdraw_nav_nonneg hsd0) (Nat.cast_nonneg _)
  by_cases hint : v.numericType.isIntegral = true
  · rcases hpc with ⟨hz, hIs⟩ | ⟨an, hann, ham, hanneg, hIpos, hb, hof⟩
    · have hp0 : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr hz
      obtain ⟨hrp, -, -, -⟩ := ClwTight.integral_clamp_eq v hint sd priced rec hpr hp0.ge hcl
      have : (0 : ℚ) ≤ 1 / 2 * 10 ^ rec.exponent := by positivity
      nlinarith
    · have hp0 := STAmount.ofNumber_nonneg _ _ _ _ hann hanneg hof
      obtain ⟨hrp, hre, hpe, -⟩ := ClwTight.integral_clamp_eq v hint sd priced rec hpr hp0 hcl
      obtain ⟨hh, -, -⟩ := ClwTight.ofNumber_half v.numericType an priced hann ham hanneg hof
        (fun h => absurd hint (by rw [h]; decide))
      rw [hpe, zpow_zero, mul_one] at hh
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      obtain ⟨hh1, hh2⟩ := abs_le.mp hh
      rw [hre, zpow_zero, mul_one]; nlinarith
  · have hfr := ClwTight.fractional_of_not_integral _ hint
    rcases hpc with ⟨hz, -⟩ | ⟨an, hann, ham, hanneg, hIpos, hb, hof⟩
    · exact absurd (ClwTight.frac_zero_contra v.assetsTotal hTn hT0 priced rec hz
        (by rw [hptype, hfr]) hcl hfnp) (fun h => h)
    have hpm : priced.mValue ≠ 0 := fun hz =>
      ClwTight.frac_zero_contra v.assetsTotal hTn hT0 priced rec hz (by rw [hptype, hfr]) hcl hfnp
    obtain ⟨hh, -, hcan⟩ := ClwTight.ofNumber_half v.numericType an priced hann ham hanneg hof
      (fun _ => hpm)
    have hpcan := hcan (by rw [hfr]; rfl)
    have hp0 := STAmount.ofNumber_nonneg _ _ _ _ hann hanneg hof
    have hppos : 0 < priced.toRat :=
      lt_of_le_of_ne hp0 (fun h => hpm ((STAmount.toRat_eq_zero_iff _).mp h.symm))
    have hrfc := WdAcc.clamp_frac_shape v.assetsTotal priced.operator_neg rec
      (STAmount.operator_neg_fczr priced ⟨hpcan.is_fractional, Or.inl hpcan⟩) hcl
    have hrint : rec.integral = false := by
      show rec.mNumericType.isIntegral = false; rw [hrfc.1]; rfl
    obtain ⟨hrm, -⟩ := STAmount.fnp_false_pos rec hrint hfnp
    obtain ⟨-, -, hcase⟩ := ClwTight.clamp_frac v.assetsTotal hTn priced rec hpcan hppos
      (hple.trans hAle) hcl hrm
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    obtain ⟨hh1, hh2⟩ := abs_le.mp hh
    rcases hcase with ⟨hRP, hRe⟩ | ⟨hl, -⟩
    · rw [hRe]; nlinarith
    · have : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
      have : (0 : ℚ) ≤ 1 / 2 * 10 ^ rec.exponent := by positivity
      nlinarith

/-- The totals after a clawback of priced destroyed shares drop by exactly the recovery. -/
lemma claw_exact (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error = none) (priced : STAmount) (prn : Number)
    (hsc : r.sharesDestroyed.Canonical) (hsd0 : 0 ≤ r.sharesDestroyed.toRat)
    (hden : r.sharesDestroyed.toRat.den = 1) (hsdle : r.sharesDestroyed.toRat ≤ 2 ^ 63 - 1)
    (hpr : v.sharesToAssetsWithdraw r.sharesDestroyed false = .ok priced)
    (hprn : priced.toNumber .to_nearest = .ok prn)
    (hgt : prn.operator_gt v.assetsAvailable = false)
    (hcl : clampToSumExponent v.assetsTotal priced.operator_neg = .ok r.assetsRecovered)
    (hfnp : r.assetsRecovered.isFractionalNonPositive = .ok false)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    (r.vault'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat := by
  obtain ⟨cr, sdn, arn, at', atr, av', st', -, -, hra, hsd, hsdn, harn, hat, hatr, hav,
    hsub, hvt, -, hvs⟩ := Exact.clawback_ok_cases v assets holderShares r hnn hok herr
  rw [← hra, ← hsd] at *
  have hvx := v.exact
  have hAT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := hvx.assetsAvailable_le
  have hT0 : 0 ≤ v.assetsTotal.toRat := hvx.assetsTotal_nonneg
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
  obtain ⟨ha0, hap, hg⟩ := Exact.clamp_payout v priced r.assetsRecovered hp0 hpnt hpc
    (fun hint => (WdAcc.price_integral_shape v _ _ _ hint hpr).2.1) (le_trans hpA hAT)
    (fun hint => Exact.total_fit _ hint _ atr v.wf.assetsTotal_norm hT0 hatr) hcl hfnp
  obtain ⟨hann', hanv'⟩ := WdAcc.payout_toNumber v _ _ _ false arn hsc hpr hcl harn
  obtain ⟨h1, -⟩ := Exact.updates_exact _ _ _ _ _ r.assetsRecovered.toRat v.wf.assetsTotal_norm
    v.wf.assetsAvailable_norm hAT hann' hanv' ha0 (le_trans hap hpA) hg hat hav
  refine ⟨by rw [hvt]; exact h1, ?_⟩
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal _ v.wf
  rw [RawVault.WF.toExact_sharesTotal _ r.vault'.wf, hvs, hST]
  obtain rfl : sn = sdn := Except.ok.inj (hsn.symm.trans hsdn)
  rw [← hsnv] at hden hsdle hsd0 ⊢
  have hSden := v.wf.sharesTotal_int
  have hSnn := v.wf.sharesTotal_nonneg
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  refine (operator_sub_exact_int _ sn st' v.wf.sharesTotal_norm hsnn hSden hden ?_ hsub).1
  rw [rat_sub_eq_num_cast _ _ hSden hden, Rat.num_intCast]
  have h1 := rat_eq_num_cast_of_den_one _ hSden
  have h2 := rat_eq_num_cast_of_den_one _ hden
  have a1 : (0 : ℤ) ≤ v.sharesTotal.toRat.num := by exact_mod_cast (h1 ▸ hSnn)
  have a2 : v.sharesTotal.toRat.num ≤ 2 ^ 63 - 1 := by
    have : ((v.sharesTotal.toRat.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by
      rw [h1]; push_cast; linarith
    exact_mod_cast this
  have a3 : (0 : ℤ) ≤ sn.toRat.num := by exact_mod_cast (h2 ▸ hsd0)
  have a4 : sn.toRat.num ≤ 2 ^ 63 - 1 := by
    have : ((sn.toRat.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by rw [h2]; push_cast; linarith
    exact_mod_cast this
  omega

end XRPL.Model.SingleAssetVault.DilG

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DilG

/-- **Clawback dilution.** With at least half the shares remaining, per-share value
drops by at most `depositε` relatively plus half a unit of the recovery's last digit per
share, on both the priced and the claw-all arms. -/
lemma Vault.clawback_no_dilution_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hL : v.toExact.lossUnrealized = 0)
    (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hmargin : r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨cr, hcomp, hcerr, hra, hsd, hL'⟩ := clawback_fields v assets holderShares r hnn hok herr
  obtain ⟨priced, prn, hpr, hprn, hgt, hcl, hfnp, hsdp⟩ :
      ∃ priced prn,
        v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
        priced.toNumber .to_nearest = .ok prn ∧
        prn.operator_gt v.assetsAvailable = false ∧
        clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
        cr.assetsRecovered.isFractionalNonPositive = .ok false ∧
        (cr.sharesDestroyed = holderShares ∨ ∃ X, (X = assets ∨
            STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) ∧
          assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed) := by
    by_cases hz : assets.isZero = true
    · obtain ⟨priced, prn, h1, h2, h3, h4, h5, h6⟩ :=
        computeClawback_zero_facts v assets holderShares cr hz hcomp hcerr
      refine ⟨priced, prn, h1, h2, h3, h4, h5, ?_⟩
      rcases h6 with h | ⟨X, hX, hsh⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, Or.inr hX, hsh⟩
    · obtain ⟨X, priced, prn, hX, hsh, hpr, hprn, hgt, hcl, hfnp⟩ :=
        Exact.computeClawback_facts v assets holderShares cr (by simpa using hz) hcomp hcerr
      exact ⟨priced, prn, hpr, hprn, hgt, hcl, hfnp, Or.inr ⟨X, hX, hsh⟩⟩
  rw [← hsd] at hpr hsdp
  rw [← hra] at hcl hfnp
  obtain ⟨hsc, hsd0, hden, hsdle⟩ :=
    clawback_sd_facts v assets holderShares _ hc hnn hSic hSc hSnn hsdp
  have hup := claw_upper v (navExact_of_zero v false hL) _ priced _ prn
    (ClwTight.numExact_of_canonical _ hsc) hsd0 hpr hprn hgt hcl hfnp
  obtain ⟨hA', hS'⟩ := claw_exact v assets holderShares r hnn hok herr priced prn hsc hsd0 hden
    hsdle hpr hprn hgt hcl hfnp hSfit
  have hnav : v.withdrawNav = v.toExact.assetsTotal := by
    show v.toExact.assetsTotal - v.toExact.lossUnrealized = _; rw [hL]; ring
  have hnav' : r.vault'.withdrawNav = v.toExact.assetsTotal - r.assetsRecovered.toRat := by
    show r.vault'.assetsTotal.toRat - r.vault'.toRawVault.lossUnrealized.toRat = _
    rw [hA', hL']
    have : v.toRawVault.lossUnrealized.toRat = 0 := hL
    rw [this]; ring
  rw [hnav', hS', hnav]
  have hI : v.idealAssetsClawback r.sharesDestroyed.toRat =
      v.toExact.assetsTotal * r.sharesDestroyed.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealAssetsClawback; rw [hnav]
  rw [hI] at hup
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hA0 : 0 ≤ v.toExact.assetsTotal := v.exact.assetsTotal_nonneg
  rcases lt_or_eq_of_le hS0 with hSpos | hSz
  · exact exit_arith _ _ _ _ _ _ hA0 hSpos (by unfold depositε; positivity) hmargin hup
  · have hA : v.toExact.assetsTotal = 0 := (v.exact.empty_shares (by exact_mod_cast hSz.symm)).1
    rw [← hSz, hA]; ring_nf; rfl

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol

/-- The share total and the loss after a successful clawback: the destroyed shares leave
exactly, the loss is untouched. -/
lemma clawback_shares_after (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    (r.vault'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat ∧
    r.vault'.toRawVault.lossUnrealized = v.toRawVault.lossUnrealized := by
  obtain ⟨cr, hcomp, hcerr, hra, hsd, hL'⟩ := clawback_fields v assets holderShares r hnn hok herr
  obtain ⟨priced, prn, hpr, hprn, hgt, hcl, hfnp, hsdp⟩ :
      ∃ priced prn,
        v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok priced ∧
        priced.toNumber .to_nearest = .ok prn ∧
        prn.operator_gt v.assetsAvailable = false ∧
        clampToSumExponent v.assetsTotal priced.operator_neg = .ok cr.assetsRecovered ∧
        cr.assetsRecovered.isFractionalNonPositive = .ok false ∧
        (cr.sharesDestroyed = holderShares ∨ ∃ X, (X = assets ∨
            STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok X) ∧
          assetsToSharesWithdraw v X true false = .ok cr.sharesDestroyed) := by
    by_cases hz : assets.isZero = true
    · obtain ⟨priced, prn, h1, h2, h3, h4, h5, h6⟩ :=
        computeClawback_zero_facts v assets holderShares cr hz hcomp hcerr
      refine ⟨priced, prn, h1, h2, h3, h4, h5, ?_⟩
      rcases h6 with h | ⟨X, hX, hsh⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, Or.inr hX, hsh⟩
    · obtain ⟨X, priced, prn, hX, hsh, hpr, hprn, hgt, hcl, hfnp⟩ :=
        Exact.computeClawback_facts v assets holderShares cr (by simpa using hz) hcomp hcerr
      exact ⟨priced, prn, hpr, hprn, hgt, hcl, hfnp, Or.inr ⟨X, hX, hsh⟩⟩
  rw [← hsd] at hpr hsdp
  rw [← hra] at hcl hfnp
  obtain ⟨hsc, hsd0, hden, hsdle⟩ :=
    clawback_sd_facts v assets holderShares _ hc hnn hSic hSc hSnn hsdp
  obtain ⟨-, hS'⟩ := claw_exact v assets holderShares r hnn hok herr priced prn hsc hsd0 hden
    hsdle hpr hprn hgt hcl hfnp hSfit
  exact ⟨hS', hL'⟩

end XRPL.Model.SingleAssetVault.DilG
