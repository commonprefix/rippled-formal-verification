import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Vault.Proofs.DepositRounding.Grid
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.ClampFacts

/-! # `Vault.deposit` entry rounding and donation -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open DepRnd

lemma Vault.roundedDepositAmount_integral_proof (v : Vault) (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) (hnz : amountDeposit.isZero = false) :
    v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) := by
  simp [Vault.roundedDepositAmount, roundToVaultExponent, hint, hnz, bind, Except.bind, pure,
    Except.pure]

lemma Vault.deposit_donation_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit true hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 := by
  obtain ⟨hround, -⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals simp_all [DepositResult.rejected]

lemma Vault.roundedDepositAmount_bounds_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  refine ⟨?_, hnz⟩
  have hmv : roundedAmount.mValue ≠ 0 := by
    intro h0
    have : roundedAmount.isZero = true := by
      unfold STAmount.isZero; rw [h0]; rfl
    rw [this] at hnz; exact Bool.noConfusion hnz
  -- the self-grid witness, used by every exact-passthrough exit
  have hself : roundedAmount = amountDeposit →
      ∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
        (10 : ℚ) ^ s ≤ |roundedAmount.toRat| := by
    intro heq
    subst heq
    exact ⟨roundedAmount.exponent, STAmount.self_grid roundedAmount,
      STAmount.ulp_le_abs_toRat roundedAmount hmv⟩
  by_cases hint : amountDeposit.integral = true
  · simp only [roundToVaultExponent, hint, if_true] at hround
    exact hself (Except.ok.inj hround).symm
  · have hfr : amountDeposit.integral = false := by
      rcases hb : amountDeposit.integral with _ | _
      · rfl
      · exact absurd hb hint
    have hc := hcanon hfr
    unfold roundToVaultExponent at hround
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hround
    -- `roundToVaultExponent` now derives the grid through `postSumExponent`, which
    -- itself prices the amount and forms the post-sum total before taking its exponent
    simp only [pure_bind] at hround
    obtain ⟨postScale, hps, hrx⟩ := bind_ok_peel _ _ _ hround
    unfold postSumExponent at hps
    obtain ⟨amountNumber, -, hps⟩ := bind_ok_peel _ _ _ hps
    obtain ⟨assetsTotal', -, hps⟩ := bind_ok_peel _ _ _ hps
    -- the amount is nonzero (a zero amount would pass through and contradict `hnz`)
    have hz : amountDeposit.isZero = false := by
      rcases hb : amountDeposit.isZero with _ | _
      · rfl
      · exfalso
        unfold STAmount.roundToExponent at hrx
        rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_pos hb] at hrx
        have : amountDeposit = roundedAmount := Except.ok.inj hrx
        rw [← this] at hnz
        rw [hb] at hnz
        exact Bool.noConfusion hnz
    by_cases hge : amountDeposit.exponent ≥ postScale
    · -- early exit: the amount already lives on a grid at least as fine
      apply hself
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true),
        if_neg (by rw [hz]; exact Bool.false_ne_true), if_pos hge] at hrx
      exact (Except.ok.inj hrx).symm
    · -- true truncation: the packaged grid theorem at `postScale`
      have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
        have hnum : amountDeposit.numericType = .fractional := hc.is_fractional
        rw [← hnum]
        exact hps
      have hps_range : (-96 : ℤ) ≤ postScale ∧ postScale ≤ 80 := by
        rcases exponent_fractional_offset assetsTotal' postScale hps_nt with h100 | hr
        · exfalso
          have := hc.exp_lo
          have hem : amountDeposit.exponent = amountDeposit.mOffset := rfl
          have hlt := not_le.mp hge
          omega
        · exact hr
      have hgrid := STAmount.roundToExponent_rounded amountDeposit roundedAmount postScale
        .downward hc hps_range.1 hps_range.2 hmv hrx
      refine ⟨postScale, hgrid, ?_⟩
      have hval : roundedAmount.toRat
          = (⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ) * 10 ^ postScale := hgrid
      have hne := STAmount.toRat_ne_zero roundedAmount hmv
      have hk : ⌊amountDeposit.toRat / 10 ^ postScale⌋ ≠ 0 := by
        intro h0
        rw [h0] at hval
        simp only [Int.cast_zero, zero_mul] at hval
        exact hne hval
      have hpow_pos : (0 : ℚ) < 10 ^ postScale := zpow_pos (by norm_num) _
      have habs : |roundedAmount.toRat|
          = |(⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ)| * 10 ^ postScale := by
        rw [hval, abs_mul, abs_of_pos hpow_pos]
      have hone : (1 : ℚ) ≤ |(⌊amountDeposit.toRat / 10 ^ postScale⌋ : ℚ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by omega)
      rw [habs]
      nlinarith

lemma Vault.deposit_under_maximum_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hcanon : amountDeposit.Canonical)
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r)
    (hmargin : ∀ m ∈ v.assetsMaximum,
      v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    r.error ≠ some .tecLIMIT_EXCEEDED := by
  intro hLE
  unfold Vault.deposit at hok
  obtain ⟨hround0, hnzR⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  -- the rounded amount is a DOWNWARD snap of a positive amount, and nonzero
  have hposR : 0 < roundedAmount.toRat := by
    obtain ⟨⟨sR, hrepR, hulpR⟩, -⟩ :=
      Vault.roundedDepositAmount_bounds_proof v amountDeposit roundedAmount
        hcanon.2 hrounded
    have hfl : roundedAmount.toRat = (⌊amountDeposit.toRat / (10:ℚ) ^ sR⌋ : ℚ) * (10:ℚ) ^ sR :=
      hrepR
    have hpow : (0:ℚ) < (10:ℚ) ^ sR := zpow_pos (by norm_num) _
    have hnn : 0 ≤ roundedAmount.toRat := by
      rw [hfl]
      have : (0:ℚ) ≤ (⌊amountDeposit.toRat / (10:ℚ) ^ sR⌋ : ℚ) := by
        have : (0:ℤ) ≤ ⌊amountDeposit.toRat / (10:ℚ) ^ sR⌋ :=
          Int.floor_nonneg.mpr (by positivity)
        exact_mod_cast this
      positivity
    have hne : roundedAmount.toRat ≠ 0 :=
      STAmount.toRat_ne_zero roundedAmount (ne_of_beq_false hnzR)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hcanonR : roundedAmount.Canonical :=
    Vault.roundedDepositAmount_canonical v amountDeposit roundedAmount hcanon hrounded
  obtain ⟨amount, hround, hok⟩ := bind_ok_peel _ _ _ hok
  have hameq : amount = roundedAmount := Except.ok.inj (hround.symm.trans hround0)
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_neg (by simp [hd])] at hok
          obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · have hcanon_amt : amount.Canonical := by rw [hameq]; exact hcanonR
            obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical amount .to_nearest
              (STAmount.Canonical.exactCanonical amount hcanon_amt)
            have hn1eq : an = n1 := by rw [han] at hn1; exact Except.ok.inj hn1
            rw [hn1eq] at hval hnorm
            have hbound : ∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat + n1.toRat ≤ m.toRat := by
              intro m hm2
              rw [hval, hameq]
              have hmarg := hmargin m hm2
              have hAeq : v.assetsTotal.toRat = v.toExact.assetsTotal := rfl
              linarith
            have hgf := deposit_maximum_guard_false v n1 at' hnorm hat hbound
            rw [hgf] at hm; exact absurd hm (by simp)
          · rw [if_neg hm] at hok
            obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp)
        · rw [if_pos (by simp [hd])] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          rcases computeDeposit_codes v amount cres hcd with h5 | h5 | h5 | ⟨a, sh, h5⟩
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5; injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp [DepositResult.rejected])
          · subst h5
            simp only [] at hok
            -- the model clamps the priced charge before recording it
            obtain ⟨rc, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨fnp, hfnp, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hfz : fnp = true
            · rw [if_pos hfz] at hok
              injection hok with h; rw [← h] at hLE
              exact absurd hLE (by simp [DepositResult.rejected])
            · rw [if_neg hfz] at hok
              obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
              · obtain ⟨shares, hats, hshz, hsad, -, -⟩ :=
                  computeDeposit_success_reduces v amount a sh hcd
                obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hats
                have hshpos : 0 < shares.toRat :=
                  assetsToSharesDeposit_pos v amount shares (by rw [hameq]; exact hcanonR)
                    (by rw [hameq]; exact hposR) hats hshz
                have hbound := deposit_real_charge_bound v amount roundedAmount a sh rc n1
                  hcanonR hnzR hposR hameq hcd hclamp hn1 hmargin
                have hn1norm : n1.isNormalized :=
                  (Vault.deposit_charge_toNumber_facts v shares a rc n1 hshc hshnt hshpos
                    hsad hclamp hn1).2
                have hgf := deposit_maximum_guard_false v n1 at' hn1norm hat hbound
                rw [hgf] at hm; exact absurd hm (by simp)
              · rw [if_neg hm] at hok
                obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                injection hok with h; rw [← h] at hLE; exact absurd hLE (by simp)

lemma DepRnd.donation_reduces (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hpos : 0 < amountDeposit.toRat) (hok : v.deposit amountDeposit true hpos = .ok r) (herr : r.error = none) :
    ∃ (amount : STAmount) (aN aT aV zN sT : Number) (v' : Vault),
      roundToVaultExponent amountDeposit v.assetsTotal = .ok amount ∧
      amount.isZero = false ∧
      amount.toNumber .to_nearest = .ok aN ∧
      v.assetsTotal.operator_add aN .to_nearest = .ok aT ∧
      (STAmount.zero .int64).toNumber .to_nearest = .ok zN ∧
      v.sharesTotal.operator_add zN .to_nearest = .ok sT ∧
      v'.toRawVault =
        { v.toRawVault with assetsTotal := aT, assetsAvailable := aV, sharesTotal := sT } ∧
      r.vault' = v' ∧ r.amountDeposit' = amount := by
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first | (simp_all [DepositResult.rejected]; done) | skip
  simp_all only [Bool.not_eq_true, Bool.true_and, beq_iff_eq, Bool.and_false,
    Bool.false_eq_true, not_false_eq_true, Bool.not_true, Bool.and_eq_true, not_and, ↓existsAndEq,
    Except.ok.injEq, and_self, and_true, true_and, exists_and_left, exists_eq_left']
  exact ⟨_, (RawVault.to_lawful_ok ‹_›).1⟩

lemma Vault.deposit_donation_no_dilution_proof (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧
      v.assetsTotal.toRat.den = 1 ∧ v.assetsAvailable.toRat.den = 1 ∧
      v.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true hpos = .ok r) (herr : r.error = none) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal := by
  obtain ⟨amount, aN, aT, aV, zN, sT, v', hround, hamz, haN, haT, hzN, hsT, hv', hr, hamt⟩ :=
    DepRnd.donation_reduces v amountDeposit r hpos hok herr
  have hzN0 : zN = Number.zero := by
    rw [zero_int64_toNumber] at hzN; exact (Except.ok.inj hzN).symm
  rw [hzN0, Number.operator_add_zero_right] at hsT
  have hsT' : sT = v.sharesTotal := (Except.ok.inj hsT).symm
  rw [hr]
  refine ⟨?_, ?_⟩
  · show v.assetsTotal.toRat - v.lossUnrealized.toRat <
      v'.toRawVault.assetsTotal.toRat - v'.toRawVault.lossUnrealized.toRat
    rw [hv']
    show v.assetsTotal.toRat - v.lossUnrealized.toRat < aT.toRat - v.lossUnrealized.toRat
    suffices h : v.assetsTotal.toRat < aT.toRat by linarith
    have hA0 : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
    by_cases hint : amountDeposit.integral = true
    · obtain ⟨-, -, hdenA, -, hbound⟩ := hint_dom hint
      have hameq : amount = amountDeposit := by
        simp only [roundToVaultExponent, hint, if_true] at hround
        exact (Except.ok.inj hround).symm
      subst hameq
      obtain ⟨hIC, hmax⟩ := hcanon.1 hint
      obtain ⟨aN', haN', haNval, haNnorm, hden⟩ :=
        STAmount.toNumber_integral_exact amount .to_nearest hIC hmax
      rw [haN'] at haN
      obtain rfl : aN' = aN := Except.ok.inj haN
      have hden' : aN'.toRat.den = 1 := by rw [haNval]; exact hden
      have hbnd : (v.assetsTotal.toRat + aN'.toRat).num.natAbs < 2 ^ 63 := by
        refine Rat.num_natAbs_lt_of_abs_le _ (Rat.den_one_add _ _ hdenA hden') ?_
        rw [haNval, abs_le]
        have : v.toExact.assetsTotal = v.assetsTotal.toRat := rfl
        constructor <;> linarith
      obtain ⟨hval, -⟩ := operator_add_exact_int v.assetsTotal aN' aT
        v.wf.assetsTotal_norm haNnorm hdenA hden' hbnd haT
      rw [hval, haNval]; linarith
    · have hfr : amountDeposit.integral = false := by simpa using hint
      obtain ⟨sg, hF1, hF2⟩ :=
        Vault.donation_grid_bound v amountDeposit amount hcanon hfr hpos hround hamz
      have hamC : amount.Canonical := by
        rcases roundToVaultExponent_canonical_or_isZero amountDeposit amount v.assetsTotal
          hcanon hround with hc | hz
        · exact hc
        · rw [hz] at hamz; exact absurd hamz (by decide)
      obtain ⟨aN', haN', haNval, haNnorm⟩ := STAmount.toNumber_exact_canonical amount .to_nearest
        (STAmount.Canonical.exactCanonical amount hamC)
      rw [haN'] at haN
      obtain rfl : aN' = aN := Except.ok.inj haN
      have hpow : (0 : ℚ) < (10 : ℚ) ^ sg := zpow_pos (by norm_num) _
      have hamt_pos : 0 < amount.toRat := lt_of_lt_of_le hpow hF1
      have hru := operator_add_nonneg_rounds v.assetsTotal aN' aT v.wf.assetsTotal_norm haNnorm
        hA0 (by rw [haNval]; exact hamt_pos.le) haT
      simp only [RoundsWithin, RatValued.toRat] at hru
      rw [haNval,
        abs_of_nonneg (show 0 ≤ v.assetsTotal.toRat + amount.toRat by linarith)] at hru
      have hlo := (abs_le.mp hru).1
      nlinarith [hF1, hF2, hpow]
  · show v'.toRawVault.sharesTotal.toRat.num.toNat = v.sharesTotal.toRat.num.toNat
    rw [hv', hsT']

end XRPL.Model.SingleAssetVault
