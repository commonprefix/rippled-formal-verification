import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # Deposit limits

A deposit is rejected for passing a limit by the Open-zone check on its charge or by the guard on
the vault maximum. On a reachable vault both read the exact new total. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- An integral `numberExponent` is never above the larger of the given exponent and zero: an
integral amount is stored at offset zero. -/
lemma numberExponent_integral_le (n : Number) (exponent : Int) (nt : NumericType) (e : Int)
    (hnt : nt.isIntegral = true) (hok : numberExponent n exponent nt = .ok e) : e ≤ max exponent 0 := by
  unfold numberExponent at hok
  by_cases hz : n.operator_eq Number.zero = true
  · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at hok
    omega
  simp only [hz, Bool.false_eq_true, if_false] at hok
  cases ha : STAmount.ofNumber nt n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hoff : a.mOffset = 0 := (STAmount.ofNumber_integral_canonical nt n .downward a hnt ha).1.offset_zero
    have hmax : max exponent a.exponent = e := hok
    rw [show a.exponent = 0 from hoff] at hmax
    omega

/-- An Open-zone rejection means the limit is passed. On an Open-zone vault the inflow check
rejects a nonnegative charge only when the cash plus the charge passes the Open-zone limit. -/
private lemma Vault.checkOpenLimit_limit (v : Vault) (hz : v.OpenZone) (charge : STAmount)
    (hc : charge.CanonicalOrZero) (hcnn : 0 ≤ charge.toRat)
    (hin : v.checkOpenLimit charge = .ok .tecLIMIT_EXCEEDED) :
    9 * (10 : ℚ) ^ (15 + v.baseExponent) < v.assetsAvailable.toRat + charge.toRat := by
  by_contra hle
  push Not at hle
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  -- the Open-zone limit is a representable `Number`
  obtain ⟨L, hLn, hLv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 15) v.baseExponent
    (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
  have hLv' : L.toRat = 9 * (10 : ℚ) ^ (15 + v.baseExponent) := by
    rw [hLv, zpow_add₀ (by norm_num)]; push_cast; ring
  -- the sum stays on the base grid
  have keyExp : ∀ (amountNum : Number) (e : ℤ), charge.toNumber .to_nearest = .ok amountNum →
      postSumExponent v.assetsAvailable amountNum v.baseExponent v.numericType = .ok e → e = v.baseExponent := by
    intro amountNum e hn he
    obtain ⟨hnv, hnn⟩ := hc.toNumber_exact _ hn
    obtain ⟨sum, hsum, hne⟩ := postSumExponent_reduces _ _ _ _ e he
    have hge := numberExponent_ge _ _ _ e hne
    by_cases hint : v.numericType.isIntegral = true
    · have := numberExponent_integral_le _ _ _ e hint hne
      have := hbint hint
      omega
    have hfr : v.numericType = .fractional := by
      cases hnt : v.numericType with
      | fractional => rfl
      | integral _ _ _ _ => rw [hnt] at hint; exact absurd rfl hint
    rw [hfr] at hne
    by_contra hneq
    have hgt : v.baseExponent < e := lt_of_le_of_ne (numberExponent_ge _ _ _ e hne) (Ne.symm hneq)
    have hr := operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hnn hsum
    have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnn hsum
    have hs0 : 0 ≤ sum.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg sum _ hr (by rw [hnv]; linarith)
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower sum v.baseExponent e hsn hs0 (by omega) hne hgt
    have hsle := Number.RoundsToRepresentable.le_of_le_normalized sum _ hr L hLn (by rw [hLv', hnv]; exact hle)
    have hp : (10 : ℚ) ^ (v.baseExponent + 16) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h16 : (10 : ℚ) ^ (v.baseExponent + 16) = 10 ^ 16 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num; ring
    rw [hLv', zpow_add₀ (by norm_num)] at hsle
    rw [h16] at hp
    norm_num at hsle
    nlinarith
  -- the capacity stays at or under the limit
  have keyCap : ∀ (amountNum capacity w : Number), charge.toNumber .to_nearest = .ok amountNum →
      v.assetsAvailable.operator_add amountNum .towards_zero = .ok capacity →
      Number.from_rep 9 (15 + v.baseExponent) largeRange.min largeRange.max .to_nearest = .ok w →
      capacity.operator_gt w = true → False := by
    intro amountNum capacity w hn hcap hw hgt
    obtain ⟨hnv, hnn⟩ := hc.toNumber_exact _ hn
    obtain ⟨w', hw', hwv, hwn⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest
      (by decide) (by unfold minExponent; omega) (by unfold maxExponent; omega)
    obtain rfl : w = w' := Except.ok.inj (hw.symm.trans hw')
    have htruth : 0 ≤ v.assetsAvailable.toRat + amountNum.toRat := by rw [hnv]; linarith
    obtain ⟨n, hlo, hcapv⟩ := operator_add_rounded_towards_zero _ _ _ v.wf.assetsAvailable_norm hnn hcap
    rw [if_pos htruth] at hlo
    have hcle : capacity.toRat ≤ v.assetsAvailable.toRat + amountNum.toRat := by
      rw [hcapv]; exact Number.lower_le _ n hlo
    have hcn : capacity.isNormalized := by
      by_cases hq : v.assetsAvailable.toRat + amountNum.toRat = 0
      · -- nothing added: the capacity is the cash itself
        have hn0 : amountNum.toRat = 0 := by rw [hnv] at hq ⊢; linarith
        rw [Number.eq_zero_of_mantissa_zero _ hnn (Number.toRat_eq_zero_iff.mp hn0),
          Number.operator_add_zero_right, Except.ok.injEq] at hcap
        rw [← hcap]; exact v.wf.assetsAvailable_norm
      -- a positive operand bounds the sum, so the capacity is not zero
      have hqpos : 0 < v.assetsAvailable.toRat + amountNum.toRat := lt_of_le_of_ne htruth (Ne.symm hq)
      obtain ⟨m, hm, hm0, hmle⟩ : ∃ m : Number, m.isNormalized ∧ 0 < m.toRat ∧
          m.toRat ≤ v.assetsAvailable.toRat + amountNum.toRat := by
        by_cases ha : 0 < v.assetsAvailable.toRat
        · exact ⟨_, v.wf.assetsAvailable_norm, ha, by rw [hnv]; linarith⟩
        · exact ⟨amountNum, hnn, by rw [hnv] at hqpos ⊢; linarith, by linarith⟩
      have hmn := Number.lower_tight _ n hlo m hm hmle
      have hc0 : capacity.mantissa_ ≠ 0 := fun h => by
        have := Number.toRat_eq_zero_of_mantissa_zero capacity h
        rw [hcapv] at this
        linarith
      exact operator_add_isNormalized _ _ _ .towards_zero v.wf.assetsAvailable_norm hnn hcap hc0
    have := (operator_gt_iff _ _ hcn hwn).mp hgt
    rw [hwv, hnv] at *
    push_cast at this
    linarith
  simp only [Vault.checkOpenLimit, Vault.exceedsOpenLimit, Vault.openLimit, bind, Except.bind, pure,
    Except.pure] at hin
  simp only [hz.assetsTotal_eq, hz.yieldUnrealized, Number.operator_add_zero_right] at hin
  walk_ok
  · have hne : (_ != v.baseExponent) = true := ‹_›
    exact absurd (keyExp _ _ ‹_› ‹_›) (by simpa using hne)
  · exact keyCap _ _ _ ‹_› ‹_› ‹_› ‹_›

/-- Where a limit rejection comes from. A deposit rejected with `tecLIMIT_EXCEEDED` rounded its amount and
priced its charge, then failed the Open-zone check, the cash update, or the guard on the maximum. -/
private lemma Vault.deposit_limit_reduces (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLIMIT_EXCEEDED)) :
    ∃ (ra : STAmount) (amounts : VaultAmounts),
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra) ∧
      (computeDeposit v ra isDonation).run = .ok (.ok amounts) ∧
      (v.checkOpenLimit amounts.assets = .ok .tecLIMIT_EXCEEDED ∨
        (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.error .tecLIMIT_EXCEEDED) ∨
        ∃ (raw : RawVault) (assetsTotal' : Number),
          v.checkOpenLimit amounts.assets = .ok .tesSUCCESS ∧
          (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw) ∧
          raw.assetsTotal = .ok assetsTotal' ∧
          ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
            assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals first
    | (have hr : (v.roundedDepositAmount amountDeposit).run = .ok (.error .tecLIMIT_EXCEEDED) := ‹_›
       exact absurd (Vault.roundedDepositAmount_rejected_code_proof v amountDeposit _ hr) (by decide))
    | (have hcd : (computeDeposit v _ isDonation).run = .ok (.error .tecLIMIT_EXCEEDED) := ‹_›
       rcases computeDeposit_codes v _ _ _ hcd with h | h | h <;> exact absurd h (by decide))
    | (have hr : (v.roundedDepositAmount amountDeposit).run = .ok (.ok _) := ‹_›
       have hcd : (computeDeposit v _ isDonation).run = .ok (.ok _) := ‹_›
       first
         | (have hin : v.checkOpenLimit _ = .ok .tecLIMIT_EXCEEDED := ‹_›
            exact ⟨_, _, hr, hcd, Or.inl hin⟩)
         | (have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.error .tecLIMIT_EXCEEDED) := ‹_›
            exact ⟨_, _, hr, hcd, Or.inr (Or.inl hadj)⟩)
         | (have hin : Vault.checkOpenLimit _ _ = .ok _ := ‹_›
            have hne : ¬ (_ != TER.tesSUCCESS) = true := ‹_›
            rcases Vault.checkOpenLimit_codes _ _ _ hin with h | h <;> subst h
            · have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.ok _) := ‹_›
              have hat : RawVault.assetsTotal _ = .ok _ := ‹_›
              exact ⟨_, _, hr, hcd, Or.inr (Or.inr ⟨_, _, hin, hadj, hat, ‹_›⟩)⟩
            · exact absurd (by decide) hne))

lemma Vault.deposit_under_maximum_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0)
    (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLIMIT_EXCEEDED)) :
    ∃ (roundedAmount : STAmount) (amounts : VaultAmounts),
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) ∧
      (9 * (10 : ℚ) ^ (15 + v.baseExponent) < v.toExact.assetsTotal + amounts.assets.toRat ∨
        ∃ m ∈ v.assetsMaximum, m.toRat < v.toExact.assetsTotal + amounts.assets.toRat) := by
  obtain ⟨ra, amounts, hra, hcd, hcase⟩ := Vault.deposit_limit_reduces v amountDeposit isDonation t hpos hok
  refine ⟨ra, amounts, hra, hcd, ?_⟩
  have hmax := Vault.maxValue_fits_of_canonical v amountDeposit hc hty
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hra
  obtain ⟨hac, -, hann⟩ := computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcd
  have hexact : v.toExact.assetsTotal = v.assetsAvailable.toRat := by
    show v.assetsAvailable.toRat + v.assetsDeployed.toRat = _
    rw [hz.assetsDeployed, Number.toRat_zero, add_zero]
  rw [hexact]
  rcases hcase with hin | hadj | ⟨raw, at', hin, hadj, hat', hgt⟩
  · exact Or.inl (Vault.checkOpenLimit_limit v hz amounts.assets hac hann hin)
  · exact absurd hadj (Vault.adjustAssetsAndShares_not_limit v _ _)
  right
  -- the charge is whole base units, so the inflow check leaves the new cash exact
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hunits : ∃ j : ℕ, amounts.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, _, -, -, hs2a, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcd
      obtain ⟨hfa, hfty⟩ := sharesToAssetsDeposit_form v _ _ hmax hs2a
      exact clampToSumExponent_units _ _ _ _ hfa (by omega) (by omega)
        (fun hi => le_of_eq (hbint (by rw [← hfty]; exact hi))) hcl
    · obtain ⟨_, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcd
      exact clampToSumExponent_units _ _ _ _ hra1 (by omega) (by omega)
        (fun hi => le_of_eq (hbint (by rw [← hra2]; exact hi))) hcl
  obtain ⟨j, hj⟩ := hunits
  obtain ⟨k, hk, hkv⟩ := Vault.checkOpenLimit_openZone v hz _ hac j hj hin
  obtain ⟨haav, -⟩ :=
    Vault.adjustAssetsAndShares_units v _ _ raw k hz hac ⟨j, by rw [hj]; push_cast; rfl⟩ hk hkv hadj
  obtain ⟨aa', st', hfr⟩ := Vault.adjustAssetsAndShares_frame v _ _ raw hadj
  obtain ⟨_, _, _, aa'', _, _, _, _, _, haa, hraw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  -- nothing is deployed, so the new total is the new cash
  have hAD : raw.assetsDeployed = Number.zero := by rw [hfr]; exact hz.assetsDeployed
  have hat : raw.assetsTotal = .ok raw.assetsAvailable := by
    unfold RawVault.assetsTotal; rw [hAD]; exact Number.operator_add_zero_right _ _
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hatn : raw.assetsAvailable.isNormalized := by
    rw [hraw]; exact STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  cases hm : v.assetsMaximum with
  | none =>
    rw [hm, Option.getD_none, show Number.zero.operator_ne Number.zero = false by decide, Bool.false_and] at hgt
    exact absurd hgt (by decide)
  | some m =>
    rw [hm] at hgt
    simp only [Option.getD_some, Bool.and_eq_true] at hgt
    have hmem : m ∈ v.assetsMaximum := by rw [hm]; exact Option.mem_some_self m
    refine ⟨m, Option.mem_some_self m, ?_⟩
    have hlt := (operator_gt_iff _ _ hatn (v.wf.assetsMaximum_norm m hmem)).mp hgt.2
    rw [haav, ← hkv] at hlt
    exact hlt

end XRPL.Model.SingleAssetVault
