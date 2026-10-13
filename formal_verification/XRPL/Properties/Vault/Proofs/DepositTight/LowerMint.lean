import XRPL.Properties.Vault.Proofs.DepositTight.LowerExact
import XRPL.Properties.Vault.Proofs.DepositTight.Shares
import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Common.Reduction

/-! # The shortfall side of the deposit share count under the mint cap -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

lemma floor_ge_of_grid (q : ℚ) (k : ℤ) (j : ℕ) (d : ℤ) (hq : q * 10 ^ j = k)
    (hk : ∀ N : ℤ, k < N * 10 ^ j → k ≤ N * 10 ^ j - d) :
    q - 1 + d / 10 ^ j ≤ (⌊q⌋ : ℚ) := by
  have h10 : (0 : ℚ) < 10 ^ j := by positivity
  have hlt := Int.lt_floor_add_one q
  have hk1 : k < (⌊q⌋ + 1) * 10 ^ j := by
    have : (k : ℚ) < ((⌊q⌋ : ℚ) + 1) * 10 ^ j := by
      rw [← hq]; exact mul_lt_mul_of_pos_right hlt h10
    exact_mod_cast this
  have hk2 : (k : ℚ) ≤ ((⌊q⌋ : ℚ) + 1) * 10 ^ j - d := by exact_mod_cast hk _ hk1
  have key : (q - 1 + d / 10 ^ j) * 10 ^ j ≤ (⌊q⌋ : ℚ) * 10 ^ j := by
    have : (q - 1 + d / 10 ^ j) * 10 ^ j = q * 10 ^ j - 10 ^ j + d := by field_simp
    rw [this, hq]; linarith
  exact le_of_mul_le_mul_right key h10

/-- `assetsToSharesDeposit` packs its truncated quotient through `ofNumber .int64`. -/
lemma ofNumber_of_assetsToShares (v : Vault) (amount shares : STAmount)
    (hok : assetsToSharesDeposit v amount = .ok shares) :
    ∃ n : Number, STAmount.ofNumber .int64 n .to_nearest = .ok shares := by
  unfold assetsToSharesDeposit at hok
  split_ifs at hok
  · obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    exact ⟨_, by rw [hsh, show sh' = shares from Except.ok.inj hlast]⟩
  · obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    exact ⟨_, by rw [hsh, show sh' = shares from Except.ok.inj hlast]⟩

lemma grid_floor (q : ℚ) (k : ℕ) (E : ℤ) (d : ℤ) (hE : E ≤ 0) (hq : q = (k : ℚ) * 10 ^ E)
    (hk : ∀ N : ℤ, (k : ℤ) < N * 10 ^ (-E).toNat → (k : ℤ) ≤ N * 10 ^ (-E).toNat - d) :
    q - 1 + d * 10 ^ E ≤ (⌊q⌋ : ℚ) := by
  set j := (-E).toNat with hjd
  have hj : E = -(j : ℤ) := by omega
  have hpow : (10 : ℚ) ^ E = 1 / 10 ^ j := by
    rw [hj, zpow_neg, zpow_natCast, one_div]
  have hq10 : q * 10 ^ j = ((k : ℤ) : ℚ) := by
    rw [hq, hpow]; push_cast; field_simp
  have h := floor_ge_of_grid q k j d hq10 hk
  rw [hpow]
  calc q - 1 + d * (1 / 10 ^ j) = q - 1 + d / 10 ^ j := by ring
    _ ≤ _ := h

set_option maxHeartbeats 1600000 in
-- Long case analysis over the quotient's grid, in one declaration.
lemma shares_lower_mint (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false)
    (hmint : v.sharesTotal.toRat + shares.toRat ≤ 9223372036854775807) :
    v.idealSharesDeposit amount.toRat * (1 - 4879 / 10 ^ 22) - 1 < shares.toRat := by
  have hsh_le : shares.toRat ≤ 9223372036854775807 := by
    obtain ⟨n, hn⟩ := ofNumber_of_assetsToShares v amount shares hok
    have hfacts := STAmount.ofNumber_integral_facts .int64 n .to_nearest shares (by decide) hn
    have h1 := le_abs_self shares.toRat
    rw [STAmount.abs_toRat, hfacts.2.1, zpow_zero, mul_one] at h1
    have h2 : (shares.mValue.toNat : ℚ) ≤ 9223372036854775807 := by
      have := hfacts.2.2; rw [maxRep_val] at this; exact_mod_cast this
    linarith
  unfold assetsToSharesDeposit at hok
  have hmv : shares.mValue ≠ 0 :=
    ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    have h00 : amount.toRat = 0 := by
      rw [STAmount.toRat_signed, h0]
      simp
    exact absurd h00 (ne_of_gt hpos)
  have hnegam : amount.mIsNegative = false := STAmount.mIsNegative_false_of_pos amount hpos
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize (amount · 10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the ideal
    have hA0 : v.toExact.assetsTotal = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal hmz
    have hideal : v.idealSharesDeposit amount.toRat
        = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℕ) := by
      unfold RawVault.idealSharesDeposit
      rw [if_pos hA0]
    have hideal_pos : 0 < v.idealSharesDeposit amount.toRat := by
      rw [hideal]; positivity
    -- the normalize input denotes the ideal
    have hin : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat = v.idealSharesDeposit amount.toRat := by
      rw [Number.toRat_of_nonneg _ rfl, hideal, STAmount.toRat_of_nonneg amount hnegam]
      show (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ)) = _
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
      ring
    -- the nonzero chain
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    -- the normalize is `RoundsWithin` the ideal
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hexact : n1.toRat = v.idealSharesDeposit amount.toRat := by
      have hbnd : amount.mantissa.toNat ≤ maxRep.toNat ∧ (-96 : ℤ) ≤ amount.exponent ∧
          amount.exponent ≤ 80 := by
        by_cases hint : amount.integral = true
        · obtain ⟨hic, hmax⟩ := hc.1 hint
          refine ⟨le_trans hic.in_range hmax, ?_, ?_⟩
          · show (-96 : ℤ) ≤ amount.mOffset; rw [hic.offset_zero]; norm_num
          · show amount.mOffset ≤ 80; rw [hic.offset_zero]; norm_num
        · have hio := hc.2 (by simpa using hint)
          refine ⟨?_, hio.exp_lo, hio.exp_hi⟩
          have := hio.mant_hi
          rw [maxRep_val]
          show amount.mValue.toNat ≤ _
          omega
      have hsc := v.wf.scale_le
      obtain ⟨Mx, ex, hdn, hval, -⟩ := doNormalize_largeRange_exact false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ)) .to_nearest
        (by have : amount.mValue.toNat ≠ 0 := fun h => hamv (UInt64.toNat_inj.mp h)
            show 1 ≤ amount.mValue.toNat; omega)
        hbnd.1 (by have := hbnd.2.1; simp only [minExponent]; omega)
        (by have := hbnd.2.2; simp only [maxExponent]; omega)
      have hd : doNormalize false amount.mantissa (amount.exponent + (v.scale.toNat : ℤ))
          largeRange.min largeRange.max .to_nearest = .ok n1 := hn1cast
      rw [hdn] at hd
      rw [← (Except.ok.inj hd), Number.toRat_of_nonneg _ rfl, ← hin, Number.toRat_of_nonneg _ rfl]
      exact hval
    have hn1pos : 0 < n1.toRat := by rw [hexact]; exact hideal_pos
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest
        (show amount.mValue ≠ 0 from hamv) hn1cast hn1m
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    -- the int64 packing is exact
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    rw [hshval, hn2val, hexact]
    have hfl := Int.sub_one_lt_floor (v.idealSharesDeposit amount.toRat)
    nlinarith [hideal_pos]
  · -- nonempty vault: shares = ⌊(S·amount)/assetsTotal rounded⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨Q, hQ, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares :=
      Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    -- the divisor is `assetsTotal` exactly: there is no subtraction stage
    set navN := v.assetsTotal with hnavN_eq
    have hApos : 0 < v.toExact.assetsTotal := by
      rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
      · exact h
      · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
    have hnav_pos : 0 < v.depositNav := by
      unfold RawVault.depositNav; exact hApos
    have hS_pos : 0 < v.sharesTotal.toRat := by
      rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
      · exact h
      · exfalso
        have hz : v.toExact.sharesTotal = 0 := by
          show v.sharesTotal.toRat.num.toNat = 0
          rw [← h]
          rfl
        have := (v.exact.empty_shares hz).1
        exact absurd this.symm (ne_of_lt hApos)
    have hS_one : 1 ≤ v.sharesTotal.toRat := by
      have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
      have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
        rw [v.wf.sharesTotal_int]
        simp
      rw [hcast]
      exact_mod_cast hnum_pos
    have hSm : v.sharesTotal.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    have hanm : amountN.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hanval]; exact hpos.ne')
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hQm : Q.mantissa_ ≠ 0 := Number.truncate_source_ne_zero Q T hT hTm
    -- navN = assetsTotal exactly, so the pricing value equals depositNav with no rounding
    have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
    have hnavm : navN.mantissa_ ≠ 0 := hmz
    have hnavN_eqNav : navN.toRat = v.depositNav := by rw [hnavN_eq]; rfl
    have hnavbound : |navN.toRat - v.depositNav| ≤ v.depositNav * (555 / 10 ^ 21) := by
      rw [hnavN_eqNav, sub_self, abs_zero]
      exact mul_nonneg (le_of_lt hnav_pos) (by norm_num)
    have hnavN_pos : 0 < navN.toRat := by rw [hnavN_eqNav]; exact hnav_pos
    -- the product stage
    have hPm : P.mantissa_ ≠ 0 := by
      intro h0
      have hsmall := operator_mul_underflow_truth_small v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP h0
      have hcombo : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
          = (10 : ℚ) ^ (-32750 : ℤ) := by
        rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num [minExponent]
      rw [hcombo] at hsmall
      have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.sharesTotal.toRat * amountN.toRat| := by
        rw [abs_mul]
        have h1 : (1 : ℚ) ≤ |v.sharesTotal.toRat| := by
          rw [abs_of_pos hS_pos]; exact hS_one
        have h2 : (10 : ℚ) ^ (-81 : ℤ) ≤ |amountN.toRat| := by
          rw [hanval]
          exact STAmount.Canonical.abs_toRat_ge amount hc hamv
        nlinarith [abs_nonneg amountN.toRat]
      have hmono : (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      linarith
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSm hanm hP hPm
    have hPbound := operator_mul_rounds_to_nearest v.sharesTotal amountN P
      v.wf.sharesTotal_norm hannorm hP hPm
    set T0 : ℚ := v.sharesTotal.toRat * amount.toRat with hT0_def
    have hT0_pos : 0 < T0 := mul_pos hS_pos hpos
    have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
      have h1 : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7)) := hPbound
      rw [hanval, ← hT0_def, abs_of_pos hT0_pos] at h1
      exact h1
    -- the division stage
    have hQbound : |Q.toRat - P.toRat / navN.toRat|
        ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := by
      have h := operator_div_rounds_to_nearest_sharp P navN Q hPnorm hnavnorm hQ hQm
      unfold divSharpε at h
      exact h
    have hPpos : 0 < P.toRat := by
      have := abs_le.mp hPb
      have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
      nlinarith
    have hPN_pos : 0 < P.toRat / navN.toRat := div_pos hPpos hnavN_pos
    have hQpos : 0 < Q.toRat := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := hQbound
      rw [abs_of_pos hPN_pos] at h1
      have := abs_le.mp h1
      nlinarith
    have h3 : |Q.toRat * navN.toRat - P.toRat| ≤ P.toRat * (555 / 10 ^ 21) := by
      have h1 : |Q.toRat - P.toRat / navN.toRat|
          ≤ P.toRat / navN.toRat * (555 / 10 ^ 21) := by
        have h0 := hQbound
        have h0' : |Q.toRat - P.toRat / navN.toRat|
            ≤ |P.toRat / navN.toRat| * (555 / 10 ^ 21) := h0
        rw [abs_of_pos hPN_pos] at h0'
        exact h0'
      have h2 : |Q.toRat - P.toRat / navN.toRat| * navN.toRat
          = |Q.toRat * navN.toRat - P.toRat| := by
        have hNne : navN.toRat ≠ 0 := hnavN_pos.ne'
        rw [show Q.toRat * navN.toRat - P.toRat
          = (Q.toRat - P.toRat / navN.toRat) * navN.toRat from by field_simp]
        rw [abs_mul, abs_of_pos hnavN_pos]
      calc |Q.toRat * navN.toRat - P.toRat|
          = |Q.toRat - P.toRat / navN.toRat| * navN.toRat := h2.symm
        _ ≤ P.toRat / navN.toRat * (555 / 10 ^ 21) * navN.toRat := by nlinarith [hnavN_pos]
        _ = P.toRat * (555 / 10 ^ 21) := by field_simp
    have hideal : v.idealSharesDeposit amount.toRat = T0 / v.depositNav := by
      unfold RawVault.idealSharesDeposit
      rw [if_neg (ne_of_gt hApos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hT0_def]
    have hQnorm : Q.isNormalized :=
      operator_div_result_isNormalized P navN Q .to_nearest hPnorm hnavnorm hPm hnavm hQ hQm
    obtain ⟨hTval, hTnorm⟩ :=
      Number.truncate_floor Q T hQnorm (Number.negative_false_of_pos Q hQpos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    rw [hshval, hTval] at hsh_le hmint ⊢
    rw [hideal]
    set A := v.depositNav with hA_def
    set I := T0 / A with hI_def
    have hA_eq : navN.toRat = A := hnavN_eqNav
    have hIpos : 0 < I := div_pos hT0_pos hnav_pos
    have hV_eq : P.toRat / navN.toRat = P.toRat / A := by rw [hA_eq]
    have hPlo : T0 * (1 - 5 / (2 ^ 63 + 7)) ≤ P.toRat := by
      have := (abs_le.mp hPb).1; linarith
    have hPhi : P.toRat ≤ T0 * (1 + 5 / (2 ^ 63 + 7)) := by
      have := (abs_le.mp hPb).2; linarith
    have hVlo : I * (1 - 5 / (2 ^ 63 + 7)) ≤ P.toRat / A := by
      rw [hI_def, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hPlo (le_of_lt hnav_pos)
    have hVhi : P.toRat / A ≤ I * (1 + 5 / (2 ^ 63 + 7)) := by
      rw [hI_def, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hPhi (le_of_lt hnav_pos)
    have hlow := operator_div_lower_exact P navN Q hPnorm hnavnorm hQ hQm
    rw [abs_of_pos hPN_pos, abs_of_pos hQpos, hV_eq] at hlow
    set V := P.toRat / A with hV_def
    set q := Q.toRat with hq_def
    have hfl := Int.sub_one_lt_floor q
    have hS1 : (⌊q⌋ : ℚ) ≤ 9223372036854775806 := by linarith
    have hbad : ∀ X : ℚ, 9223372036854775807 ≤ X → X ≤ q → False := by
      intro X hX hXq; linarith
    have hclose : ∀ γ t B : ℚ, 0 < γ → V ≤ B * γ → V - ⌊q⌋ ≤ 1 - t * γ →
        B * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) < t * (1 - 5 / (2 ^ 63 + 7)) →
        I * (1 - 4879 / 10 ^ 22) - 1 < ⌊q⌋ := by
      intro γ t B hγ hVB hs hc
      have hIB : I * (1 - 5 / (2 ^ 63 + 7)) ≤ B * γ := le_trans hVlo hVB
      have h1 : I * (1 - 5 / (2 ^ 63 + 7)) * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22)
          ≤ B * γ * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) :=
        mul_le_mul_of_nonneg_right hIB (by norm_num)
      have h2 : B * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) * γ
          < t * (1 - 5 / (2 ^ 63 + 7)) * γ := mul_lt_mul_of_pos_right hc hγ
      have h3 : I * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) * (1 - 5 / (2 ^ 63 + 7))
          < t * γ * (1 - 5 / (2 ^ 63 + 7)) := by linarith
      have h4 : I * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) < t * γ :=
        lt_of_mul_lt_mul_right h3 (by norm_num)
      linarith
    have hp10 : ∀ E : ℤ, 1 ≤ E → (10 : ℚ) ≤ 10 ^ E := fun E hE => by
      calc (10 : ℚ) = 10 ^ (1 : ℤ) := by norm_num
        _ ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) hE
    have hp1 : ∀ E : ℤ, 0 ≤ E → (1 : ℚ) ≤ 10 ^ E := fun E hE => one_le_zpow₀ (by norm_num) hE
    rcases hlow with ⟨hVq, E, n, hn1, hn2, hn10, hqn⟩ | ⟨E, m, hm, hqm, hVlt, hcase⟩ |
        ⟨E, hqE, hVE⟩
    · by_cases hnr : n ≤ 9223372036854775807
      · have hE : E ≤ 0 := by
          by_contra hE
          have h := hp10 E (by omega)
          have hn' : (10 : ℚ) ^ 18 ≤ n := by exact_mod_cast hn1
          exact hbad (10 ^ 18 * 10) (by norm_num) (by rw [hqn]; nlinarith)
        have hfg := grid_floor q n E 1 hE hqn (fun N h => by omega)
        have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
        have hnq : (n : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hnr
        refine hclose (10 ^ E) 1 9223372036854775807 hγ ?_ ?_ (by norm_num)
        · rw [hqn] at hVq; nlinarith
        · push_cast at hfg; linarith
      · obtain ⟨n', rfl⟩ : ∃ n', n = 10 * n' := ⟨n / 10, by have := hn10 (by omega); omega⟩
        have hqn' : q = (n' : ℚ) * 10 ^ (E + 1) := by
          rw [hqn, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; push_cast; ring
        have hE : E + 1 ≤ 0 := by
          by_contra hE
          have h := hp1 E (by omega)
          have hn' : (9223372036854775808 : ℚ) ≤ ((10 * n' : ℕ) : ℚ) := by
            exact_mod_cast (by omega : 9223372036854775808 ≤ 10 * n')
          exact hbad ((10 * n' : ℕ) : ℚ) (by linarith)
            (by rw [hqn]; exact le_mul_of_one_le_right (by positivity) h)
        have hfg := grid_floor q n' (E + 1) 1 hE hqn' (fun N h => by omega)
        have hγ : (0 : ℚ) < 10 ^ (E + 1) := zpow_pos (by norm_num) _
        have hnq : (n' : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (by omega : n' ≤ 9223372036854775807)
        refine hclose (10 ^ (E + 1)) 1 9223372036854775807 hγ ?_ ?_ (by norm_num)
        · rw [hqn'] at hVq; nlinarith
        · push_cast at hfg; linarith
    · have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
      rcases hcase with ⟨hVh, hmr⟩ | rfl | rfl
      · have hE : E ≤ 0 := by
          by_contra hE
          have h := hp10 E (by omega)
          have hm' : (922337203685477581 : ℚ) ≤ m := by exact_mod_cast hm
          exact hbad (922337203685477581 * 10) (by norm_num) (by rw [hqm]; nlinarith)
        have hfg := grid_floor q m E 1 hE hqm (fun N h => by omega)
        have hmq : (m : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hmr
        refine hclose (10 ^ E) (1 / 2) (9223372036854775807 + 1 / 2) hγ ?_ ?_ (by norm_num)
        · nlinarith
        · push_cast at hfg; linarith
      · have hE : E ≤ -1 := by
          by_contra hE
          have h := hp1 E (by omega)
          exact hbad 9223372036854775807 (le_refl _) (by rw [hqm]; push_cast; nlinarith)
        have hfg := grid_floor q _ E 3 (by omega) hqm (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
        refine hclose (10 ^ E) 2 (9223372036854775807 + 1) hγ ?_ ?_ (by norm_num)
        · push_cast at hVlt; linarith
        · push_cast at hfg hVlt hqm; linarith
      · have hE : E ≤ -1 := by
          by_contra hE
          have h := hp1 E (by omega)
          exact hbad 9223372036854775810 (by norm_num) (by rw [hqm]; push_cast; nlinarith)
        have hfg := grid_floor q _ E 10 (by omega) hqm (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
        refine hclose (10 ^ E) 9 (9223372036854775810 + 1) hγ ?_ ?_ (by norm_num)
        · push_cast at hVlt; linarith
        · push_cast at hfg hVlt hqm; linarith
    · have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
      have hE : E ≤ -1 := by
        by_contra hE
        have h := hp1 E (by omega)
        exact hbad 9223372036854775807 (le_refl _) (by rw [hqE]; nlinarith)
      have hfg := grid_floor q 9223372036854775807 E 3 (by omega) (by rw [hqE]; push_cast; ring)
        (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
      refine hclose (10 ^ E) (3 / 2) (9223372036854775808 + 1 / 2) hγ hVE ?_ (by norm_num)
      push_cast at hfg; linarith

end XRPL.Model.SingleAssetVault.DepTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- **Sharp shortfall of the share count under the mint cap.** With the issued shares
fitting the share issuance's `maxRep` cap, they fall short of the ideal by less than one
share plus `4879·10⁻²²` relatively. -/
lemma Vault.deposit_sharesIssued_lower_mint_proof (v : Vault)
    (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hcanon : roundedAmount.Canonical) (hpos : 0 < roundedAmount.toRat)
    (_hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hposA : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hposA = .ok r) (herr : r.error = none)
    (hmint : v.sharesTotal.toRat + r.sharesIssued.toRat ≤ maxRep.toNat) :
    v.idealSharesDeposit roundedAmount.toRat * (1 - 4879 / 10 ^ 22) - 1
      < r.sharesIssued.toRat := by
  obtain ⟨hround0, -⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, _, _, _, _, hcd, _, _, _, _, _, _, _, hshr, _⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hposA hok herr
  have hameq : amount = roundedAmount := by
    rw [hround0] at hround
    exact (Except.ok.inj hround).symm
  obtain ⟨p, hcdp, -, -⟩ := hcd rfl
  obtain ⟨shares, hats, hsz, _, _, hsheq⟩ := computeDeposit_success_reduces v amount p sh hcdp
  rw [hameq] at hats
  have hshare_eq : r.sharesIssued = shares := by rw [hshr, hsheq]
  rw [hshare_eq] at hmint ⊢
  rw [maxRep_val] at hmint
  exact shares_lower_mint v roundedAmount shares hcanon hpos hats hsz (by exact_mod_cast hmint)

end XRPL.Model.SingleAssetVault
