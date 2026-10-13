import XRPL.Properties.Vault.Proofs.Roundtrip.IntCert
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard

/-! # Integer sums past the int64 cusp

Two non-negative `Number`s whose exact sum is an integer above `maxRep` add to at most
`maxRep` only when the sum is `maxRep + 1`: `maxRep + 2` rounds up to `maxRepUp`. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma push6_round (g : Guard) : (g.push 6).round .to_nearest = 1 := by
  have hd := toNat_push_digits g 6
  have h6 : (6 : UInt64).toNat % 16 = 6 := by decide
  rw [h6] at hd
  have hgt : (g.push 6).digits_ > 0x5000_0000_0000_0000 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hd]
    have : (0x5000_0000_0000_0000 : UInt64).toNat = 5 * 2 ^ 60 := by decide
    rw [this]; omega
  have hne : ¬ (g.push 6).empty := by
    intro he
    have h0 : (g.push 6).digits_ = 0 := by
      unfold Guard.empty Guard.unrecoverable at he
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      exact he.1
    rw [h0] at hgt; exact absurd hgt (by decide)
  rw [round_to_nearest_def hne, if_pos hgt]

lemma cusp809 (g : Guard) (ze : Int) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp false 9223372036854775809 ze largeRange.min largeRange.max .to_nearest loc
      = .ok res)
    (hres : res.mantissa_ ≠ 0) :
    (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ = 9223372036854775810 * 10 ^ ze := by
  have hpo : g.pushOverflow 9223372036854775809 .to_nearest = g.push 6 := by
    unfold Guard.pushOverflow
    rw [if_pos (by decide)]
    simp only [show ¬ ((9223372036854775809 : UInt64) % 10 < 9) by decide, if_false,
      show ((9223372036854775809 : UInt64) == maxRep) = false by decide]
    rfl
  unfold Guard.doRoundUp at hok
  rw [hpo] at hok
  dsimp only at hok
  rw [push6_round] at hok
  simp only [beq_self_eq_true, Bool.true_or, if_true] at hok
  rw [if_neg (show ¬ ((9223372036854775809 : UInt64) < largeRange.max ∧
      (9223372036854775809 : UInt64) < maxRep) by decide),
    if_pos (show maxRep < (9223372036854775809 : UInt64) ∧
      (9223372036854775809 : UInt64) < maxRepUp by decide)] at hok
  unfold Guard.bringIntoRange at hok
  rw [if_neg (show ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) by decide)] at hok
  dsimp only at hok
  by_cases hu : ze < minExponent ∨ (maxRepUp : UInt64) = 0
  · simp only [if_pos hu] at hok
    have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
    simp only [hzexp, if_false] at hok
    exact absurd (by rw [← Except.ok.inj hok]) hres
  · simp only [if_neg hu] at hok
    by_cases ho : ze > maxExponent
    · simp only [if_pos ho] at hok; exact absurd hok (by simp)
    · simp only [if_neg ho] at hok
      obtain rfl := Except.ok.inj hok
      show ((maxRepUp : UInt64).toNat : ℚ) * 10 ^ ze = _
      rw [show (maxRepUp : UInt64).toNat = 9223372036854775810 by decide]; norm_num

lemma add_cusp (x y A : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hok : Number.operator_add x y .to_nearest = .ok A)
    (hint : ∃ n : ℤ, x.toRat + y.toRat = n) (hbig : 9223372036854775807 < x.toRat + y.toRat)
    (hA : A.toRat ≤ 9223372036854775807) : x.toRat + y.toRat ≤ 9223372036854775808 := by
  have hnotz : ¬ x.operator_eq y.operator_neg = true := by
    intro hcon
    have hnegy : y.operator_neg = { y with negative_ := !y.negative_ } := by
      unfold Number.operator_neg
      rw [if_neg (by simpa using hym)]
    unfold Number.operator_eq at hcon
    rw [hnegy] at hcon
    simp only [Bool.and_eq_true, beq_iff_eq] at hcon
    have := hcon.1.1
    rw [hxneg, hyneg] at this
    exact Bool.noConfusion this
  obtain ⟨zm, ze', f, g, res, hzlo, hzhi, hf0, hf1, hfl, hval, hrup, habs, hresm, hrep, hsign,
      -, -, -⟩ :=
    operator_add_algorithmic_facts_same_sign_to_nearest x y A hx hy hxm hym (by rw [hxneg, hyneg])
      hnotz hok
  set v := x.toRat + y.toRat with hvdef
  have hv0 : 0 < v := lt_trans (by norm_num) hbig
  rw [abs_of_pos hv0] at hval
  have hA0 : 0 ≤ A.toRat := Number.toRat_nonneg_of_nonnegative A (hsign.trans hxneg)
  rw [abs_of_nonneg hA0] at habs
  have hzlo' : (922337203685477580 : ℚ) ≤ zm.toNat := by exact_mod_cast hzlo
  have hzhi' : (zm.toNat : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hzhi
  -- a sum from `maxRepUp` on packs to at least `maxRepUp`
  have hv810 : v < 9223372036854775810 := by
    by_contra h; push Not at h
    have hN : (⟨false, 9223372036854775810, 0⟩ : Number).isNormalized := by decide
    have hNv : (⟨false, 9223372036854775810, 0⟩ : Number).toRat = 9223372036854775810 := by
      rw [Number.toRat_of_nonneg _ rfl]
      rw [show (9223372036854775810 : UInt64).toNat = 9223372036854775810 by decide]; norm_num
    have := Number.RoundsToRepresentable.ge_of_ge_normalized A v
      (operator_add_rounded_to_nearest x y A hx hy hok) _ hN (by rw [hNv]; exact h)
    rw [hNv] at this; linarith
  have hu0 : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  rcases (show ze' ≤ -1 ∨ ze' = 0 ∨ 1 ≤ ze' by omega) with hk | hk | hk
  · exfalso
    have : (10 : ℚ) ^ ze' ≤ 1 / 10 := by
      have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hk
      norm_num at this ⊢; exact this
    have := mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ zm.toNat + f by positivity)
    linarith
  · subst hk
    rw [zpow_zero, mul_one] at hval
    obtain ⟨n, hn⟩ := hint
    have hf : f = 0 := by
      have h1 : f = (n : ℚ) - zm.toNat := by rw [← hn, hvdef] at *; linarith
      obtain ⟨k, hk⟩ : ∃ k : ℤ, f = k := ⟨n - zm.toNat, by rw [h1]; push_cast; ring⟩
      rw [hk] at hf0 hf1 ⊢
      have : (0 : ℤ) ≤ k := by exact_mod_cast hf0
      have : k < 1 := by exact_mod_cast hf1
      have : k = 0 := by omega
      rw [this]; simp
    rw [hf, add_zero] at hval
    by_contra hgt; push Not at hgt
    have hz809 : zm = 9223372036854775809 := by
      have h1 : (9223372036854775808 : ℚ) < zm.toNat := by linarith
      have h2 : (zm.toNat : ℚ) < 9223372036854775810 := by linarith
      have h1' : 9223372036854775808 < zm.toNat := by exact_mod_cast h1
      have h2' : zm.toNat < 9223372036854775810 := by exact_mod_cast h2
      have : zm.toNat = 9223372036854775809 := by omega
      exact UInt64.toNat_inj.mp (by rw [this]; decide)
    subst hz809
    have := cusp809 g 0 .overflow res hrup hresm
    rw [← habs, zpow_zero, mul_one] at this
    linarith
  · exfalso
    have h10 : (10 : ℚ) ≤ 10 ^ ze' := by
      have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hk
      simpa using this
    have hzm : zm.toNat = 922337203685477580 := by
      have : (zm.toNat : ℚ) * 10 < 922337203685477581 * 10 := by nlinarith
      have : zm.toNat < 922337203685477581 := by exact_mod_cast (by linarith : (zm.toNat : ℚ) < 922337203685477581)
      omega
    have hf8 := hfl hzm
    have hr1 := represents_f_gt_half hrep (by linarith)
    have hv' := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' (Or.inl hr1)
      (by rw [hzm]; decide) .overflow res hrup hresm
    rw [hzm] at hv'
    rw [← habs] at hv'
    push_cast at hv'
    nlinarith

/-- An integer point `n ∈ [0, maxRep]` is a normalized `Number`. -/
lemma int_point (n : ℤ) (h0 : 0 ≤ n) (h1 : n ≤ 9223372036854775807) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = n := by
  rcases lt_or_eq_of_le h0 with hp | rfl
  · obtain ⟨w, hw, -, hv⟩ := Number.exists_normalized_of_pos_nat n.toNat (by omega) (by omega)
    refine ⟨w, hw, ?_⟩
    rw [hv]
    have : ((n.toNat : ℤ) : ℚ) = (n : ℚ) := by rw [Int.toNat_of_nonneg h0]
    exact_mod_cast this
  · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero]; simp⟩

/-- The rounded sum of a positive total and a non-negative integer charge, under the int64
cap, is at most one unit above the exact sum, at most three below, and at most one below
unless the charge is within `10¹⁸` of the cap. -/
lemma add_err (T cN A : Number) (hT : T.isNormalized) (hT0 : 0 < T.toRat) (hcN : cN.isNormalized)
    (c : ℤ) (hcv : cN.toRat = c) (hc0 : 0 ≤ c)
    (hok : Number.operator_add T cN .to_nearest = .ok A) (hcap : A.toRat ≤ 9223372036854775807) :
    A.toRat - (T.toRat + c) ≤ 1 ∧ -3 ≤ A.toRat - (T.toRat + c) ∧
    (-1 ≤ A.toRat - (T.toRat + c) ∨ 9223372036854775807 - 10 ^ 18 < (c : ℚ)) := by
  have hrr := operator_add_rounded_to_nearest T cN A hT hcN hok
  rw [hcv] at hrr
  set v := T.toRat + c with hvdef
  have hv0 : 0 < v := by have : (0 : ℚ) ≤ c := by exact_mod_cast hc0
                         linarith
  have hA0 := Number.RoundsToRepresentable.nonneg_of_nonneg A v hrr hv0.le
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊v⌋ := ⟨_, rfl⟩
  have hn1 : (n : ℚ) ≤ v := by rw [hn]; exact Int.floor_le v
  have hn2 : v < n + 1 := by rw [hn]; exact Int.lt_floor_add_one v
  have hn0 : 0 ≤ n := by rw [hn]; exact Int.floor_nonneg.mpr hv0.le
  have hmx : (⟨false, 9223372036854775807, 0⟩ : Number).isNormalized := by decide
  have hmxv : (⟨false, 9223372036854775807, 0⟩ : Number).toRat = 9223372036854775807 := by
    rw [Number.toRat_of_nonneg _ rfl]
    rw [show (9223372036854775807 : UInt64).toNat = 9223372036854775807 by decide]; norm_num
  -- above: one unit
  have hup : A.toRat ≤ v + 1 := by
    by_cases hnM : n + 1 ≤ 9223372036854775807
    · obtain ⟨w, hw, hwv⟩ := int_point (n + 1) (by omega) hnM
      have := Number.RoundsToRepresentable.le_of_le_normalized A v hrr w hw (by rw [hwv]; push_cast; linarith)
      rw [hwv] at this; push_cast at this; linarith
    · have : (9223372036854775807 : ℚ) ≤ n := by
        have : (9223372036854775807 : ℤ) ≤ n := by omega
        exact_mod_cast this
      linarith
  -- below `maxRep + 1`: one unit
  have hlo : n ≤ 9223372036854775807 → v - 1 ≤ A.toRat := fun hnM => by
    obtain ⟨w, hw, hwv⟩ := int_point n hn0 hnM
    have := Number.RoundsToRepresentable.ge_of_ge_normalized A v hrr w hw (by rw [hwv]; exact hn1)
    rw [hwv] at this; linarith
  by_cases hnM : n ≤ 9223372036854775807
  · have := hlo hnM
    exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
  push Not at hnM
  have hvM : (9223372036854775808 : ℚ) ≤ v := by
    have : (9223372036854775808 : ℤ) ≤ n := by omega
    have : (9223372036854775808 : ℚ) ≤ n := by exact_mod_cast this
    linarith
  have hAM : 9223372036854775807 ≤ A.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized A v hrr _ hmx (by rw [hmxv]; linarith)
    rwa [hmxv] at this
  have hv810 : v < 9223372036854775810 := by
    by_contra h; push Not at h
    have hN : (⟨false, 9223372036854775810, 0⟩ : Number).isNormalized := by decide
    have hNv : (⟨false, 9223372036854775810, 0⟩ : Number).toRat = 9223372036854775810 := by
      rw [Number.toRat_of_nonneg _ rfl]
      rw [show (9223372036854775810 : UInt64).toNat = 9223372036854775810 by decide]; norm_num
    have := Number.RoundsToRepresentable.ge_of_ge_normalized A v hrr _ hN (by rw [hNv]; exact h)
    rw [hNv] at this; linarith
  refine ⟨by linarith, by linarith, ?_⟩
  by_cases hTi : ∃ k : ℤ, T.toRat = k
  · left
    obtain ⟨k, hk⟩ := hTi
    have hcm : cN.mantissa_ ≠ 0 := by
      intro hm
      have hc0' : c = 0 := by
        have := Number.toRat_eq_zero_of_mantissa_zero cN hm
        rw [hcv] at this; exact_mod_cast this
      have := Number.RoundsToRepresentable.eq_of_representable A v hrr T hT (by rw [hvdef, hc0']; simp)
      linarith
    have hTm : T.mantissa_ ≠ 0 := fun hm => by
      rw [Number.toRat_eq_zero_of_mantissa_zero T hm] at hT0; exact lt_irrefl _ hT0
    have hcpos : (0 : ℚ) < cN.toRat := by
      rw [hcv]; rcases lt_or_eq_of_le hc0 with h | h
      · exact_mod_cast h
      · exfalso; subst h; rw [Int.cast_zero] at hcv
        exact hcm (by
          by_contra hne
          exact Number.toRat_ne_zero_of_mantissa_ne_zero cN hne hcv)
    have := add_cusp T cN A hT hcN hTm hcm (Number.negative_false_of_pos T hT0)
      (Number.negative_false_of_pos cN hcpos) hok ⟨k + c, by rw [hcv, hk]; push_cast; ring⟩
      (by rw [hcv]; linarith) hcap
    rw [hcv] at this
    linarith
  · right
    have hT81 : T.toRat < 922337203685477581 := by
      by_contra h; push Not at h
      exact hTi (num_int_of_ge T hT h)
    linarith

end XRPL.Model.SingleAssetVault.RtT
