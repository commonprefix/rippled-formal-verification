import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.WithdrawMono.Clamp
import XRPL.Properties.Vault.Proofs.WithdrawMono.Grid
import XRPL.Properties.Vault.Proofs.WithdrawMono.Exponent
import XRPL.Properties.Vault.Proofs.WithdrawMono.Price
import XRPL.Properties.Vault.Proofs.WithdrawMono.Zero
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Clamp

/-! # The clamped payout sits on a grid close to the post-subtraction total -/

namespace XRPL.Model.SingleAssetVault.Exact

open XRPL.Model.Protocol

/-- The grid-and-proximity conclusion shared by both clamp branches. -/
def GridNear (T : Number) (a : ℚ) : Prop :=
  ∃ s j : ℤ, -100 ≤ s ∧ s ≤ 80 ∧ a = (j : ℚ) * 10 ^ s ∧
    (s ≤ T.exponent_ → T.toRat - a < 2 ^ 63 * 10 ^ s)

private lemma pow_normalized (k : ℕ) (s : ℤ) (hk : 1 ≤ k) (hk' : k < 2 ^ 63)
    (hlo : -100 ≤ s) (hhi : s ≤ 80) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (k : ℚ) * 10 ^ s :=
  exists_normalized_grid k s hk hk' (by unfold minExponent; omega) (by unfold maxExponent; omega)

/-- A `to_nearest` rounding below a representable bound bounds the exact value. -/
private lemma lt_of_rounds (sm : Number) (z b : ℚ) (hr : Number.RoundsToRepresentable sm z .to_nearest)
    (w : Number) (hw : w.isNormalized) (hwv : w.toRat = b) (hsm : sm.toRat < b) : z < b := by
  by_contra hc
  rw [not_lt] at hc
  have := Number.RoundsToRepresentable.ge_of_ge_normalized sm z hr w hw (by rw [hwv]; exact hc)
  rw [hwv] at this
  linarith

/-- A normalized nonnegative `Number` is below `10^19` steps of its exponent. -/
private lemma lt_pow19 (n : Number) (hn : n.isNormalized) (hn0 : 0 ≤ n.toRat) (hm : n.mantissa_ ≠ 0) :
    n.toRat < (10 : ℚ) ^ (n.exponent_ + 19) := by
  rw [Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn hn0),
    zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ n.exponent_)]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast (hn.mantissaBounds_nat hm).2)
    (zpow_pos (by norm_num) _)

/-- `roundToExponent` leaves a canonical amount whose exponent is at least the scale. -/
private lemma rte_id (p a : STAmount) (s : ℤ) (hc : p.IOUCanonical) (hs : s ≤ p.mOffset)
    (hok : STAmount.roundToExponent p s .downward = .ok a) : a = p := by
  have hint : ¬ p.integral = true := by
    unfold STAmount.integral; rw [hc.is_fractional]; decide
  have hnz : ¬ p.isZero = true := by
    unfold STAmount.isZero
    intro h
    have h0 : p.mValue = 0 := beq_iff_eq.mp h
    have := hc.mant_lo; rw [h0] at this; simp at this
  unfold STAmount.roundToExponent at hok
  have hs2 : p.exponent ≥ s := hs
  simp only [hint, hnz, hs2, ↓reduceIte] at hok
  exact (Except.ok.inj hok).symm

/-- **Fractional clamp.** A positive canonical payout `p ≤ T` clamps to `a ≤ p` on a
grid `10^s` with `T - a` below `2^63` steps. -/
lemma clamp_grid_frac (T : Number) (p a : STAmount) (hT : T.isNormalized)
    (hc : p.IOUCanonical) (hpos : 0 < p.toRat) (hpT : p.toRat ≤ T.toRat)
    (ha : a.mValue ≠ 0)
    (hcl : clampToSumExponent T p.operator_neg = .ok a) :
    0 ≤ a.toRat ∧ a.toRat ≤ p.toRat ∧ GridNear T a.toRat := by
  obtain ⟨dn, sm, pe, hdn, hsum, hpe, hrte⟩ := WdMono.clamp_neg_frac T p a hc hpos hcl
  have hpz : p.mValue ≠ 0 := by
    intro h; have := hc.mant_lo; rw [h] at this; simp at this
  have hnc : p.operator_neg.IOUCanonical := by
    rcases (STAmount.operator_neg_fczr p ⟨hc.is_fractional, Or.inl hc⟩).2 with h | h
    · exact h
    · exfalso; apply hpz
      have hmv : p.operator_neg.mValue = p.mValue := by
        unfold STAmount.operator_neg; split <;> rfl
      rw [← hmv]; exact h
  obtain ⟨dn', hdn', hdnv, hdnn⟩ := STAmount.toNumber_iou_exact _ .to_nearest hnc
  obtain rfl : dn' = dn := Except.ok.inj (hdn'.symm.trans hdn)
  rw [STAmount.operator_neg_toRat] at hdnv
  have hrs := operator_add_rounded_to_nearest T dn' sm hT hdnn hsum
  rw [hdnv] at hrs
  have hz0 : (0 : ℚ) ≤ T.toRat + -p.toRat := by linarith
  have hsm0 := Number.RoundsToRepresentable.nonneg_of_nonneg sm _ hrs hz0
  obtain ⟨st, hst, hste⟩ : ∃ st, STAmount.ofNumber .fractional sm .to_nearest = .ok st ∧
      st.exponent = pe := by
    unfold numberExponent at hpe
    obtain ⟨st, h1, h2⟩ := bind_ok_peel _ _ _ hpe
    exact ⟨st, h1, Except.ok.inj h2⟩
  have hp96 := hc.exp_lo
  have hp80 := hc.exp_hi
  -- the underflow branch: the payout is unchanged and `T - p` is below `10^-81`
  have hunder : T.toRat + -p.toRat < (10 : ℚ) ^ (-81 : ℤ) → pe = -100 →
      0 ≤ a.toRat ∧ a.toRat ≤ p.toRat ∧ GridNear T a.toRat := by
    intro hsmall hpe100
    obtain rfl : a = p := rte_id p a pe hc (by omega) hrte
    obtain ⟨z, hz⟩ := STAmount.exists_int_grid a
    refine ⟨hpos.le, le_rfl, a.mOffset, z, by omega, hp80, hz, fun _ => ?_⟩
    have h1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 2 ^ 63 * 10 ^ a.mOffset := by
      have : (10 : ℚ) ^ (-81 : ℤ) = 10 ^ 15 * 10 ^ (-96 : ℤ) := by norm_num
      rw [this]
      have h2 : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ a.mOffset := zpow_le_zpow_right₀ (by norm_num) hp96
      have h3 : (0 : ℚ) ≤ 10 ^ (-96 : ℤ) := by positivity
      nlinarith
    linarith
  have hw81 : ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (-81 : ℤ) := by
    obtain ⟨w, hw, hwv⟩ := pow_normalized 1 (-81) le_rfl (by norm_num) (by norm_num) (by norm_num)
    exact ⟨w, hw, by rw [hwv]; norm_num⟩
  obtain ⟨w81, hw81n, hw81v⟩ := hw81
  by_cases hsmz : sm.mantissa_ = 0
  · have hsm00 : sm.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero sm hsmz
    have hstz : st.mValue = 0 := WdMono.ofNumber_mant0 _ sm _ st hsmz hst
    have hpe' := (STAmount.ofNumber_frac_exp_range .fractional sm .to_nearest st rfl hst).1 hstz
    exact hunder (lt_of_rounds sm _ _ hrs w81 hw81n hw81v (by rw [hsm00]; positivity))
      (by rw [← hste]; exact hpe')
  have hsmn : sm.isNormalized := operator_add_isNormalized T dn' sm .to_nearest hT hdnn hsum hsmz
  obtain ⟨ex, hex, hcase⟩ := WdMono.ofNumber_frac_tn_exp sm st hsmn
    (Number.negative_false_of_nonneg sm hsmn hsm0) hsmz hst
  have hex3 : sm.exponent_ + 3 ≤ ex := by rcases hex with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hsm19 := lt_pow19 sm hsmn hsm0 hsmz
  rcases hcase with ⟨hexl, -, hst100⟩ | ⟨hexl, hstnz, hstex⟩
  · refine hunder (lt_of_rounds sm _ _ hrs w81 hw81n hw81v ?_) (by rw [← hste, hst100])
    calc sm.toRat < (10 : ℚ) ^ (sm.exponent_ + 19) := hsm19
      _ ≤ 10 ^ (-81 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  · have hpeq : pe = ex := by rw [← hste, hstex]
    subst hpeq
    have hpe80 : pe ≤ 80 := WdMono.pe_le sm pe hpe
    obtain ⟨w16, hw16n, hw16v⟩ := pow_normalized (10 ^ 16) pe (by norm_num) (by norm_num)
      (by omega) hpe80
    have hnearp : T.toRat + -p.toRat < (10 : ℚ) ^ 16 * 10 ^ pe := by
      refine lt_of_rounds sm _ _ hrs w16 hw16n (by rw [hw16v]; push_cast; ring) ?_
      calc sm.toRat < (10 : ℚ) ^ (sm.exponent_ + 19) := hsm19
        _ ≤ 10 ^ (pe + 16) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 10 ^ 16 * 10 ^ pe := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm]; norm_num
    obtain ⟨ha0, hap, hgrid, hmax⟩ := WdMono.rte_facts p a pe hc hpos hpe80 hrte
    obtain ⟨j, hj⟩ := hgrid pe le_rfl
    have hpe0 : (0 : ℚ) < 10 ^ pe := zpow_pos (by norm_num) _
    have hfl := hmax ha ⌊p.toRat / 10 ^ pe⌋ (by
      have := Int.floor_le (p.toRat / 10 ^ pe)
      calc (⌊p.toRat / 10 ^ pe⌋ : ℚ) * 10 ^ pe ≤ p.toRat / 10 ^ pe * 10 ^ pe :=
            mul_le_mul_of_nonneg_right this hpe0.le
        _ = p.toRat := by field_simp)
    have hgap : p.toRat - a.toRat < 10 ^ pe := by
      have := Int.lt_floor_add_one (p.toRat / 10 ^ pe)
      have h2 : p.toRat < ((⌊p.toRat / 10 ^ pe⌋ : ℚ) + 1) * 10 ^ pe := by
        rwa [div_lt_iff₀ hpe0] at this
      nlinarith
    refine ⟨ha0, hap, pe, j, by omega, hpe80, hj, fun _ => ?_⟩
    nlinarith

/-- **Integral clamp.** A nonnegative offset-`0` payout passes through unchanged, on
the unit grid. -/
lemma clamp_grid_int (T : Number) (p a : STAmount) (hint : p.integral = true)
    (hoff : p.mOffset = 0) (hp0 : 0 ≤ p.toRat) (hTfit : T.toRat < 2 ^ 63)
    (hcl : clampToSumExponent T p.operator_neg = .ok a) :
    a.toRat = p.toRat ∧ GridNear T a.toRat := by
  have hap := WdMono.clampToSumExponent_neg_int_toRat T p a hint hp0 hcl
  obtain ⟨z, hz⟩ := STAmount.exists_int_grid p
  refine ⟨hap, 0, z, by norm_num, by norm_num, ?_, fun _ => ?_⟩
  · rw [hap, hz]; show (z : ℚ) * 10 ^ p.mOffset = _; rw [hoff]
  · rw [hap]; norm_num; linarith

end XRPL.Model.SingleAssetVault.Exact
