import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Compare.Common.Proofs

/-! # Amounts on decimal grids

Two amounts on the grids `10 ^ a` and `10 ^ b` that differ, differ by at least the finer step. So
flooring a canonical amount onto a coarser grid either keeps it or lowers it by at least one step
of its own grid, and by less than one step of the coarser grid. -/

namespace XRPL.Model.Protocol

/-- Two different values on the grids `10 ^ a` and `10 ^ b` differ by at least the finer step. -/
lemma grid_diff_ge (x y : ℚ) (a b zx zy : ℤ) (hx : x = (zx : ℚ) * 10 ^ a) (hy : y = (zy : ℚ) * 10 ^ b)
    (hlt : y < x) : (10 : ℚ) ^ min a b ≤ x - y := by
  have hstep : ∀ c : ℤ, min a b ≤ c → (10 : ℚ) ^ c = 10 ^ (c - min a b).toNat * 10 ^ min a b := by
    intro c hc
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ (by norm_num), sub_add_cancel]
  set n : ℤ := zx * 10 ^ (a - min a b).toNat - zy * 10 ^ (b - min a b).toNat
  have hn : x - y = (n : ℚ) * 10 ^ min a b := by
    rw [hx, hy, hstep a (min_le_left a b), hstep b (min_le_right a b)]
    push_cast [n]
    ring
  have hp : (0 : ℚ) < 10 ^ min a b := zpow_pos (by norm_num) _
  have hn1 : 1 ≤ n := by
    have h : (0 : ℚ) < n := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonpos_of_nonneg h hp.le
      linarith
    exact_mod_cast h
  rw [hn]
  have : (1 : ℚ) ≤ n := by exact_mod_cast hn1
  nlinarith

/-- A smaller positive canonical amount has the smaller or equal exponent. -/
lemma STAmount.IOUCanonical.exponent_le (a b : STAmount) (ha : a.IOUCanonical) (hb : b.IOUCanonical)
    (hpos : 0 < a.toRat) (hle : a.toRat ≤ b.toRat) : a.exponent ≤ b.exponent := by
  obtain ⟨ha1, -⟩ := STAmount.IOUCanonical.toRat_bounds a ha hpos
  obtain ⟨-, hb2⟩ := STAmount.IOUCanonical.toRat_bounds b hb (by linarith)
  by_contra hlt
  push Not at hlt
  have h1 : (10 : ℚ) ^ (b.exponent + 16) ≤ 10 ^ (a.exponent + 15) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hp : (0 : ℚ) < 10 ^ b.exponent := zpow_pos (by norm_num) _
  linarith

/-- Flooring a canonical amount onto a grid keeps it, or lowers it by at least one step of its
own grid and by at most one step of the coarser grid less one of its own. -/
lemma STAmount.IOUCanonical.floor_bounds (P R : STAmount) (e : ℤ) (hP : P.IOUCanonical)
    (hR : R.IOUCanonical) (hRpos : 0 < R.toRat)
    (hfl : R.toRat = (⌊P.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e) :
    R.toRat + 1 / 2 * (10 : ℚ) ^ P.exponent ≤ P.toRat + 1 / 2 * (10 : ℚ) ^ R.exponent ∧
    P.toRat - R.toRat + 1 / 2 * (10 : ℚ) ^ P.exponent ≤
      max (1 / 2 * (10 : ℚ) ^ R.exponent) ((10 : ℚ) ^ e - 1 / 2 * (10 : ℚ) ^ R.exponent) := by
  have he : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hRle : R.toRat ≤ P.toRat := by
    rw [hfl]
    calc (⌊P.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e ≤ P.toRat / 10 ^ e * 10 ^ e :=
          mul_le_mul_of_nonneg_right (Int.floor_le _) he.le
      _ = P.toRat := div_mul_cancel₀ _ he.ne'
  have hPpos : 0 < P.toRat := lt_of_lt_of_le hRpos hRle
  have hPlt : P.toRat < R.toRat + 10 ^ e := by
    have h := Int.lt_floor_add_one (P.toRat / 10 ^ e)
    rw [div_lt_iff₀ he] at h
    rw [hfl]; linarith
  -- the two amounts are whole numbers of steps of their own grids
  have hPneg : P.mIsNegative = false := by
    by_contra h
    have hv := STAmount.toRat_of_neg P (by simpa using h)
    have h0 : (0 : ℚ) ≤ P.mValue.toNat * 10 ^ P.mOffset := by positivity
    linarith
  have hPv : P.toRat = ((P.mValue.toNat : ℤ) : ℚ) * 10 ^ P.exponent := by
    rw [STAmount.toRat_of_nonneg P hPneg]; push_cast; rfl
  have hp : (0 : ℚ) < 10 ^ P.exponent := zpow_pos (by norm_num) _
  have hr : (0 : ℚ) < 10 ^ R.exponent := zpow_pos (by norm_num) _
  by_cases heq : R.toRat = P.toRat
  · -- the floor keeps the amount, so it is the same canonical amount
    have hRP : R = P := STAmount.eq_of_exactCanonical R P (Or.inl hR) (Or.inl hP)
      (by rw [hR.is_fractional, hP.is_fractional])
      (fun h0 => by rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hRpos; exact lt_irrefl _ hRpos) heq
    rw [hRP]
    exact ⟨le_refl _, by rw [sub_self, zero_add]; exact le_max_left _ _⟩
  have hlt : R.toRat < P.toRat := lt_of_le_of_ne hRle heq
  -- the floor lowers it by at least one step of its own grid, so that grid is the finer one
  have hgap := grid_diff_ge _ _ _ _ _ _ hPv hfl hlt
  have hpe : P.exponent < e := by
    by_contra h
    push Not at h
    rw [min_eq_right h] at hgap
    linarith
  rw [min_eq_left hpe.le] at hgap
  -- and by at most one step of the coarser grid less one of its own
  have hgap' := grid_diff_ge (R.toRat + 10 ^ e) P.toRat e P.exponent (⌊P.toRat / 10 ^ e⌋ + 1) _
    (by rw [hfl]; push_cast; ring) hPv hPlt
  rw [min_eq_right hpe.le] at hgap'
  have hRe : R.exponent ≤ P.exponent := STAmount.IOUCanonical.exponent_le R P hR hP hRpos hRle
  have hrp : (10 : ℚ) ^ R.exponent ≤ 10 ^ P.exponent := zpow_le_zpow_right₀ (by norm_num) hRe
  exact ⟨by linarith, le_trans (by linarith) (le_max_right _ _)⟩

end XRPL.Model.Protocol
