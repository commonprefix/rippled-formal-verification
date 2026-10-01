import XRPL.Properties.Vault.Proofs.WithdrawTight

/-! # The fractional shortfall has no relative term

The charge and the payout sit on their own 16-digit grids, so the shortfall is a multiple
of the finer grid `g`, while twice the absolute terms is one too. A relative excess below
`g/2` is then absorbed: the payout is at least `0.4` of the charge, so the grids differ by
at most one decade, and `2·10⁻¹⁷` of the charge stays under half a step of either. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma grid_absorb (L A R g : ℚ) (hg : 0 < g) (hL : ∃ k : ℤ, L = k * g)
    (hA : ∃ h : ℤ, 2 * A = h * g) (hLA : L ≤ A + R) (hR : R < g / 2) : L ≤ A := by
  obtain ⟨k, rfl⟩ := hL
  obtain ⟨h, hh⟩ := hA
  have h1 : (2 * k : ℚ) * g < (h + 1) * g := by nlinarith
  have h2 : (2 * k : ℚ) < h + 1 := lt_of_mul_lt_mul_right h1 hg.le
  have h3 : 2 * k ≤ h := by
    have : 2 * k < h + 1 := by exact_mod_cast h2
    omega
  have h4 : (2 * k : ℚ) ≤ h := by exact_mod_cast h3
  nlinarith

lemma pow_split (e m : ℤ) (h : m ≤ e) : ∃ k : ℕ, (10 : ℚ) ^ e = ((10 ^ k : ℕ) : ℚ) * 10 ^ m := by
  refine ⟨(e - m).toNat, ?_⟩
  rw [show e = ((e - m).toNat : ℤ) + m by omega, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast
  congr 2
  omega

lemma iou_val (c : STAmount) (hc : c.IOUCanonical) (hc0 : 0 < c.toRat) :
    c.toRat = (c.mValue.toNat : ℚ) * 10 ^ c.exponent ∧ (10 : ℚ) ^ 15 ≤ c.mValue.toNat ∧
      (c.mValue.toNat : ℚ) < 10 ^ 16 := by
  refine ⟨STAmount.toRat_of_nonneg c (STAmount.mIsNegative_false_of_pos c hc0), ?_, ?_⟩
  · exact_mod_cast hc.mant_lo
  · exact_mod_cast hc.mant_hi

lemma frac_grid (c a : STAmount) (t : ℤ) (R : ℚ) (hc : c.IOUCanonical) (ha : a.IOUCanonical)
    (hc0 : 0 < c.toRat) (ha0 : 0 < a.toRat) (hR : R ≤ c.toRat * (2 * (1 / 10 ^ 17)))
    (ha4 : 2 * c.toRat ≤ 5 * a.toRat)
    (hloss : c.toRat - a.toRat ≤ R + 1 / 2 * (10 : ℚ) ^ c.exponent +
      max (1 / 2 * (10 : ℚ) ^ a.exponent) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ a.exponent)) :
    c.toRat - a.toRat ≤ 1 / 2 * (10 : ℚ) ^ c.exponent +
      max (1 / 2 * (10 : ℚ) ^ a.exponent) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ a.exponent) := by
  obtain ⟨hcv, hc1, hc2⟩ := iou_val c hc hc0
  obtain ⟨hav, ha1, ha2⟩ := iou_val a ha ha0
  set ec := c.exponent
  set ea := a.exponent
  have huc : (0 : ℚ) < 10 ^ ec := zpow_pos (by norm_num) _
  have hua : (0 : ℚ) < 10 ^ ea := zpow_pos (by norm_num) _
  -- the payout's grid is at most one decade finer
  have hea : ec - 1 ≤ ea := by
    by_contra h; push Not at h
    have h1 : (10 : ℚ) ^ ea * 100 ≤ 10 ^ ec := by
      rw [show ec = ea + 2 + (ec - ea - 2) by ring, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
      have : (1 : ℚ) ≤ 10 ^ (ec - ea - 2) := one_le_zpow₀ (by norm_num) (by omega)
      have : (10 : ℚ) ^ (2 : ℤ) = 100 := by norm_num
      nlinarith
    have h2 : a.toRat < 10 ^ 16 * 10 ^ ea := by rw [hav]; exact mul_lt_mul_of_pos_right ha2 hua
    have h3 : 10 ^ 15 * 10 ^ ec ≤ c.toRat := by rw [hcv]; exact mul_le_mul_of_nonneg_right hc1 huc.le
    nlinarith
  set m := min ec ea with hm
  have hg : (0 : ℚ) < 10 ^ m := zpow_pos (by norm_num) _
  obtain ⟨kc, hkc⟩ := pow_split ec m (min_le_left _ _)
  obtain ⟨ka, hka⟩ := pow_split ea m (min_le_right _ _)
  have hL : ∃ k : ℤ, c.toRat - a.toRat = k * 10 ^ m :=
    ⟨c.mValue.toNat * 10 ^ kc - a.mValue.toNat * 10 ^ ka, by rw [hcv, hav, hkc, hka]; push_cast; ring⟩
  have hA : ∃ h : ℤ, 2 * (1 / 2 * (10 : ℚ) ^ ec +
      max (1 / 2 * (10 : ℚ) ^ ea) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ ea)) = h * 10 ^ m := by
    rcases le_total (1 / 2 * (10 : ℚ) ^ ea) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ ea) with hmx | hmx
    · rw [max_eq_right hmx]
      have hte : ea ≤ t := by
        by_contra h; push Not at h
        have : (10 : ℚ) ^ t < 10 ^ ea := zpow_lt_zpow_right₀ (by norm_num) h
        linarith
      obtain ⟨kt, hkt⟩ := pow_split t m (le_trans (min_le_right _ _) hte)
      exact ⟨10 ^ kc + 2 * 10 ^ kt - 10 ^ ka, by rw [hkc, hka, hkt]; push_cast; ring⟩
    · rw [max_eq_left hmx]
      exact ⟨10 ^ kc + 10 ^ ka, by rw [hkc, hka]; push_cast; ring⟩
  refine grid_absorb _ _ R _ hg hL hA (by linarith) ?_
  rcases le_total ec ea with hle | hle
  · have hmc : m = ec := min_eq_left hle
    rw [hmc]
    have : c.toRat < 10 ^ 16 * 10 ^ ec := by rw [hcv]; exact mul_lt_mul_of_pos_right hc2 huc
    have : c.toRat * (2 * (1 / 10 ^ 17)) < 10 ^ ec / 5 := by nlinarith
    linarith
  · have hma : m = ea := min_eq_right hle
    rw [hma]
    have h1 : a.toRat < 10 ^ 16 * 10 ^ ea := by rw [hav]; exact mul_lt_mul_of_pos_right ha2 hua
    have : c.toRat * (2 * (1 / 10 ^ 17)) < 10 ^ ea / 2 := by nlinarith
    linarith

/-- A payout floored onto the post-withdrawal grid keeps at least half the priced amount. -/
lemma clamp_half (T : Number) (q a : STAmount) (hc : q.IOUCanonical) (hpos : 0 < q.toRat)
    (hcl : clampToSumExponent T q.operator_neg = .ok a)
    (hfnp : a.isFractionalNonPositive = .ok false) :
    a.IOUCanonical ∧ 0 < a.toRat ∧ q.toRat ≤ 2 * a.toRat := by
  obtain ⟨dn, s, pe, -, -, hpe, hrte⟩ := WdMono.clamp_neg_frac _ _ _ hc hpos hcl
  by_cases hge : pe ≤ q.exponent
  · rw [WdTight.rte_ge q _ pe hc hge hrte]; exact ⟨hc, hpos, by linarith⟩
  replace hge := not_le.mp hge
  obtain ⟨ha0, -, hgrid, hmax⟩ := WdMono.rte_facts q _ pe hc hpos (WdMono.pe_le _ _ hpe) hrte
  have hant := WdMono.roundToExponent_frac_nt _ _ _ _ hc.is_fractional hrte
  have haz : a.mValue ≠ 0 := fun h => by
    rw [WdMono.fnp_zero _ hant h] at hfnp; exact absurd (Except.ok.inj hfnp) (by decide)
  have hapos := WdMono.pos_of_nonneg _ ha0 haz
  have hacan : a.IOUCanonical := by
    rcases (STAmount.roundToExponent_fczr q _ pe .downward
      ⟨hc.is_fractional, Or.inl hc⟩ hrte).2 with h | h
    · exact h
    · exact absurd h haz
  refine ⟨hacan, hapos, ?_⟩
  have h10 : (0 : ℚ) < 10 ^ pe := zpow_pos (by norm_num) _
  have hlt : q.toRat - a.toRat < 10 ^ pe := by
    have h1 : (⌊q.toRat / 10 ^ pe⌋ : ℚ) * 10 ^ pe ≤ q.toRat := by
      have := Int.floor_le (q.toRat / 10 ^ pe); rwa [le_div_iff₀ h10] at this
    have h2 := hmax haz _ h1
    have h3 : q.toRat < ((⌊q.toRat / 10 ^ pe⌋ : ℚ) + 1) * 10 ^ pe := by
      have := Int.lt_floor_add_one (q.toRat / 10 ^ pe); rwa [div_lt_iff₀ h10] at this
    linarith
  obtain ⟨za, hza⟩ := hgrid pe le_rfl
  have hza1 : (1 : ℚ) ≤ za := by
    have : (0 : ℚ) < za := by
      by_contra h; replace h := not_lt.mp h
      have := mul_nonpos_of_nonpos_of_nonneg h h10.le
      linarith
    have : 0 < za := by exact_mod_cast this
    exact_mod_cast (show 1 ≤ za by omega)
  have : 10 ^ pe ≤ a.toRat := by rw [hza]; nlinarith
  linarith

/-- The redemption's exact worth is at least `0.98` of a fractional charge. -/
lemma frac_worth (c : STAmount) (S s I J I₂ : ℚ) (hcc : c.IOUCanonical) (hcpos : 0 < c.toRat)
    (hS0 : 0 ≤ S) (hs : 0 < s) (hI0 : 0 ≤ I)
    (hover : c.toRat - I ≤ I * (2 / 10 ^ 18) + 1 / 2 * (10 : ℚ) ^ c.exponent)
    (hJ : J * (S + s) = S * I + s * c.toRat) (hI₂ : (1 - 1 / 10 ^ 18) * J ≤ I₂) :
    c.toRat * (98 / 100) ≤ I₂ := by
  obtain ⟨hv, h1, -⟩ := iou_val c hcc hcpos
  have hu : (10 : ℚ) ^ c.exponent * 10 ^ 15 ≤ c.toRat := by
    rw [hv, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (zpow_pos (show (0 : ℚ) < 10 by norm_num) _).le
  have hIc : c.toRat * (99 / 100) ≤ I := by
    have : I * (2 / 10 ^ 18) ≤ I * (1 / 1000) := mul_le_mul_of_nonneg_left (by norm_num) hI0
    linarith
  have hSs : 0 < S + s := by linarith
  have hJc : c.toRat * (99 / 100) ≤ J := by
    have h1 : S * (c.toRat * (99 / 100)) ≤ S * I := mul_le_mul_of_nonneg_left hIc hS0
    have h2 : s * (c.toRat * (99 / 100)) ≤ s * c.toRat := mul_le_mul_of_nonneg_left (by linarith) hs.le
    have : c.toRat * (99 / 100) * (S + s) ≤ J * (S + s) := by rw [hJ]; linarith
    exact le_of_mul_le_mul_right this hSs
  have : J * (1 / 10 ^ 18) ≤ J * (1 / 1000) := mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
  linarith

/-- The fractional shortfall: the relative term of the pricing chain is absorbed by the
grids once the payout keeps `0.4` of the charge. -/
lemma frac_loss_final (c a q : STAmount) (t : ℤ) (I₂ an : ℚ)
    (hcc : c.IOUCanonical) (hcpos : 0 < c.toRat) (hacan : a.IOUCanonical) (hapos : 0 < a.toRat)
    (hqcan : q.IOUCanonical) (hqpos : 0 < q.toRat) (hqa : q.toRat ≤ 2 * a.toRat)
    (hI₂ : c.toRat * (98 / 100) ≤ I₂) (han : I₂ * (1 - 1 / 10 ^ 17) ≤ an)
    (hhalf : |q.toRat - an| ≤ 1 / 2 * (10 : ℚ) ^ q.exponent)
    (hloss : c.toRat - a.toRat ≤ c.toRat * (2 * (1 / 10 ^ 17)) + 1 / 2 * (10 : ℚ) ^ c.exponent +
      max (1 / 2 * (10 : ℚ) ^ a.exponent) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ a.exponent)) :
    c.toRat - a.toRat ≤ 1 / 2 * (10 : ℚ) ^ c.exponent +
      max (1 / 2 * (10 : ℚ) ^ a.exponent) ((10 : ℚ) ^ t - 1 / 2 * (10 : ℚ) ^ a.exponent) := by
  obtain ⟨hqv, hq1, -⟩ := iou_val q hqcan hqpos
  have hu : (10 : ℚ) ^ q.exponent * 10 ^ 15 ≤ q.toRat := by
    rw [hqv, mul_comm]
    exact mul_le_mul_of_nonneg_right hq1 (zpow_pos (show (0 : ℚ) < 10 by norm_num) _).le
  have h1 := (abs_le.mp hhalf).1
  have hI₂0 : 0 ≤ I₂ := le_trans (by positivity) hI₂
  have h2 : I₂ * (1 / 10 ^ 17) ≤ I₂ * (1 / 1000) := mul_le_mul_of_nonneg_left (by norm_num) hI₂0
  have hq9 : c.toRat * (9 / 10) ≤ q.toRat := by linarith
  exact frac_grid c a t _ hcc hacan hcpos hapos le_rfl (by linarith) hloss

end XRPL.Model.SingleAssetVault.RtT
