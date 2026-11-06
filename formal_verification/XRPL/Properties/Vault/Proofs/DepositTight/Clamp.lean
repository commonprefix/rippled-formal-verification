import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # The deposit clamp undercharges by less than one post-sum grid step -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- The post-sum grid is never finer than the delta's own digits. The rounded sum of a nonnegative
total and a positive canonical delta is at least the delta, so its 16-digit exponent is at least the delta's. -/
lemma post_exp_ge (A : Number) (p : STAmount) (pn : Number) (exponent e : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hp : p.IOUCanonical) (hppos : 0 < p.toRat)
    (hpn : p.toNumber .to_nearest = .ok pn)
    (he : postSumExponent A pn exponent .fractional = .ok e) :
    p.exponent ≤ e := by
  obtain ⟨sum, hsum, hne⟩ := postSumExponent_reduces A pn exponent .fractional e he
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest hp
  rw [hsn, Except.ok.injEq] at hpn
  subst hpn
  have hrsum := operator_add_rounded_to_nearest A sn sum hA hsnn hsum
  have hsum_norm := operator_add_isNormalized_to_nearest_sz A sn sum hA hsnn hsum
  have hge : sn.toRat ≤ sum.toRat :=
    Number.RoundsToRepresentable.ge_of_ge_normalized sum _ hrsum sn hsnn (by linarith)
  have hband := (STAmount.IOUCanonical.toRat_bounds p hp hppos).1
  exact numberExponent_frac_of_le sum exponent e p.exponent hsum_norm hp.exp_lo
    (by rw [hsnv] at hge; linarith) hne

/-- The clamp undercharges by less than one post-sum grid step. A positive canonical delta
clamped to a nonzero amount on the grid `10 ^ e` keeps everything but the digits below that step. -/
lemma clamp_sum_ge (A : Number) (p c : STAmount) (pn : Number) (exponent e : ℤ)
    (hp : p.IOUCanonical) (hppos : 0 < p.toRat)
    (hlo : -96 ≤ exponent) (hhi : exponent ≤ 80)
    (hpn : p.toNumber .to_nearest = .ok pn)
    (he : postSumExponent A pn exponent .fractional = .ok e)
    (hcl : clampToSumExponent A p exponent = .ok c) (hc : c.mValue ≠ 0) :
    p.toRat - 10 ^ e < c.toRat := by
  obtain ⟨pn', e', hpn', he', -, hval⟩ :=
    clampToSumExponent_frac_floor A p c exponent ⟨hp.is_fractional, Or.inl hp⟩ hlo hhi hc hcl
  rw [hpn, Except.ok.injEq] at hpn'
  subst hpn'
  rw [show p.numericType = .fractional from hp.is_fractional, he, Except.ok.injEq] at he'
  subst he'
  rw [hval, abs_of_pos hppos]
  have hpow : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hfl := Int.lt_floor_add_one (p.toRat / 10 ^ e)
  have hmul : p.toRat / 10 ^ e * 10 ^ e = p.toRat := div_mul_cancel₀ _ hpow.ne'
  nlinarith

end XRPL.Model.SingleAssetVault.DepTight
