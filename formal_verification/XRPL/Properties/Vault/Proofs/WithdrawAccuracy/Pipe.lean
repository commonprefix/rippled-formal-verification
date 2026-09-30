import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Price
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Burn

/-! # The `sharesToAssetsWithdraw` pricing pipeline -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

/-- The two paths of `sharesToAssetsWithdraw` under an exact pricing value. -/
lemma price_cases (v : Vault) (sh p : STAmount) (w : Bool)
    (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    ∃ nav : Number, nav.toRat = (if w then v.depositNav else v.withdrawNav) ∧
    nav.isNormalized ∧
    ((nav.mantissa_ = 0 ∧ p = STAmount.zero v.numericType) ∨
     (nav.mantissa_ ≠ 0 ∧ ∃ sn NS an, sh.toNumber .to_nearest = .ok sn ∧
        nav.operator_mul sn .to_nearest = .ok NS ∧
        NS.operator_div v.sharesTotal .to_nearest = .ok an ∧
        STAmount.ofNumber v.numericType an .to_nearest = .ok p)) := by
  obtain ⟨nv, hnv, hnvq⟩ := hnav
  refine ⟨nv, hnvq, ?_⟩
  cases w <;> simp only at hnv <;>
    refine ⟨operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm
      (by first | exact v.wf.lossUnrealized_norm | exact Or.inl rfl) hnv, ?_⟩ <;>
    simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok <;>
    rw [hnv] at hok <;> simp only at hok <;> walk_ok
  all_goals first
    | exact Or.inl ⟨beq_iff_eq.mp ‹(nv.mantissa_ == 0) = true›, rfl⟩
    | exact Or.inr ⟨by simpa using ‹¬ (nv.mantissa_ == 0) = true›, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩

lemma depositε_val : depositε = 1 / 100000000000000000 := by
  unfold depositε
  rw [show ((-17) : ℤ) = -(17 : ℕ) from rfl, zpow_neg, zpow_natCast]
  norm_num

/-- A normalized `Number` of value `k · 10 ^ s` for small `k`. -/
lemma normalized_of (k : ℕ) (s : ℤ) (hk : 1 ≤ k) (hk' : k < 10 ^ 16)
    (hs_lo : -32000 ≤ s) (hs_hi : s ≤ 32000) :
    ∃ x : Number, x.isNormalized ∧ x.toRat = (k : ℚ) * 10 ^ s := by
  obtain ⟨x, hx, -, -, hv, -⟩ := exists_normalized_of_int_mul_pow k s hk hk'
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  exact ⟨x, hx, hv⟩

/-- When the burned shares are worth at least `10 ^ (-82)`, the pre-packing price
`an` is positive and within `depositε` below the worth. -/
lemma price_an_lower (v : Vault) (sh p : STAmount) (w : Bool)
    (hc : sh.Canonical) (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p)
    (hI : (10 : ℚ) ^ (-82 : ℤ) ≤ v.idealAssetsWithdraw w sh.toRat) :
    ∃ an : Number, STAmount.ofNumber v.numericType an .to_nearest = .ok p ∧
      an.isNormalized ∧ an.negative_ = false ∧ 0 < an.toRat ∧
      v.idealAssetsWithdraw w sh.toRat * (1 - depositε) ≤ an.toRat := by
  obtain ⟨nav, hnavq, hnavn, hcase⟩ := price_cases v sh p w hnav hok
  have hideal : v.idealAssetsWithdraw w sh.toRat =
      nav.toRat * sh.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdraw
    rw [hnavq, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rw [hideal] at hI ⊢
  have ht : (0 : ℚ) < 10 ^ (-82 : ℤ) := by positivity
  rcases hcase with ⟨hm0, -⟩ | ⟨hm, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav hm0] at hI; simp at hI; linarith
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  have hsn_eq : sn = sn0 := (Except.ok.inj (hsn0.symm.trans hsn)).symm
  subst hsn_eq
  set ST := v.sharesTotal.toRat with hST
  have hST0 : 0 ≤ ST := v.wf.sharesTotal_nonneg
  have hSTpos : 0 < ST := by
    rcases lt_or_eq_of_le hST0 with h | h
    · exact h
    · rw [← h, div_zero] at hI; linarith
  have hST1 : 1 ≤ ST := by
    have := rat_one_le_sub_of_lt ST 0 v.wf.sharesTotal_int rfl hSTpos; linarith
  set I := nav.toRat * sh.toRat / ST with hIdef
  set T0 := nav.toRat * sh.toRat with hT0
  have hT0I : T0 = I * ST := by rw [hIdef]; field_simp
  set t := (10 : ℚ) ^ (-82 : ℤ) with htdef
  have hT0pos : t ≤ T0 := by rw [hT0I]; nlinarith
  obtain ⟨m1, hm1, hm1v⟩ := normalized_of 1 (-82) le_rfl (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨m2, hm2, hm2v⟩ := normalized_of 1 (-83) le_rfl (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_one, one_mul] at hm1v hm2v
  have ht2 : (10 : ℚ) ^ (-83 : ℤ) ≤ t * (1 - 5 / (2 ^ 63 + 7)) := by rw [htdef]; norm_num
  have ht2pos : (0 : ℚ) < 10 ^ (-83 : ℤ) := by positivity
  have hNS1 : t ≤ NS.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized NS _
      (operator_mul_rounded_to_nearest nav sn NS hnavn hsnn hmul) m1 hm1
      (by rw [hm1v, hsnv]; exact hT0pos)
    rwa [hm1v] at this
  have hNSm : NS.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  obtain ⟨-, hsnm⟩ := operator_mul_operands_ne_zero hnavn hsnn hmul hNSm
  have hNSn := operator_mul_result_isNormalized nav sn NS .to_nearest hnavn hsnn hm hsnm hmul hNSm
  have hmulb : |NS.toRat - T0| ≤ |T0| * (5 / (2 ^ 63 + 7)) := by
    have := operator_mul_rounds_to_nearest nav sn NS hnavn hsnn hmul hNSm
    rw [hsnv] at this; exact this
  rw [abs_of_pos (show (0 : ℚ) < T0 by linarith)] at hmulb
  obtain ⟨hmb1, -⟩ := abs_le.mp hmulb
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  have hQ : I * (1 - 5 / (2 ^ 63 + 7)) ≤ NS.toRat / ST := by
    rw [le_div_iff₀ hSTpos]; nlinarith
  have hIpos : 0 < I := by linarith
  have han_lo : (10 : ℚ) ^ (-83 : ℤ) ≤ an.toRat := by
    have := Number.RoundsToRepresentable.ge_of_ge_normalized an _
      (operator_div_rounded_to_nearest NS v.sharesTotal an hNSn v.wf.sharesTotal_norm hdiv) m2
      hm2 (by
        rw [hm2v]
        have h3 : t * (1 - 5 / (2 ^ 63 + 7)) ≤ I * (1 - 5 / (2 ^ 63 + 7)) :=
          mul_le_mul_of_nonneg_right hI (by norm_num)
        show _ ≤ NS.toRat / ST
        linarith)
    rwa [hm2v] at this
  have hanm : an.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  have hdivb := operator_div_rounds_to_nearest NS v.sharesTotal an hNSn v.wf.sharesTotal_norm hdiv hanm
  change |an.toRat - NS.toRat / ST| ≤ |NS.toRat / ST| * (6 / (2 ^ 63 - 3)) at hdivb
  have hQpos : 0 < NS.toRat / ST := div_pos (by linarith) hSTpos
  rw [abs_of_pos hQpos] at hdivb
  obtain ⟨hdb1, -⟩ := abs_le.mp hdivb
  have hann := operator_div_result_isNormalized NS v.sharesTotal an .to_nearest hNSn
    v.wf.sharesTotal_norm hNSm hSTm hdiv hanm
  refine ⟨an, hof, hann, Number.negative_false_of_normalized_nonneg an hann (by linarith),
    by linarith, ?_⟩
  rw [depositε_val]
  have hc1 : (1 : ℚ) - 1 / 100000000000000000 ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
    norm_num
  nlinarith

/-- The ideal payout of nonnegative shares is nonnegative. -/
lemma ideal_nonneg (v : Vault) (w : Bool) (s : ℚ) (hs : 0 ≤ s) :
    0 ≤ v.idealAssetsWithdraw w s := by
  unfold RawVault.idealAssetsWithdraw
  have hx := v.exact
  have : 0 ≤ (if w then v.depositNav else v.withdrawNav) := by
    cases w
    · show 0 ≤ v.toExact.assetsTotal - v.toExact.lossUnrealized; exact hx.withdraw_nav_nonneg
    · show 0 ≤ v.toExact.assetsTotal; exact hx.assetsTotal_nonneg
  positivity

/-- An offset-`0` integral record with a cleared sign is worth its magnitude, and
any record with the same fields is worth at most that. -/
lemma clamp_integral_ge (a b : STAmount) (hoff : a.mOffset = 0)
    (hboff : b.mOffset = a.mOffset) (hbmv : b.mValue = a.mValue)
    (hbneg : b.mValue = 0 ∨ b.mIsNegative = false) : a.toRat ≤ b.toRat ∧ 0 ≤ b.toRat := by
  rw [STAmount.toRat_of_offset_zero a hoff, STAmount.toRat_of_offset_zero b (hboff.trans hoff)]
  unfold STAmount.signedDrops
  rw [hbmv]
  rcases hbneg with h | h
  · rw [hbmv] at h; simp [h]
  · rw [h]; constructor
    · split <;> simp
    · simp

end XRPL.Model.SingleAssetVault.WdAcc
