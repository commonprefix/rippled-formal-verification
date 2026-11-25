import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Lawful
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Loan.Common.OverpaymentSkip
import XRPL.Properties.Protocol.Common.ErrorKinds

/-! # Steps of the vault transactions that always compute

The steps a VaultDeposit, a VaultSet and a VaultDelete run outside the pricing return a value: sums of balances, the
conversion of a sum within the asset's largest amount, and the clamp of an amount onto a balance's grid. -/

namespace XRPL.Model.Protocol.VaultDepositNoException

open XRPL.Model.Protocol

/-- The asset is an IOU, XRP or an MPT. -/
abbrev IsAsset (nt : NumericType) : Prop := nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64

/-- A to-nearest sum of a nonnegative exact sum stays between zero and any normalized Number above that sum. -/
lemma add_nearest_bounds (x y n w : Number) (hx : x.isNormalized) (hy : y.isNormalized) (hw : w.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok n) (h0 : 0 ≤ x.toRat + y.toRat)
    (hle : x.toRat + y.toRat ≤ w.toRat) : 0 ≤ n.toRat ∧ n.toRat ≤ w.toRat := by
  have hlow : ∀ l, Number.lower (x.toRat + y.toRat) = some l → 0 ≤ l.toRat ∧ l.toRat ≤ w.toRat := by
    intro l hl
    refine ⟨?_, le_trans (Number.lower_le _ l hl) hle⟩
    have := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact h0)
    rwa [Number.toRat_zero] at this
  have hup : ∀ u, Number.upper (x.toRat + y.toRat) = some u → 0 ≤ u.toRat ∧ u.toRat ≤ w.toRat := fun u hu =>
    ⟨le_trans h0 (Number.le_upper _ u hu), Number.upper_tight _ u hu w hw hle⟩
  rcases Number.operator_add_rounded_to_nearest x y n hx hy hok with ⟨l, hl, hv⟩ | ⟨u, hu, hv⟩
  · rw [hv]; exact hlow l hl
  · rw [hv]; exact hup u hu

/-- The largest XRP amount is `10^17` drops. -/
lemma maxAmount_native : NumericType.native.maxAmount = 100000000000000000 := by
  unfold NumericType.maxAmount
  rw [ite_eq_left (show NumericType.native.isIntegral = true from rfl),
    show NumericType.native.maxValue.toNat = 100000000000000000 from rfl]
  norm_num

/-- The largest MPT amount is `2^63 - 1` units. -/
lemma maxAmount_int64 : NumericType.int64.maxAmount = 9223372036854775807 := by
  unfold NumericType.maxAmount
  rw [ite_eq_left (show NumericType.int64.isIntegral = true from rfl),
    show NumericType.int64.maxValue.toNat = 9223372036854775807 from rfl]
  norm_num

/-- The largest amount of an asset is a normalized Number. -/
lemma maxAmount_number (nt : NumericType) (hnt : IsAsset nt) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = nt.maxAmount := by
  have hs : minExponent + 18 ≤ (0 : Int) ∧ (0 : Int) ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  rcases hnt with rfl | rfl | rfl
  · obtain ⟨w, hw, hv⟩ := Number.exists_normalized_int_mul_pow 9999999999999999 80 (by norm_num)
      (by unfold minExponent maxExponent; omega)
    exact ⟨w, hw, by rw [hv, NumericType.maxAmount_fractional]; norm_num⟩
  · obtain ⟨w, hw, hv⟩ := Number.exists_normalized_int_mul_pow 100000000000000000 0 (by norm_num) hs
    exact ⟨w, hw, by rw [hv, maxAmount_native]; norm_num⟩
  · obtain ⟨w, hw, hv⟩ := Number.exists_normalized_int_mul_pow 9223372036854775807 0 (by norm_num) hs
    exact ⟨w, hw, by rw [hv, maxAmount_int64]; norm_num⟩

/-- A Number between zero and the largest amount of the asset converts to an amount, in every mode. -/
lemma ofNumber_computes (nt : NumericType) (hnt : IsAsset nt) (n : Number) (mode : rounding_mode)
    (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) (hle : n.toRat ≤ nt.maxAmount) :
    ∃ r, STAmount.ofNumber nt n mode = .ok r := by
  refine (STAmount.ofNumber_ok_iff nt n mode hn hnt (Or.inl h0)).mpr ?_
  rcases hnt with rfl | rfl | rfl
  · rw [STAmount.roundsInRange_fractional_iff]
    refine roundsWithinUnits_of_abs_le mode _ _ _ (by positivity) ?_
    rw [abs_of_nonneg h0]
    rw [NumericType.maxAmount_fractional] at hle
    norm_num at hle ⊢
    exact hle
  · rw [STAmount.roundsInRange_native_iff]
    refine roundsWithinUnits_of_abs_le mode _ _ _ (by norm_num) ?_
    rw [abs_of_nonneg h0]
    rw [maxAmount_native] at hle
    norm_num
    exact hle
  · rw [STAmount.roundsInRange_int64_iff]
    refine roundsWithinUnits_of_abs_le mode _ _ _ (by norm_num) ?_
    rw [abs_of_nonneg h0]
    rw [maxAmount_int64] at hle
    norm_num
    exact hle

/-- The exponent a balance has after a credit computes while the sum is within the largest amount of the asset. -/
lemma postSumExponent_computes (nt : NumericType) (hnt : IsAsset nt) (A d : Number) (b : Int)
    (hA : A.isNormalized) (hd : d.isNormalized) (hA0 : 0 ≤ A.toRat) (hd0 : 0 ≤ d.toRat)
    (hsum : A.toRat + d.toRat ≤ nt.maxAmount) : ∃ e, postSumExponent A d b nt = .ok e := by
  have hlt : nt.maxAmount < 10 ^ 96 := NumericType.maxAmount_lt nt
  have hbig : (10 : ℚ) ^ 96 < 10 ^ 200 := by norm_num
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_abs A d .to_nearest hA hd
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_nonneg hd0]; linarith)
  obtain ⟨w, hw, hwv⟩ := maxAmount_number nt hnt
  obtain ⟨hs0, hsle⟩ := add_nearest_bounds A d s w hA hd hw hs (by linarith) (by rw [hwv]; exact hsum)
  have hsn := Number.operator_add_isNormalized_any A d s .to_nearest hA hd hs
  unfold postSumExponent
  rw [hs, ok_bind]
  unfold numberExponent
  by_cases hz : s.operator_eq Number.zero = true
  · exact ⟨b, by simp [hz, pure, Except.pure]⟩
  · obtain ⟨st, hst⟩ := ofNumber_computes nt hnt s .downward hsn hs0 (by rw [← hwv]; exact hsle)
    exact ⟨max b st.exponent, by simp [hz, hst, bind, Except.bind, pure, Except.pure]⟩

/-- Clamping an amount onto the grid of a balance computes while the balance plus the amount is within the largest
IOU amount. An XRP or MPT amount is returned as it is. -/
lemma clampToSumExponent_computes (A : Number) (delta : STAmount) (b : Int) (hA : A.isNormalized)
    (hA0 : 0 ≤ A.toRat) (hd : delta.CanonicalOrZero) (hd0 : 0 ≤ delta.toRat) (hb : -96 ≤ b ∧ b ≤ 80)
    (hsum : delta.integral = false → A.toRat + delta.toRat ≤ NumericType.fractional.maxAmount) :
    ∃ r, clampToSumExponent A delta b = .ok r := by
  by_cases hint : delta.integral = true
  · exact ⟨_, clampToSumExponent_integral A delta b hint⟩
  have hfr : delta.integral = false := by simpa using hint
  have hfz := hd.fracCanonZero hfr
  obtain ⟨dn, hdn⟩ := hd.toNumber_ok
  obtain ⟨hdv, hdnn⟩ := hd.toNumber_exact dn hdn
  obtain ⟨e, he⟩ := postSumExponent_computes .fractional (Or.inl rfl) A dn b hA hdnn hA0 (by rw [hdv]; exact hd0)
    (by rw [hdv]; exact hsum hfr)
  obtain ⟨-, he_lo, he_hi⟩ := postSumExponent_range A dn b .fractional e hb.1 hb.2 he
  -- the magnitude is a nonnegative IOU amount or zero
  have habs : ∃ r, STAmount.roundToExponent (if delta.negative = true then delta.operator_neg else delta) e
      .towards_zero = .ok r := by
    rcases hfz.2 with hio | hz
    · have hm : delta.mValue ≠ 0 := fun h => by have := hio.mant_lo; rw [h] at this; simp at this
      by_cases hn : delta.negative = true
      · rw [ite_eq_left hn]
        refine STAmount.roundToExponent_towards_zero_ok _ e ?_ ?_ he_lo he_hi
        · unfold STAmount.operator_neg
          rw [ite_eq_right (by simpa using hm)]
          exact ⟨hio.is_fractional, hio.mant_lo, hio.mant_hi, hio.exp_lo, hio.exp_hi⟩
        · unfold STAmount.operator_neg
          rw [ite_eq_right (by simpa using hm)]
          simpa [STAmount.negative] using hn
      · rw [ite_eq_right hn]
        exact STAmount.roundToExponent_towards_zero_ok _ e hio (by simpa [STAmount.negative] using hn) he_lo he_hi
    · have hz' : (if delta.negative = true then delta.operator_neg else delta).mValue = 0 := by
        split
        · unfold STAmount.operator_neg; rw [ite_eq_left (by simp [hz])]; exact hz
        · exact hz
      generalize (if delta.negative = true then delta.operator_neg else delta) = dabs at hz'
      refine ⟨dabs, ?_⟩
      unfold STAmount.roundToExponent
      by_cases hi : dabs.integral = true
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi, ite_eq_left (by simp [STAmount.isZero, hz'])]
  obtain ⟨r, hr⟩ := habs
  refine ⟨r, ?_⟩
  unfold clampToSumExponent
  simp only [bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right hint, hdn]
  have hnt : delta.numericType = .fractional := hfz.1
  simp only [hnt, he]
  exact hr

end XRPL.Model.Protocol.VaultDepositNoException

namespace XRPL.Model.SingleAssetVault.VaultDepositNoException

open XRPL.Model.Protocol
open XRPL.Model.Protocol.VaultDepositNoException
open XRPL.Model.Lending (Vault.HoldsAsset)

open private STAmount.roundToNumericType_towards_zero_ok from XRPL.Properties.Lending.Loan.Common.OverpaymentSkip

/-- A value an asset stores exactly is below `10^96` in size. -/
lemma representable_abs_lt (nt : NumericType) (q : ℚ) (h : STAmount.Representable nt q) : |q| < 10 ^ 96 := by
  rcases h with h0 | h
  · rw [h0]; norm_num
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, -, hk, hkv⟩ := h
    have hk' : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
    rw [hkv, abs_of_nonneg (by positivity)]
    linarith
  | fractional =>
    obtain ⟨m, e, -, hm, -, he, hv⟩ := h
    have hm' : (m : ℚ) < 10 ^ 16 := by exact_mod_cast hm
    have hpe : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    rw [hv, abs_of_nonneg (by positivity)]
    calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := mul_lt_mul_of_pos_right hm' hp
      _ ≤ 10 ^ 16 * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left hpe (by norm_num)
      _ = 10 ^ 96 := by norm_num

/-- The total of a lawful vault computes: both balances are amounts of the asset, far below the top exponent. -/
lemma assetsTotal_computes (v : Vault) : ∃ A, v.assetsTotal = .ok A := by
  have h1 := representable_abs_lt _ _ v.exact.assetsAvailable_representable
  have h2 := representable_abs_lt _ _ v.exact.assetsDeployed_representable
  exact Number.operator_add_ok_of_abs _ _ .downward v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm
    (lt_trans h1 (by norm_num)) (lt_trans h2 (by norm_num))

/-- The VaultDelete checks always compute. -/
lemma canVaultDelete_computes (v : Vault) : ∃ t, v.canVaultDelete = .ok t := by
  obtain ⟨A, hA⟩ := assetsTotal_computes v
  unfold Vault.canVaultDelete
  simp only [bind, Except.bind, pure, Except.pure, hA]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The base-grid check of a new AssetsMaximum computes for a normalized value at least zero. -/
lemma isOnExponentGrid_computes (v : Vault) (hasset : Vault.HoldsAsset v) (m : Number)
    (hn : m.isNormalized) (h0 : Number.zero.operator_le m = true) :
    ∃ b, m.isOnExponentGrid v.baseExponent v.numericType = .ok b := by
  have hm0 : 0 ≤ m.toRat := by
    have := (Number.operator_le_iff _ _ Number.zero_isNormalized hn).mp h0
    rwa [Number.toRat_zero] at this
  unfold Number.isOnExponentGrid
  by_cases hr : STAmount.isRounded v.numericType m = true
  · exact ⟨false, by simp [hr, pure, Except.pure]⟩
  · have hr' : STAmount.isRounded v.numericType m = false := by simpa using hr
    obtain ⟨c, hc⟩ := STAmount.roundToNumericType_towards_zero_ok v.numericType m v.baseExponent hn hm0 hr' hasset
      (by have := v.baseExponent_bounds; omega)
    exact ⟨c.operator_eq m, by simp [hr', hc, bind, Except.bind, pure, Except.pure]⟩

/-- The VaultSet checks compute for a normalized AssetsMaximum at least zero. -/
lemma canVaultUpdate_computes (v : Vault) (hasset : Vault.HoldsAsset v) (assetsMaximum : Option Number)
    (blockDeposit : Option Bool)
    (hmax : ∀ m ∈ assetsMaximum, m.isNormalized ∧ Number.zero.operator_le m = true) :
    ∃ t, v.canVaultUpdate assetsMaximum blockDeposit = .ok t := by
  obtain ⟨A, hA⟩ := assetsTotal_computes v
  unfold Vault.canVaultUpdate
  cases assetsMaximum with
  | none =>
    simp only [bind, Except.bind, pure, Except.pure]
    split_ifs <;> exact ⟨_, rfl⟩
  | some m =>
    obtain ⟨hn, h0⟩ := hmax m rfl
    obtain ⟨b, hb⟩ := isOnExponentGrid_computes v hasset m hn h0
    simp only [bind, Except.bind, pure, Except.pure, hb, hA]
    split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.SingleAssetVault.VaultDepositNoException
