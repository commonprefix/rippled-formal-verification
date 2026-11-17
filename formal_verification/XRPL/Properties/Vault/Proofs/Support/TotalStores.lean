import XRPL.Model.Vault.VaultBalances
import XRPL.Properties.Protocol.Common.TenthBipsTotality
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.Common.NormalizedSum
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.STAmount.Range.Common.OfNumber
import XRPL.Properties.Protocol.STAmount.Range.Common.Units
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality
import XRPL.Properties.Vault.Proofs.Support.IOUTotality
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # The total a balance update stores

C++ `syncAssetsTotal` stores AssetsAvailable + AssetsDeployed as an amount of the asset after every balance update,
and the update fails when that amount cannot be built. `TotalStores` says it can. It holds while the sum is within the
largest amount of the asset, and a smaller sum of balances stores when a larger one does. -/

namespace XRPL.Model.Protocol

/-- A sum of two values that are not negative is zero only when both are. -/
lemma Number.add_nonneg_zero_sum (x y r : Number) (mode : rounding_mode) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hok : x.operator_add y mode = .ok r) (hr0 : r.mantissa_ = 0) :
    x.toRat + y.toRat = 0 := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have hrx : r = x := by
      unfold Number.operator_add at hok; rw [if_pos hy_guard] at hok; exact (Except.ok.inj hok).symm
    rw [Number.toRat_eq_zero_of_mantissa_zero y (Number.mantissa_eq_zero_of_operator_eq_zero hy_guard), ← hrx,
      Number.toRat_eq_zero_of_mantissa_zero r hr0]
    ring
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have hry : r = y := by
      unfold Number.operator_add at hok; rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj hok).symm
    rw [Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hx_guard), ← hry,
      Number.toRat_eq_zero_of_mantissa_zero r hr0]
    ring
  by_cases heq : x.operator_eq y.operator_neg = true
  · have h := (Number.operator_eq_iff _ _ hx (Number.operator_neg_isNormalized y hy)).mp heq
    rw [Number.toRat_neg] at h
    linarith
  · exfalso
    have hxm : x.mantissa_ ≠ 0 := fun h => hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
    have hym : y.mantissa_ ≠ 0 := fun h => hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
    have hsign : x.negative_ = y.negative_ := by
      rw [Number.negative_false_of_nonneg x hx hx0, Number.negative_false_of_nonneg y hy hy0]
    obtain ⟨_, _, _, _, _, hspec⟩ := Number.operator_add_algorithmic_facts_same_sign_anyMode x y r mode hx hy hxm hym
      hsign heq hok
    exact hspec.result_mant_ne hr0

/-- A downward sum of two values that are not negative never lands below a representable value under the
exact sum. -/
lemma Number.add_downward_floor (x y r w : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hok : x.operator_add y .downward = .ok r)
    (hw : w.isNormalized) (hwt : w.toRat ≤ x.toRat + y.toRat) : w.toRat ≤ r.toRat := by
  by_cases hr0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r hr0]
    linarith [Number.add_nonneg_zero_sum x y r _ hx hy hx0 hy0 hok hr0]
  · obtain ⟨n, hn, hv⟩ := Number.operator_add_rounded_downward x y r hx hy hok hr0
    rw [hv]
    exact Number.lower_tight _ n hn w hw hwt

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- C++ `syncAssetsTotal` can store the total of the two balances: their downward sum is an amount of the asset. -/
def TotalStores (nt : NumericType) (available deployed : Number) : Prop :=
  ∃ total amount, available.operator_add deployed .downward = .ok total ∧
    STAmount.ofNumber nt total .downward = .ok amount

/-- The vault's own total is an amount of its asset. A balance update leaves every vault so. -/
def Vault.TotalStored (v : Vault) : Prop := TotalStores v.numericType v.assetsAvailable v.assetsDeployed

/-- A normalized `Number` below `10^97` in size leaves room for an addition. -/
private lemma exponent_room (x : Number) (hx : x.isNormalized) (h : |x.toRat| < 10 ^ 97) :
    x.exponent_ + 22 ≤ maxExponent := by
  by_cases h0 : x.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero x hx h0]; decide
  · have := Number.exponent_lt_of_abs_lt x hx h0 79 (by norm_num; exact h)
    unfold maxExponent
    omega

/-- A downward value at least zero is in the downward range of an asset when it is at most the asset's largest
amount, or below `10^96` for an IOU. -/
private lemma roundsInRange_downward (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (t : ℚ) (h0 : 0 ≤ t)
    (hint : nt.isIntegral = true → t < (nt.maxValue.toNat : ℚ) + 1)
    (hfrac : nt.isIntegral = false → t < 10 ^ 96) : STAmount.RoundsInRange nt .downward t := by
  rcases hasset with rfl | rfl | rfl
  · exact ⟨by linarith [show (0 : ℚ) ≤ 9999999999999999 * 10 ^ 80 by positivity], hfrac rfl⟩
  · rw [STAmount.roundsInRange_native_iff]
    have := hint rfl
    simp only [RoundsWithinUnits, mul_one]
    exact ⟨by linarith, by simpa using this⟩
  · rw [STAmount.roundsInRange_int64_iff]
    have := hint rfl
    simp only [RoundsWithinUnits, mul_one]
    exact ⟨by linarith, by simpa using this⟩

/-- The downward range of an asset, read back: a value in it is below the asset's largest amount plus one, or
below `10^96` for an IOU. -/
private lemma lt_of_roundsInRange_downward (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (t : ℚ)
    (h : STAmount.RoundsInRange nt .downward t) :
    (nt.isIntegral = true → t < (nt.maxValue.toNat : ℚ) + 1) ∧ (nt.isIntegral = false → t < 10 ^ 96) := by
  rcases hasset with rfl | rfl | rfl
  · exact ⟨fun hi => absurd hi (by decide), fun _ => h.2⟩
  · rw [STAmount.roundsInRange_native_iff] at h
    simp only [RoundsWithinUnits, mul_one] at h
    exact ⟨fun _ => by simpa using h.2, fun hi => absurd hi (by decide)⟩
  · rw [STAmount.roundsInRange_int64_iff] at h
    simp only [RoundsWithinUnits, mul_one] at h
    exact ⟨fun _ => by simpa using h.2, fun hi => absurd hi (by decide)⟩

/-- The largest XRP or MPT amount is below `10^96`. -/
private lemma maxValue_lt (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hi : nt.isIntegral = true) :
    (nt.maxValue.toNat : ℚ) + 1 < 10 ^ 96 := by
  rcases hasset with rfl | rfl | rfl
  · exact absurd hi (by decide)
  · rw [show NumericType.native.maxValue.toNat = 100000000000000000 from rfl]
    norm_num
  · rw [show NumericType.int64.maxValue.toNat = 9223372036854775807 from rfl]
    norm_num

/-- Two balances at least zero store their total when their sum is within the largest amount of XRP or an MPT, or
below `10^96` for an IOU. -/
lemma TotalStores.of_le (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (a d : Number)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat)
    (hint : nt.isIntegral = true → a.toRat + d.toRat ≤ nt.maxValue.toNat)
    (hfrac : nt.isIntegral = false → a.toRat + d.toRat < 10 ^ 96) : TotalStores nt a d := by
  have hsum : a.toRat + d.toRat < 10 ^ 96 := by
    by_cases hi : nt.isIntegral = true
    · linarith [hint hi, maxValue_lt nt hasset hi]
    · exact hfrac (by simpa using hi)
  obtain ⟨total, htotal⟩ := Number.operator_add_ok_of_exp a d .downward ha hd
    (exponent_room a ha (by rw [abs_of_nonneg ha0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
    (exponent_room d hd (by rw [abs_of_nonneg hd0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
  obtain ⟨hle, h0⟩ := Number.operator_add_downward_nonneg_le a d total ha hd ha0 hd0 htotal
  have htn := Number.operator_add_isNormalized_any a d total _ ha hd htotal
  obtain ⟨amount, hamount⟩ := (STAmount.ofNumber_ok_iff_proof nt total .downward htn hasset (Or.inl h0)).mpr
    (roundsInRange_downward nt hasset _ h0 (fun hi => by linarith [hint hi]) (fun hi => by linarith [hfrac hi]))
  exact ⟨total, amount, htotal, hamount⟩

/-- A smaller sum of balances stores when a larger one does. -/
lemma TotalStores.mono {nt : NumericType} {a d : Number} (h : TotalStores nt a d)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat) (a' d' : Number)
    (ha' : a'.isNormalized) (hd' : d'.isNormalized) (ha'0 : 0 ≤ a'.toRat) (hd'0 : 0 ≤ d'.toRat)
    (hle : a'.toRat + d'.toRat ≤ a.toRat + d.toRat) : TotalStores nt a' d' := by
  obtain ⟨total, amount, htotal, hamount⟩ := h
  have htn := Number.operator_add_isNormalized_any a d total _ ha hd htotal
  obtain ⟨-, h0⟩ := Number.operator_add_downward_nonneg_le a d total ha hd ha0 hd0 htotal
  have hrange := (STAmount.ofNumber_ok_iff_proof nt total .downward htn hasset (Or.inl h0)).mp ⟨amount, hamount⟩
  obtain ⟨hint, hfrac⟩ := lt_of_roundsInRange_downward nt hasset _ hrange
  have ht96 : total.toRat < 10 ^ 96 := by
    by_cases hi : nt.isIntegral = true
    · linarith [hint hi, maxValue_lt nt hasset hi]
    · exact hfrac (by simpa using hi)
  -- each new balance is a `Number` at or below the old sum, so it is at or below the old total
  have hat : a'.toRat ≤ total.toRat :=
    Number.add_downward_floor a d total a' ha hd ha0 hd0 htotal ha' (by linarith)
  have hdt : d'.toRat ≤ total.toRat :=
    Number.add_downward_floor a d total d' ha hd ha0 hd0 htotal hd' (by linarith)
  obtain ⟨total', htotal'⟩ := Number.operator_add_ok_of_exp a' d' .downward ha' hd'
    (exponent_room a' ha' (by rw [abs_of_nonneg ha'0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
    (exponent_room d' hd' (by rw [abs_of_nonneg hd'0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
  obtain ⟨hle', h0'⟩ := Number.operator_add_downward_nonneg_le a' d' total' ha' hd' ha'0 hd'0 htotal'
  have htn' := Number.operator_add_isNormalized_any a' d' total' _ ha' hd' htotal'
  have htt : total'.toRat ≤ total.toRat :=
    Number.add_downward_floor a d total total' ha hd ha0 hd0 htotal htn' (by linarith)
  obtain ⟨amount', hamount'⟩ := (STAmount.ofNumber_ok_iff_proof nt total' .downward htn' hasset (Or.inl h0')).mpr
    (roundsInRange_downward nt hasset _ h0' (fun hi => by linarith [hint hi]) (fun hi => by linarith [hfrac hi]))
  exact ⟨total', amount', htotal', hamount'⟩

/-- Balances whose total stores sum to less than the largest amount of XRP or an MPT plus ten, or `10^96` for an
IOU plus the last digit the `Number` sum drops. -/
lemma TotalStores.total_lt {nt : NumericType} {a d : Number} (h : TotalStores nt a d)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat) :
    ∃ total : Number, a.operator_add d .downward = .ok total ∧ total.isNormalized ∧ 0 ≤ total.toRat ∧
      total.toRat ≤ a.toRat + d.toRat ∧
      (nt.isIntegral = true → total.toRat < (nt.maxValue.toNat : ℚ) + 1) ∧
      (nt.isIntegral = false → total.toRat < 10 ^ 96) := by
  obtain ⟨total, amount, htotal, hamount⟩ := h
  have htn := Number.operator_add_isNormalized_any a d total _ ha hd htotal
  obtain ⟨hle, h0⟩ := Number.operator_add_downward_nonneg_le a d total ha hd ha0 hd0 htotal
  have hrange := (STAmount.ofNumber_ok_iff_proof nt total .downward htn hasset (Or.inl h0)).mp ⟨amount, hamount⟩
  obtain ⟨hint, hfrac⟩ := lt_of_roundsInRange_downward nt hasset _ hrange
  exact ⟨total, htotal, htn, h0, hle, hint, hfrac⟩

/-- A value the asset stores exactly is below `10^96`. -/
private lemma representable_lt {nt : NumericType} {x : ℚ} (h : STAmount.Representable nt x) : x < 10 ^ 96 := by
  rcases h with rfl | h
  · norm_num
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, -, hk, rfl⟩ := h
    have : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
    linarith [show (9223372036854775807 : ℚ) < 10 ^ 96 by norm_num]
  | fractional =>
    obtain ⟨m, e, -, hm, -, he, rfl⟩ := h
    have hm' : (m : ℚ) < 10 ^ 16 := by exact_mod_cast hm
    have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := mul_lt_mul_of_pos_right hm' hp
      _ ≤ 10 ^ 16 * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left he' (by norm_num)
      _ = 10 ^ 96 := by norm_num

/-- A value the asset stores exactly converts to an amount in `downward` mode. -/
lemma ofNumber_downward_ok_of_representable (nt : NumericType) (x : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hrep : STAmount.Representable nt x.toRat) :
    ∃ amount, STAmount.ofNumber nt x .downward = .ok amount := by
  by_cases hz : x.toRat = 0
  · have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx (Number.toRat_eq_zero_iff.mp hz)
    subst hx0
    cases nt <;> exact ⟨_, rfl⟩
  have hlt := representable_lt hrep
  rcases hrep with h | h
  · exact absurd h hz
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨hmo, k, hk, hk63, hv⟩ := h
    exact STAmount.ofNumber_integral_ok_of_le _ x .downward rfl hmo hx (Number.negative_false_of_nonneg x hx h0)
      (by rw [hv]; exact Rat.den_natCast k)
      (by
        rw [hv]
        have : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
        linarith [show (2 : ℚ) ^ 63 - 1 = 9223372036854775807 by norm_num])
      (by rw [hv]; exact_mod_cast hk)
  | fractional =>
    exact STAmount.ofNumber_fractional_downward_ok x hx (lt_of_le_of_ne h0 (Ne.symm hz)) hlt

/-- Balances whose exact sum the asset stores exactly store their total. This needs no condition on the asset. -/
lemma TotalStores.of_representable (nt : NumericType) (a d : Number) (ha : a.isNormalized) (hd : d.isNormalized)
    (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat) (hrep : STAmount.Representable nt (a.toRat + d.toRat)) :
    TotalStores nt a d := by
  obtain ⟨w, hw, hwv⟩ := hrep.number
  have hlt := representable_lt hrep
  obtain ⟨total, htotal⟩ := Number.operator_add_ok_of_exp a d .downward ha hd
    (exponent_room a ha (by rw [abs_of_nonneg ha0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
    (exponent_room d hd (by rw [abs_of_nonneg hd0]; linarith [show (10 : ℚ) ^ 96 ≤ 10 ^ 97 by norm_num]))
  obtain ⟨hle, h0⟩ := Number.operator_add_downward_nonneg_le a d total ha hd ha0 hd0 htotal
  have htn := Number.operator_add_isNormalized_any a d total _ ha hd htotal
  have hge := Number.add_downward_floor a d total w ha hd ha0 hd0 htotal hw (le_of_eq hwv)
  have hteq : total.toRat = a.toRat + d.toRat := le_antisymm hle (by rw [← hwv]; exact hge)
  obtain ⟨amount, hamount⟩ := ofNumber_downward_ok_of_representable nt total htn h0 (by rw [hteq]; exact hrep)
  exact ⟨total, amount, htotal, hamount⟩

/-- With no cash, a deployed balance the asset stores exactly is its own total. -/
lemma TotalStores.of_zero_available (nt : NumericType) (d : Number) (hd : d.isNormalized) (hd0 : 0 ≤ d.toRat)
    (hrep : STAmount.isRounded nt d = false) : TotalStores nt Number.zero d :=
  TotalStores.of_representable nt Number.zero d Number.zero_isNormalized hd (by rw [Number.toRat_zero]) hd0
    (by rw [Number.toRat_zero, zero_add]; exact (STAmount.isRounded_eq_false_iff nt d hd hd0).mp hrep)

/-- With nothing deployed, a cash balance the asset stores exactly is its own total. -/
lemma TotalStores.of_zero_deployed (nt : NumericType) (a : Number) (ha : a.isNormalized) (ha0 : 0 ≤ a.toRat)
    (hrep : STAmount.isRounded nt a = false) : TotalStores nt a Number.zero :=
  TotalStores.of_representable nt a Number.zero ha Number.zero_isNormalized ha0 (by rw [Number.toRat_zero])
    (by rw [Number.toRat_zero, add_zero]; exact (STAmount.isRounded_eq_false_iff nt a ha ha0).mp hrep)

/-- Balances that sum to at most `9·10^16` units store their total on an IOU, XRP or an MPT. -/
lemma TotalStores.of_le_units (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (a d : Number)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat)
    (hle : a.toRat + d.toRat ≤ 9 * 10 ^ 16) : TotalStores nt a d := by
  have h96 : a.toRat + d.toRat < 10 ^ 96 := lt_of_le_of_lt hle (by norm_num)
  refine TotalStores.of_le nt hasset a d ha hd ha0 hd0 (fun hi => ?_) (fun _ => h96)
  rcases hasset with rfl | rfl | rfl
  · exact absurd hi (by decide)
  · rw [show NumericType.native.maxValue.toNat = 100000000000000000 from rfl]
    push_cast
    linarith
  · rw [show NumericType.int64.maxValue.toNat = 9223372036854775807 from rfl]
    push_cast
    linarith

/-- Balances that sum to less than `10^16` units store their total on an IOU, XRP or an MPT. -/
lemma TotalStores.of_lt_open (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (a d : Number)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat)
    (hlt : a.toRat + d.toRat < 10 ^ 16) : TotalStores nt a d := by
  have h96 : a.toRat + d.toRat < 10 ^ 96 := lt_of_lt_of_le hlt (by norm_num)
  refine TotalStores.of_le nt hasset a d ha hd ha0 hd0 (fun hi => ?_) (fun _ => h96)
  rcases hasset with rfl | rfl | rfl
  · exact absurd hi (by decide)
  · rw [show NumericType.native.maxValue.toNat = 100000000000000000 from rfl]
    push_cast
    linarith
  · rw [show NumericType.int64.maxValue.toNat = 9223372036854775807 from rfl]
    push_cast
    linarith

end XRPL.Model.SingleAssetVault
