import XRPL.Model.Vault.VaultDeposit

/-! # Monadic reduction toolkit for `Vault.deposit`

Building blocks for stepping the `Except Error` do-blocks of the deposit
pipeline: the two `Except` bind identities (both `rfl`), a clean `if`-form
characterization of `roundedDepositAmount` once `roundToVaultExponent` is known,
and the two bridges that read that characterization back. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- `Except.ok`-bind step, definitional. -/
theorem ok_bind {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- `Except.error`-bind short-circuit, definitional. -/
theorem err_bind {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `tryCatch` on a caught error runs the handler, definitional. -/
theorem tryCatch_error {ε α} (e : ε) (h : ε → Except ε α) :
    (tryCatch (Except.error e) h) = h e := rfl

/-- Peel one `Except`-bind out of an `.ok` result: the head succeeded and the
continuation reached the same `.ok`. -/
theorem bind_ok_peel {α β} (x : Except Error α) (f : α → Except Error β) (r : β)
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx, err_bind] at h; exact absurd h (by simp)
  | ok a => rw [hx, ok_bind] at h; exact ⟨a, rfl, h⟩

/-- Clean `if`-form of `roundedDepositAmount` when `roundToVaultExponent` succeeds. -/
theorem roundedDepositAmount_ok (v : Vault) (amountDeposit ra' : STAmount)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .ok ra') :
    v.roundedDepositAmount amountDeposit =
      (if ra'.isZero then .ok (.rejected .tecPRECISION_LOSS) else .ok (.rounded ra')) := by
  simp only [Vault.roundedDepositAmount, hr, ok_bind]; rfl

/-- `roundedDepositAmount` propagates a `roundToVaultExponent` error. -/
theorem roundedDepositAmount_err (v : Vault) (amountDeposit : STAmount) (e : Error)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .error e) :
    v.roundedDepositAmount amountDeposit = .error e := by
  simp only [Vault.roundedDepositAmount, hr, err_bind]

/-- A `rounded` outcome means `roundToVaultExponent` produced exactly that nonzero
amount. -/
theorem roundedDepositAmount_rounded (v : Vault) (amountDeposit ra : STAmount)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rounded ra)) :
    roundToVaultExponent amountDeposit v.assetsTotal = .ok ra ∧ ra.isZero = false := by
  cases hr : roundToVaultExponent amountDeposit v.assetsTotal with
  | error e => rw [roundedDepositAmount_err v amountDeposit e hr] at h; exact absurd h (by simp)
  | ok ra' =>
    rw [roundedDepositAmount_ok v amountDeposit ra' hr] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hz
      rw [Except.ok.injEq, RoundingResult.rounded.injEq] at h
      subst h
      exact ⟨rfl, by simpa using hz⟩

/-- A `rejected` outcome pins the code to `tecPRECISION_LOSS` and means
`roundToVaultExponent` produced a zero amount. -/
theorem roundedDepositAmount_rejected (v : Vault) (amountDeposit : STAmount) (ter : TER)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ∃ ra, roundToVaultExponent amountDeposit v.assetsTotal = .ok ra ∧ ra.isZero = true ∧
      ter = .tecPRECISION_LOSS := by
  cases hr : roundToVaultExponent amountDeposit v.assetsTotal with
  | error e => rw [roundedDepositAmount_err v amountDeposit e hr] at h; exact absurd h (by simp)
  | ok ra' =>
    rw [roundedDepositAmount_ok v amountDeposit ra' hr] at h
    split at h
    · rename_i hz
      rw [Except.ok.injEq, RoundingResult.rejected.injEq] at h
      exact ⟨ra', rfl, hz, h.symm⟩
    · exact absurd h (by simp)

/-! ## `clampToSumExponent` on integral amounts

An integral amount carries no digits below the vault's grid, so the clamp has
nothing to do: it returns the magnitude unchanged without consulting
`postSumExponent`, rounding, or throwing. This is the branch the int64/XRP
vaults take, and it is what makes the clamp inert for them. -/

/-- `operator_neg` is involutive: it only toggles the sign flag, and a zero
amount is left alone by both applications. -/
theorem STAmount.operator_neg_neg (s : STAmount) : s.operator_neg.operator_neg = s := by
  unfold STAmount.operator_neg
  by_cases h : (s.mValue == 0) = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    simp only [if_neg h, Bool.not_not]

/-- The clamp is the identity on the magnitude of an integral delta. -/
theorem clampToSumExponent_integral (amount : Number) (delta : STAmount)
    (hint : delta.integral = true) :
    clampToSumExponent amount delta
      = .ok (if delta.negative then delta.operator_neg else delta) := by
  unfold clampToSumExponent
  simp only []
  rw [if_pos hint]
  rfl

/-- The withdraw/clawback call shape: the clamp is handed `-a` for an integral `a`
whose sign flag is clear (or which is zero, where the flag cannot matter because
`operator_neg` is then the identity), and returns `a` itself. -/
theorem clampToSumExponent_integral_neg (amount : Number) (a : STAmount)
    (hint : a.integral = true) (hsgn : a.mValue = 0 ∨ a.mIsNegative = false) :
    clampToSumExponent amount a.operator_neg = .ok a := by
  by_cases hmv : a.mValue = 0
  · -- zero: `operator_neg` is the identity, so either clamp branch returns `a`
    have hz : a.operator_neg = a := by
      unfold STAmount.operator_neg; rw [if_pos (beq_iff_eq.mpr hmv)]
    rw [hz, clampToSumExponent_integral amount a hint]
    by_cases hn : a.negative = true
    · rw [if_pos hn]
      unfold STAmount.operator_neg; rw [if_pos (beq_iff_eq.mpr hmv)]
    · rw [if_neg hn]
  · have hnn : a.mIsNegative = false := by
      rcases hsgn with h | h
      · exact absurd h hmv
      · exact h
    have hne : (a.mValue == 0) = false := beq_eq_false_iff_ne.mpr hmv
    have hnegint : a.operator_neg.integral = true := by
      unfold STAmount.integral STAmount.operator_neg
      rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
      exact hint
    have hneg : a.operator_neg.negative = true := by
      unfold STAmount.negative STAmount.operator_neg
      rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
      show (!a.mIsNegative) = true
      rw [hnn]; rfl
    rw [clampToSumExponent_integral amount a.operator_neg hnegint, hneg, if_pos rfl,
      STAmount.operator_neg_neg]

/-- The deposit call shape: the clamp is handed a nonnegative integral charge and
returns it unchanged. -/
theorem clampToSumExponent_integral_pos (amount : Number) (a : STAmount)
    (hint : a.integral = true) (hsgn : a.mValue = 0 ∨ a.mIsNegative = false) :
    clampToSumExponent amount a = .ok a := by
  rw [clampToSumExponent_integral amount a hint]
  by_cases hn : a.negative = true
  · -- a set sign flag forces a zero mantissa here, where `operator_neg` is the identity
    rw [if_pos hn]
    have hmv : a.mValue = 0 := by
      rcases hsgn with h | h
      · exact h
      · exact absurd (show a.mIsNegative = true from hn) (by rw [h]; exact Bool.false_ne_true)
    unfold STAmount.operator_neg; rw [if_pos (beq_iff_eq.mpr hmv)]
  · rw [if_neg hn]

/-- An integral amount never trips the `isFractionalNonPositive` guard. -/
theorem STAmount.isFractionalNonPositive_integral (a : STAmount) (hint : a.integral = true) :
    a.isFractionalNonPositive = .ok false := by
  unfold STAmount.isFractionalNonPositive
  rw [if_pos hint]

end XRPL.Model.SingleAssetVault
