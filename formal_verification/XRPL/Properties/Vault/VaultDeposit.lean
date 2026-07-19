import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.WitnessSupport

/-! # `Vault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.roundedDepositAmount` -/

/-- `roundedAmount` is `amountDeposit` with every digit below some grid step
`10 ^ s` discarded and the digits above kept unchanged, and it is nonzero. As an
equation: `roundedAmount.toRat = ⌊amountDeposit.toRat / 10 ^ s⌋ * 10 ^ s`. The
grid step never exceeds the rounded amount itself (`10 ^ s ≤ |roundedAmount|`),
so the truncation always keeps the leading digit. A fractional `amountDeposit`
must be canonical and its exponent within the `roundToExponent` domain
(`-81 ≤ exponent`, i.e. `|amountDeposit| ≥ 10 ^ (-66)`). -/
theorem Vault.roundedDepositAmount_bounds (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false →
      amountDeposit.IOUCanonical ∧ (-81 : ℤ) ≤ amountDeposit.exponent)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false :=
  Vault.roundedDepositAmount_bounds_proof v amountDeposit roundedAmount hcanon hrounded

/-- Witness: the truncation in `roundedDepositAmount_bounds` is not vacuous, a
lawful vault and an `amountDeposit` exist where digits are actually dropped. -/
theorem Vault.roundedDepositAmount_truncation_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.Lawful ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat := sorry

/-- An integral `amountDeposit` passes through `roundedDepositAmount`
unchanged. -/
theorem Vault.roundedDepositAmount_integral (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) -- an integral vault's amounts are integral
    (hnz : amountDeposit.isZero = false) :
    v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) :=
  Vault.roundedDepositAmount_integral_proof v amountDeposit hint hnz

/-! ## `Vault.deposit` -/

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem Vault.deposit_donation (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 :=
  Vault.deposit_donation_proof v amountDeposit roundedAmount r hrounded hok herr


/-- When the vault's exchange rate still equals `10 ^ scale`, the ideal share
amount is the empty-vault formula: pricing an empty vault at `10 ^ scale` is
the special case of the general formula, not a different rule. -/
theorem Vault.idealSharesDeposit_initial_rate (amount : ℚ)
    (hv : v.Lawful) -- the starting vault is lawful
    (hrate : (v.toExact.sharesTotal : ℚ) = v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat :=
  Vault.idealSharesDeposit_initial_rate_proof v hv amount hrate

/-- A larger rounded amount never buys fewer shares from the same vault. -/
theorem Vault.deposit_shares_monotone
    (hv : v.Lawful) -- the starting vault is lawful
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    -- both deposited amounts are positive, the preflight guard
    (hpos₁ : 0 < amountDeposit₁.toRat)
    (hpos₂ : 0 < amountDeposit₂.toRat)
    -- both amounts round to a nonzero roundedAmount
    (hrounded₁ : v.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : v.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    -- both deposits succeed, each starting from the same vault v
    (hok₁ : v.deposit amountDeposit₁ false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.deposit amountDeposit₂ false = .ok r₂) (herr₂ : r₂.error = none)
    -- the first rounded amount is at most the second
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    -- the first deposit is issued at most as many shares
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat := sorry

/-- Issued shares are a nonnegative integer matching `idealSharesDeposit` of
`roundedAmount` up to the `Number` stage error and the final truncation: at
most `depositε` relatively above, less than one whole share plus `depositε`
below. -/
theorem Vault.deposit_sharesIssued (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hcanon : roundedAmount.Canonical) -- the rounded amount is stored canonically
    (hpos : 0 < roundedAmount.toRat) -- the rounded amount is positive, the preflight guard
    -- the net asset value clears the deep-underflow threshold of the Number line
    (hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - depositε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + depositε) :=
  Vault.deposit_sharesIssued_proof v amountDeposit roundedAmount r hv hcanon hpos hnav
    hrounded hok herr

/-- Witness: the truncation term in `deposit_sharesIssued` cannot be dropped, a
run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem Vault.deposit_sharesIssued_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesIssued
        (v.idealSharesDeposit roundedAmount.toRat) depositε := sorry

/-- The taken amount `amountDeposit'` never exceeds `amountDeposit`, is at
most `depositε` relatively below the exact value of the issued shares, and
overpays it by at most the stage budget plus 2 ULP. -/
theorem Vault.deposit_charge (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) ≤ r.amountDeposit'.toRat ∧
    -- amountDeposit' overpays the issued shares' worth by at most the relative
    -- stage error plus 2 ULP (the other direction is already capped by the
    -- relative conjunct)
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      v.idealChargeDeposit r.sharesIssued.toRat * depositε +
        2 * (10 : ℚ) ^ r.amountDeposit'.exponent := sorry

/-- Witness: the ULP term in `deposit_charge` cannot be dropped, a run exists
whose taken amount misses the exact share value by more than `depositε`
relative. -/
theorem Vault.deposit_charge_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.amountDeposit'
        (v.idealChargeDeposit r.sharesIssued.toRat) depositε := sorry

/-- Integral strengthening of `deposit_charge`: the overcharge stays below
one whole unit plus the stage error. -/
theorem Vault.deposit_charge_integral (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε := sorry

/-- Both stored totals are the old value plus `amountDeposit'`, up to the
`depositε` relative error of the `Number` addition, and the share total
update is exact whenever the sum is representable. -/
theorem Vault.deposit_vault_updates (amountDeposit : STAmount) (isDonation : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none) :
    -- assetsTotal' = assetsTotal + taken amount, within depositε
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable + taken amount, within depositε
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal + issued shares, exactly, whenever the
    -- sum fits in the share domain (int64)
    ((v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat) := sorry

/-! ### Witness data for `deposit_vault_updates_attained`

An int64 vault holding `9000000000000000007` (a canonical 19-digit balance) with
`1e18` shares outstanding, nothing lent. A donation of the integral amount
`9000000000000000006` makes the exact new total `18000000000000000013`, which is
20 digits and rounds to nearest at 19 significant digits, storing
`18000000000000000010`. That stored value differs from the exact sum, so the
`depositε` error term in `deposit_vault_updates` cannot be dropped. -/

/-- The witness vault. -/
def wvDVU : Vault :=
  { assetsTotal := ⟨false, 9000000000000000007, 0⟩
  , assetsAvailable := ⟨false, 9000000000000000007, 0⟩
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness donation amount, `9000000000000000006` int64. -/
def waDVU : STAmount := STAmount.unchecked .int64 9000000000000000006 0 false

/-- The post-donation vault: both asset fields store `18000000000000000010`, the
exact sum `18000000000000000013` rounded to 19 significant digits. -/
def wvDVU' : Vault :=
  { assetsTotal := ⟨false, 1800000000000000001, 1⟩
  , assetsAvailable := ⟨false, 1800000000000000001, 1⟩
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness deposit result. -/
def wrDVU : DepositResult := ⟨none, wvDVU', waDVU, STAmount.zero .int64⟩

section
set_option maxRecDepth 10000

/-- Hand trace of the `Number` addition `9000000000000000007 + 9000000000000000006`
to nearest: the exact 20-digit sum drops one digit (rounded down) to
`18000000000000000010`. Stepped through the WF pipeline because the kernel does
not reduce it. -/
private theorem wvDVU_add :
    Number.operator_add ⟨false, 9000000000000000007, 0⟩ ⟨false, 9000000000000000006, 0⟩ .to_nearest
      = .ok ⟨false, 1800000000000000001, 1⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 9000000000000000006, 0⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 9000000000000000007, 0⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 9000000000000000007, 0⟩ : Number).operator_eq
      (⟨false, 9000000000000000006, 0⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((0 : Int) < 0)), if_neg (by decide : ¬ ((0 : Int) > 0)),
    show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (9000000000000000007 : UInt64) + toUInt128 (9000000000000000006 : UInt64)
      = (18000000000000000013 : UInt128) from by decide]
  rw [show (decide ((18000000000000000013 : UInt128) > toUInt128 largeRange.max) ||
           decide ((18000000000000000013 : UInt128) > toUInt128 maxRepUp)) = true from by decide]
  simp only [if_true]
  rw [show Guard.new.doDropDigit128 (18000000000000000013 : UInt128) 0
      = ({ digits_ := 3458764513820540928, xbit_ := false, sbit_ := false },
         (1800000000000000001 : UInt128), (1 : Int)) from by
    unfold Guard.doDropDigit128 Guard.new Guard.push; rfl]
  simp only
  rw [show toUInt64 (1800000000000000001 : UInt128) = (1800000000000000001 : UInt64) from by decide]
  rw [show ({ digits_ := 3458764513820540928, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (1800000000000000001 : UInt64) (1 : Int) largeRange.min largeRange.max .to_nearest
      "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 1800000000000000001, exponent_ := 1 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize doNormalize
  rw [show (((1800000000000000001 : UInt64)) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUp largeRange.min (1800000000000000001 : UInt64) 1
        = ((1800000000000000001 : UInt64), (1 : Int)) by unfold doNormalize_scaleUp; rw [if_neg (by decide)],
     show doNormalize_scaleDown largeRange.max (1800000000000000001 : UInt64) (1 : Int) Guard.new
        = .ok ((1800000000000000001 : UInt64), (1 : Int), Guard.new) by
        unfold doNormalize_scaleDown; rw [dif_neg (by decide)]]
  simp only []
  rw [show ((1 : Int) < minExponent || (1800000000000000001 : UInt64) < largeRange.min) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (1800000000000000001 : UInt64) (1 : Int) Guard.new
        = .ok ((1800000000000000001 : UInt64), (1 : Int), Guard.new) from by
      unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  rw [show Guard.new.doRoundUp false (1800000000000000001 : UInt64) (1 : Int)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 1800000000000000001, exponent_ := 1 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `waDVU` converts to the `Number` `9000000000000000006` (normalize identity). -/
private theorem wvDVU_amt_toNumber : waDVU.toNumber .to_nearest = .ok ⟨false, 9000000000000000006, 0⟩ := by
  unfold STAmount.toNumber waDVU
  rw [if_pos (show (STAmount.unchecked .int64 9000000000000000006 0 false).integral = true from rfl),
    show (STAmount.unchecked .int64 9000000000000000006 0 false).intAmount
        = .ok { value := 9000000000000000006 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show (STAmount.unchecked .int64 9000000000000000006 0 false).integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 9000000000000000006 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 9000000000000000006 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_id .to_nearest false 9000000000000000006 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]

/-- `roundToVaultExponent` returns an integral amount unchanged. -/
private theorem wvDVU_round : roundToVaultExponent waDVU wvDVU.assetsTotal = .ok waDVU := by
  unfold roundToVaultExponent; rw [if_pos (show waDVU.integral = true from rfl)]; rfl

/-- The witness donation runs to `wrDVU`. -/
private theorem wvDVU_run : wvDVU.deposit waDVU true = .ok wrDVU := by
  show wvDVU.deposit waDVU true = .ok ⟨none, wvDVU', waDVU, STAmount.zero .int64⟩
  unfold Vault.deposit
  rw [wvDVU_round]
  simp only [ok_bind]
  rw [if_neg (show ¬ (waDVU.isZero = true) from by decide),
    if_neg (show ¬ ((true && wvDVU.sharesTotal.mantissa_ == 0) = true) from by decide),
    if_neg (show ¬ ((wvDVU.isInsolvent && !true) = true) from by simp)]
  simp only [if_true, pure_bind, wvDVU_amt_toNumber, zero_int64_toNumber, ok_bind]
  simp only [show wvDVU.assetsTotal = (⟨false, 9000000000000000007, 0⟩ : Number) from rfl,
             show wvDVU.assetsAvailable = (⟨false, 9000000000000000007, 0⟩ : Number) from rfl,
             show wvDVU.sharesTotal = (⟨false, 1000000000000000000, 0⟩ : Number) from rfl,
             wvDVU_add, operator_add_zero_right, ok_bind]
  rw [show wvDVU.assetsMaximum = (none : Option Number) from rfl]
  simp only [Option.any_none, Bool.false_eq_true, if_false]
  show pure _ = Except.ok wrDVU
  rfl

/-- The witness vault is lawful. -/
private theorem wvDVU_lawful : wvDVU.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 9000000000000000007, 0⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 9000000000000000007, 0⟩ : Number).isNormalized; norm_isNormalized
  · intro m hm; rw [show wvDVU.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 1000000000000000000, 0⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 1000000000000000000, 0⟩ : Number).toRat; rw [toRat_nat_exp0]; norm_num
  · show (⟨false, 1000000000000000000, 0⟩ : Number).toRat.den = 1
    rw [toRat_nat_exp0]; decide
  · intro _; rfl
  · decide
  · have hAT : wvDVU.toExact.assetsTotal = 9000000000000000007 := by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num
    have hAA : wvDVU.toExact.assetsAvailable = 9000000000000000007 := by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num
    have hI : wvDVU.toExact.interestUnrealized = 0 := by
      simp only [Vault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hL : wvDVU.toExact.lossUnrealized = 0 := by
      simp only [Vault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hST : wvDVU.toExact.sharesTotal = 1000000000000000000 := by
      simp only [Vault.toExact]
      rw [show wvDVU.sharesTotal = (⟨false, 1000000000000000000, 0⟩ : Number) from rfl, toRat_nat_exp0]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]; norm_num
    · rw [hAA]; norm_num
    · rw [hAT, hAA]
    · intro m hm; rw [show wvDVU.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
    · intro h; rw [hST] at h; norm_num at h
    · intro m hm; rw [show wvDVU.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]; norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]; norm_num
    · intro _; rw [hI, hAT]; norm_num
    · rw [hAT, hI, hL]; norm_num
    · intro h; rw [hI] at h; norm_num at h

end

/-- Witness: the error term in `deposit_vault_updates` cannot be dropped, a run
exists where the stored total is not the exact sum. The int64 witness `wvDVU`
donates `9000000000000000006`; the stored total `18000000000000000010` differs
from the exact sum `18000000000000000013`. -/
theorem Vault.deposit_vault_updates_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (r : DepositResult),
      v.Lawful ∧ v.deposit amountDeposit isDonation = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat := by
  refine ⟨wvDVU, waDVU, true, wrDVU, wvDVU_lawful, wvDVU_run, rfl, ?_⟩
  show (⟨false, 1800000000000000001, 1⟩ : Number).toRat ≠ wvDVU.toExact.assetsTotal + waDVU.toRat
  rw [Number.toRat_of_nonneg _ rfl,
    show (⟨false, 1800000000000000001, 1⟩ : Number).mantissa_.toNat = 1800000000000000001 from by decide,
    show (⟨false, 1800000000000000001, 1⟩ : Number).exponent_ = 1 from rfl,
    show wvDVU.toExact.assetsTotal = 9000000000000000007 from by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num,
    show waDVU.toRat = 9000000000000000006 from by
      unfold STAmount.toRat waDVU STAmount.unchecked
      rw [show ((STAmount.mk .int64 9000000000000000006 0 false).mValue).toNat = 9000000000000000006 from by decide]
      norm_num [Rat.mkRat_one]]
  norm_num

/-- Integral strengthening of `deposit_vault_updates`: in-domain integer
sums are stored exactly. -/
theorem Vault.deposit_vault_updates_integral (amountDeposit : STAmount) (isDonation : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (r : DepositResult)
    (hnt : v.numericType = .int64 ∨ v.numericType = .native) -- the vault holds an integral asset
    (hcanon : amountDeposit.IntegralCanonical) -- an integral vault's amounts are integral
    (hty : amountDeposit.mNumericType = v.numericType) -- the deposit is in the vault's asset
    -- an integral vault's stored totals are integers
    (hdenA : v.assetsTotal.toRat.den = 1)
    (hdenAv : v.assetsAvailable.toRat.den = 1)
    (hok : v.deposit amountDeposit isDonation = .ok r) (herr : r.error = none)
    -- the new total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable + r.amountDeposit'.toRat :=
  Vault.deposit_vault_updates_integral_proof v amountDeposit isDonation hv r hnt hcanon hty
    hdenA hdenAv hok herr hsz

/-- The `assetsMaximum` guard checks `assetsTotal'`, which the caller cannot
know in advance, but `assetsTotal + roundedAmount` bounds the true new total,
and rounding it cannot cross the maximum: a lawful `assetsMaximum` is
normalized, so it lies on the `Number` line, and rounding to nearest never
lands above a point of the line the true value was at or under. No error
margin is needed. -/
theorem Vault.deposit_under_maximum (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : v.deposit amountDeposit isDonation = .ok r)
    -- assetsTotal + roundedAmount fits under the maximum m
    (hmargin : ∀ m ∈ v.assetsMaximum,
      v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    -- the assetsMaximum guard cannot fire
    r.error ≠ some .tecLIMIT_EXCEEDED := sorry

end XRPL.Model.SingleAssetVault
