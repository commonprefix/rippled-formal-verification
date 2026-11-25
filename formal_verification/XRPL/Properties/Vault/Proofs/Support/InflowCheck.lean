import XRPL.Properties.Vault.Proofs.Support.IOUTotality
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale

/-! # The deposit inflow check

C++ `checkOptionalVaultInflow` rounds the deposit toward zero at its posterior exponent before it checks it. A deposit
passes a charge it already rounded that way, so the check reads the charge as it is. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The inflow check on the charge as it is, without the rounding C++ applies first. -/
def Vault.checkOpenLimitUnrounded (v : Vault) (amount : STAmount) : Except Error TER := do
  let assetsTotal ← v.assetsTotal
  let amountNum ← amount.toNumber .to_nearest
  let exponent ← postSumExponent assetsTotal amountNum v.baseExponent v.numericType

  if exponent != v.baseExponent then
    return .tecLIMIT_EXCEEDED

  let exceedsOpenLimit ← v.exceedsOpenLimit amountNum
  if exceedsOpenLimit then
    return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

/-- A charge as a deposit computes it: an amount of the vault's asset clamped onto the post-sum grid of the vault's
total. An IOU amount is canonical or zero and nonnegative. -/
def Vault.ClampedCharge (v : Vault) (charge : STAmount) : Prop :=
  ∃ (A : Number) (a : STAmount), v.assetsTotal = .ok A ∧ a.mNumericType = v.numericType ∧
    (a.integral = false → a.FracCanonZero ∧ 0 ≤ a.toRat) ∧ clampToSumExponent A a v.baseExponent = .ok charge

/-- Rounding a nonnegative IOU amount toward zero onto a grid it already sits on returns it unchanged. -/
lemma STAmount.roundToExponent_towards_zero_of_grid (c : STAmount) (s : ℤ) (hcz : c.FracCanonZero)
    (h0 : 0 ≤ c.toRat) (hk : ∃ k : ℤ, c.toRat = (k : ℚ) * 10 ^ s) (hs_lo : -81 ≤ s) (hs_hi : s ≤ 80) :
    STAmount.roundToExponent c s .towards_zero = .ok c := by
  by_cases hz : c.mValue = 0
  · exact STAmount.roundToExponent_eq_self c s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))
  have hci : c.IOUCanonical := hcz.2.resolve_right hz
  have hneg : c.mIsNegative = false := STAmount.mIsNegative_false_of_nonneg c h0 hz
  obtain ⟨r, hr⟩ := STAmount.roundToExponent_towards_zero_ok c s hci hneg (by omega) hs_hi
  have hrnd := STAmount.roundToExponent_rounded_any c r s .towards_zero hci hs_lo hs_hi hr
  obtain ⟨k, hkv⟩ := hk
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hval : r.toRat = c.toRat := by
    simp only [RoundsToRepresentableAt] at hrnd
    change r.toRat = _ at hrnd
    rw [hrnd, ite_eq_left h0, hkv, mul_div_assoc, div_self hp.ne', mul_one, Int.floor_intCast]
  have hrF : r.FracCanonZero := STAmount.roundToExponent_fczr c r s .towards_zero hcz hr
  have hr0 : r.mValue ≠ 0 := by
    intro h
    have hr0' : r.toRat = 0 := by unfold STAmount.toRat; simp [h]
    exact STAmount.toRat_ne_zero c hz (hval.symm.trans hr0')
  rw [hr, STAmount.eq_of_exactCanonical r c (Or.inl (hrF.2.resolve_right hr0)) (Or.inl hci)
    (hrF.1.trans hcz.1.symm) hr0 hval]

/-- An IOU amount clamped onto the post-sum grid of a nonnegative total also sits on the grid of its own post-sum
exponent. That exponent is no larger, since the clamped amount is no larger than the original. -/
lemma clampToSumExponent_on_own_grid (A : Number) (a c : STAmount) (b : Int) (cn : Number) (e : Int)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (ha : a.FracCanonZero) (ha0 : 0 ≤ a.toRat)
    (hlo : -96 ≤ b) (hhi : b ≤ 80) (h₁ : clampToSumExponent A a b = .ok c)
    (hcN : c.toNumber .to_nearest = .ok cn) (he : postSumExponent A cn b .fractional = .ok e) :
    ∃ k : ℤ, c.toRat = (k : ℚ) * 10 ^ e := by
  by_cases hc0 : c.mValue = 0
  · exact ⟨0, by unfold STAmount.toRat; simp [hc0]⟩
  have hia : a.IOUCanonical := ha.2.resolve_right fun h => hc0 (clampToSumExponent_zero A a c b h h₁)
  obtain ⟨aNum, e₁, haN, he₁, -, hcval⟩ := clampToSumExponent_frac_floor A a c b ha hlo hhi hc0 h₁
  have hcF : c.FracCanonZero := clampToSumExponent_frac_shape A a c b ha h₁
  have hci : c.IOUCanonical := hcF.2.resolve_right hc0
  have hcb := clampToSumExponent_frac_bounds A a c b ha hlo hhi h₁
  obtain ⟨an, han, hanv, hann⟩ := STAmount.toNumber_iou_exact a .to_nearest hia
  obtain ⟨cn', hcn', hcnv, hcnn⟩ := STAmount.toNumber_iou_exact c .to_nearest hci
  rw [han, Except.ok.injEq] at haN
  rw [hcn', Except.ok.injEq] at hcN
  subst haN hcN
  have hnta : a.numericType = .fractional := hia.is_fractional
  rw [hnta] at he₁
  have hle : cn'.toRat ≤ an.toRat := by
    rw [hcnv, hanv]
    have := hcb.2
    rwa [abs_of_nonneg ha0] at this
  have h21 : e ≤ e₁ :=
    postSumExponent_mono A cn' an b e e₁ hA hA0 hcnn hann (by rw [hcnv]; exact hcb.1) hle hlo he he₁
  refine ⟨⌊|a.toRat| / 10 ^ e₁⌋ * 10 ^ (e₁ - e).toNat, ?_⟩
  rw [hcval]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
  congr 2
  ring

/-- The inflow check reads a deposit's charge as it is: the rounding C++ applies first leaves a clamped charge
unchanged. -/
lemma Vault.checkOpenLimit_of_clamped (v : Vault) (charge : STAmount) (h : v.ClampedCharge charge) :
    v.checkOpenLimit charge = v.checkOpenLimitUnrounded charge := by
  obtain ⟨A, a, hat, hty, ha, hcl⟩ := h
  have hbr := v.baseExponent_range
  -- the second clamp returns the charge once its post-sum exponent computes
  have hfix : clampToSumExponent A charge v.baseExponent = .ok charge ∨
      ∃ cn, charge.toNumber .to_nearest = .ok cn ∧ clampToSumExponent A charge v.baseExponent =
        (postSumExponent A cn v.baseExponent v.numericType >>= fun _ => Except.ok charge) := by
    by_cases hint : a.integral = true
    · -- an XRP or MPT amount clamps to its magnitude, which a second clamp keeps
      left
      rw [clampToSumExponent_integral A a _ hint, Except.ok.injEq] at hcl
      subst hcl
      obtain ⟨hnt', -, -, -⟩ := clamp_magnitude a
      have hint' : (if a.negative = true then a.operator_neg else a).integral = true := by
        unfold STAmount.integral at hint ⊢; rw [hnt']; exact hint
      rw [clampToSumExponent_integral A _ _ hint']
      congr 1
      by_cases hn : a.negative = true
      · rw [ite_eq_left hn]
        by_cases hz : a.mValue = 0
        · unfold STAmount.operator_neg; simp [hz]
        · have hpos : a.operator_neg.negative = false := by
            unfold STAmount.operator_neg STAmount.negative at *
            simp [hz, hn]
          rw [ite_eq_right (by simp [hpos])]
      · rw [ite_eq_right hn, ite_eq_right hn]
    · right
      have hfr : a.integral = false := by simpa using hint
      obtain ⟨haF, ha0⟩ := ha hfr
      obtain ⟨hA, hAD⟩ := Vault.assetsTotal_ge_deployed v A hat
      have hA0 : 0 ≤ A.toRat := le_trans v.exact.assetsDeployed_nonneg hAD
      have hcF : charge.FracCanonZero := clampToSumExponent_frac_shape A a charge v.baseExponent haF hcl
      have hcb := clampToSumExponent_frac_bounds A a charge v.baseExponent haF hbr.1 hbr.2 hcl
      have hcfr : charge.integral = false := by unfold STAmount.integral; rw [hcF.1]; rfl
      have hcnt : charge.numericType = .fractional := hcF.1
      have hvnt : v.numericType = .fractional := by rw [← hty]; exact haF.1
      obtain ⟨cn, hcN⟩ : ∃ cn, charge.toNumber .to_nearest = .ok cn := by
        rcases hcF.2 with hci | hz
        · obtain ⟨cn, hcn, -⟩ := STAmount.toNumber_iou_exact charge .to_nearest hci
          exact ⟨cn, hcn⟩
        · exact STAmount.CanonicalOrZero.toNumber_ok (Or.inr (by simp [STAmount.isZero, hz]))
      have hmag : (if charge.negative = true then charge.operator_neg else charge) = charge := by
        by_cases hn : charge.negative = true
        · rw [ite_eq_left hn]
          by_cases hz : charge.mValue = 0
          · unfold STAmount.operator_neg; simp [hz]
          · exact absurd hn (by simp [STAmount.negative, STAmount.mIsNegative_false_of_nonneg charge hcb.1 hz])
        · rw [ite_eq_right hn]
      refine ⟨cn, hcN, ?_⟩
      rw [hvnt]
      cases hps : postSumExponent A cn v.baseExponent .fractional with
      | error err =>
        simp only [clampToSumExponent, hcfr, Bool.false_eq_true, ite_false, hmag, hcN, hcnt, hps, bind,
          Except.bind, pure, Except.pure]
      | ok e =>
        obtain ⟨k, hk⟩ := clampToSumExponent_on_own_grid A a charge v.baseExponent cn e hA hA0 haF ha0
          hbr.1 hbr.2 hcl hcN hps
        obtain ⟨-, -, he_hi⟩ := postSumExponent_range A cn v.baseExponent .fractional e hbr.1 hbr.2 hps
        have he_lo : v.baseExponent ≤ e := (postSumExponent_range A cn v.baseExponent .fractional e hbr.1 hbr.2 hps).1
        simp only [clampToSumExponent, hcfr, Bool.false_eq_true, ite_false, hmag, hcN, hcnt, hps, bind,
          Except.bind, pure, Except.pure]
        exact STAmount.roundToExponent_towards_zero_of_grid charge e hcF hcb.1 ⟨k, hk⟩
          (by have := v.baseExponent_bounds.1; omega) he_hi
  unfold Vault.checkOpenLimit Vault.checkOpenLimitUnrounded
  rw [hat, ok_bind, ok_bind]
  rcases hfix with hfix | ⟨cn, hcN, hfix⟩
  · rw [hfix, ok_bind]
  · rw [hfix, hcN, ok_bind]
    cases hps : postSumExponent A cn v.baseExponent v.numericType with
    | error err => rfl
    | ok e => simp only [ok_bind, hcN, hps]

/-- The charge of a successful deposit computation is a clamped charge, for a deposit of the vault's asset whose IOU
amount is canonical. -/
lemma Vault.deposit_clampedCharge (v : Vault) (amount ra : STAmount) (isDonation : Bool) (amounts : VaultAmounts)
    (hty : amount.mNumericType = v.numericType) (hc : amount.integral = false → amount.IOUCanonical)
    (hra : (v.roundedDepositAmount amount).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts)) :
    v.ClampedCharge amounts.assets := by
  obtain ⟨A₀, -, hcl₀, hnz₀⟩ := roundedDepositAmount_rounded v amount ra hra
  have hm : ra.mValue ≠ 0 := (STAmount.isZero_eq_false_iff _).mp hnz₀
  -- the rounded deposit keeps the amount's type, and an IOU one is a positive canonical amount
  have hrat : ra.mNumericType = v.numericType := by
    by_cases hint : amount.integral = true
    · rw [clampToSumExponent_integral A₀ amount _ hint, Except.ok.injEq] at hcl₀
      rw [← hcl₀, (clamp_magnitude amount).1, hty]
    · have hio := hc (by simpa using hint)
      rw [(clampToSumExponent_frac_shape A₀ amount ra _ ⟨hio.is_fractional, Or.inl hio⟩ hcl₀).1, ← hty,
        hio.is_fractional]
  have hraf : ra.integral = false → ra.FracCanonZero ∧ 0 < ra.toRat := by
    intro hrf
    have hfr : amount.integral = false := by unfold STAmount.integral at hrf ⊢; rw [hty, ← hrat]; exact hrf
    have hio := hc hfr
    have haF : amount.FracCanonZero := ⟨hio.is_fractional, Or.inl hio⟩
    have hb := clampToSumExponent_frac_bounds A₀ amount ra v.baseExponent haF v.baseExponent_range.1
      v.baseExponent_range.2 hcl₀
    exact ⟨clampToSumExponent_frac_shape A₀ amount ra v.baseExponent haF hcl₀,
      lt_of_le_of_ne hb.1 (STAmount.toRat_ne_zero ra hm).symm⟩
  cases isDonation
  · obtain ⟨assets, A, hsh, hsz, hsta, -, hat, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
    have hast := sharesToAssetsDeposit_mNumericType v amounts.shares assets hsta
    refine ⟨A, assets, hat, hast, fun hfr => ?_, hcl⟩
    -- an IOU deposit prices a positive count of shares to a nonnegative IOU amount
    have hrf : ra.integral = false := by unfold STAmount.integral at hfr ⊢; rw [hrat, ← hast]; exact hfr
    obtain ⟨hrF, hrp⟩ := hraf hrf
    have hrc : ra.Canonical := ⟨fun h => absurd h (by rw [hrf]; decide), fun _ => hrF.2.resolve_right hm⟩
    obtain ⟨hshc, hsht⟩ := assetsToSharesDeposit_int64_canonical v ra amounts.shares hsh
    have hshp := assetsToSharesDeposit_pos v ra amounts.shares hrc hrp hsh hsz
    refine ⟨⟨NumericType.eq_fractional_of_not_integral hfr, ?_⟩,
      sharesToAssetsDeposit_nonneg v amounts.shares assets hshc hsht hshp hsta⟩
    exact (sharesToAssetsDeposit_exactCanonical_or_zero v amounts.shares assets hshc hsht hsta).imp_left
      fun hx => hx.iouCanonical hfr
  · obtain ⟨A, -, hat, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
    exact ⟨A, ra, hat, hrat, fun hrf => ⟨(hraf hrf).1, (hraf hrf).2.le⟩, hcl⟩

end XRPL.Model.SingleAssetVault
