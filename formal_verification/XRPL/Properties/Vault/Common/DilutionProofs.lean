import XRPL.Properties.Vault.VaultDeposit
import XRPL.Properties.Vault.Vault
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.Common.RoundToExponentGrid
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Lawful
import XRPL.Properties.Vault.Unchanged

/-! # Cross-operation dilution composition proofs (deposit side)

Proof bodies for the deposit-side dilution headlines in `Dilution.lean`
(`deposit_no_dilution`, `deposit_donation_no_dilution`). Per-share value is
`withdrawNav / sharesTotal`; the headlines are its cross-multiplied
monotonicity statement across one operation.

The composition rests on two facts about any successful deposit: it rewrites
only the three stored balance fields, so the two unrealized fields are
preserved and `withdrawNav` moves by exactly the change in the stored
`assetsTotal` (`deposit_withdrawNav_change`); and a donation issues no shares,
so the share total is unchanged (`deposit_donation_sharesTotal_eq`). The
residual numeric cores are documented at their use sites.

This file also holds the withdraw/clawback single-operation dilution proofs and
the compounding induction `ReachableFromIn.no_dilution_proof` (whose inductive
`Vault.ReachableFromIn` lives in `ReachableDefs`). The induction carries `Lawful`
and the `interest = loss = 0` invariant across steps, so it imports `Lawful` for
the per-operation `*_lawful` theorems, `Unchanged` for the `*_error_unchanged`
theorems, and `Preservation` for `*_preserves_unrealized`, `*_asset_parity`, and
the result-nonneg / shape lemmas. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- A successful deposit (of any kind) moves `withdrawNav` by exactly the change
in the stored `assetsTotal`: it rewrites only the three balance fields, leaving
`interestUnrealized` and `lossUnrealized` untouched, so they cancel in the
difference. -/
theorem Vault.deposit_withdrawNav_change (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult) (hok : v.deposit amountDeposit isDonation = .ok r)
    (herr : r.error = none) :
    r.vault'.withdrawNav - v.withdrawNav =
      r.vault'.toExact.assetsTotal - v.toExact.assetsTotal := by
  obtain ⟨amount, aD, sC, cN, sN, at', av', st', hround, hamz, hshdon, hinsolv, hdon, hcomp,
    hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit isDonation r hok herr
  subst hr
  show ((at' : Number).toRat - v.lossUnrealized.toRat)
      - (v.assetsTotal.toRat - v.lossUnrealized.toRat)
      = (at' : Number).toRat - v.assetsTotal.toRat
  ring

/-- A successful donation leaves the raw stored share total unchanged: it issues
`STAmount.zero`, whose `Number` is `Number.zero`, and adding it is the
`operator_add` fast path. -/
theorem Vault.deposit_donation_sharesTotal_eq (amountDeposit : STAmount)
    (r : DepositResult) (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.vault'.sharesTotal = v.sharesTotal := by
  obtain ⟨amount, aD, sC, cN, sN, at', av', st', hround, hamz, hshdon, hinsolv, hdon, hcomp,
    hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit true r hok herr
  obtain ⟨_, hsC⟩ := hdon rfl
  subst hr
  show st' = v.sharesTotal
  have hsNz : sN = Number.zero := by
    rw [hsC, zero_int64_toNumber] at hsN; exact (Except.ok.inj hsN).symm
  rw [hsNz, operator_add_zero_right] at hst
  exact (Except.ok.inj hst).symm

/-- The `toExact` share projection is likewise unchanged by a successful
donation. -/
theorem Vault.deposit_donation_sharesTotal_toExact (amountDeposit : STAmount)
    (r : DepositResult) (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal := by
  have h := Vault.deposit_donation_sharesTotal_eq v amountDeposit r hok herr
  show r.vault'.sharesTotal.toRat.num.toNat = v.sharesTotal.toRat.num.toNat
  rw [h]

/-- A `.checked .fractional` of a canonical 16-digit mantissa whose exponent clears
`cMinOffset` lands on the record verbatim, so its value is nonzero. This is the slice of
`checked_iou_cases` that does NOT presuppose `result.mValue ≠ 0`: the exponent lower
bound `cMinOffset ≤ exp` rules out the underflow-to-zero branch, and success rules out
the overflow branch. -/
lemma STAmount.checked_fractional_nonzero (mant : UInt64) (exp : Int) (neg : Bool)
    (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent)
    (hge : cMinOffset ≤ exp)
    (result : STAmount) (hok : STAmount.checked .fractional mant exp neg mode = .ok result) :
    result = ⟨.fractional, mant, exp, neg⟩ := by
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  have h_int : ¬ (STAmount.unchecked .fractional mant exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_sd : (STAmount.unchecked .fractional mant exp neg).signedDrops.toInt64
      = if neg then -mant.toInt64 else mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat < 10 ^ 16 from h_hi),
        signed_mantissa_toInt neg mant h_fit]
    show (STAmount.unchecked .fractional mant exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  have hnhi : ¬ exp > cMaxOffset := by
    intro hhi
    have hb : STAmount.checked .fractional mant exp neg mode = .error .overflow := by
      rw [STAmount.checked]; unfold STAmount.canonicalize
      rw [if_neg h_int, hiou, if_pos hhi]
    rw [hb] at hok; simp at hok
  push_neg at hnhi
  have hexp_lo : (-96 : ℤ) ≤ exp := by unfold cMinOffset at hge; omega
  have hexp_hi : exp ≤ 80 := by unfold cMaxOffset at hnhi; omega
  have hc : (⟨.fractional, mant, exp, neg⟩ : STAmount).IOUCanonical :=
    ⟨rfl, h_lo, h_hi, hexp_lo, hexp_hi⟩
  have hcid := STAmount.canonicalize_canonical_id ⟨.fractional, mant, exp, neg⟩ mode hc
  rw [STAmount.checked,
      show STAmount.unchecked .fractional mant exp neg = (⟨.fractional, mant, exp, neg⟩ : STAmount)
        from rfl, hcid] at hok
  exact (Except.ok.inj hok).symm

/-- Proof body of `Vault.deposit_donation_no_dilution`. The share half is
`deposit_donation_sharesTotal_toExact`. The strict increase reduces, via
`deposit_withdrawNav_change`, to the stored `assetsTotal` strictly rising, split on
whether the donation amount is integral.

* Integral (`amountDeposit.integral = true`): `roundToVaultExponent` passes the amount
  through unchanged and, under the int64-domain hypothesis (`hint_dom`), the stored add
  is exact (`deposit_vault_updates_integral`), so `A' = A + amountDeposit > A`. The
  domain bound is necessary: a lawful (but non-reachable) integral vault with a huge
  `assetsTotal` (ULP above `amountDeposit`) would round the donation away, leaving
  `A' = A`.
* Fractional: the postScale grid argument (`donation_grid_bound`): a surviving donation
  is at least one grid step `10^s ≤ roundedAmount`, and `A < 10^(s+16)`, so
  `A·depositε < 10^s·(1-depositε) ≤ roundedAmount·(1-depositε)`, which with
  `deposit_vault_updates` (`A' ≥ (A + roundedAmount)(1 - depositε)`) gives `A' > A`. -/
theorem Vault.deposit_donation_no_dilution_proof (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    -- integer-domain bound for the integral branch: on an int64/native vault whose stored
    -- totals are whole numbers, the post-donation total stays in the int64 domain, so the
    -- add is exact (ULP = 1) and the donation cannot round away. Vacuous for fractional
    -- amounts. Necessary: the WF predicate is weaker than reachability and admits a `10^30`
    -- integral `assetsTotal` whose ULP swallows a unit donation.
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧
      v.assetsTotal.toRat.den = 1 ∧ v.assetsAvailable.toRat.den = 1 ∧
      v.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal := by
  refine ⟨?_, Vault.deposit_donation_sharesTotal_toExact v amountDeposit r hok herr⟩
  have hchange := Vault.deposit_withdrawNav_change v amountDeposit true r hok herr
  -- Reduce to: the stored assetsTotal strictly increases.
  suffices hAlt : v.toExact.assetsTotal < r.vault'.toExact.assetsTotal by linarith [hchange]
  have hnz : amountDeposit.isZero = false := by
    rcases hz : amountDeposit.isZero with _ | _
    · rfl
    · exfalso
      have hmv : amountDeposit.mValue = 0 := by unfold STAmount.isZero at hz; exact beq_iff_eq.mp hz
      have : amountDeposit.toRat = 0 := by rw [STAmount.toRat_signed, hmv]; simp
      linarith [hpos]
  by_cases hint : amountDeposit.integral = true
  · -- integral donation: passthrough + exact in-domain add
    obtain ⟨hnt, hty, hdenA, hdenAv, hbound⟩ := hint_dom hint
    have hrd : v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) :=
      Vault.roundedDepositAmount_integral v amountDeposit hint hnz
    have hAmt' : r.amountDeposit' = amountDeposit :=
      (Vault.deposit_donation v amountDeposit amountDeposit r hrd hok herr).1
    have hIC : amountDeposit.IntegralCanonical := (hcanon.1 hint).1
    have hbound' : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1 := by
      rw [hAmt']; exact hbound
    obtain ⟨hAT', -⟩ :=
      Vault.deposit_vault_updates_integral_proof v amountDeposit true hv r hnt hIC hty hdenA hdenAv
        hok herr hbound'
    show v.toExact.assetsTotal < r.vault'.toExact.assetsTotal
    show v.toExact.assetsTotal < r.vault'.assetsTotal.toRat
    rw [hAT', hAmt']; linarith [hpos]
  · -- FRACTIONAL BRANCH (postScale grid). `donation_grid_bound` delivers, for the single
    -- post-deposit scale `s`, both the grid-step lower bound `10^s ≤ amount` and the ceiling
    -- `A < 2·10^16·10^s`. With `deposit_vault_updates`'s `A' ≥ (A + amount)(1 - depositε)`, the
    -- residue cannot cancel the donation: `A·depositε < 10^(s-1) < 10^s·(1 - depositε) ≤ amount·(1
    -- - depositε)`, so `A < A'`.
    have hfr : amountDeposit.integral = false := by
      rcases hb : amountDeposit.integral with _ | _
      · rfl
      · exact absurd hb hint
    obtain ⟨amount, aD, sC, cN, sN, at', av', st', hround, hamz, hshdon, hinsolv, hdon, hcomp,
      hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
      Vault.deposit_success_reduces v amountDeposit true r hok herr
    obtain ⟨hAssetEq, -⟩ := hdon rfl
    have hAmt' : r.amountDeposit' = amount := by rw [hr]; exact hAssetEq
    have hamt_nn : 0 ≤ amount.toRat :=
      Vault.roundToVaultExponent_nonneg amountDeposit amount v.assetsTotal hcanon (le_of_lt hpos) hround
    have hamt_mv : amount.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
    have hamt_pos : 0 < amount.toRat :=
      lt_of_le_of_ne hamt_nn (Ne.symm (STAmount.toRat_ne_zero amount hamt_mv))
    obtain ⟨s, hF1, hF2⟩ :=
      Vault.donation_grid_bound v hv amountDeposit amount hcanon hfr hpos hround hamz
    have hF2' : v.toExact.assetsTotal < 2 * 10 ^ 16 * (10 : ℚ) ^ s := hF2
    have hAnn : 0 ≤ v.toExact.assetsTotal := hv.valid.assetsTotal_nonneg
    have hpow_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
    have hkey : v.toExact.assetsTotal * depositε < amount.toRat * (1 - depositε) := by
      rw [depositε_eq]; nlinarith [hF1, hF2', hpow_pos]
    have hru := (Vault.deposit_vault_updates v amountDeposit true hv hcanon hpos r hok herr).1
    rw [hAmt'] at hru
    simp only [RoundsWithin, RatValued.toRat] at hru
    have hsum_nn : 0 ≤ v.toExact.assetsTotal + amount.toRat := add_nonneg hAnn (le_of_lt hamt_pos)
    rw [abs_of_nonneg hsum_nn] at hru
    have hru2 := abs_le.mp hru
    show v.toExact.assetsTotal < r.vault'.assetsTotal.toRat
    nlinarith [hkey, hru2.1]

/-- Shares-positive and the raw-stage update lower bound for a successful
non-donation deposit: the issued shares are a positive count, and the stored
`assetsTotal` after the deposit is within one `operator_add` stage
(`6/(2^63-3)`) below `assetsTotal + amountDeposit'`. Both come from
`deposit_success_reduces` and `operator_add_nonneg_rounds`. -/
theorem Vault.deposit_nonneg_and_update_lower (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    0 < r.sharesIssued.toRat ∧
    (v.toExact.assetsTotal + r.amountDeposit'.toRat) * (1 - 6 / (2 ^ 63 - 3)) ≤
      r.vault'.toExact.assetsTotal := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, hshdon, hinsolv, hdon, hcomp,
    hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  have hamCanon : am.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit am v.assetsTotal hcanon hround
      with hc | hz
    · exact hc
    · rw [hz] at hamz; exact absurd hamz (by decide)
  have ham_nn : 0 ≤ am.toRat :=
    Vault.roundToVaultExponent_nonneg amountDeposit am v.assetsTotal hcanon (le_of_lt hpos) hround
  have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
  have ham_pos : 0 < am.toRat :=
    lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
  obtain ⟨shares, hats, hshz, hsad, _, hseq⟩ :=
    computeDeposit_success_reduces v am aD sC (hcomp rfl)
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v hv am shares hamCanon ham_pos hats hshz
  obtain ⟨hval, hnorm⟩ :=
    sharesToAssetsDeposit_toNumber_exact v hv shares aD cN hshc hshnt hsad hcN
  have hcN_nn : 0 ≤ cN.toRat := by
    rw [hval]; exact sharesToAssetsDeposit_nonneg v hv shares aD hshc hshnt hshpos hsad
  have hAnn : 0 ≤ v.assetsTotal.toRat := hv.valid.assetsTotal_nonneg
  have hru := operator_add_nonneg_rounds v.assetsTotal cN at' hv.wf.assetsTotal_norm hnorm
    hAnn hcN_nn hat
  have hT_nn : 0 ≤ v.assetsTotal.toRat + cN.toRat := add_nonneg hAnn hcN_nn
  simp only [RoundsWithin, RatValued.toRat] at hru
  rw [abs_of_nonneg hT_nn] at hru
  have habs := abs_le.mp hru
  subst hr
  refine ⟨by show 0 < sC.toRat; rw [hseq]; exact hshpos, ?_⟩
  show (v.assetsTotal.toRat + aD.toRat) * (1 - 6 / (2 ^ 63 - 3)) ≤ at'.toRat
  rw [← hval]
  nlinarith [habs.1, hru]

/-- Raw-stage charge lower bound (cross-multiplied) for a successful non-donation
deposit into a nonempty vault with no unrealized interest (`depositNav =
assetsTotal`) whose taken amount is nonzero (`hcnz`, the `isZero = false`
precondition class of `deposit_charge` conjunct 2, ruling out the deep
fractional charge underflow): the taken amount times the share total is at least
the issued shares' `assetsTotal`-worth, deflated by the raw pipeline stage
`19/(2^63-3)`. Composes `sharesToAssetsDeposit_charge_nonempty_raw` (the `Q` band,
whose nonzero branch the nonzero charge selects) with the upward `ofNumber`
floor. -/
theorem Vault.deposit_charge_lower (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hcnz : r.amountDeposit'.isZero = false)
    (hSpos : 0 < (v.toExact.sharesTotal : ℚ))
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    v.toExact.assetsTotal * r.sharesIssued.toRat * (1 - 19 / (2 ^ 63 - 3)) ≤
      r.amountDeposit'.toRat * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, hshdon, hinsolv, hdon, hcomp,
    hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r hok herr
  have haDeq : r.amountDeposit' = aD := by rw [hr]
  have hSnat : 0 < v.toExact.sharesTotal := by exact_mod_cast hSpos
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le hv.valid.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd ((Vault.isInsolvent_iff v hv).mpr ⟨h.symm, hSnat⟩) (by rw [hinsolv rfl]; decide)
  have hmz : v.assetsTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hApos)
  obtain ⟨shares, hats, hshz, hsad, _, hseq⟩ :=
    computeDeposit_success_reduces v am aD sC (hcomp rfl)
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hamCanon : am.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit am v.assetsTotal hcanon hround
      with hc | hz
    · exact hc
    · rw [hz] at hamz; exact absurd hamz (by decide)
  have ham_nn : 0 ≤ am.toRat :=
    Vault.roundToVaultExponent_nonneg amountDeposit am v.assetsTotal hcanon (le_of_lt hpos) hround
  have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
  have ham_pos : 0 < am.toRat :=
    lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v hv am shares hamCanon ham_pos hats hshz
  have hideal_eq : v.idealChargeDeposit shares.toRat =
      v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold Vault.idealChargeDeposit Vault.depositNav
    rw [if_neg (ne_of_gt hApos)]
  obtain ⟨Q, hcQ, hidpos, hQnz, hQz⟩ :=
    sharesToAssetsDeposit_charge_nonempty_raw v hv shares aD hshc hshnt hshpos hmz hsad
  -- nonzero charge selects the nonzero `Q` branch
  have haDnz : aD.mValue ≠ 0 := by
    have hz : aD.isZero = false := haDeq ▸ hcnz
    unfold STAmount.isZero at hz; exact ne_of_beq_false hz
  have hQm : Q.mantissa_ ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward aD hint hcQ haDnz
    · have hfrac : v.numericType = .fractional := by
        cases hnt : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
      exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .upward aD hfrac hcQ haDnz
  obtain ⟨hQnorm, hQneg, hband⟩ := hQnz hQm
  rw [hideal_eq] at hband
  have hfloor : Q.toRat ≤ aD.toRat :=
    STAmount.ofNumber_upward_ge v.numericType Q aD hQnorm hQneg hcQ haDnz
  subst hr
  rw [hseq]
  -- goal: A·shares·(1-δc) ≤ aD·S, from aD ≥ Q ≥ ideal(1-δc) and ideal·S = A·shares
  have hbandle := abs_le.mp hband
  have hAmul : v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) *
      (v.toExact.sharesTotal : ℚ) = v.toExact.assetsTotal * shares.toRat := by
    field_simp
  have hQlowS :
      v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) *
          (1 - 19 / (2 ^ 63 - 3)) * (v.toExact.sharesTotal : ℚ)
        ≤ Q.toRat * (v.toExact.sharesTotal : ℚ) :=
    mul_le_mul_of_nonneg_right (by nlinarith [hbandle.1]) (le_of_lt hSpos)
  have hQS : Q.toRat * (v.toExact.sharesTotal : ℚ) ≤ aD.toRat * (v.toExact.sharesTotal : ℚ) :=
    mul_le_mul_of_nonneg_right hfloor (le_of_lt hSpos)
  nlinarith [hQlowS, hQS, hAmul]

/-- **Composition core** (with `interestUnrealized = lossUnrealized = 0`, so
`withdrawNav = assetsTotal = A` for both states). Given the charge lower bound in
cross-multiplied form `A·x·(1-δc) ≤ c·S` and the update lower bound
`(A+c)(1-δu) ≤ A'`, with the two raw `Number` stage errors summing under the
budget `ε`, per-share value does not drop by more than `1-ε`:
`A·(S+x)·(1-ε) ≤ A'·S`. Reused verbatim by the withdraw/clawback siblings. -/
lemma deposit_no_dilution_arith (A S x c A' δc δu ε : ℚ)
    (hS : 0 < S) (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hcS : A * x * (1 - δc) ≤ c * S)
    (hA' : (A + c) * (1 - δu) ≤ A')
    (hδu0 : 0 ≤ δu) (hδc0 : 0 ≤ δc) (hsum : δu + δc ≤ ε) (hε1 : ε ≤ 1) :
    A * (S + x) * (1 - ε) ≤ A' * S := by
  have h1u : (0 : ℚ) ≤ 1 - δu := by linarith
  have hAS' : (A + c) * (1 - δu) * S ≤ A' * S := mul_le_mul_of_nonneg_right hA' (le_of_lt hS)
  have key1 : A * x * (1 - δc) * (1 - δu) ≤ c * S * (1 - δu) :=
    mul_le_mul_of_nonneg_right hcS h1u
  have hbracket : (0 : ℚ) ≤ ε - δc - δu + δc * δu := by nlinarith [mul_nonneg hδc0 hδu0]
  have t1 : (0 : ℚ) ≤ A * S * (ε - δu) := mul_nonneg (mul_nonneg hA (le_of_lt hS)) (by linarith)
  have t2 : (0 : ℚ) ≤ A * x * (ε - δc - δu + δc * δu) :=
    mul_nonneg (mul_nonneg hA hx) hbracket
  nlinarith [hAS', key1, t1, t2]

/-- **Withdraw/clawback composition core** (with `interestUnrealized =
lossUnrealized = 0`, so `withdrawNav = assetsTotal = A` for both states). Given the
payout upper bound in the exchange form `p ≤ A·x/S·(1+δc)`, the update lower bound
`(A-p)(1-δu) ≤ A'`, the payout not exceeding the assets (`0 ≤ A - p`), and the
near-final margin `2·x ≤ S` (at least half the shares remain to absorb the interior
overpay `~A·x·δc/S`), with the two raw `Number` stage errors summing under the budget
`ε`, per-share value does not drop by more than `1-ε`: `A·(S-x)·(1-ε) ≤ A'·S`. Reused
by both the withdraw and clawback siblings. -/
lemma withdraw_no_dilution_arith (A S x p A' δc δu ε : ℚ)
    (hS : 0 < S) (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hmargin : 2 * x ≤ S)
    (hp : p ≤ A * x / S * (1 + δc))
    (hA' : (A - p) * (1 - δu) ≤ A')
    (hδu0 : 0 ≤ δu) (hδc0 : 0 ≤ δc) (hδu1 : δu ≤ 1) (hsum : δu + δc ≤ ε) :
    A * (S - x) * (1 - ε) ≤ A' * S := by
  have h1u : (0 : ℚ) ≤ 1 - δu := by linarith
  -- clear the `/S` in the payout bound: `p·S ≤ A·x·(1+δc)`
  have hpS : p * S ≤ A * x * (1 + δc) := by
    have := mul_le_mul_of_nonneg_right hp (le_of_lt hS)
    rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hS)] at this
  -- push the update lower bound to `·S`
  have hAS' : (A - p) * (1 - δu) * S ≤ A' * S := mul_le_mul_of_nonneg_right hA' (le_of_lt hS)
  -- the interior overpay budget: `S-x ≥ x` absorbs `x·δc·(1-δu)` inside `(S-x)(ε-δu)`
  have hmarg : x ≤ S - x := by linarith
  have hbudget : (0 : ℚ) ≤ ε - δu - δc + δc * δu := by nlinarith [mul_nonneg hδc0 hδu0]
  have t1 : (0 : ℚ) ≤ A * (S - x - x) * (ε - δu) :=
    mul_nonneg (mul_nonneg hA (by linarith)) (by linarith)
  have t2 : (0 : ℚ) ≤ A * x * (ε - δu - δc + δc * δu) :=
    mul_nonneg (mul_nonneg hA hx) hbudget
  nlinarith [hAS', hpS, t1, t2, mul_nonneg hA hx, h1u, mul_nonneg (mul_nonneg hA hx) hδc0]

/-- Proof body of `Vault.deposit_no_dilution`. Under `interestUnrealized =
lossUnrealized = 0` (so `withdrawNav = assetsTotal`), `deposit_withdrawNav_change`
and `deposit_vault_updates`'s exact share conjunct reduce the goal to
`deposit_no_dilution_arith` on `A = assetsTotal`, `A' = assetsTotal'`,
`x = sharesIssued`. The two remaining `have`s are the raw-stage bounds (documented
at their sites); the headline `depositε`-level bounds would over-count to
`(1-depositε)^2`, hence the raw constants. -/
theorem Vault.deposit_no_dilution_proof (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hL : v.toExact.lossUnrealized = 0)
    (hcnz : r.amountDeposit'.isZero = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  -- withdrawNav collapses to assetsTotal on both states (interest = loss = 0, preserved).
  have hNav_v : v.withdrawNav = v.toExact.assetsTotal := by
    unfold Vault.withdrawNav; rw [hL]; ring
  have hchange := Vault.deposit_withdrawNav_change v amountDeposit false r hok herr
  have hNav_r : r.vault'.withdrawNav = r.vault'.toExact.assetsTotal := by
    rw [hNav_v] at hchange; linarith
  -- the share total rises by exactly the issued shares (in-domain).
  have hupd := Vault.deposit_vault_updates v amountDeposit false hv hcanon hpos r hok herr
  have hSharesEq : (r.vault'.toExact.sharesTotal : ℚ) =
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat := hupd.2.2 hSsz
  rw [ge_iff_le, hNav_r, hNav_v, hSharesEq]
  -- basic sign facts
  have hAnn : 0 ≤ v.toExact.assetsTotal := hv.valid.assetsTotal_nonneg
  have hbounds := Vault.deposit_nonneg_and_update_lower v amountDeposit r hv hcanon hpos hok herr
  have hxnn : 0 ≤ r.sharesIssued.toRat := le_of_lt hbounds.1
  -- the shares total is positive unless the vault is empty (`empty_shares` invariant).
  rcases eq_or_lt_of_le (by exact_mod_cast Nat.zero_le v.toExact.sharesTotal :
      (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ)) with hS0 | hSpos
  · -- S = 0 ⇒ assetsTotal = 0 (empty_shares) ⇒ both sides are 0.
    have hSnat : v.toExact.sharesTotal = 0 := by exact_mod_cast hS0.symm
    have hA0 : v.toExact.assetsTotal = 0 := (hv.valid.empty_shares hSnat).1
    rw [← hS0, hA0]; simp
  · -- S > 0: apply the composition core with the two raw-stage bounds.
    refine deposit_no_dilution_arith v.toExact.assetsTotal (v.toExact.sharesTotal : ℚ)
      r.sharesIssued.toRat r.amountDeposit'.toRat r.vault'.toExact.assetsTotal
      (19 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3)) depositε hSpos hxnn hAnn ?_ ?_
      (by norm_num) (by norm_num) (by rw [depositε_eq]; norm_num) (by rw [depositε_eq]; norm_num)
    · -- charge lower bound at the raw pipeline stage `19/(2^63-3)`.
      exact Vault.deposit_charge_lower v amountDeposit r hv hcanon hpos hcnz hSpos hok herr
    · -- update lower bound at the raw `operator_add` stage `6/(2^63-3)`.
      exact hbounds.2

/-! ## Withdraw / clawback dilution -/

/-- Raw-stage sibling of `Number.sub_recovery_rounds_within`: a `to_nearest`
subtraction of a (possibly-zero) recovery from a normalized nonnegative operand rounds
within the raw `6/(2^63-3)` stage error, not the widened `depositε`. The zero recovery
is exact, equal operands cancel to zero, and a genuine nonzero difference clears the
underflow threshold so `operator_sub_rounds_to_nearest` applies directly. The dilution
composition needs this tighter granularity: budgeting the subtraction at `depositε`
alone would over-count the concentration error past the headline `1 - depositε`. -/
lemma Number.sub_recovery_rounds_within_raw (x arn result : Number) (E : Int)
    (hx : x.isNormalized) (hxsign : x.negative_ = false)
    (hxm : arn.mantissa_ ≠ 0 → x.mantissa_ ≠ 0)
    (harn : arn.isNormalized) (harnsign : arn.negative_ = false)
    (hEx : arn.mantissa_ ≠ 0 → E ≤ x.exponent_) (hEarn : arn.mantissa_ ≠ 0 → E ≤ arn.exponent_)
    (hE : minExponent + 18 ≤ E)
    (hok : x.operator_sub arn .to_nearest = .ok result) :
    RoundsWithin result (x.toRat - arn.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  have hεnn : (0 : ℚ) ≤ (6 / (2 ^ 63 - 3 : ℚ)) := by norm_num
  by_cases harnm : arn.mantissa_ = 0
  · have hres : result = x := Number.operator_sub_zero_right x arn result harnm hok
    have harn0 : arn.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero arn harnm
    show |result.toRat - (x.toRat - arn.toRat)| ≤ |x.toRat - arn.toRat| * (6 / (2 ^ 63 - 3 : ℚ))
    rw [hres, harn0]
    have h0 : x.toRat - (x.toRat - 0) = 0 := by ring
    rw [h0, abs_zero]
    exact mul_nonneg (abs_nonneg _) hεnn
  · by_cases heq : x.operator_eq arn = true
    · have hres : result = Number.zero :=
        Number.operator_sub_eq_zero_of_operator_eq x arn result (hxm harnm) harnm heq hok
      have hval : x.toRat = arn.toRat := (operator_eq_iff x arn hx harn).mp heq
      show |result.toRat - (x.toRat - arn.toRat)| ≤ |x.toRat - arn.toRat| * (6 / (2 ^ 63 - 3 : ℚ))
      rw [hres, hval, Number.toRat_zero]
      have h0 : (0 : ℚ) - (arn.toRat - arn.toRat) = 0 := by ring
      rw [h0, abs_zero]
      exact mul_nonneg (abs_nonneg _) hεnn
    · have hresm : result.mantissa_ ≠ 0 :=
        Number.operator_sub_result_ne_zero_of_grid x arn result E hx harn (hxm harnm) harnm hxsign
          harnsign (hEx harnm) (hEarn harnm) hE heq hok
      exact operator_sub_rounds_to_nearest x arn result hx harn (hxm harnm) harnm heq hok hresm

/-- A stored asset field minus a nonnegative priced payout rounds within the raw
`6/(2^63-3)` stage. The payout `pn` is nonnegative and, when nonzero, clears `10⁻⁸¹`,
so both the stored field and the payout sit on a grid whose exponents clear `-99`, and
the raw subtraction bound applies. -/
lemma Vault.stored_sub_payout_raw (stored pn result : Number)
    (hstored_norm : stored.isNormalized) (hstored_nn : 0 ≤ stored.toRat)
    (hpn_norm : pn.isNormalized) (hpn_nn : 0 ≤ pn.toRat)
    (hle : pn.toRat ≤ stored.toRat)
    (hpn_floor : pn.mantissa_ ≠ 0 → (10 : ℚ) ^ (-81 : ℤ) ≤ |pn.toRat|)
    (hsub : stored.operator_sub pn .to_nearest = .ok result) :
    RoundsWithin result (stored.toRat - pn.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  have hpn_pos_of : pn.mantissa_ ≠ 0 → 0 < pn.toRat := fun hm =>
    lt_of_le_of_ne hpn_nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero pn hm))
  have hxm : pn.mantissa_ ≠ 0 → stored.mantissa_ ≠ 0 := fun hm =>
    Number.mantissa_ne_zero_of_toRat_ne_zero (lt_of_lt_of_le (hpn_pos_of hm) hle).ne'
  have hstored_neg : stored.negative_ = false :=
    Number.negative_false_of_norm_nonneg stored hstored_norm hstored_nn
  have hpn_neg : pn.negative_ = false :=
    Number.negative_false_of_norm_nonneg pn hpn_norm hpn_nn
  have hEx : pn.mantissa_ ≠ 0 → (-99 : ℤ) ≤ stored.exponent_ := fun hm => by
    have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ |stored.toRat| := by
      rw [abs_of_nonneg hstored_nn]
      have hp := hpn_floor hm; rw [abs_of_nonneg hpn_nn] at hp; linarith [hle]
    exact Number.exponent_ge_of_abs_toRat_ge stored hstored_norm (hxm hm) hfloor
  have hEpn : pn.mantissa_ ≠ 0 → (-99 : ℤ) ≤ pn.exponent_ := fun hm =>
    Number.exponent_ge_of_abs_toRat_ge pn hpn_norm hm (hpn_floor hm)
  exact Number.sub_recovery_rounds_within_raw stored pn result (-99)
    hstored_norm hstored_neg hxm hpn_norm hpn_neg hEx hEpn (by norm_num [minExponent]) hsub

/-- A stored asset field minus a `sharesToAssetsWithdraw`-priced payout rounds within
the raw `6/(2^63-3)` stage. The payout's `toNumber` lift is value-exact and normalized,
and its `disj`-canonical magnitude clears `10⁻⁸¹`, so `stored_sub_payout_raw` applies.
Shared by the withdraw and clawback dilution proofs (both price through the same
pipeline). -/
lemma Vault.sharesToAssetsWithdraw_sub_stored_raw (v : Vault) (hv : v.Lawful)
    (shares payout : STAmount) (waive : Bool) (pn stored result : Number)
    (hc : shares.Canonical)
    (hprice : v.sharesToAssetsWithdraw shares waive = .ok payout)
    (hnum : payout.toNumber .to_nearest = .ok pn)
    (hpay_nn : 0 ≤ payout.toRat)
    (hstored_norm : stored.isNormalized) (hstored_nn : 0 ≤ stored.toRat)
    (hle : payout.toRat ≤ stored.toRat)
    (hsub : stored.operator_sub pn .to_nearest = .ok result) :
    RoundsWithin result (stored.toRat - payout.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  obtain ⟨hpn_val, hpn_norm⟩ :=
    Vault.sharesToAssetsWithdraw_toNumber_facts v hv shares payout waive pn hc hprice hnum
  have hpn_floor : pn.mantissa_ ≠ 0 → (10 : ℚ) ^ (-81 : ℤ) ≤ |pn.toRat| := fun hm => by
    have hne : pn.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero pn hm
    have hmv : payout.mValue ≠ 0 := fun h0 => hne (by rw [hpn_val, STAmount.toRat_signed, h0]; simp)
    rw [hpn_val]
    exact STAmount.canonical_disj_abs_toRat_ge payout
      (Vault.sharesToAssetsWithdraw_disj_canonical v hv shares payout waive hc hprice hmv) hmv
  have h := Vault.stored_sub_payout_raw stored pn result hstored_norm hstored_nn
    hpn_norm (by rw [hpn_val]; exact hpay_nn) (by rw [hpn_val]; exact hle) hpn_floor hsub
  rwa [hpn_val] at h

/-- A successful withdrawal moves `withdrawNav` by exactly the change in the stored
`assetsTotal`: both the final and the non-final exit rewrite only the three balance
fields, leaving `interestUnrealized` and `lossUnrealized` untouched, so they cancel in
the difference. -/
theorem Vault.withdraw_withdrawNav_change (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.vault'.withdrawNav - v.withdrawNav =
      r.vault'.toExact.assetsTotal - v.toExact.assetsTotal := by
  obtain ⟨cw, aN, sta, hcomp, herr2, han, hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr
  rcases hdisj with ⟨-, -, allAvail, -, hr⟩ |
      ⟨-, sbn, at', av', st', atr, atr', -, hat, -, -, -, hav, hst2, hr⟩
  · subst hr
    simp only [Vault.withdrawNav, Vault.toExact, Number.toRat_zero]; ring
  · subst hr
    simp only [Vault.withdrawNav, Vault.toExact]; ring

/-- Proof body of `Vault.withdraw_no_dilution`. Under `interestUnrealized =
lossUnrealized = 0` (so `withdrawNav = assetsTotal`), the exact-final exit zeroes the
share total (`S' = 0`, both sides `0`); the non-final exit reduces, via
`withdraw_withdrawNav_change` and the exact share subtraction, to
`withdraw_no_dilution_arith` on `A = assetsTotal`, `A' = assetsTotal'`,
`x = sharesBurned`, `p = assets'`. The payout upper bound comes from
`sharesToAssetsWithdraw_spec_raw` (`12/(2^63-3)`) and the update lower bound from the
raw `operator_sub` stage (`6/(2^63-3)`); the near-final margin `sharesBurned ≤
sharesTotal/2` keeps at least half the shares to absorb the interior overpay
`~A·x·δc/S`, so the concentration stays within `depositε`. -/
theorem Vault.withdraw_no_dilution_proof (amount : WithdrawAmount) (r : WithdrawResult)
    (hv : v.Lawful)
    (hL : v.toExact.lossUnrealized = 0)
    (hnav : v.WithdrawNavExact false)
    (hcnz : r.assets'.isZero = false)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hmargin : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  set A : ℚ := v.toExact.assetsTotal with hA_def
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hS_def
  have hAnn : 0 ≤ A := hv.valid.assetsTotal_nonneg
  have hl0 : v.lossUnrealized.toRat = 0 := hL
  have hNav_v : v.withdrawNav = A := by
    unfold Vault.withdrawNav; rw [hL]; ring
  -- reduce the run
  obtain ⟨cw, aN, sta, hcomp, herr2, han, hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces v amount false r hok herr
  rcases hdisj with ⟨-, -, allAvail, -, hr⟩ |
      ⟨hfin', sbn, at', av', st', atr, atr', hsbn, hat, -, -, -, hav, hst2, hr⟩
  · -- exact-final exit: `sharesTotal' = 0`, both sides are `0`
    have hSt0 : (r.vault'.toExact.sharesTotal : ℚ) = 0 := by
      rw [hr]; simp only [Vault.toExact, Number.toRat_zero]; norm_num
    have hNav_r : r.vault'.withdrawNav = 0 := by
      rw [hr]; simp only [Vault.withdrawNav, Vault.toExact, Number.toRat_zero, hl0]; ring
    rw [ge_iff_le, hNav_r, hSt0]; simp
  · -- non-final exit: the composition core
    have hfin : r.sharesBurned.operator_eq sta = false := by rw [hsb]; exact hfin'
    have hprice : v.sharesToAssetsWithdraw r.sharesBurned false = .ok r.assets' :=
      Vault.withdraw_payout_priced v amount false sta r hok herr hsta hfin
    obtain ⟨hp_nn, hideal_nn, hp_up, -⟩ :=
      Vault.sharesToAssetsWithdraw_spec_raw v hv r.sharesBurned r.assets' false hnn hc hnav hprice
    set x : ℚ := r.sharesBurned.toRat with hx_def
    set p : ℚ := r.assets'.toRat with hp_def
    have hideal_eq : v.idealAssetsWithdraw false x = A * x / S := by
      unfold Vault.idealAssetsWithdraw
      rw [if_neg (by decide : ¬ ((false : Bool) = true)), hNav_v]
    rw [hideal_eq] at hp_up
    -- payout is a positive value below the available balance
    have hp_ne : p ≠ 0 := by rw [hp_def]; exact STAmount.toRat_ne_zero r.assets' (ne_of_beq_false hcnz)
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nn (Ne.symm hp_ne)
    have hra : r.assets' = cw.assets' := by rw [hr]
    have hnum_r : r.assets'.toNumber .to_nearest = .ok aN := by rw [hra]; exact han
    obtain ⟨haN_val, haN_norm⟩ :=
      Vault.sharesToAssetsWithdraw_toNumber_facts v hv r.sharesBurned r.assets' false aN hc hprice hnum_r
    have hle_AA : p ≤ v.assetsAvailable.toRat := by
      have hbridge := operator_lt_iff v.assetsAvailable aN hv.wf.assetsAvailable_norm haN_norm
      by_contra hcp; push_neg at hcp
      have : v.assetsAvailable.operator_lt aN = true := by rw [hbridge, haN_val]; exact hcp
      rw [this] at hlt; exact absurd hlt (by simp)
    have hle_AT : p ≤ v.assetsTotal.toRat := le_trans hle_AA hv.valid.assetsAvailable_le
    have hApm : 0 ≤ A - p := by have : p ≤ A := hle_AT; linarith
    -- raw-stage update lower bound on the stored `assetsTotal`
    have hround : RoundsWithin at' (v.assetsTotal.toRat - r.assets'.toRat) .to_nearest
        (6 / (2 ^ 63 - 3 : ℚ)) :=
      Vault.sharesToAssetsWithdraw_sub_stored_raw v hv r.sharesBurned r.assets' false aN
        v.assetsTotal at' hc hprice hnum_r hp_nn hv.wf.assetsTotal_norm
        hv.valid.assetsTotal_nonneg hle_AT hat
    have hA'_lo : (A - p) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ at'.toRat := by
      have h : |at'.toRat - (A - p)| ≤ |A - p| * (6 / (2 ^ 63 - 3 : ℚ)) := hround
      rw [abs_of_nonneg hApm] at h
      have hab := abs_le.mp h
      nlinarith [hab.1]
    -- share total positive: a zero total would empty the vault and zero the payout
    have hSpos : 0 < S := by
      have hAAp : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le hp_pos hle_AA
      have hApos : 0 < A := lt_of_lt_of_le hAAp hv.valid.assetsAvailable_le
      rcases eq_or_lt_of_le (show (0 : ℚ) ≤ S by rw [hS_def]; positivity) with hS0 | hSp
      · exfalso
        have hSnat : v.toExact.sharesTotal = 0 := by
          have : ((v.toExact.sharesTotal : ℕ) : ℚ) = 0 := by rw [← hS_def]; exact hS0.symm
          exact_mod_cast this
        exact absurd (hv.valid.empty_shares hSnat).1 (ne_of_gt hApos)
      · exact hSp
    have hmargin' : 2 * x ≤ S := by rw [hx_def]; linarith [hmargin]
    -- assemble the composition core
    have hcore : A * (S - x) * (1 - depositε) ≤ at'.toRat * S :=
      withdraw_no_dilution_arith A S x p at'.toRat (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3))
        depositε hSpos hnn hAnn hmargin' hp_up hA'_lo (by norm_num) (by norm_num)
        (by norm_num) (by rw [depositε_eq]; norm_num)
    -- convert the stored fields back to the headline form
    have hNav_r : r.vault'.withdrawNav = at'.toRat := by
      rw [hr]; simp only [Vault.withdrawNav, Vault.toExact, hl0]; ring
    have hint_sb : r.sharesBurned.integral = true := by
      show r.sharesBurned.mNumericType.isIntegral = true; rw [hSnt]; decide
    have hxden : x.den = 1 := by
      rw [hx_def]; exact STAmount.IntegralCanonical.den_eq_one r.sharesBurned (hc.1 hint_sb).1
    have hSden : S.den = 1 := by rw [hS_def]; exact Rat.den_natCast _
    have hxle : x ≤ S := by rw [hx_def]; linarith [hmargin, hSpos]
    have hSharesEq : (r.vault'.toExact.sharesTotal : ℚ) = S - x := by
      have hval := (Vault.withdraw_vault_updates_proof v amount false hv sta r hp_nn hnn hc hSnt
        hok herr hsta hfin).2.2 hSfit
      show ((r.vault'.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = S - x
      exact Number.natCast_num_toNat_of_int_sub r.vault'.sharesTotal S x hval hSden hxden hxle
    rw [ge_iff_le, hNav_v, hNav_r, hSharesEq]
    exact hcore

/-- A successful clawback moves `withdrawNav` by exactly the change in the stored
`assetsTotal`: it rewrites only the three balance fields, leaving `interestUnrealized`
and `lossUnrealized` untouched. -/
theorem Vault.clawback_withdrawNav_change (assets holderShares : STAmount) (r : ClawbackResult)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav - v.withdrawNav =
      r.vault'.toExact.assetsTotal - v.toExact.assetsTotal := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra_eq, hsd_eq, sbn, arn, at', st', av', atr, atr',
      hsbn, harn, hat, -, -, -, hst, hav, hr⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  subst hr
  simp only [Vault.withdrawNav, Vault.toExact]; ring

/-- Proof body of `Vault.clawback_no_dilution`. Clawback prices its recovery with the
same `sharesToAssetsWithdraw` pipeline as a withdrawal (`idealAssetsClawback =
idealAssetsWithdraw false`), so it reduces to `withdraw_no_dilution_arith` exactly like
`withdraw_no_dilution_proof`: recovery upper `p ≤ A·x/S·(1 + 12/(2^63-3))`, stored
`assetsTotal` update lower at the raw `6/(2^63-3)` subtraction stage, and the near-final
margin `sharesDestroyed ≤ sharesTotal/2`. There is no final exit (a clawback is always
partial), and the destroyed shares are nonzero, so the margin keeps the share total
positive; a zero amount (claw all holder shares) is covered through the holder-balance
side conditions. -/
theorem Vault.clawback_no_dilution_proof (assets holderShares : STAmount) (r : ClawbackResult)
    (hv : v.Lawful)
    (hL : v.toExact.lossUnrealized = 0)
    (hnav : v.WithdrawNavExact false)
    (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hmargin : r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
  set A : ℚ := v.toExact.assetsTotal with hA_def
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hS_def
  have hAnn : 0 ≤ A := hv.valid.assetsTotal_nonneg
  have hl0 : v.lossUnrealized.toRat = 0 := hL
  have hNav_v : v.withdrawNav = A := by unfold Vault.withdrawNav; rw [hL]; ring
  -- recovery priced through the withdraw pipeline
  obtain ⟨hnn_sd, hcanon_sd, hprice, hle_AA, hsdnz⟩ :=
    Vault.clawback_recovery_priced' v assets holderShares r hv hnav hc hSc hSnn hok herr
  obtain ⟨hp_nn, hideal_nn, hp_up, -⟩ :=
    Vault.sharesToAssetsWithdraw_spec_raw v hv r.sharesDestroyed r.assetsRecovered false
      hnn_sd hcanon_sd hnav hprice
  set x : ℚ := r.sharesDestroyed.toRat with hx_def
  set p : ℚ := r.assetsRecovered.toRat with hp_def
  have hideal_eq : v.idealAssetsWithdraw false x = A * x / S := by
    unfold Vault.idealAssetsWithdraw
    rw [if_neg (by decide : ¬ ((false : Bool) = true)), hNav_v]
  rw [hideal_eq] at hp_up
  -- the destroyed shares are nonzero, so the near-final margin forces `0 < S`
  have hxpos : 0 < x :=
    STAmount.Canonical.toRat_pos_of_nonneg r.sharesDestroyed hcanon_sd hnn_sd hsdnz
  -- reduce for the stored `assetsTotal` subtraction
  obtain ⟨cr, hcomp, herr2, hcrnz, hra_eq, hsd_eq, sbn, arn, at', st', av', atr, atr',
      hsbn, harn, hat, -, -, -, hst, hav, hr⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  have hnum_r : r.assetsRecovered.toNumber .to_nearest = .ok arn := by rw [hra_eq]; exact harn
  have hle_AT : p ≤ v.assetsTotal.toRat := le_trans hle_AA hv.valid.assetsAvailable_le
  have hApm : 0 ≤ A - p := by have : p ≤ A := hle_AT; linarith
  have hround : RoundsWithin at' (v.assetsTotal.toRat - r.assetsRecovered.toRat) .to_nearest
      (6 / (2 ^ 63 - 3 : ℚ)) :=
    Vault.sharesToAssetsWithdraw_sub_stored_raw v hv r.sharesDestroyed r.assetsRecovered false arn
      v.assetsTotal at' hcanon_sd hprice hnum_r hp_nn hv.wf.assetsTotal_norm
      hv.valid.assetsTotal_nonneg hle_AT hat
  have hA'_lo : (A - p) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ at'.toRat := by
    have h : |at'.toRat - (A - p)| ≤ |A - p| * (6 / (2 ^ 63 - 3 : ℚ)) := hround
    rw [abs_of_nonneg hApm] at h
    have hab := abs_le.mp h
    nlinarith [hab.1]
  have hSpos : 0 < S := by linarith [hxpos, hmargin]
  have hmargin' : 2 * x ≤ S := by rw [hx_def]; linarith [hmargin]
  have hcore : A * (S - x) * (1 - depositε) ≤ at'.toRat * S :=
    withdraw_no_dilution_arith A S x p at'.toRat (12 / (2 ^ 63 - 3)) (6 / (2 ^ 63 - 3))
      depositε hSpos hnn_sd hAnn hmargin' hp_up hA'_lo (by norm_num) (by norm_num)
      (by norm_num) (by rw [depositε_eq]; norm_num)
  have hNav_r : r.vault'.withdrawNav = at'.toRat := by
    rw [hr]; simp only [Vault.withdrawNav, Vault.toExact, hl0]; ring
  have hle_x : x ≤ S := by rw [hx_def]; linarith [hmargin, hSpos]
  have hSharesEq : (r.vault'.toExact.sharesTotal : ℚ) = S - x :=
    (Vault.clawback_vault_updates_proof' v assets holderShares r hv hnav hc hSic hSc hSnn
      hok herr).2.2 ⟨hle_x, hSfit⟩
  rw [ge_iff_le, hNav_v, hNav_r, hSharesEq]
  exact hcore

private lemma navEq (vv : Vault)
    (hL : vv.toExact.lossUnrealized = 0) : vv.withdrawNav = vv.toExact.assetsTotal := by
  unfold Vault.withdrawNav; rw [hL]; ring

set_option maxHeartbeats 1600000 in
-- high budget: compound induction over n operations with per-step nlinarith
/-- Along any margin-respecting history of `n` operations from a lawful vault with no
unrealized interest or loss, per-share value decreases by at most the compounded factor
`(1 - depositε) ^ n`.

The two `interest = loss = 0` base hypotheses are an induction invariant (every modeled
operation preserves them, and each step's `no_dilution` needs them). The near-final
margins live in the withdraw/clawback constructors of `ReachableFromIn`, so every step
satisfies its per-op `no_dilution`/strict-increase theorem. The proof is the compounding
induction: `refl` is the base `(1 - depositε)^0 = 1`; each step composes the prior
factor with its single-op factor via `deposit_no_dilution` (#1), the donation
strict-increase (#3), `withdraw_no_dilution` (#4), `clawback_no_dilution` (#6), and the
`burnShares` share-only decrease, carrying `Lawful` and `interest = loss = 0` forward by
the field preservation the success reductions expose. -/
theorem Vault.ReachableFromIn.no_dilution_proof (w : Vault) (n : ℕ)
    (hw : w.Lawful)
    (hwL : w.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending), the same record-level
    -- parity `Vault.Reachable` gets from `create`; it is preserved by every step and is needed to
    -- carry `Lawful` forward through the compounding induction (each `*_lawful` step consumes it)
    (hwAV : w.assetsAvailable = w.assetsTotal)
    (h : Vault.ReachableFromIn w v n) :
    v.withdrawNav * (w.toExact.sharesTotal : ℚ) ≥
      w.withdrawNav * (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n := by
  suffices H : ∀ (u : Vault) (m : ℕ), Vault.ReachableFromIn w u m →
      u.Lawful ∧ u.toExact.lossUnrealized = 0 ∧
      u.assetsAvailable = u.assetsTotal ∧
      (0 < (u.toExact.sharesTotal : ℚ) ∨ w.withdrawNav = 0) ∧
      u.withdrawNav * (w.toExact.sharesTotal : ℚ) ≥
        w.withdrawNav * (u.toExact.sharesTotal : ℚ) * (1 - depositε) ^ m by
    exact (H v n h).2.2.2.2
  intro u m hum
  induction hum with
  | refl =>
    refine ⟨hw, hwL, hwAV, ?_, ?_⟩
    · by_cases hSw : (0 : ℚ) < (w.toExact.sharesTotal : ℚ)
      · exact Or.inl hSw
      · refine Or.inr ?_
        have hSw0 : w.toExact.sharesTotal = 0 := by
          have hle : (w.toExact.sharesTotal : ℚ) ≤ 0 := not_lt.mp hSw
          have hge : (0 : ℚ) ≤ (w.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
          have : (w.toExact.sharesTotal : ℚ) = 0 := le_antisymm hle hge
          exact_mod_cast this
        have hA0 : w.toExact.assetsTotal = 0 := (hw.valid.empty_shares hSw0).1
        unfold Vault.withdrawNav; rw [hA0, hwL]; ring
    · rw [pow_zero, mul_one]
  | deposit u' k amount isDonation r prev hrun hcanon hpos hcnz hSsz ih =>
    obtain ⟨hLu, hLu0, hAVu, hSuw, hratio_u⟩ := ih
    -- the taken amount and issued shares are nonnegative (derived from the run)
    obtain ⟨hDnn, hSnn⟩ :=
      Vault.deposit_result_nonneg u' amount isDonation hLu hcanon (le_of_lt hpos) r hrun
    have he_nn : (0 : ℚ) ≤ 1 - depositε := by rw [depositε_eq]; norm_num
    have he_le1 : (1 : ℚ) - depositε ≤ 1 := by rw [depositε_eq]; norm_num
    have hSu_nn : (0 : ℚ) ≤ (u'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hSw_nn : (0 : ℚ) ≤ (w.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hNu_nn : 0 ≤ u'.withdrawNav := hLu.valid.withdraw_nav_nonneg
    have hLr : r.vault'.Lawful :=
      Vault.deposit_lawful u' amount isDonation hLu hLu0 hAVu hcanon (le_of_lt hpos) r hrun hSsz
    have hLeq := Vault.deposit_preserves_unrealized u' amount isDonation r hrun
    have hLr0 : r.vault'.toExact.lossUnrealized = 0 := by
      show r.vault'.lossUnrealized.toRat = 0; rw [hLeq]; exact hLu0
    have hAVr : r.vault'.assetsAvailable = r.vault'.assetsTotal :=
      Vault.deposit_asset_parity u' amount isDonation r hAVu hrun
    have hNr_nn : 0 ≤ r.vault'.withdrawNav := hLr.valid.withdraw_nav_nonneg
    have hSr_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hSle : (u'.toExact.sharesTotal : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := by
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.deposit_error_unchanged u' amount isDonation r hrun herr
        rw [hveq]
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        have heq := (Vault.deposit_vault_updates u' amount isDonation hLu hcanon hpos r hrun herr').2.2 hSsz
        rw [heq]; linarith [hSnn]
    have hstep : r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) ≥
        u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.deposit_error_unchanged u' amount isDonation r hrun herr
        rw [hveq]; nlinarith [mul_nonneg hNu_nn hSu_nn, he_le1]
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        by_cases hdon : isDonation = true
        · subst hdon
          have hSeq : (r.vault'.toExact.sharesTotal : ℚ) = (u'.toExact.sharesTotal : ℚ) := by
            have := Vault.deposit_donation_sharesTotal_toExact u' amount r hrun herr'
            exact_mod_cast this
          have hNav_u := navEq u' hLu0
          have hNr_eq := navEq r.vault' hLr0
          have hupd := (Vault.deposit_vault_updates u' amount true hLu hcanon hpos r hrun herr').1
          simp only [RoundsWithin, RatValued.toRat] at hupd
          rw [show r.vault'.assetsTotal.toRat = r.vault'.toExact.assetsTotal from rfl] at hupd
          have hAnn : 0 ≤ u'.toExact.assetsTotal := hLu.valid.assetsTotal_nonneg
          have hsum_nn : 0 ≤ u'.toExact.assetsTotal + r.amountDeposit'.toRat := add_nonneg hAnn hDnn
          rw [abs_of_nonneg hsum_nn] at hupd
          have hupd2 := abs_le.mp hupd
          have hNr_lb : u'.withdrawNav * (1 - depositε) ≤ r.vault'.withdrawNav := by
            rw [hNav_u, hNr_eq]
            nlinarith [hupd2.1, mul_nonneg hDnn he_nn]
          rw [hSeq]
          nlinarith [mul_le_mul_of_nonneg_right hNr_lb hSu_nn]
        · have hnd : isDonation = false := by
            cases isDonation with | true => exact absurd rfl hdon | false => rfl
          subst hnd
          exact Vault.deposit_no_dilution_proof u' amount r hLu hcanon hpos hLu0 hcnz hSsz hrun herr'
    refine ⟨hLr, hLr0, hAVr, ?_, ?_⟩
    · rcases hSuw with hSu_pos | hNw0
      · exact Or.inl (lt_of_lt_of_le hSu_pos hSle)
      · exact Or.inr hNw0
    · rcases hSuw with hSu_pos | hNw0
      · rw [pow_succ]
        have hey_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
          mul_nonneg hSr_nn he_nn
        have h1 : u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)
            * (w.toExact.sharesTotal : ℚ)
            ≤ r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (w.toExact.sharesTotal : ℚ) :=
          mul_le_mul_of_nonneg_right hstep hSw_nn
        have h2 : w.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (1 - depositε) ^ k
            * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε))
            ≤ u'.withdrawNav * (w.toExact.sharesTotal : ℚ)
              * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)) :=
          mul_le_mul_of_nonneg_right hratio_u hey_nn
        have key : (w.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)
              * ((1 - depositε) ^ k * (1 - depositε))) * (u'.toExact.sharesTotal : ℚ)
            ≤ (r.vault'.withdrawNav * (w.toExact.sharesTotal : ℚ))
              * (u'.toExact.sharesTotal : ℚ) := by
          nlinarith [h1, h2]
        exact le_of_mul_le_mul_right key hSu_pos
      · rw [hNw0]; simp only [zero_mul]; exact mul_nonneg hNr_nn hSw_nn
  | withdraw u' k amount r prev hrun hnav hcnz hSc hcanon hSnt hSneg hmargin hSfit ih =>
    obtain ⟨hLu, hLu0, hAVu, hSuw, hratio_u⟩ := ih
    have he_nn : (0 : ℚ) ≤ 1 - depositε := by rw [depositε_eq]; norm_num
    have he_le1 : (1 : ℚ) - depositε ≤ 1 := by rw [depositε_eq]; norm_num
    have hSu_nn : (0 : ℚ) ≤ (u'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hSw_nn : (0 : ℚ) ≤ (w.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hNu_nn : 0 ≤ u'.withdrawNav := hLu.valid.withdraw_nav_nonneg
    have hnn : 0 ≤ r.sharesBurned.toRat := STAmount.toRat_nonneg_of _ hSneg
    -- the paid amount is nonnegative (derived from the run)
    have hDnn : 0 ≤ r.assets'.toRat :=
      Vault.withdraw_assets_nonneg u' amount false hLu hLu0 r hrun hSc hSnt hSneg
    have hsle : r.sharesBurned.toRat ≤ (u'.toExact.sharesTotal : ℚ) := by linarith [hmargin, hSu_nn]
    have hLr : r.vault'.Lawful :=
      Vault.withdraw_lawful u' amount false hLu hLu0 hAVu r hrun hSc hSnt hSneg hsle hSfit
    have hLeq := Vault.withdraw_preserves_unrealized u' amount false r hrun
    have hLr0 : r.vault'.toExact.lossUnrealized = 0 := by
      show r.vault'.lossUnrealized.toRat = 0; rw [hLeq]; exact hLu0
    have hAVr : r.vault'.assetsAvailable = r.vault'.assetsTotal :=
      Vault.withdraw_asset_parity u' amount false r hAVu hrun
    have hNr_nn : 0 ≤ r.vault'.withdrawNav := hLr.valid.withdraw_nav_nonneg
    have hSr_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hstep : r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) ≥
        u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.withdraw_error_unchanged u' amount false r hrun herr
        rw [hveq]; nlinarith [mul_nonneg hNu_nn hSu_nn, he_le1]
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        exact Vault.withdraw_no_dilution_proof u' amount r hLu hLu0 hnav hcnz hnn hcanon hSnt hmargin hSfit hrun herr'
    -- conjunct 5: 0 < S_r  (when 0 < S_u)
    have hSrpos : 0 < (u'.toExact.sharesTotal : ℚ) → 0 < (r.vault'.toExact.sharesTotal : ℚ) := by
      intro hSu_pos
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.withdraw_error_unchanged u' amount false r hrun herr
        rw [hveq]; exact hSu_pos
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        obtain ⟨cw, aN', sta, hcomp, herr2, han, hlt, hst, hsb, hdisj⟩ :=
          Vault.withdraw_success_reduces u' amount false r hrun herr'
        have hSfit' : u'.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
          have := hSfit; rwa [Vault.WF.toExact_sharesTotal u' hLu.wf] at this
        obtain ⟨hsta_nt, hsta_off, hsta_neg, hsta_mv, hsta_val⟩ :=
          STAmount.ofNumber_int64_shape u'.sharesTotal .to_nearest sta
          hLu.wf.sharesTotal_norm hLu.wf.sharesTotal_nonneg hLu.wf.sharesTotal_int hSfit' hst
        have hstaS : sta.toRat = (u'.toExact.sharesTotal : ℚ) := by
          rw [hsta_val, Vault.WF.toExact_sharesTotal u' hLu.wf]
        have hsta_mv_le : sta.mValue.toNat ≤ 2 ^ 63 - 1 := by
          have h1 : ((sta.mValue.toNat : ℕ) : ℚ) ≤ 2 ^ 63 - 1 := by
            rw [hsta_mv]; exact hSfit'
          have h2 : ((sta.mValue.toNat : ℕ) : ℤ) ≤ 2 ^ 63 - 1 := by exact_mod_cast h1
          omega
        have hsta_ec : sta.ExactCanonical := Or.inr ⟨⟨by rw [hsta_nt]; decide, hsta_off,
          by rw [hsta_nt]; show sta.mValue.toNat ≤ (2 ^ 63 - 1 : ℕ); exact hsta_mv_le⟩, hsta_mv_le⟩
        rcases hdisj with ⟨hfinT, -, allAvail, -, hr⟩ |
            ⟨hfinF, sbn, at', av', st', atr, atr', hsbn, hat, -, -, -, hav, hst2, hr⟩
        · exfalso
          have hcmp : STAmount.CmpFaithful r.sharesBurned sta :=
            STAmount.CmpFaithful.ofExactCanonical r.sharesBurned sta (Or.inr ⟨hSc, by
              have := hSc.in_range; have hmax : (r.sharesBurned.mNumericType).maxValue.toNat ≤ 2 ^ 63 - 1 := by
                rw [hSnt]; decide
              omega⟩) hsta_ec
              (by show (r.sharesBurned.mNumericType == sta.mNumericType) = true
                  rw [hSnt, hsta_nt]; rfl)
              (fun _ => hSneg) (fun _ => hsta_neg)
          have heqv := STAmount.operator_eq_eq r.sharesBurned sta hcmp
          rw [hsb] at heqv
          rw [heqv] at hfinT
          have hval_eq : cw.sharesRedeemed.toRat = sta.toRat := of_decide_eq_true hfinT
          rw [← hsb, hstaS] at hval_eq
          rw [hval_eq] at hmargin
          linarith [hSu_pos]
        · have hupd := (Vault.withdraw_vault_updates_proof u' amount false hLu sta r hDnn hnn hcanon hSnt
            hrun herr' hst (by rw [hsb]; exact hfinF)).2.2 hSfit
          have hSrq : (r.vault'.toExact.sharesTotal : ℚ)
              = (u'.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat := by
            have hcast : ((r.vault'.toExact.sharesTotal : ℕ) : ℚ) = r.vault'.sharesTotal.toRat :=
              Vault.WF.toExact_sharesTotal r.vault' hLr.wf
            rw [show (r.vault'.toExact.sharesTotal : ℚ)
                  = ((r.vault'.toExact.sharesTotal : ℕ) : ℚ) from rfl, hcast, hupd]
          rw [hSrq]; linarith [hmargin, hSu_pos]
    refine ⟨hLr, hLr0, hAVr, ?_, ?_⟩
    · rcases hSuw with hSu_pos | hNw0
      · exact Or.inl (hSrpos hSu_pos)
      · exact Or.inr hNw0
    · rcases hSuw with hSu_pos | hNw0
      · rw [pow_succ]
        have hey_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
          mul_nonneg hSr_nn he_nn
        have h1 : u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)
            * (w.toExact.sharesTotal : ℚ)
            ≤ r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (w.toExact.sharesTotal : ℚ) :=
          mul_le_mul_of_nonneg_right hstep hSw_nn
        have h2 : w.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (1 - depositε) ^ k
            * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε))
            ≤ u'.withdrawNav * (w.toExact.sharesTotal : ℚ)
              * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)) :=
          mul_le_mul_of_nonneg_right hratio_u hey_nn
        have key : (w.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)
              * ((1 - depositε) ^ k * (1 - depositε))) * (u'.toExact.sharesTotal : ℚ)
            ≤ (r.vault'.withdrawNav * (w.toExact.sharesTotal : ℚ))
              * (u'.toExact.sharesTotal : ℚ) := by
          nlinarith [h1, h2]
        exact le_of_mul_le_mul_right key hSu_pos
      · rw [hNw0]; simp only [zero_mul]; exact mul_nonneg hNr_nn hSw_nn

  | clawback u' k assets holderShares r prev hrun hnav hcanon hSic hSc hSnn hmargin hSfit ih =>
    obtain ⟨hLu, hLu0, hAVu, hSuw, hratio_u⟩ := ih
    have he_nn : (0 : ℚ) ≤ 1 - depositε := by rw [depositε_eq]; norm_num
    have he_le1 : (1 : ℚ) - depositε ≤ 1 := by rw [depositε_eq]; norm_num
    have hSu_nn : (0 : ℚ) ≤ (u'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hSw_nn : (0 : ℚ) ≤ (w.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hNu_nn : 0 ≤ u'.withdrawNav := hLu.valid.withdraw_nav_nonneg
    -- success derives S_u > 0 (nonzero destroyed shares under the margin)
    have hsuc_pos : r.error = none → 0 < (u'.toExact.sharesTotal : ℚ) := by
      intro herr'
      obtain ⟨hnn_sd, hcanon_sd, -, -, hsdnz⟩ :=
        Vault.clawback_recovery_priced' u' assets holderShares r hLu hnav hcanon hSc hSnn
          hrun herr'
      have hxpos : 0 < r.sharesDestroyed.toRat :=
        STAmount.Canonical.toRat_pos_of_nonneg r.sharesDestroyed hcanon_sd hnn_sd hsdnz
      linarith [hmargin, hxpos]
    have hLr : r.vault'.Lawful := by
      by_cases herr : r.error.isSome = true
      · rw [(Vault.clawback_error_unchanged u' assets holderShares r hrun herr).1]; exact hLu
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        have hSu_pos := hsuc_pos herr'
        have hslt : r.sharesDestroyed.toRat < (u'.toExact.sharesTotal : ℚ) := by
          linarith [hmargin, hSu_pos]
        exact Vault.clawback_lawful u' assets holderShares hLu hLu0 hAVu hcanon r hSic hSc hSnn
          hrun hslt hSfit
    have hLeq := Vault.clawback_preserves_unrealized u' assets holderShares r hrun
    have hLr0 : r.vault'.toExact.lossUnrealized = 0 := by
      show r.vault'.lossUnrealized.toRat = 0; rw [hLeq]; exact hLu0
    have hAVr : r.vault'.assetsAvailable = r.vault'.assetsTotal :=
      Vault.clawback_asset_parity u' assets holderShares r hAVu hrun
    have hNr_nn : 0 ≤ r.vault'.withdrawNav := hLr.valid.withdraw_nav_nonneg
    have hSr_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hstep : r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) ≥
        u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := by
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.clawback_error_unchanged u' assets holderShares r hrun herr
        rw [hveq]; nlinarith [mul_nonneg hNu_nn hSu_nn, he_le1]
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        exact Vault.clawback_no_dilution_proof u' assets holderShares r hLu hLu0 hnav hcanon
          hSic hSc hSnn hmargin hSfit hrun herr'
    have hSrpos : 0 < (u'.toExact.sharesTotal : ℚ) → 0 < (r.vault'.toExact.sharesTotal : ℚ) := by
      intro hSu_pos
      by_cases herr : r.error.isSome = true
      · obtain ⟨hveq, -, -⟩ := Vault.clawback_error_unchanged u' assets holderShares r hrun herr
        rw [hveq]; exact hSu_pos
      · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
        have hle_x : r.sharesDestroyed.toRat ≤ (u'.toExact.sharesTotal : ℚ) := by
          linarith [hmargin, hSu_pos]
        have hSrq := (Vault.clawback_vault_updates_proof' u' assets holderShares r hLu hnav hcanon
          hSic hSc hSnn hrun herr').2.2 ⟨hle_x, hSfit⟩
        rw [hSrq]; linarith [hmargin, hSu_pos]
    refine ⟨hLr, hLr0, hAVr, ?_, ?_⟩
    · rcases hSuw with hSu_pos | hNw0
      · exact Or.inl (hSrpos hSu_pos)
      · exact Or.inr hNw0
    · rcases hSuw with hSu_pos | hNw0
      · rw [pow_succ]
        have hey_nn : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
          mul_nonneg hSr_nn he_nn
        have h1 : u'.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)
            * (w.toExact.sharesTotal : ℚ)
            ≤ r.vault'.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (w.toExact.sharesTotal : ℚ) :=
          mul_le_mul_of_nonneg_right hstep hSw_nn
        have h2 : w.withdrawNav * (u'.toExact.sharesTotal : ℚ) * (1 - depositε) ^ k
            * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε))
            ≤ u'.withdrawNav * (w.toExact.sharesTotal : ℚ)
              * ((r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε)) :=
          mul_le_mul_of_nonneg_right hratio_u hey_nn
        have key : (w.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)
              * ((1 - depositε) ^ k * (1 - depositε))) * (u'.toExact.sharesTotal : ℚ)
            ≤ (r.vault'.withdrawNav * (w.toExact.sharesTotal : ℚ))
              * (u'.toExact.sharesTotal : ℚ) := by
          nlinarith [h1, h2]
        exact le_of_mul_le_mul_right key hSu_pos
      · rw [hNw0]; simp only [zero_mul]; exact mul_nonneg hNr_nn hSw_nn

  | burnShares u' k sharesDestroyed sharesTotalAmount u'' prev hcan hcanon hSneg hle hnn hden hSfit hburn ih =>
    obtain ⟨hLu, hLu0, hAVu, hSuw, hratio_u⟩ := ih
    have he_nn : (0 : ℚ) ≤ 1 - depositε := by rw [depositε_eq]; norm_num
    -- canBurnShares success: assetsTotal = 0, sharesTotal ≠ 0
    have hguard : (u'.sharesTotal.mantissa_ == 0 ||
        (u'.assetsTotal.mantissa_ != 0 || u'.assetsAvailable.mantissa_ != 0)) = false := by
      by_contra hg
      have hg' : (u'.sharesTotal.mantissa_ == 0 ||
          (u'.assetsTotal.mantissa_ != 0 || u'.assetsAvailable.mantissa_ != 0)) = true := by
        cases h : (u'.sharesTotal.mantissa_ == 0 ||
          (u'.assetsTotal.mantissa_ != 0 || u'.assetsAvailable.mantissa_ != 0)) with
        | true => rfl
        | false => exact absurd h hg
      unfold Vault.canBurnShares at hcan
      rw [if_pos hg'] at hcan
      exact CanBurnSharesResult.noConfusion (Except.ok.inj hcan)
    rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hguard
    obtain ⟨hsh0, hat0, hav0⟩ := hguard
    have hshne : u'.sharesTotal.mantissa_ ≠ 0 := by
      simpa using (beq_eq_false_iff_ne.mp hsh0)
    have hatz : u'.assetsTotal.mantissa_ = 0 := by simpa using bne_eq_false_iff_eq.mp hat0
    have hAu0 : u'.toExact.assetsTotal = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero _ hatz
    have hNu0 : u'.withdrawNav = 0 := by rw [navEq u' hLu0, hAu0]
    have hSu_pos : (0 : ℚ) < (u'.toExact.sharesTotal : ℚ) := by
      have hST : ((u'.toExact.sharesTotal : ℕ) : ℚ) = u'.sharesTotal.toRat :=
        Vault.WF.toExact_sharesTotal u' hLu.wf
      have hne : u'.sharesTotal.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero _ hshne
      have hge : 0 ≤ u'.sharesTotal.toRat := hLu.wf.sharesTotal_nonneg
      rw [hST]; exact lt_of_le_of_ne hge (Ne.symm hne)
    -- N_w = 0 forced by the ratio
    have hNw0 : w.withdrawNav = 0 := by
      have hrat := hratio_u
      rw [hNu0, zero_mul, ge_iff_le] at hrat
      have hp_pos : (0 : ℚ) < (1 - depositε) ^ k := by
        apply pow_pos; rw [depositε_eq]; norm_num
      have hNw_nn : 0 ≤ w.withdrawNav := hw.valid.withdraw_nav_nonneg
      have hc_pos : 0 < (u'.toExact.sharesTotal : ℚ) * (1 - depositε) ^ k := mul_pos hSu_pos hp_pos
      rcases eq_or_lt_of_le hNw_nn with h | h
      · exact h.symm
      · exact absurd hrat (not_le.mpr (by nlinarith [mul_pos h hc_pos]))
    -- invariant preservation
    have hLr : u''.Lawful :=
      Vault.burnShares_lawful u' sharesDestroyed sharesTotalAmount u'' hLu hcan hcanon hSneg hle hSfit hburn
    have hLeq := Vault.burnShares_preserves_unrealized u' sharesDestroyed u'' hburn
    have hLr0 : u''.toExact.lossUnrealized = 0 := by
      show u''.lossUnrealized.toRat = 0; rw [hLeq]; exact hLu0
    have hAVr : u''.assetsAvailable = u''.assetsTotal :=
      Vault.burnShares_asset_parity u' sharesDestroyed u'' hAVu hburn
    have hNr_nn : 0 ≤ u''.withdrawNav := hLr.valid.withdraw_nav_nonneg
    have hSw_nn : (0 : ℚ) ≤ (w.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    refine ⟨hLr, hLr0, hAVr, Or.inr hNw0, ?_⟩
    rw [hNw0, zero_mul, zero_mul]
    exact mul_nonneg hNr_nn hSw_nn

end XRPL.Model.SingleAssetVault
