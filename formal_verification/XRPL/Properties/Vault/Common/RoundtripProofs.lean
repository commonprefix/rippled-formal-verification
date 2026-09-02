import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.DepositChargeFrac
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.State
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.VaultDecidable

/-! # Proof support for `Vault.deposit_withdraw_roundtrip` -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Raw-stage composition of the deposit-then-withdraw round trip on the value
path, in exact rationals. `Q` is the interior (pre-`ofNumber`) charge, `C` the
stored charge (`Q ≤ C ≤ Q + UC`), `at'` the stored total, `IA` the payout ideal.
The three raw relative stages (charge `19/(2^63-3)`, store `6/(2^63-3)`, payout
`12/(2^63-3)`) compose under `2·depositε`, and the two directed-rounding ULPs
(`UC` upward charge snap, `UA` downward payout snap) enter additively with
coefficient one each. -/
private lemma roundtrip_algebra
    (C A IC Q at' IA Av S STv UA UC : ℚ)
    (hS : 0 < S) (hSTv : 0 < STv) (_hAv : 0 ≤ Av)
    (hC : 0 < C) (hIC : 0 < IC)
    (hicid : Av * S = IC * STv)
    (hQlo : IC * (1 - 19 / (2 ^ 63 - 3)) ≤ Q)
    (hQhi : Q ≤ IC * (1 + 19 / (2 ^ 63 - 3)))
    (hQClo : Q ≤ C)
    (hQChi : C ≤ Q + UC)
    (hstlo : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) ≤ at')
    (hsthi : at' ≤ (Av + C) * (1 + 6 / (2 ^ 63 - 3)))
    (hIAid : IA * (STv + S) = at' * S)
    (_hIAnn : 0 ≤ IA) (_hAnn : 0 ≤ A) (_hUAnn : 0 ≤ UA) (hUCnn : 0 ≤ UC)
    (hAhi : A ≤ IA * (1 + 12 / (2 ^ 63 - 3)))
    (hAlo : IA - A ≤ IA * (12 / (2 ^ 63 - 3)) + UA) :
    A ≤ C * (1 + 2 * depositε) ∧
    C - A ≤ C * (2 * depositε) + UA + UC := by
  have hP : (0 : ℚ) < STv + S := by positivity
  -- charge, one-sided in terms of C
  have hICleC : IC * (1 - 19 / (2 ^ 63 - 3)) ≤ C := le_trans hQlo hQClo
  have hCleIC : C ≤ IC * (1 + 19 / (2 ^ 63 - 3)) + UC := by linarith [hQChi, hQhi]
  -- coefficient facts
  have hf1 : (1 + 6 / (2 ^ 63 - 3) : ℚ)
      ≤ (1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3)) := by norm_num
  -- IC·(1+6/d) ≤ C·(1+26/d)
  have hIC1 : IC * (1 + 6 / (2 ^ 63 - 3)) ≤ C * (1 + 26 / (2 ^ 63 - 3)) := by
    have h1 : IC * (1 + 6 / (2 ^ 63 - 3))
        ≤ IC * ((1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3))) :=
      mul_le_mul_of_nonneg_left hf1 (le_of_lt hIC)
    have h3 : IC * (1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3))
        ≤ C * (1 + 26 / (2 ^ 63 - 3)) :=
      mul_le_mul_of_nonneg_right hICleC (by norm_num)
    nlinarith [h1, h3]
  -- L1 : IA ≤ C·(1+26/d)
  have hL1 : IA ≤ C * (1 + 26 / (2 ^ 63 - 3)) := by
    have key : IA * (STv + S) ≤ C * (1 + 26 / (2 ^ 63 - 3)) * (STv + S) := by
      have e1 : IA * (STv + S) = at' * S := hIAid
      have e2 : at' * S ≤ (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S :=
        mul_le_mul_of_nonneg_right hsthi (le_of_lt hS)
      have e3 : (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S
          = (IC * STv + C * S) * (1 + 6 / (2 ^ 63 - 3)) := by
        have : (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S
            = (Av * S + C * S) * (1 + 6 / (2 ^ 63 - 3)) := by ring
        rw [this, hicid]
      have ha : IC * (1 + 6 / (2 ^ 63 - 3)) * STv ≤ C * (1 + 26 / (2 ^ 63 - 3)) * STv :=
        mul_le_mul_of_nonneg_right hIC1 (le_of_lt hSTv)
      have hb : C * S * (1 + 6 / (2 ^ 63 - 3)) ≤ C * S * (1 + 26 / (2 ^ 63 - 3)) :=
        mul_le_mul_of_nonneg_left (by norm_num) (mul_nonneg (le_of_lt hC) (le_of_lt hS))
      nlinarith [e1, e2, e3, ha, hb]
    exact le_of_mul_le_mul_right key hP
  -- C - IC ≤ UC + IC·19/d  and  IC·19/d ≤ C·20/d
  have hCIC : C - IC ≤ UC + IC * (19 / (2 ^ 63 - 3)) := by nlinarith [hCleIC]
  have hIC19 : IC * (19 / (2 ^ 63 - 3)) ≤ C * (20 / (2 ^ 63 - 3)) := by
    nlinarith [hICleC, hIC]
  -- L2 : C·(1-26/d) - UC ≤ IA
  have hL2 : C * (1 - 26 / (2 ^ 63 - 3)) - UC ≤ IA := by
    have key : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (STv + S) ≤ IA * (STv + S) := by
      have e1 : (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) ≤ IA * (STv + S) := by
        have e2 : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S ≤ at' * S :=
          mul_le_mul_of_nonneg_right hstlo (le_of_lt hS)
        have e3 : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S
            = (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by
          have : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S
              = (Av * S + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by ring
          rw [this, hicid]
        rw [← e3]; rw [hIAid]; exact e2
      -- (IC·STv + C·S)(1-6/d) ≥ (C(1-6/d) - (UC+IC·19/d))(STv+S)
      --   ≥ (C(1-26/d) - UC)(STv+S)
      have hkey2 : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (STv + S)
          ≤ (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by
        nlinarith [hCIC, hIC19, hUCnn, hSTv, hS, hC, hIC,
          mul_nonneg (le_of_lt hSTv) hUCnn, mul_nonneg (le_of_lt hS) hUCnn,
          mul_pos hSTv hS]
      linarith [e1, hkey2]
    exact le_of_mul_le_mul_right key hP
  -- upper conjunct
  have hup : A ≤ C * (1 + 2 * depositε) := by
    have h1 : A ≤ C * (1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) := by
      have := mul_le_mul_of_nonneg_right hL1 (by norm_num : (0:ℚ) ≤ 1 + 12 / (2 ^ 63 - 3))
      linarith [hAhi, this]
    have h2 : C * (1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) ≤ C * (1 + 2 * depositε) := by
      have hfup : ((1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) : ℚ) ≤ 1 + 2 * depositε := by
        rw [depositε_eq]; norm_num
      nlinarith [hfup, hC]
    linarith [h1, h2]
  -- loss conjunct
  have hloss : C - A ≤ C * (2 * depositε) + UA + UC := by
    have hA_lo : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3)) - UA ≤ A := by
      have h1 : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3))
          ≤ IA * (1 - 12 / (2 ^ 63 - 3)) :=
        mul_le_mul_of_nonneg_right hL2 (by norm_num)
      linarith [hAlo, h1]
    have hfin : C - ((C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3)) - UA)
        ≤ C * (2 * depositε) + UA + UC := by
      have hfl : (38 / (2 ^ 63 - 3) - 312 / (2 ^ 63 - 3) ^ 2 : ℚ) ≤ 2 * depositε := by
        rw [depositε_eq]; norm_num
      nlinarith [hfl, hC, hUCnn]
    linarith [hA_lo, hfin]
  exact ⟨hup, hloss⟩

/-- The interior charge `Q` of a nonzero nonempty-vault charge, with its raw
`19/(2^63-3)` band around the ideal, sandwiched by the upward `ofNumber` snap
`Q ≤ c ≤ Q + 10^c.exponent`. The deposit NAV is `assetsTotal`, so the ideal
collapses to `assetsTotal · shares / sharesTotal`. Feeds the charge inputs of
`roundtrip_algebra`. -/
private lemma roundtrip_charge_Q (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hcnz : c.isZero = false)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      v.idealChargeDeposit shares.toRat * (1 - 19 / (2 ^ 63 - 3)) ≤ Q.toRat ∧
      Q.toRat ≤ v.idealChargeDeposit shares.toRat * (1 + 19 / (2 ^ 63 - 3)) ∧
      Q.toRat ≤ c.toRat ∧
      c.toRat ≤ Q.toRat + (10 : ℚ) ^ c.exponent ∧
      0 < v.idealChargeDeposit shares.toRat ∧
      v.idealChargeDeposit shares.toRat =
        v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hideal_eq : v.idealChargeDeposit shares.toRat =
      v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealChargeDeposit RawVault.depositNav
    rw [if_neg (ne_of_gt hApos)]
  obtain ⟨Q, hcQ, hidpos, hQnz, hQz⟩ :=
    sharesToAssetsDeposit_charge_nonempty_raw v shares c hshc hshnt hshpos hmz hsad
  have hc0 : c.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hcnz; exact hcnz)
  have hQm : Q.mantissa_ ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward c hint hcQ hc0
    · have hfrac : v.numericType = .fractional := by
        cases hnt : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
      exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .upward c hfrac hcQ hc0
  obtain ⟨hQnorm, hQneg, hband⟩ := hQnz hQm
  have hbandle := abs_le.mp hband
  refine ⟨Q, ?_, ?_, ?_, ?_, hidpos, hideal_eq⟩
  · nlinarith [hbandle.1]
  · nlinarith [hbandle.2]
  · exact STAmount.ofNumber_upward_ge v.numericType Q c hQnorm hQneg hcQ hc0
  · -- upward `ofNumber` ceiling, single ULP
    by_cases hint : v.numericType.isIntegral = true
    · have hwithin := STAmount.ofNumber_integral_within_one v.numericType Q .upward c
        hint hQnorm hQneg hcQ
      have hcexp : c.exponent = 0 :=
        (sharesToAssetsDeposit_integral_canonical v shares c hint hsad).1.offset_zero
      rw [hcexp]; simp only [zpow_zero]
      have := (abs_lt.mp hwithin).2; linarith
    · obtain ⟨hr_lo, hr_hi⟩ := hQnorm.mantissaBounds_nat hQm
      have hre_lo : minExponent ≤ Q.exponent_ := by
        rcases hQnorm with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show Q.mantissa_ = 0 by rw [h0]; rfl) hQm
        · exact hlo
      have hintf : v.numericType.isIntegral = false := by
        cases h : v.numericType.isIntegral with
        | true => exact absurd h hint | false => rfl
      have hfrac : v.numericType = .fractional := by
        cases hnt : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hintf; simp [NumericType.isIntegral] at hintf
      have hok' : STAmount.ofNumber .fractional Q .upward = .ok c := by rw [← hfrac]; exact hcQ
      have hre_hi : Q.exponent_ + 4 ≤ maxExponent :=
        STAmount.ofNumber_iou_success_exp_range Q .upward c hr_lo hr_hi hre_lo hok' hc0
      exact STAmount.ofNumber_upward_ceiling_bounds v.numericType Q c hfrac
        hr_lo hr_hi hre_lo hre_hi hcQ hc0

/-- Adding a nonzero `Number` on the right of `Number.zero` returns it verbatim (the
second fast path of `operator_add`). -/
private lemma zero_operator_add_ne (y : Number) (hy : y.operator_eq Number.zero = false) :
    Number.zero.operator_add y .to_nearest = .ok y := by
  unfold Number.operator_add
  rw [if_neg (by rw [hy]; exact Bool.false_ne_true),
      if_pos (show Number.zero.operator_eq Number.zero = true from by decide)]
  rfl

/-- Adding a value-zero `Number` on the right of `Number.zero` returns `Number.zero`
(the first fast path of `operator_add`). -/
private lemma zero_operator_add_zero (y : Number) (hy : y.operator_eq Number.zero = true) :
    Number.zero.operator_add y .to_nearest = .ok Number.zero := by
  unfold Number.operator_add
  rw [if_pos hy]
  rfl

/-- **`ofNumber ∘ toNumber` is value-preserving on a canonical charge.** The `toNumber`
lift of an `ExactCanonical` amount snaps back verbatim under `ofNumber` for the same
numeric type: integral amounts are integer-valued (`ofNumber_integral_exact`), fractional
amounts keep at most 16 significant digits so the 19-digit re-lift re-rounds losslessly
(`normalizeToRange_16_exact` recovers the 16-digit mantissa, `checked_iou_cases` re-packs
the canonical record). -/
private lemma ofNumber_charge_roundtrip (nt : NumericType) (c : STAmount) (cN : Number)
    (A : STAmount) (hnt : c.mNumericType = nt) (hc : c.ExactCanonical) (hcnn : 0 ≤ c.toRat)
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hA : STAmount.ofNumber nt cN .to_nearest = .ok A) (hAnz : A.mValue ≠ 0) :
    A.toRat = c.toRat := by
  rcases hc with hiou | ⟨hint, hsz⟩
  · -- fractional: the 19-digit lift re-rounds to the canonical 16-digit record verbatim
    have hntf : nt = .fractional := by rw [← hnt]; exact hiou.is_fractional
    subst hntf
    have hmv_pos : 0 < c.mValue.toNat := by have := hiou.mant_lo; omega
    have hcneg : c.mIsNegative = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      have hlt : c.toRat < 0 := by
        rw [STAmount.toRat_of_neg c h]
        have hp : (0:ℚ) < (c.mValue.toNat : ℚ) * 10 ^ c.mOffset :=
          mul_pos (by exact_mod_cast hmv_pos) (by positivity)
        linarith
      linarith
    have hcform : cN = ⟨false, c.mValue * 10 * 10 * 10, c.mOffset - 3⟩ := by
      have hcan := STAmount.toNumber_iou_canonical c .to_nearest hiou
      rw [hcneg] at hcan
      rw [hcan] at hcN
      exact (Except.ok.inj hcN).symm
    have hcNneg : cN.negative_ = false := by rw [hcform]
    have hcNmant : cN.mantissa_ = c.mValue * 10 * 10 * 10 := by rw [hcform]
    have hcNexp : cN.exponent_ = c.mOffset - 3 := by rw [hcform]
    have hM3 : (c.mValue * 10 * 10 * 10).toNat = c.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hiou.mant_hi
    have hq3 : c.mValue * 10 * 10 * 10 / 10 / 10 / 10 = c.mValue := by
      apply UInt64.toNat_inj.mp
      rw [m_div_thousand_toNat, hM3]; omega
    set neg : Bool := decide (cN.signum < 0) with hneg_def
    set working : Number := if neg then cN.operator_neg else cN with hw_def
    have hneg0 : neg = false := by rw [hneg_def, Number.signum_neg_decide]; exact hcNneg
    have hwork : working = cN := by rw [hw_def, hneg0]; exact if_neg Bool.false_ne_true
    have hnz : working.normalizeToRange kMinValue kMaxValue .to_nearest
        = .ok (c.mValue.toInt64, c.mOffset) := by
      rw [hwork]
      have h : cN.normalizeToRange cMinValue cMaxValue .to_nearest
          = .ok (c.mValue.toInt64, c.mOffset) := by
        rw [normalizeToRange_16_exact cN .to_nearest
            (by rw [hcNmant, hM3]; have := hiou.mant_lo; omega)
            (by rw [hcNmant, hM3]; have := hiou.mant_hi; omega)
            (by rw [hcNmant, hM3]; omega)
            (by rw [hcNexp]; have := hiou.exp_lo; unfold minExponent; omega)
            (by rw [hcNexp]; have := hiou.exp_hi; unfold maxExponent; omega),
            hcNneg, if_neg Bool.false_ne_true, hcNmant, hq3, hcNexp,
            show c.mOffset - 3 + 3 = c.mOffset from by ring]
      exact h
    have hof : STAmount.ofNumber .fractional cN .to_nearest
        = STAmount.checked .fractional (c.mValue.toInt64).toUInt64 c.mOffset neg .to_nearest := by
      unfold STAmount.ofNumber
      rw [if_neg (by decide), ← hneg_def, ← hw_def, hnz]
    rw [hneg0] at hof
    rw [show (c.mValue.toInt64).toUInt64 = c.mValue from rfl] at hof
    rw [hof] at hA
    have hAeq : A = ⟨.fractional, c.mValue, c.mOffset, false⟩ :=
      (STAmount.checked_iou_cases .fractional c.mValue c.mOffset false .to_nearest rfl
        hiou.mant_lo hiou.mant_hi
        (by have := hiou.exp_lo; unfold minExponent; omega)
        (by have := hiou.exp_hi; unfold maxExponent; omega)
        A hA hAnz).2.2
    rw [hAeq, STAmount.toRat_of_nonneg (⟨.fractional, c.mValue, c.mOffset, false⟩ : STAmount) rfl,
        STAmount.toRat_of_nonneg c hcneg]
  · -- integral: integer-valued, exact via `ofNumber_integral_exact`
    have hnti : nt.isIntegral = true := by rw [← hnt]; exact hint.is_integral
    obtain ⟨an, han, hval, hnorm⟩ :=
      STAmount.toNumber_exact_canonical c .to_nearest (Or.inr ⟨hint, hsz⟩)
    have hancN : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
    have hval' : cN.toRat = c.toRat := hancN ▸ hval
    have hnorm' : cN.isNormalized := hancN ▸ hnorm
    have hden : cN.toRat.den = 1 := by rw [hval']; exact STAmount.IntegralCanonical.den_eq_one c hint
    rw [STAmount.ofNumber_integral_exact nt cN .to_nearest A hnti hnorm' hden hA]
    exact hval'

set_option maxHeartbeats 1000000 in
set_option linter.style.maxHeartbeats false in
/-- **Proof body of `Vault.deposit_withdraw_roundtrip`.** Wires the banked raw
pricing bounds into `roundtrip_algebra`: the charge band
(`sharesToAssetsDeposit_charge_nonempty_raw`, `19/(2^63-3)`) plus the upward
`ofNumber` ceiling, the stored-total band (`operator_add_nonneg_rounds`,
`6/(2^63-3)`), and the payout band (`sharesToAssetsWithdraw_spec_raw`,
`12/(2^63-3)`) with its downward floor. `r₁.vault'` is a `Vault` from
`deposit_lawful`; `WithdrawNavExact` on `r₁.vault'` is derived from
`deposit_preserves_unrealized` + `hI`/`hL`. Splits empty (final withdrawal,
`assets' = amountDeposit'` exactly) vs non-empty, with the charge/payout
underflow (`isZero`) corners discharged separately. -/
theorem Vault.deposit_withdraw_roundtrip_proof (v : Vault) (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)

    (hL : v.toExact.lossUnrealized = 0)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical)
    (_hAV : v.assetsAvailable = v.assetsTotal)
    (hDc : r₁.amountDeposit'.ExactCanonical)
    (hDnn : 0 ≤ r₁.amountDeposit'.toRat)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂)
    (herr₂ : r₂.error = none) :
    r₂.assets'.toRat ≤ r₁.amountDeposit'.toRat * (1 + 2 * depositε) ∧
    (r₂.assets'.isZero = false →
      r₁.amountDeposit'.toRat - r₂.assets'.toRat ≤
        r₁.amountDeposit'.toRat * (2 * depositε)
          + (10 : ℚ) ^ r₂.assets'.exponent + (10 : ℚ) ^ r₁.amountDeposit'.exponent) := by
  -- destructure the deposit result so its scalar fields are concrete
  obtain ⟨re, rlv, rad, rsc⟩ := r₁
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, _hshdon, hinsolv, _hdon,
    hcomp, hcN, hsN, hat, hav, hst, hmax, hamt, hshr, hrv⟩ :=
    Vault.deposit_success_reduces v amountDeposit false _ hok₁ herr₁
  -- read the component facts through the constructor projections, then substitute
  have hamt' : rad = aD := hamt
  have hshr' : rsc = sC := hshr
  have herr' : re = none := herr₁
  subst rad; subst rsc; subst re
  have hok₂' : rlv.withdraw (.vaultShares sC) false = .ok r₂ := hok₂
  set V' : RawVault := { v with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } with hV'def
  -- the deposited state `rlv` is lawful; its record is `V'`
  have hrlv : rlv.toRawVault = V' := hrv
  have hWF₁ : V'.WF := hrlv ▸ rlv.wf
  -- `rlv` and the record `V'` denote the same lawful vault (the proof fields are irrelevant)
  have hRW : rlv = (⟨V', hWF₁, hrlv ▸ rlv.valid⟩ : Vault) := by
    obtain ⟨rr, rwf, rval⟩ := rlv
    obtain rfl : rr = V' := hrlv
    rfl
  have hinsolv' : v.isInsolvent = false := hinsolv rfl
  obtain ⟨shares, hats, hshz, hsad, _hgt, hseq⟩ := computeDeposit_success_reduces v am aD sC (hcomp rfl)
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hamCanon : am.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit am v.assetsTotal hcanon hround with hc | hz
    · exact hc
    · rw [hz] at hamz; exact absurd hamz (by decide)
  have ham_nn : 0 ≤ am.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit am v.assetsTotal hcanon (le_of_lt hpos) hround
  have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
  have ham_pos : 0 < am.toRat := lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
  have hshpos : 0 < shares.toRat := assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
  have hSCpos : 0 < sC.toRat := by rw [hseq]; exact hshpos
  have hsad' : sharesToAssetsDeposit v sC = .ok aD := by rw [hseq]; exact hsad
  have hshc' : sC.IntegralCanonical := hseq ▸ hshc
  have hshnt' : sC.mNumericType = .int64 := hseq ▸ hshnt
  obtain ⟨hcN_val, hcN_norm⟩ := sharesToAssetsDeposit_toNumber_exact v sC aD cN hshc' hshnt' hsad' hcN
  have hcN_nn : 0 ≤ cN.toRat := by rw [hcN_val]; exact hDnn
  have hL0 : v.lossUnrealized = Number.zero := by
    have hmzL : v.lossUnrealized.mantissa_ = 0 := by
      by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero v.lossUnrealized h) hL
    exact Number.eq_zero_of_mantissa_zero v.lossUnrealized v.wf.lossUnrealized_norm hmzL
  have hNav₁ : V'.WithdrawNavExact false := by
    refine ⟨at', ?_, ?_⟩
    · show at'.operator_sub v.lossUnrealized .to_nearest = .ok at'
      rw [hL0]; exact operator_sub_zero_right _ _
    · show at'.toRat = at'.toRat - v.lossUnrealized.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]; ring
  obtain ⟨cw, aN', sta, hcomp2, herr_cw, haN', hlt, hsta, hsb, hdisj⟩ :=
    Vault.withdraw_success_reduces rlv (.vaultShares sC) false r₂ hok₂' herr₂
  -- the withdraw reduction speaks of `rlv`; rephrase it as the reconstructed record
  rw [hRW] at hcomp2 hlt hsta hdisj
  obtain ⟨hstw, hsr⟩ := computeWithdrawByShares_none_reduces _ sC false cw hcomp2 herr_cw
  have hSC_canon : sC.Canonical := by
    refine ⟨fun _ => ⟨hshc', ?_⟩, fun hf => ?_⟩
    · rw [hshnt']; decide
    · rw [show sC.integral = sC.mNumericType.isIntegral from rfl, hshnt'] at hf; exact absurd hf (by decide)
  have hpay := Vault.sharesToAssetsWithdraw_spec_raw ⟨V', hWF₁, hrlv ▸ rlv.valid⟩ sC cw.assets' false hSCpos.le hSC_canon hNav₁ hstw
  have hAnn : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hru := operator_add_nonneg_rounds v.assetsTotal cN at' v.wf.assetsTotal_norm hcN_norm hAnn hcN_nn hat
  have hTnn : 0 ≤ v.assetsTotal.toRat + cN.toRat := add_nonneg hAnn hcN_nn
  simp only [RoundsWithin, RatValued.toRat] at hru
  rw [abs_of_nonneg hTnn] at hru
  have hstore := abs_le.mp hru
  have hSharesEq : (V'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) + sC.toRat := by
    rw [← hrlv]
    exact (Vault.deposit_vault_updates v amountDeposit false hcanon hpos
      ⟨none, rlv, aD, sC⟩ hok₁ herr₁).2.2 hSsz
  have hAT_ex : v.toExact.assetsTotal = v.assetsTotal.toRat := rfl
  have hSTvnn : (0:ℚ) ≤ (v.toExact.sharesTotal : ℚ) := by positivity
  have hV'ST : V'.sharesTotal.toRat = (v.toExact.sharesTotal : ℚ) + sC.toRat := by
    rw [← RawVault.WF.toExact_sharesTotal V' hWF₁, hSharesEq]
  have hIA_eq : V'.idealAssetsWithdraw false sC.toRat
      = at'.toRat * sC.toRat / ((v.toExact.sharesTotal : ℚ) + sC.toRat) := by
    unfold RawVault.idealAssetsWithdraw RawVault.withdrawNav
    rw [if_neg (by decide), hSharesEq]
    have hwn : V'.toExact.assetsTotal - V'.toExact.lossUnrealized
        = at'.toRat := by
      show at'.toRat - v.lossUnrealized.toRat = at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]; ring
    rw [hwn]
  have hUAnn : (0:ℚ) ≤ (10:ℚ) ^ r₂.assets'.exponent := le_of_lt (zpow_pos (by norm_num) _)
  have hUCnn : (0:ℚ) ≤ (10:ℚ) ^ aD.exponent := le_of_lt (zpow_pos (by norm_num) _)
  rcases hdisj with ⟨hfin, hlossg, allAvail, hallAvail, hrfin⟩ |
      ⟨hne, sbn, at2, av2, st2, atr, atr2, hsbn, hat2, hatr, hatr2, hg2, hav2, hst2, hrnf⟩
  · -- FINAL branch: the empty starting vault (`sharesTotal = 0`), where redeeming the
    -- issued shares is the whole-share-total withdrawal that pays `assetsAvailable'`.
    -- The empty-vault invariant forces `assetsAvailable = 0`, so the stored total is
    -- `av' = cN = amountDeposit'.toNumber` and the payout `ofNumber v.numericType av'`
    -- snaps back to `amountDeposit'` exactly (`ofNumber_charge_roundtrip`). Both conjuncts
    -- reduce to `A = C`.
    have hDnn' : 0 ≤ aD.toRat := hDnn
    have hr2a : r₂.assets' = allAvail := by rw [hrfin.1]
    -- Empty starting vault: the whole share total is redeemed, so `sharesTotal = 0`.
    have hSeq : sC.toRat = V'.sharesTotal.toRat :=
      (Vault.operator_eq_total_iff ⟨V', hWF₁, hrlv ▸ rlv.valid⟩ sta sC hSCpos hSC_canon hshnt' hsta).mp
        (by rw [← hsr]; exact hfin)
    have hSTv0 : (v.toExact.sharesTotal : ℚ) = 0 := by rw [hV'ST] at hSeq; linarith
    have hSTvN : v.toExact.sharesTotal = 0 := by exact_mod_cast hSTv0
    obtain ⟨_, hAA0⟩ := v.exact.empty_shares hSTvN
    have hAA0' : v.assetsAvailable.toRat = 0 := hAA0
    have hAAm0 : v.assetsAvailable.mantissa_ = 0 := by
      by_contra h
      exact (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsAvailable h) hAA0'
    have hAAzero : v.assetsAvailable = Number.zero :=
      Number.eq_zero_of_mantissa_zero v.assetsAvailable v.wf.assetsAvailable_norm hAAm0
    rw [hAAzero] at hav
    have hV'aa : V'.assetsAvailable = av' := by rw [hV'def]
    have hV'nt : V'.numericType = v.numericType := by rw [hV'def]
    rw [hV'nt, hV'aa] at hallAvail
    have hnt_aD : aD.mNumericType = v.numericType :=
      sharesToAssetsDeposit_mNumericType v sC aD hsad'
    rw [hr2a]
    show allAvail.toRat ≤ aD.toRat * (1 + 2 * depositε) ∧
        (allAvail.isZero = false → aD.toRat - allAvail.toRat ≤
          aD.toRat * (2 * depositε) + (10 : ℚ) ^ allAvail.exponent + (10 : ℚ) ^ aD.exponent)
    by_cases hAz : allAvail.mValue = 0
    · -- zero payout: both conjuncts hold trivially
      have hA0 : allAvail.toRat = 0 := (STAmount.toRat_eq_zero_iff allAvail).mpr hAz
      refine ⟨?_, ?_⟩
      · rw [hA0]; exact mul_nonneg hDnn' (by rw [depositε_eq]; norm_num)
      · intro hcontra
        rw [STAmount.isZero, hAz] at hcontra
        exact absurd hcontra (by decide)
    · -- nonzero payout: exact value roundtrip `A = C`
      have hcNnz : cN.operator_eq Number.zero = false := by
        by_contra hc
        have hc' : cN.operator_eq Number.zero = true := by
          cases h : cN.operator_eq Number.zero with
          | true => rfl
          | false => exact absurd h hc
        have havz : av' = Number.zero :=
          Except.ok.inj (hav.symm.trans (zero_operator_add_zero cN hc'))
        have hsrc := STAmount.ofNumber_source_ne_zero v.numericType av' .to_nearest allAvail
          hallAvail hAz
        rw [havz] at hsrc; exact hsrc rfl
      have havcN : av' = cN := Except.ok.inj (hav.symm.trans (zero_operator_add_ne cN hcNnz))
      rw [havcN] at hallAvail
      have hkey : allAvail.toRat = aD.toRat :=
        ofNumber_charge_roundtrip v.numericType aD cN allAvail hnt_aD hDc hDnn' hcN hallAvail hAz
      refine ⟨?_, ?_⟩
      · rw [hkey]
        have hprod : (0:ℚ) ≤ aD.toRat * (2 * depositε) :=
          mul_nonneg hDnn' (by rw [depositε_eq]; norm_num)
        have hexpand : aD.toRat * (1 + 2 * depositε)
            = aD.toRat + aD.toRat * (2 * depositε) := by ring
        rw [hexpand]; linarith
      · intro _
        rw [hkey]
        have h1 : (0:ℚ) ≤ aD.toRat * (2 * depositε) :=
          mul_nonneg hDnn' (by rw [depositε_eq]; norm_num)
        have h2 : (0:ℚ) ≤ (10:ℚ) ^ allAvail.exponent := le_of_lt (zpow_pos (by norm_num) _)
        have h3 : (0:ℚ) ≤ (10:ℚ) ^ aD.exponent := le_of_lt (zpow_pos (by norm_num) _)
        linarith
  · have hr2a : r₂.assets' = cw.assets' := by rw [hrnf.1]
    have hr2exp : r₂.assets'.exponent = cw.assets'.exponent := by rw [hr2a]
    have hStvpos : 0 < (v.toExact.sharesTotal : ℚ) := by
      have hiff := Vault.operator_eq_total_iff ⟨V', hWF₁, hrlv ▸ rlv.valid⟩ sta sC hSCpos hSC_canon hshnt' hsta
      have hne' : sC.operator_eq sta = false := by rw [← hsr]; exact hne
      have hne_val : sC.toRat ≠ V'.sharesTotal.toRat := by
        intro heq; rw [hiff.mpr heq] at hne'; exact absurd hne' (by decide)
      rw [hV'ST] at hne_val
      have hSTne : (v.toExact.sharesTotal : ℚ) ≠ 0 := fun h0 => hne_val (by rw [h0]; ring)
      exact lt_of_le_of_ne hSTvnn (Ne.symm hSTne)
    by_cases hAz : cw.assets'.isZero = true
    · refine ⟨?_, ?_⟩
      · rw [hr2a, (STAmount.toRat_eq_zero_iff cw.assets').mpr
          (by rw [STAmount.isZero] at hAz; exact beq_iff_eq.mp hAz)]
        exact mul_nonneg hDnn (by rw [depositε_eq]; norm_num)
      · intro hcontra; rw [hr2a] at hcontra; rw [hAz] at hcontra; exact absurd hcontra (by decide)
    · have hAnz : cw.assets'.isZero = false := by
        cases hb : cw.assets'.isZero with
        | true => exact absurd hb hAz | false => rfl
      have hmz : v.assetsTotal.mantissa_ ≠ 0 := by
        have hApos : 0 < v.assetsTotal.toRat := by
          by_contra h; push_neg at h
          have hA0 : v.assetsTotal.toRat = 0 := le_antisymm h hAnn
          have hins : v.isInsolvent = true := (Vault.isInsolvent_iff_proof ⟨v.toRawVault, v.wf, (RawVault.valid_iff_exact v.toRawVault v.wf).mpr v.exact⟩).mpr
            ⟨hA0, by exact_mod_cast hStvpos⟩
          rw [hins] at hinsolv'; exact absurd hinsolv' (by decide)
        exact Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hApos)
      have hCnz : aD.isZero = false := by
        by_contra hz0
        have hz : aD.isZero = true := by
          cases hb : aD.isZero with | true => rfl | false => exact absurd hb hz0
        have haD0 : aD.mValue = 0 := by rw [STAmount.isZero] at hz; exact beq_iff_eq.mp hz
        have hC0 : aD.toRat = 0 := (STAmount.toRat_eq_zero_iff aD).mpr haD0
        have hApos : 0 < v.toExact.assetsTotal :=
          lt_of_le_of_ne hAnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz))
        obtain ⟨Q, hcQ, hidpos, hQnz, hQz⟩ :=
          sharesToAssetsDeposit_charge_nonempty_raw v sC aD hshc' hshnt' hSCpos hmz hsad'
        have hIC_eq' : v.idealChargeDeposit sC.toRat
            = v.toExact.assetsTotal * sC.toRat / (v.toExact.sharesTotal : ℚ) := by
          unfold RawVault.idealChargeDeposit RawVault.depositNav
          rw [if_neg (ne_of_gt hApos)]
        have hmvne : cw.assets'.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hAnz; exact hAnz)
        have hA_lo : (10 : ℚ) ^ (-81 : ℤ) ≤ cw.assets'.toRat := by
          have hcanon := Vault.sharesToAssetsWithdraw_disj_canonical ⟨V', hWF₁, hrlv ▸ rlv.valid⟩ sC cw.assets' false hSC_canon hstw hmvne
          have := STAmount.canonical_disj_abs_toRat_ge cw.assets' hcanon hmvne
          rwa [abs_of_nonneg hpay.1] at this
        have hcNm : cN.mantissa_ = 0 := by
          by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero cN h) (by rw [hcN_val]; exact hC0)
        have hcN0 : cN = Number.zero := Number.eq_zero_of_mantissa_zero cN hcN_norm hcNm
        have hat'_eq : at' = v.assetsTotal := by
          have hh := hat; rw [hcN0, operator_add_zero_right] at hh; exact (Except.ok.inj hh).symm
        have hat'_toRat : at'.toRat = v.toExact.assetsTotal := by rw [hAT_ex, hat'_eq]
        by_cases hQm : Q.mantissa_ = 0
        · have hICsmall := hQz hQm
          have hIA_le_IC : V'.idealAssetsWithdraw false sC.toRat ≤ v.idealChargeDeposit sC.toRat := by
            rw [hIA_eq, hIC_eq', hat'_toRat]
            exact div_le_div_of_nonneg_left (mul_nonneg hAnn hSCpos.le) hStvpos (by linarith [hSCpos])
          have h2 : V'.idealAssetsWithdraw false sC.toRat * (1 + 12 / (2 ^ 63 - 3))
              ≤ v.idealChargeDeposit sC.toRat * (1 + 12 / (2 ^ 63 - 3)) :=
            mul_le_mul_of_nonneg_right hIA_le_IC (by norm_num)
          have hApow : (16 : ℚ) < (10 : ℚ) ^ (32669 : ℤ) :=
            calc (16 : ℚ) < (10 : ℚ) ^ (2 : ℤ) := by norm_num
              _ ≤ (10 : ℚ) ^ (32669 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
          have hchain : (16 : ℚ) * 10 ^ (-32750 : ℤ) < 10 ^ (-81 : ℤ) := by
            rw [show (-81 : ℤ) = 32669 + (-32750) from by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
            exact mul_lt_mul_of_pos_right hApow (zpow_pos (by norm_num) _)
          have hA_small : cw.assets'.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
            have hlt : v.idealChargeDeposit sC.toRat * (1 + 12 / (2 ^ 63 - 3)) < 16 * 10 ^ (-32750 : ℤ) := by
              nlinarith [hICsmall, hidpos, zpow_pos (show (0:ℚ) < 10 by norm_num) (-32750 : ℤ)]
            linarith [hpay.2.2.1, h2, hlt, hchain]
          linarith [hA_lo, hA_small]
        · by_cases hint : v.numericType.isIntegral = true
          · obtain ⟨hQnorm, hQneg, _⟩ := hQnz hQm
            have hge := STAmount.ofNumber_integral_upward_ge v.numericType Q aD hint hQnorm hQneg hcQ
            have hQpos : 0 < Q.toRat :=
              lt_of_le_of_ne (by rw [Number.toRat_of_nonneg Q hQneg]; positivity)
                (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero Q hQm))
            linarith [hge, hC0]
          · have hnt : aD.mNumericType = v.numericType :=
              STAmount.ofNumber_mNumericType v.numericType Q .upward aD hcQ
            have hfrac : v.numericType.isIntegral = false := by
              cases h : v.numericType.isIntegral with | true => exact absurd h hint | false => rfl
            rcases hDc with hio | ⟨hic, _⟩
            · have hml := hio.mant_lo; rw [haD0] at hml; simp at hml
            · have hii := hic.is_integral; rw [hnt, hfrac] at hii; exact absurd hii (by decide)
      have hCpos : 0 < aD.toRat := by
        have h := STAmount.toRat_ne_zero aD (ne_of_beq_false (by rw [STAmount.isZero] at hCnz; exact hCnz))
        exact lt_of_le_of_ne hDnn (Ne.symm h)
      obtain ⟨Q, hQlo, hQhi, hQClo, hQChi, hICpos, hIC_eq⟩ :=
        roundtrip_charge_Q v sC aD hshc' hshnt' hSCpos hmz hCnz hsad'
      have hicid : v.toExact.assetsTotal * sC.toRat
          = v.idealChargeDeposit sC.toRat * (v.toExact.sharesTotal : ℚ) := by
        rw [hIC_eq]; field_simp
      have hIAid : V'.idealAssetsWithdraw false sC.toRat
          * ((v.toExact.sharesTotal : ℚ) + sC.toRat) = at'.toRat * sC.toRat := by
        rw [hIA_eq, div_mul_cancel₀ _ (add_pos hStvpos hSCpos).ne']
      have halg := roundtrip_algebra aD.toRat cw.assets'.toRat (v.idealChargeDeposit sC.toRat)
        Q.toRat at'.toRat (V'.idealAssetsWithdraw false sC.toRat) v.toExact.assetsTotal
        sC.toRat (v.toExact.sharesTotal : ℚ) ((10:ℚ)^cw.assets'.exponent) ((10:ℚ)^aD.exponent)
        hSCpos hStvpos hAnn hCpos hICpos hicid hQlo hQhi hQClo hQChi
        (by rw [hAT_ex, ← hcN_val]; nlinarith [hstore.1, hstore.2])
        (by rw [hAT_ex, ← hcN_val]; nlinarith [hstore.1, hstore.2])
        hIAid hpay.2.1 hpay.1 (le_of_lt (zpow_pos (by norm_num) _)) (le_of_lt (zpow_pos (by norm_num) _))
        hpay.2.2.1 (hpay.2.2.2 hAnz)
      refine ⟨?_, ?_⟩
      · rw [hr2a]; exact halg.1
      · intro _; rw [hr2a]; exact halg.2


/-! ## Witness for `Vault.deposit_withdraw_roundtrip_attained`

The `wvF` family in `DepositWitness` hand-steps the deposit of `1` fractional
unit into the vault `(3 assets, 7·10¹⁵ shares)`, issuing `⌊7·10¹⁵/3⌋ =
2333333333333333` shares for a taken amount `wcF = 0.9999999999999999`. Redeeming
exactly those shares from the post-deposit vault `wvF'` pays back
`0.9999999999999998`, one 16-digit ULP `10⁻¹⁶` short of the taken amount, which
exceeds the `2·depositε` relative band (`≈ 2·10⁻¹⁷`): the ULP dominates. The
concrete deposit and withdraw runs and the strict miss are settled by
`native_decide` on the fully computable pipeline; this is the single witness leaf
where the compiler axioms (`Lean.ofReduceBool`, `Lean.trustCompiler`) are
admitted, per the approved witness policy. -/

/-- Value of the witness vault's stored share total. -/
private theorem wvF_shares_toRat' :
    (⟨false, 7000000000000000000, -3⟩ : Number).toRat = ((7000000000000000 : ℕ) : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((7000000000000000000 : UInt64).toNat) = 7000000000000000000 from by decide]
  norm_num

/-- The witness vault's representation is well-formed (kernel-checked). -/
private theorem wvF_WF : wvF.WF := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Number.operator_sub_self_ok wvF.assetsTotal .downward⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · intro m hm; rw [show wvF.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [wvF_shares_toRat']; positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [wvF_shares_toRat']; exact Rat.den_natCast _
  · intro _; rfl
  · decide

/-- The witness vault satisfies the invariant (kernel-checked). -/
private theorem wvF_Valid : wvF.Valid := by
  have wvF_exact_assetsTotal : wvF.toExact.assetsTotal = 3 := by
    show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
    rw [Number.toRat_of_nonneg _ rfl,
        show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
    norm_num
  have wvF_exact_sharesTotal : wvF.toExact.sharesTotal = 7000000000000000 := by
    show wvF.sharesTotal.toRat.num.toNat = _
    rw [show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl, wvF_shares_toRat']
    norm_num
    rfl
  refine (RawVault.valid_iff_exact wvF wvF_WF).mpr ?_
  have hAT := wvF_exact_assetsTotal
  have hAA : wvF.toExact.assetsAvailable = 3 := by
    show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
    rw [Number.toRat_of_nonneg _ rfl,
        show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
    norm_num
  have hST := wvF_exact_sharesTotal
  have hL : wvF.toExact.lossUnrealized = 0 := by
    simp only [RawVault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAT]; norm_num
  · rw [hAA]; norm_num
  · rw [hAT, hAA]
  · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · intro h; rw [hST] at h; exact absurd h (by norm_num)
  · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · rw [hL]
  · rw [hL, hAT, hAA]; norm_num
  · rw [hAT, hL]; norm_num

/-- The witness vault as a `Vault`. `.toRawVault` is defeq `wvF` by construction,
so the witness deposit/withdraw runs stay computable under `native_decide`. -/
private def wvF_lawful' : Vault := ⟨wvF, wvF_WF, wvF_Valid⟩

set_option linter.style.nativeDecide false in
/-- **Proof body of `Vault.deposit_withdraw_roundtrip_attained`.** Instantiates the
round trip at the `wvF` witness: deposit `waF` into `wvF` yields `wrF` (charge
`wcF`), and redeeming the issued `wsF` shares from `wvF'` misses `wcF` by a full
16-digit ULP, past the relative band. The concrete deposit/withdraw runs and the
strict miss are settled by `native_decide` (compiler axioms admitted here only,
per the approved witness policy). -/
theorem Vault.deposit_withdraw_roundtrip_attained_proof :
    ∃ (v : Vault) (amountDeposit : STAmount) (r₁ : DepositResult) (r₂ : WithdrawResult),
      0 < amountDeposit.toRat ∧
      v.toExact.lossUnrealized = 0 ∧
      v.deposit amountDeposit false = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂ ∧
      r₂.error = none ∧
      RoundsWithinWitness r₂.assets' r₁.amountDeposit'.toRat (2 * depositε) := by
  refine ⟨wvF_lawful', waF, wrF,
    (wvF'L.withdraw (.vaultShares wsF) false).toOption.getD ⟨none, wvF'L, wcF, wsF⟩,
    ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · unfold RoundsWithinWitness; native_decide

end XRPL.Model.SingleAssetVault
