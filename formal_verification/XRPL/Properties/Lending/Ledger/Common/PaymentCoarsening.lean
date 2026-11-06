import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue

/-! # A payment that reaches `10^16` base units coarsens the vault

When AssetsAvailable plus a payment's principal and interest reaches `10^16` base units (the line), AssetsAvailable'
reaches it too, whether AssetsAvailable was below the line or already past it. So a payment that leaves
AssetsAvailable below the line was paid at base scale, with AssetsAvailable below the line before it as well. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private roundDown_shape ofNumber_frac_exact_of_units pow_add_nat
  from XRPL.Properties.Lending.Ledger.Common.DefaultCredit
open private sub_exact from XRPL.Properties.Lending.Common.SumRounding
open private add_downward_ge_any floor_mul_ge pow_grid STAmount.ofNumber_frac_downward_ge
  Loan.unimpairIfImpaired_balances from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps

/-- An IOU sum rounded to the nearest 16-digit amount stays at a line it reaches. -/
private lemma STAmount.round_iou_line (aa a' : Number) (b : Int) (haan : aa.isNormalized)
    (haaW : 10 ^ 16 * 10 ^ b ≤ aa.toRat) (hb : -10 ≤ b ∧ b ≤ 0)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') : 10 ^ 16 * 10 ^ b ≤ a'.toRat := by
  have hpb : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hp81 : (0 : ℚ) < 10 ^ (-81 : ℤ) := zpow_pos (by norm_num) _
  have hbW : (10 : ℚ) ^ b ≤ 10 ^ 16 * 10 ^ b := le_mul_of_one_le_left (zpow_pos (by norm_num) _).le (by norm_num)
  unfold STAmount.roundToNumericType at ha'
  cases hof : STAmount.ofNumber .fractional aa .to_nearest with
  | error e => rw [hof] at ha'; cases ha'
  | ok r =>
  rw [hof] at ha'
  simp only at ha'
  have hrf := STAmount.ofNumber_fractional_fczr aa _ r hof
  have haa0 : 0 ≤ aa.toRat := by linarith
  have haam : aa.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero aa h0] at haaW; linarith
  have hrz : r.mValue ≠ 0 := by
    intro hz
    have := STAmount.ofNumber_fractional_zero_below_min .fractional aa r .to_nearest rfl haan
      (Number.negative_false_of_nonneg aa haan haa0) haam hof hz
    linarith
  rw [STAmount.FracCanonZero.toNumber_val hrf .to_nearest a' ha']
  have hrc : r.IOUCanonical := hrf.2.resolve_right hrz
  have hN := STAmount.ofNumber_to_nearest_neighbour .fractional aa r haan haa0 hof (Or.inr hrz)
  unfold RoundsToRepresentableAt at hN
  change r.toRat = _ ∨ r.toRat = _ at hN
  have hp' : (0 : ℚ) < 10 ^ r.exponent := zpow_pos (by norm_num) _
  rcases hN with hfl | hce
  · rw [hfl]
    refine floor_mul_ge _ _ _ haaW ?_
    by_cases heb : r.exponent ≤ 16 + b
    · refine Or.inl ⟨((10 ^ (16 + b - r.exponent).toNat : ℕ) : ℤ), ?_⟩
      rw [← pow_grid, show r.exponent + ((16 + b - r.exponent).toNat : ℕ) = 16 + b by omega,
        zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    · refine Or.inr ⟨15, ?_, ?_⟩
      · calc (10 : ℚ) ^ 16 * 10 ^ b = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
          _ ≤ 10 ^ (r.exponent + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 10 ^ (15 : ℕ) * 10 ^ r.exponent := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      · -- the floor is a canonical amount, at least `10^15` steps, and at most the value
        have hr15 : (10 : ℚ) ^ (15 : ℕ) * 10 ^ r.exponent ≤ r.toRat := by
          rw [STAmount.toRat_of_nonneg r (STAmount.mIsNegative_false_of_nonneg r (by rw [hfl]; positivity) hrz)]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrc.mant_lo) (zpow_pos (by norm_num) _).le
        have hfle : (⌊aa.toRat / 10 ^ r.exponent⌋ : ℚ) * 10 ^ r.exponent ≤ aa.toRat := by
          have := Int.floor_le (aa.toRat / 10 ^ r.exponent)
          rw [le_div_iff₀ hp'] at this
          exact this
        rw [hfl] at hr15
        linarith
  · rw [hce]
    have := Int.le_ceil (aa.toRat / 10 ^ r.exponent)
    rw [div_le_iff₀ hp'] at this
    linarith

/-- An IOU credit that takes AssetsAvailable to `10^16` base units leaves it there. When AssetsAvailable plus the
amount reaches the line, AssetsAvailable' reaches it too, whether AssetsAvailable was below it or past it. -/
private lemma vault_credit_reaches (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded .fractional A = false)
    (hAg : ∃ k : ℕ, A.toRat = k * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat) (hb : -10 ≤ b ∧ b ≤ 0)
    (hreach : 10 ^ 16 * 10 ^ b ≤ A.toRat + c.toRat)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    10 ^ 16 * 10 ^ b ≤ a'.toRat := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hW0 : (0 : ℚ) < 10 ^ 16 * 10 ^ b := by positivity
  obtain ⟨Wn, hWn, hWv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) b (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hWv' : Wn.toRat = 10 ^ 16 * 10 ^ b := by rw [hWv]; push_cast; ring
  obtain ⟨-, hcrx⟩ := sumRoundAndSubtract_downward_le A c b .fractional st hA hA0 hc hc0 ⟨by omega, by omega⟩ h
  obtain ⟨hcrv, hcrn⟩ := hcrx cr hcr
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ h
  have hErange := postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE

  have hsumn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsum
  obtain ⟨-, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  have hsumW : 10 ^ 16 * 10 ^ b ≤ sum.toRat := by
    rw [← hWv']
    exact add_downward_ge_any A c sum Wn hA hc hsum hWn (by rw [hWv']; exact hW0) (by rw [hWv']; exact hreach)
  obtain ⟨G, j, hEG, hG80, hsG, hj, hsum'v, -, hsfl, hGj⟩ :=
    roundDown_shape sum sum' E hsumn hs0 ⟨by omega, hErange.2.2⟩ hsum'
  have hsum'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  have hs'0 : 0 ≤ sum'.toRat := by rw [hsum'v]; positivity
  have hpG : (0 : ℚ) < 10 ^ G := zpow_pos (by norm_num) _
  have hsum'W : 10 ^ 16 * 10 ^ b ≤ sum'.toRat := by
    by_cases hGb : G ≤ 16 + b
    · -- the line is on the grid `10^G`, and the floor of a sum past it
      have hX : (10 : ℚ) ^ 16 * 10 ^ b = ((10 ^ (16 + b - G).toNat : ℕ) : ℚ) * 10 ^ G := by
        rw [← pow_add_nat, show G + ((16 + b - G).toNat : ℕ) = 16 + b by omega,
          zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num
      rw [hX, hsum'v]
      have hlt : ((10 ^ (16 + b - G).toNat : ℕ) : ℚ) < (j : ℚ) + 1 := by
        have : ((10 ^ (16 + b - G).toNat : ℕ) : ℚ) * 10 ^ G < ((j : ℚ) + 1) * 10 ^ G := by
          rw [← hX, add_mul, one_mul, ← hsum'v]; linarith
        exact lt_of_mul_lt_mul_right this hpG.le
      have : 10 ^ (16 + b - G).toNat ≤ j := by
        have : (10 ^ (16 + b - G).toNat : ℕ) < j + 1 := by exact_mod_cast hlt
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hpG.le
    · -- a grid coarser than the line: the floor is at least one unit of it
      push Not at hGb
      have hj1 : 1 ≤ j := by
        rcases hGj with hGE | hj15
        · -- the exponent after the payment comes from the sum, which is then past `10^(E + 14)`
          subst hGE
          obtain ⟨s0, hs0', hne⟩ := postSumExponent_reduces _ _ _ _ _ hE
          have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0'
          have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0' (by linarith)
          obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b G hs0n hs00 (by omega) hne (by omega)
          obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (G + 14) (by constructor <;> norm_num)
            ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
          rw [show ((1 : ℤ) : ℚ) = 1 by norm_num, one_mul] at hwv
          have h1415 : (10 : ℚ) ^ (G + 14) < 10 ^ (G + 15) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
          have hge14 : (10 : ℚ) ^ (G + 14) ≤ A.toRat + c.toRat := by
            by_contra hlt14
            push Not at hlt14
            have := operator_add_le_of_le_normalized _ _ _ _ hA hc hs0' hw (by rw [hwv]; linarith)
            rw [hwv] at this
            linarith
          have hs14 := add_downward_ge_any A c sum w hA hc hsum hw (by rw [hwv]; positivity) (by rw [hwv]; exact hge14)
          rw [hwv] at hs14
          have h014 : (10 : ℚ) ^ G < 10 ^ (G + 14) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
          by_contra hj0
          have : j = 0 := by omega
          rw [this] at hsum'v
          simp only [Nat.cast_zero, zero_mul] at hsum'v
          linarith
        · exact le_trans (by norm_num) hj15
      rw [hsum'v]
      calc (10 : ℚ) ^ 16 * 10 ^ b = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
        _ ≤ 10 ^ G := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ ≤ (j : ℚ) * 10 ^ G := le_mul_of_one_le_left hpG.le (by exact_mod_cast hj1)

  obtain ⟨g, kA, hbg, hgG, hkA, hAv⟩ : ∃ (g : Int) (kA : ℕ), b ≤ g ∧ g ≤ G ∧ kA < 10 ^ 16 ∧
      A.toRat = kA * 10 ^ g := by
    rcases (STAmount.isRounded_eq_false_iff _ A hA hA0).mp hArep with h0 | ⟨m, e, hmlo, hmhi, helo, hehi, hv⟩
    · exact ⟨G, 0, by omega, le_rfl, by norm_num, by rw [h0]; simp⟩
    · have hpe : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
      have hm15 : (10 : ℚ) ^ (15 : ℤ) ≤ m := by norm_num; exact_mod_cast hmlo
      have hApos : 0 < A.toRat := by rw [hv]; nlinarith
      have hAsum : A.toRat ≤ sum.toRat := add_downward_ge_any A c sum A hA hc hsum hA hApos (by linarith)
      have hsm : sum.mantissa_ ≠ 0 := fun h0 => by
        rw [Number.toRat_eq_zero_of_mantissa_zero sum h0] at hAsum; linarith
      -- the sum reaches AssetsAvailable, so its 16th digit is no finer than AssetsAvailable's
      have heG : e ≤ G := by
        have h3 := hsG hsm
        obtain ⟨-, hhi⟩ := hsumn.mantissaBounds_nat hsm
        have hsv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsumn hs0)
        have h1 : (10 : ℚ) ^ (e + 15) < 10 ^ (sum.exponent_ + 19) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
          have hm19 : (sum.mantissa_.toNat : ℚ) < 10 ^ (19 : ℤ) := by norm_num; exact_mod_cast hhi
          have hps : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
          calc (10 : ℚ) ^ e * 10 ^ (15 : ℤ) ≤ A.toRat := by
                rw [hv, mul_comm]; exact mul_le_mul_of_nonneg_right hm15 hpe.le
            _ ≤ sum.toRat := hAsum
            _ = sum.mantissa_.toNat * 10 ^ sum.exponent_ := hsv
            _ < 10 ^ (19 : ℤ) * 10 ^ sum.exponent_ := mul_lt_mul_of_pos_right hm19 hps
            _ = 10 ^ sum.exponent_ * 10 ^ (19 : ℤ) := mul_comm _ _
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
        omega
      obtain ⟨a, ha⟩ := hAg
      by_cases hbe : b ≤ e
      · exact ⟨e, m, hbe, heG, hmhi, hv⟩
      · push Not at hbe
        refine ⟨b, a, le_rfl, by omega, ?_, ha⟩
        have hlt : (a : ℚ) * 10 ^ b < 10 ^ 16 * 10 ^ b := by
          rw [← ha, hv]
          calc (m : ℚ) * 10 ^ e < 10 ^ 16 * 10 ^ e := mul_lt_mul_of_pos_right (by exact_mod_cast hmhi) hpe
            _ ≤ 10 ^ 16 * 10 ^ b :=
              mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hbe.le) (by positivity)
        have := lt_of_mul_lt_mul_right hlt hp.le
        exact_mod_cast this
  have hpg : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _

  have hsplit : (10 : ℚ) ^ G = ((10 ^ (G - g).toNat : ℕ) : ℚ) * 10 ^ g := by
    rw [← pow_add_nat]; congr 1; omega
  set K : ℤ := ((j * 10 ^ (G - g).toNat : ℕ) : ℤ) - kA with hK
  have hKv : sum'.toRat - A.toRat = (K : ℚ) * 10 ^ g := by
    rw [hsum'v, hAv, hsplit, hK]; push_cast; ring
  have hKlo : -(kA : ℤ) ≤ K := by rw [hK]; omega
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ hsum'n hA hd
  have hstf := STAmount.ofNumber_fractional_fczr d _ st hst

  have hcrW : 10 ^ 16 * 10 ^ b ≤ A.toRat + cr.toRat := by
    by_cases hKhi : K ≤ 10 ^ 16
    · -- a difference of at most `10^16` units is exact, and the credit is the floored sum less AssetsAvailable
      have hedge : K.natAbs = 10 ^ 16 → g ≤ 79 := by
        intro hK16
        have hKeq : K = 10 ^ 16 := by omega
        have h1 : (10 : ℚ) ^ 16 * 10 ^ g ≤ sum'.toRat := by
          have := hKv
          rw [hKeq] at this
          push_cast at this
          linarith
        have h2 : sum'.toRat < 10 ^ 16 * 10 ^ G := by
          rw [hsum'v]
          exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) hpG
        have h3 : (10 : ℚ) ^ g < 10 ^ G := lt_of_mul_lt_mul_left (h1.trans_lt h2) (by positivity)
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h3
        omega
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow K g ⟨by omega, by omega⟩
        ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
      have hdv : d.toRat = sum'.toRat - A.toRat := sub_exact sum' A d w _ hsum'n hA hs'0 hA0 hd hw (by rw [hwv, hKv])
      have hstv : st.toRat = d.toRat :=
        ofNumber_frac_exact_of_units d g K _ st hdn (by rw [hdv, hKv]) (by omega) ⟨by omega, by omega⟩ hedge hst
      rw [hcrv, hstv, hdv]
      linarith
    · -- a larger difference is positive, and so is its IOU, past `10^16` units of `10^g`
      push Not at hKhi
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) g (by constructor <;> norm_num)
        ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
      have hwv' : w.toRat = 10 ^ 16 * 10 ^ g := by rw [hwv]; push_cast; ring
      have hdw : 10 ^ 16 * 10 ^ g ≤ d.toRat := by
        rw [← hwv']
        unfold Number.operator_sub at hd
        refine add_downward_ge_any sum' A.operator_neg d w hsum'n (Number.operator_neg_isNormalized A hA) hd hw
          (by rw [hwv']; positivity) ?_
        rw [Number.toRat_neg, hwv']
        have : ((10 ^ 16 : ℤ) : ℚ) ≤ (K : ℚ) := by exact_mod_cast hKhi.le
        push_cast at this
        nlinarith
      have hstw : 10 ^ 16 * 10 ^ g ≤ st.toRat := by
        refine STAmount.ofNumber_frac_downward_ge d st _ hdn ?_ hdw (fun s hs => ?_) hst
        · have : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ g := zpow_le_zpow_right₀ (by norm_num) (by omega)
          have : (10 : ℚ) ^ g ≤ 10 ^ 16 * 10 ^ g := le_mul_of_one_le_left hpg.le (by norm_num)
          linarith
        · by_cases hsg : s ≤ 16 + g
          · refine Or.inl ⟨((10 ^ (16 + g - s).toNat : ℕ) : ℤ), ?_⟩
            rw [← pow_grid, show s + ((16 + g - s).toNat : ℕ) = 16 + g by omega,
              zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            norm_num
          · refine Or.inr ?_
            calc (10 : ℚ) ^ 16 * 10 ^ g = 10 ^ (16 + g) := by
                  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
              _ ≤ 10 ^ (s + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
              _ = 10 ^ (15 : ℕ) * 10 ^ s := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      have hbg' : (10 : ℚ) ^ 16 * 10 ^ b ≤ 10 ^ 16 * 10 ^ g :=
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hbg) (by positivity)
      rw [hcrv]
      linarith

  have haaW : 10 ^ 16 * 10 ^ b ≤ aa.toRat := by
    rw [← hWv']
    exact Number.roundsToRepresentable_ge aa _ (operator_add_rounded_to_nearest _ _ _ hA hcrn haa) Wn hWn
      (by rw [hWv']; exact hcrW)
  exact STAmount.round_iou_line aa a' b (operator_add_isNormalized_to_nearest_sz _ _ _ hA hcrn haa) haaW hb ha'

/-- A payment that leaves AssetsAvailable below `10^16` base units was paid at base scale: AssetsAvailable plus
principalPaid + interestPaid was below the line before it. -/
lemma LendingLedger.pay_below_line {L L' : LendingLedger} (hR : L.Reachable) {k : Nat} {pt : LoanPaymentType}
    {amount : Number} (h : (L.apply (.loanPay k pt amount)).run = .ok (.ok L')) {loan : Loan} (hat : L.LoanAt k loan)
    {p : UnsettledPayment Vault} (hpay : (loan.payInstalments L.vault pt amount L.now).run = .ok (.ok p))
    (hA' : L'.vault.assetsAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent) :
    L.vault.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent := by
  obtain ⟨e, loan', r, -, hat', -, hok, rfl, -⟩ := LendingLedger.loanPay_parts h
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hat'
  obtain rfl := (hat.unique he₂ hb₂ hw₂).symm
  change r.pool'.assetsAvailable.toRat < _ at hA'
  have hasset := hR.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, -, -, -, -, -⟩ := LendingLedger.base_grid_proof L hR hmax
  obtain ⟨hls, hnt⟩ := hR.loanAt_scale hat
  obtain ⟨hblo, hbhi, hbint⟩ := L.vault.baseExponent_bounds
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid L.vault
  have hp : (0 : ℚ) < 10 ^ L.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ L.vault.assetsAvailable.toRat := L.vault.exact.assetsAvailable_nonneg

  obtain ⟨q, hq, hs⟩ := Loan.pay_ok loan L.vault pt amount L.now r hok
  rw [hpay] at hq
  obtain rfl := Except.ok.inj (Except.ok.inj hq)
  obtain ⟨-, hu', hst, -, -⟩ := Loan.payInstalments_ok loan L.vault pt amount L.now p hpay
  obtain ⟨hpAA, -, hpnt, hpbe⟩ := Loan.unimpairIfImpaired_balances loan L.vault p.pool loan.unimpaired
    (hR.storesAvailable hmax) hu'
  obtain ⟨toPool, _, _, _, _, raw, _, hsums, hadj, hlaw, -, -, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  obtain ⟨hPg, hIg⟩ := Loan.payInstalments_onGrid loan L.vault pt amount L.now p (by rw [hls]; omega) hpay
  rw [hls] at hPg hIg
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hparts
  obtain ⟨⟨hP0s, hI0s⟩, -⟩ := hparts
  have hP0 := Number.toRat_nonneg_of_not_signum_neg _ hPg.1 hP0s
  have hI0 := Number.toRat_nonneg_of_not_signum_neg _ hIg.1 hI0s
  obtain ⟨tot, credit, htot, hcred, hto⟩ := hsums.toPool
  rw [hpb, hnt, hpbe] at hcred
  obtain ⟨hsa, -⟩ := Vault.adjustBalances_ok_inv p.pool _ raw hadj
  obtain ⟨aa, haa, hround⟩ := hsa.cash
  rw [hpnt] at hround
  have hrA : r.pool'.assetsAvailable = raw.assetsAvailable := by
    rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl, (RawVault.to_lawful_ok hlaw).1]
  rw [hrA] at hA'
  obtain ⟨Wn, hWn, hWv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) L.vault.baseExponent
    (by constructor <;> norm_num) ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hWv' : Wn.toRat = 10 ^ 16 * 10 ^ L.vault.baseExponent := by rw [hWv]; push_cast; ring

  -- were the sum past the line, so would AssetsAvailable plus the rounded sum of principal and interest
  by_contra hge
  push Not at hge
  have htotn := operator_add_isNormalized_to_nearest_sz _ _ _ hPg.1 hIg.1 htot
  have htot0 : 0 ≤ tot.toRat := operator_add_nonneg _ _ _ hPg.1 hIg.1 htot (by linarith)
  have hpAA0 : 0 ≤ p.pool.assetsAvailable.toRat := by rw [hpAA]; exact hAA0
  have htotW : 10 ^ 16 * 10 ^ L.vault.baseExponent ≤ p.pool.assetsAvailable.toRat + tot.toRat := by
    by_cases hsmall : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat <
        10 ^ 16 * 10 ^ L.vault.baseExponent
    · have := Number.add_exact_of_grid hPg hIg (by nlinarith) (by nlinarith) hsr htot
      rw [this, hpAA]
      linarith
    · push Not at hsmall
      have := Number.roundsToRepresentable_ge tot _ (operator_add_rounded_to_nearest _ _ _ hPg.1 hIg.1 htot) Wn hWn
        (by rw [hWv']; exact hsmall)
      rw [hWv'] at this
      linarith
  obtain ⟨n, hn⟩ := hR.assetsAvailable_units hasset
  cases hint : L.vault.numericType.isIntegral
  · -- an IOU vault: AssetsAvailable' reaches the line too
    have hfr := NumericType.eq_fractional_of_not_integral hint
    rw [hfr] at hcred hround
    have hArep : STAmount.isRounded .fractional p.pool.assetsAvailable = false := by
      rw [STAmount.isRounded_eq_false_iff _ _ p.pool.wf.assetsAvailable_norm hpAA0, hpAA]
      have := hR.storesAvailable hmax
      rw [hfr] at this
      exact (STAmount.isRounded_eq_false_iff _ _ L.vault.wf.assetsAvailable_norm hAA0).mp this
    have := vault_credit_reaches p.pool.assetsAvailable tot L.vault.baseExponent credit toPool aa raw.assetsAvailable
      p.pool.wf.assetsAvailable_norm hpAA0 hArep ⟨n, by rw [hpAA, hn]⟩ htotn htot0 ⟨hblo, hbhi⟩ htotW hcred hto
      haa hround
    linarith
  · -- an XRP or MPT vault: the credit is the sum floored to a whole unit, which keeps AssetsAvailable' past the line
    have hb0 : L.vault.baseExponent = 0 := hbint hint
    unfold sumRoundAndSubtract at hcred
    rw [if_pos hint] at hcred
    obtain ⟨x, hx, hcred⟩ := bind_ok_peel _ _ _ hcred
    obtain rfl : x = credit := Except.ok.inj hcred
    have htneg := Number.negative_false_of_nonneg tot htotn htot0
    obtain ⟨iv, hiv, hxv⟩ := STAmount.ofNumber_integral_toRat _ tot _ x hint htneg hx
    obtain ⟨-, hfl2⟩ := Number.to_rep_downward_floor tot iv htotn htneg hiv
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ x hint hx
    have hsmall : x.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, hsnv, -⟩ := STAmount.toNumber_integral_small_exact x .to_nearest hic hsmall
    rw [hsn, Except.ok.injEq] at hto
    subst hto
    have hcrn : sn.isNormalized := STAmount.toNumber_isNormalized x _ sn hsn
    rw [hb0, zpow_zero, mul_one] at htotW hWv' hA' hn
    rw [hpAA, hn] at htotW
    -- AssetsAvailable is a whole number, so it reaches the line with the floor of the sum as well
    have hline : (10 ^ 16 : ℤ) ≤ (n : ℤ) + iv.toInt := by
      have : ((10 ^ 16 : ℤ) : ℚ) < (n : ℤ) + iv.toInt + 1 := by push_cast; linarith
      have : (10 ^ 16 : ℤ) < (n : ℤ) + iv.toInt + 1 := by exact_mod_cast this
      omega
    have haaW : (10 ^ 16 : ℚ) ≤ aa.toRat := by
      have := Number.roundsToRepresentable_ge aa _
        (operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa) Wn hWn (by
          rw [hWv', hsnv, hxv, hpAA, hn]
          have : ((10 ^ 16 : ℤ) : ℚ) ≤ ((n : ℤ) + iv.toInt : ℤ) := by exact_mod_cast hline
          push_cast at this
          linarith)
      rwa [hWv'] at this
    have haan := operator_add_isNormalized_to_nearest_sz _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa
    -- rounding to the asset lands on the floor or the ceiling of a value past the line
    unfold STAmount.roundToNumericType at hround
    cases hof : STAmount.ofNumber L.vault.numericType aa .to_nearest with
    | error e => rw [hof] at hround; cases hround
    | ok rr =>
    rw [hof] at hround
    simp only at hround
    obtain ⟨hic', hty'⟩ := STAmount.ofNumber_integral_canonical _ _ _ rr hint hof
    have hsmall' : rr.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic'.in_range
      rw [hty'] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn', hsn', hsnv', -⟩ := STAmount.toNumber_integral_small_exact rr .to_nearest hic' hsmall'
    rw [hsn', Except.ok.injEq] at hround
    have hN := STAmount.ofNumber_to_nearest_neighbour _ aa rr haan (by linarith) hof (Or.inl hint)
    unfold RoundsToRepresentableAt at hN
    change rr.toRat = _ ∨ rr.toRat = _ at hN
    rw [show rr.exponent = rr.mOffset from rfl, hic'.offset_zero, zpow_zero, div_one, mul_one, mul_one] at hN
    have hge' : ((10 ^ 16 : ℤ) : ℚ) ≤ raw.assetsAvailable.toRat := by
      rw [← hround, hsnv']
      rcases hN with hfl | hce
      · rw [hfl]; exact_mod_cast Int.le_floor.mpr (by push_cast; exact haaW)
      · rw [hce]; push_cast; exact haaW.trans (Int.le_ceil _)
    push_cast at hge'
    linarith

end XRPL.Model.Lending
