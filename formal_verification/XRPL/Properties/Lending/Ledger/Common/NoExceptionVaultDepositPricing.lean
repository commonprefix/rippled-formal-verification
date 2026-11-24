import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultDepositSteps
import XRPL.Properties.Vault.Proofs.NoInternalErrors
import XRPL.Properties.Vault.Proofs.Support.NoOverflow

/-! # The pricing of a deposit fails only as C++ catches it

A VaultDeposit prices its shares inside a block that turns every overflow error into `tecPATH_DRY`, and the pricing
fails with nothing else. On XRP the price is at most the deposited amount, so it is an XRP amount. -/

namespace XRPL.Model.SingleAssetVault.VaultDepositNoException

open XRPL.Model.Protocol
open XRPL.Model.Protocol.VaultDepositNoException
open XRPL.Model.Protocol.ErrorKinds
open XRPL.Model.Lending (Vault.HoldsAsset)

/-- The share pricing of a deposit fails only with an overflow error or a wrap. -/
lemma assetsToSharesDeposit_error (v : Vault) (amount : STAmount) {e : Error}
    (h : assetsToSharesDeposit v amount = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [assetsToSharesDeposit, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | exact number_add_error v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm ‹_›
    | exact number_normalized_error ‹_›
    | exact number_truncate_error ‹_›
    | exact ofNumber_int64_error ‹_›
    | exact toNumber_error ‹_›
    | exact number_mul_error ‹_›
    | exact number_div_error ‹_›

/-- On an empty vault the price of the shares a positive amount buys always converts to an amount: the shares are
that amount in share units, within the largest amount of the asset. -/
lemma empty_charge_computes (v : Vault) (hasset : Vault.HoldsAsset v) (ra shares : STAmount)
    (hrc : ra.Canonical) (hrp : 0 < ra.toRat) (hrle : ra.toRat ≤ v.numericType.maxAmount) (A : Number)
    (hA : v.assetsTotal = .ok A) (hmz : A.mantissa_ = 0) (hs : assetsToSharesDeposit v ra = .ok shares)
    (hsz : shares.isZero = false) :
    ∃ c, STAmount.checked v.numericType shares.mantissa (shares.exponent - v.scale.toNat) false .to_nearest
      = .ok c := by
  obtain ⟨hic, hint64⟩ := assetsToSharesDeposit_int64_canonical v ra shares hs
  have hshpos := assetsToSharesDeposit_pos v ra shares hrc hrp hs hsz
  have hneg := STAmount.mIsNegative_false_of_pos shares hshpos
  have hval : shares.toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_nonneg shares hneg, hic.offset_zero, zpow_zero, mul_one]
  have hin := hic.in_range
  rw [hint64] at hin
  have hm : shares.mantissa ≤ maxRep := by
    rw [UInt64.le_iff_toNat_le]
    exact hin
  have hmq : (shares.mValue.toNat : ℚ) ≤ 9223372036854775807 := by
    exact_mod_cast (show shares.mValue.toNat ≤ 9223372036854775807 from hin)
  refine (STAmount.checked_ok_iff v.numericType _ _ false .to_nearest hasset hm).mpr ?_
  rw [STAmount.unchecked_toRat, ite_eq_right (by decide), one_mul]
  show STAmount.RoundsInRange v.numericType .to_nearest
    ((shares.mValue.toNat : ℚ) * 10 ^ (shares.mOffset - (v.scale.toNat : ℤ)))
  rw [hic.offset_zero, zero_sub]
  by_cases hint : v.numericType.isIntegral = true
  · -- XRP or an MPT: the shares are the amount itself
    obtain ⟨hIs, -, hshv⟩ := DepTight.empty_shares_floor v ra shares hrc hrp A hA hmz hs hsz
    have hscale : v.scale.toNat = 0 := by rw [v.wf.scale_integral hint]; rfl
    rw [hIs, hscale] at hshv
    have hfl : shares.toRat ≤ ra.toRat := by
      rw [hshv]
      simpa using Int.floor_le (ra.toRat * (10 : ℚ) ^ ((0 : ℕ) : ℤ))
    rw [hscale]
    have hle : (shares.mValue.toNat : ℚ) ≤ v.numericType.maxAmount := by rw [← hval]; linarith
    simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_one]
    rcases hasset with hfr | hna | hi64
    · rw [hfr] at hint; cases hint
    · rw [hna, STAmount.roundsInRange_native_iff]
      rw [hna, maxAmount_native] at hle
      exact roundsWithinUnits_of_abs_le _ _ _ _ (by norm_num) (by rw [abs_of_nonneg (by positivity)]; simpa using hle)
    · rw [hi64, STAmount.roundsInRange_int64_iff]
      rw [hi64, maxAmount_int64] at hle
      exact roundsWithinUnits_of_abs_le _ _ _ _ (by norm_num) (by rw [abs_of_nonneg (by positivity)]; simpa using hle)
  · -- an IOU: at most the largest int64 in share units, scaled down
    have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    rw [hfr, STAmount.roundsInRange_fractional_iff]
    refine roundsWithinUnits_of_abs_le _ _ _ _ (by positivity) ?_
    have hp : (0 : ℚ) < 10 ^ (-(v.scale.toNat : ℤ)) := zpow_pos (by norm_num) _
    have hp1 : (10 : ℚ) ^ (-(v.scale.toNat : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    rw [abs_of_nonneg (by positivity)]
    calc (shares.mValue.toNat : ℚ) * 10 ^ (-(v.scale.toNat : ℤ)) ≤ 9223372036854775807 * 1 :=
          mul_le_mul hmq hp1 hp.le (by norm_num)
      _ ≤ (9999999999999999 : ℕ) * (10 : ℚ) ^ (80 : ℤ) := by norm_num

/-- On a vault that holds assets the price of the shares a positive amount buys is a Number at most that amount,
up to the rounding of the share count and of the two pricing steps. -/
lemma charge_number_le (v : Vault) (ra shares : STAmount) (hrc : ra.Canonical) (hrp : 0 < ra.toRat)
    (A sn P Q : Number) (hA : v.assetsTotal = .ok A) (hmz : A.mantissa_ ≠ 0)
    (hs : assetsToSharesDeposit v ra = .ok shares) (hsz : shares.isZero = false)
    (hsn : shares.toNumber .to_nearest = .ok sn) (hP : A.operator_mul sn .to_nearest = .ok P)
    (hQ : P.operator_div v.sharesTotal .to_nearest = .ok Q) :
    Q.isNormalized ∧ 0 ≤ Q.toRat ∧ Q.toRat ≤ ra.toRat * (1 + sharesOverε) * (1 + 1 / 10 ^ 18) ^ 2 := by
  obtain ⟨hic, hint64⟩ := assetsToSharesDeposit_int64_canonical v ra shares hs
  have hshpos := assetsToSharesDeposit_pos v ra shares hrc hrp hs hsz
  have hshc : shares.Canonical := hic.canonical (by rw [hint64]; decide)
  obtain ⟨hsv, hsnorm⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hshc) sn hsn
  obtain ⟨hAn, hApos⟩ := Vault.assetsTotal_pos v A hA hmz
  have hS1 := Vault.sharesTotal_one_le v A hA hmz
  have hSpos : (0 : ℚ) < v.sharesTotal.toRat := by linarith
  obtain ⟨hQn, hQ0, hQle⟩ := Number.mul_div_facts A sn v.sharesTotal P Q hAn hsnorm v.wf.sharesTotal_norm hApos.le
    (by rw [hsv]; exact hshpos.le) hSpos hP hQ
  obtain ⟨q, hqv, hqb, -⟩ := DepTight.shares_spec_exact v ra shares hrc hrp A hA hs hsz
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf

  -- the shares exceed the ideal count by at most `sharesOverε`
  have hsle : shares.toRat ≤ v.sharesTotal.toRat * ra.toRat / A.toRat * (1 + sharesOverε) := by
    have h1 := Int.floor_le q
    have h2 := (abs_le.mp hqb).2
    unfold RawVault.idealSharesDepositAt at h2
    rw [ite_eq_right (ne_of_gt hApos), hST] at h2
    rw [hqv]
    linarith
  have key : A.toRat * sn.toRat / v.sharesTotal.toRat ≤ ra.toRat * (1 + sharesOverε) := by
    rw [hsv, div_le_iff₀ hSpos]
    calc A.toRat * shares.toRat
        ≤ A.toRat * (v.sharesTotal.toRat * ra.toRat / A.toRat * (1 + sharesOverε)) :=
          mul_le_mul_of_nonneg_left hsle hApos.le
      _ = ra.toRat * (1 + sharesOverε) * v.sharesTotal.toRat := by field_simp
  exact ⟨hQn, hQ0, le_trans hQle (mul_le_mul_of_nonneg_right key (by positivity))⟩

/-- The asset pricing of a deposit fails only with an overflow error or a wrap. For XRP the price is at most the
amount, so it is an XRP amount. -/
lemma sharesToAssetsDeposit_error (v : Vault) (hasset : Vault.HoldsAsset v) (ra shares : STAmount)
    (hrc : ra.Canonical) (hrp : 0 < ra.toRat) (hrle : ra.toRat ≤ v.numericType.maxAmount)
    (hs : assetsToSharesDeposit v ra = .ok shares) (hsz : shares.isZero = false) {e : Error}
    (h : sharesToAssetsDeposit v shares = .error e) : isOverflow e = true ∨ e = .wrap := by
  simp only [sharesToAssetsDeposit, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals try first
    | exact number_add_error v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm ‹_›
    | exact toNumber_error ‹_›
    | exact number_mul_error ‹_›
    | exact number_div_error ‹_›
  · -- an empty vault: the price always converts
    obtain ⟨c, hc⟩ := empty_charge_computes v hasset ra shares hrc hrp hrle _ ‹_› ‹_› hs hsz
    have hbad : STAmount.checked v.numericType shares.mantissa (shares.exponent - v.scale.toNat) false .to_nearest
        = .error e := ‹_›
    rw [hc] at hbad
    cases hbad
  · rename_i _ A hA hmz _ sn hsn _ P hP _ Q hQ _ hbad
    rcases hasset with hfr | hna | hi64
    · rw [hfr] at hbad
      exact ofNumber_fractional_error hbad
    · -- XRP: the price is below the amount plus a half
      exfalso
      obtain ⟨hQn, hQ0, hQle⟩ := charge_number_le v ra shares hrc hrp A sn P Q hA hmz hs hsz hsn hP hQ
      rw [hna, maxAmount_native] at hrle
      have hlt : Q.toRat < 100000000000000000 + 1 / 2 := by
        unfold sharesOverε at hQle
        nlinarith
      have hok : ∃ r, STAmount.ofNumber NumericType.native Q .to_nearest = .ok r := by
        refine (STAmount.ofNumber_ok_iff _ Q .to_nearest hQn (Or.inr (Or.inl rfl)) (Or.inl hQ0)).mpr ?_
        rw [STAmount.roundsInRange_native_iff]
        left
        rw [abs_of_nonneg hQ0]
        norm_num
        linarith
      obtain ⟨r, hr⟩ := hok
      rw [hna, hr] at hbad
      cases hbad
    · rw [hi64] at hbad
      exact ofNumber_int64_error hbad

/-- Two amounts of one asset always compare. -/
lemma operator_gt_ne_error (lhs rhs : STAmount) (h : lhs.mNumericType = rhs.mNumericType) {e : Error} :
    lhs.operator_gt rhs ≠ .error e := by
  unfold STAmount.operator_gt STAmount.operator_lt
  rw [ite_eq_right (by simp [STAmount.areComparable, h])]
  exact nofun

/-- The check for an IOU amount at most zero always computes. -/
lemma isFractionalNonPositive_ne_error (a : STAmount) {e : Error} : a.isFractionalNonPositive ≠ .error e := by
  unfold STAmount.isFractionalNonPositive
  split
  · exact nofun
  · unfold STAmount.operator_le STAmount.operator_lt
    rw [ite_eq_right (by simp [STAmount.areComparable, STAmount.zero_mNumericType, STAmount.numericType])]
    exact nofun

/-- The deposit computation fails only with a wrap. It turns the overflow errors of its pricing into `tecPATH_DRY`,
and every other step computes. -/
lemma computeDeposit_error (v : Vault) (hasset : Vault.HoldsAsset v) (ra : STAmount) (isDonation : Bool)
    (hrc : ra.Canonical) (hrp : 0 < ra.toRat) (hrty : ra.mNumericType = v.numericType)
    (hrle : ra.toRat ≤ v.numericType.maxAmount) {e : Error}
    (h : computeDeposit v ra isDonation = .error e) : e = .wrap := by
  have hkind : ∀ {e' : Error}, isOverflow e' = false → isOverflow e' = true ∨ e' = .wrap → e' = .wrap := by
    intro e' hf hk
    rcases hk with hk | hk
    · rw [hf] at hk; cases hk
    · exact hk
  obtain ⟨A, hA⟩ := assetsTotal_computes v
  have hAn := (Vault.assetsTotal_ge_deployed v A hA).1
  simp only [computeDeposit] at h
  unfold_ter at h
  rw [hA] at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  all_goals first
    | exact hkind ‹_› (assetsToSharesDeposit_error v ra ‹_›)
    | exact hkind ‹_› (sharesToAssetsDeposit_error v hasset ra _ hrc hrp hrle ‹_› ‹_› ‹_›)
    | exact hkind ‹_› (clampToSumExponent_error hAn ‹_›)
    | exact absurd ‹_› (isFractionalNonPositive_ne_error _)
    | exact absurd ‹_› (operator_gt_ne_error _ _
        ((sharesToAssetsDeposit_form v _ _ hasset.maxValue_le ‹_›).2.trans hrty.symm))

end XRPL.Model.SingleAssetVault.VaultDepositNoException
