import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Protocol.Number.Add.Common.Downward.AlgorithmicFacts

/-! # Deposit exchange of assets for shares

The vault total the deposit prices against, and the shares `assetsToSharesDeposit` mints: a
canonical `int64` amount, positive when nonzero. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A lawful vault's nonzero computed total is normalized and positive. It is the downward sum
of two nonnegative balances, and rounding down never passes below the representable zero. -/
lemma Vault.assetsTotal_pos (v : Vault) (assetsTotal : Number) (h : v.assetsTotal = .ok assetsTotal)
    (hm : assetsTotal.mantissa_ ≠ 0) : assetsTotal.isNormalized ∧ 0 < assetsTotal.toRat := by
  have hn := operator_add_isNormalized _ _ _ .downward v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm h hm
  obtain ⟨n, hlo, hval⟩ :=
    operator_add_rounded_downward _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm h hm
  have hsum : (0 : ℚ) ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat :=
    add_nonneg v.exact.assetsAvailable_nonneg v.exact.assetsDeployed_nonneg
  have h0 : 0 ≤ n.toRat := by
    have := Number.lower_tight _ n hlo Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact hsum)
    rwa [Number.toRat_zero] at this
  refine ⟨hn, lt_of_le_of_ne (by rw [hval]; exact h0) ?_⟩
  exact Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero assetsTotal hm)

/-- A lawful vault's computed total covers its deployed assets, and is normalized. A downward sum of two
nonnegative balances never rounds below the representable deployed amount. -/
lemma Vault.assetsTotal_ge_deployed (v : Vault) (assetsTotal : Number) (h : v.assetsTotal = .ok assetsTotal) :
    assetsTotal.isNormalized ∧ v.assetsDeployed.toRat ≤ assetsTotal.toRat := by
  have hAA := v.wf.assetsAvailable_norm
  have hAD := v.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  unfold RawVault.assetsTotal at h
  by_cases hd : v.assetsDeployed.mantissa_ = 0
  · -- nothing deployed: the total is the cash
    rw [Number.eq_zero_of_mantissa_zero _ hAD hd, Number.operator_add_zero_right] at h
    obtain rfl := Except.ok.inj h
    rw [Number.eq_zero_of_mantissa_zero _ hAD hd, Number.toRat_zero]
    exact ⟨hAA, hAA0⟩
  by_cases ha : v.assetsAvailable.mantissa_ = 0
  · -- no cash: the total is the deployed amount
    have h' := h
    replace h' := Number.operator_add_ok_spec h'
    unfold Number.operator_addSpec at h'
    rw [Number.operator_eq_zero_false_of_mantissa_ne _ hd, if_neg Bool.false_ne_true,
      Number.eq_zero_of_mantissa_zero _ hAA ha, if_pos (by decide)] at h'
    obtain rfl := Except.ok.inj h'
    exact ⟨hAD, le_refl _⟩
  -- both nonzero and nonnegative: a same-sign sum, which never flushes to zero
  have hADnn : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hna := Number.negative_false_of_nonneg _ hAA hAA0
  have hnd := Number.negative_false_of_nonneg _ hAD hADnn
  have hnz : ¬ v.assetsAvailable.operator_eq v.assetsDeployed.operator_neg = true := by
    simp [Number.operator_eq, Number.operator_neg, hd, hna, hnd]
  obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_downward _ _ _ hAA hAD ha hd
    (by rw [hna, hnd]) hnz h
  obtain ⟨n, hlo, hval⟩ := operator_add_rounded_downward _ _ _ hAA hAD h hspec.result_mant_ne
  refine ⟨hspec.result_norm, ?_⟩
  rw [hval]
  exact Number.lower_tight _ n hlo _ hAD (by linarith)

/-- The computed total is zero exactly when the vault holds nothing. Cash and deployed assets
are nonnegative, and a sum of two nonzero nonnegative amounts never flushes to zero. -/
lemma Vault.assetsTotal_eq_zero_iff (v : Vault) (assetsTotal : Number) (h : v.assetsTotal = .ok assetsTotal) :
    assetsTotal.mantissa_ = 0 ↔ v.toExact.assetsTotal = 0 := by
  have hAD := v.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hsum : v.toExact.assetsTotal = v.assetsAvailable.toRat + v.assetsDeployed.toRat := rfl
  have hge := (v.assetsTotal_ge_deployed assetsTotal h).2
  unfold RawVault.assetsTotal at h
  constructor
  · intro hm
    -- the total covers the deployed assets, so nothing is deployed and the total is the cash
    rw [Number.toRat_eq_zero_of_mantissa_zero _ hm] at hge
    have hd : v.assetsDeployed.toRat = 0 := le_antisymm hge hAD0
    rw [Number.eq_zero_of_mantissa_zero _ hAD (Number.toRat_eq_zero_iff.mp hd),
      Number.operator_add_zero_right] at h
    obtain rfl := Except.ok.inj h
    rw [hsum, Number.toRat_eq_zero_of_mantissa_zero _ hm, hd, add_zero]
  · intro h0
    rw [hsum] at h0
    have ha : v.assetsAvailable.toRat = 0 := by linarith
    have hd : v.assetsDeployed.toRat = 0 := by linarith
    rw [Number.eq_zero_of_mantissa_zero _ hAD (Number.toRat_eq_zero_iff.mp hd),
      Number.operator_add_zero_right, Except.ok.injEq] at h
    rw [← h]
    exact Number.toRat_eq_zero_iff.mp ha

/-- The share scale is at most `vaultMaximumIOUScale = 10`, so in particular at most 18. -/
lemma Vault.scale_toNat_le (v : Vault) : v.scale.toNat ≤ 18 := by
  have h := v.wf.scale_le
  unfold vaultMaximumIOUScale at h
  have : v.scale.toNat ≤ 10 := UInt8.le_iff_toNat_le.mp h
  omega

/-- A vault with no shares holds no assets, so its exact total is zero. -/
lemma Vault.exact_assetsTotal_eq_zero (v : Vault) (h0 : v.toExact.sharesTotal = 0) :
    v.toExact.assetsTotal = 0 := by
  obtain ⟨ha, hd⟩ := v.exact.empty_shares h0
  unfold RawVault.Exact.assetsTotal
  rw [ha, hd, add_zero]

/-- A lawful vault's computed total never exceeds the exact total: it rounds the sum down. -/
lemma Vault.assetsTotal_le_exact (v : Vault) (assetsTotal : Number) (h : v.assetsTotal = .ok assetsTotal) :
    assetsTotal.toRat ≤ v.toExact.assetsTotal := by
  have hsum : (0 : ℚ) ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat :=
    add_nonneg v.exact.assetsAvailable_nonneg v.exact.assetsDeployed_nonneg
  by_cases hm : assetsTotal.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm]; exact hsum
  obtain ⟨n, hlo, hval⟩ :=
    operator_add_rounded_downward _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm h hm
  rw [hval]
  exact Number.lower_le _ n hlo

/-- The shares side of the exchange always packs through `ofNumber .int64`, so a
successful result is a canonical `int64` record. -/
lemma assetsToSharesDeposit_int64_canonical (v : Vault) (amount shares : STAmount)
    (hok : assetsToSharesDeposit v amount = .ok shares) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 := by
  simp only [assetsToSharesDeposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals exact STAmount.ofNumber_integral_canonical .int64 _ .to_nearest shares (by decide) ‹_›

/-- The issued shares are strictly positive. A positive canonical amount prices to a nonnegative share
count, so a nonzero count is positive. -/
lemma assetsToSharesDeposit_pos (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    0 < shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  have hne0 : shares.toRat ≠ 0 := STAmount.toRat_ne_zero shares hmv
  have hamv : amount.mValue ≠ 0 := by
    intro h0
    exact absurd (show amount.toRat = 0 by rw [STAmount.toRat_signed, h0]; simp) (ne_of_gt hpos)
  suffices h : 0 ≤ shares.toRat from lt_of_le_of_ne h (Ne.symm hne0)
  unfold assetsToSharesDeposit at hok
  obtain ⟨navN, hat, hok⟩ := bind_ok_peel _ _ _ hok
  dsimp only at hok
  by_cases hmz : navN.mantissa_ = 0
  · -- empty vault: shares = ⌊normalize(amount·10^scale)⌋
    rw [if_pos hmz] at hok
    obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    have hn2m : n2.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hmv
    have hn1m : n1.mantissa_ ≠ 0 := Number.truncate_source_ne_zero n1 n2 hn2 hn2m
    have hn1cast : (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).normalize largeRange.min largeRange.max
          .to_nearest = .ok n1 := hn1
    have hn1norm : n1.isNormalized :=
      normalize_result_isNormalized _ n1 .to_nearest hamv hn1cast hn1m
    have hin_nonneg : 0 ≤ (Number.unchecked false amount.mantissa
        (amount.exponent + (v.scale.toNat : ℤ))).toRat := by
      rw [Number.toRat_of_nonneg _ rfl]; positivity
    have hround := normalize_rounds_to_nearest _ n1 hn1cast hn1m
    have hn1_nonneg : 0 ≤ n1.toRat := by
      have hb : |n1.toRat - (Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat|
          ≤ |(Number.unchecked false amount.mantissa
          (amount.exponent + (v.scale.toNat : ℤ))).toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := hround
      rw [abs_of_nonneg hin_nonneg] at hb
      have hab := abs_le.mp hb
      nlinarith [hin_nonneg]
    have hn1pos : 0 < n1.toRat :=
      lt_of_le_of_ne hn1_nonneg (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero n1 hn1m))
    obtain ⟨hn2val, hn2norm⟩ :=
      Number.truncate_floor n1 n2 hn1norm (Number.negative_false_of_pos n1 hn1pos) hn2
    have hshval : shares.toRat = n2.toRat :=
      STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide)
        (hn2norm hn2m) (by rw [hn2val]; exact Rat.den_intCast _) hsh
    rw [hshval, hn2val]
    exact_mod_cast Int.floor_nonneg.mpr hn1_nonneg
  · -- nonempty vault: shares = ⌊(sharesTotal·amount)/nav⌋
    rw [if_neg hmz] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
    have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
    rw [hsh'] at hsh
    have hTm : T.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
    have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
    obtain ⟨hnavnorm, hnavpos⟩ := Vault.assetsTotal_pos v navN hat hmz
    have hnavm : navN.mantissa_ ≠ 0 := hmz
    have hPm : P.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
        (Number.not_operator_eq_zero_of_mantissa_ne hnavm) hT0 hT0m
    obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
    have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
    rw [haneq] at hanval hannorm
    obtain ⟨hSTm, hanm⟩ :=
      operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
    have hPnorm : P.isNormalized :=
      operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
        v.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
    have hT0norm : T0.isNormalized :=
      operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hnavm hT0 hT0m
    have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact le_of_lt hpos
    have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
    have hPnn : 0 ≤ P.toRat := by
      have hb : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
        operator_mul_rounds_to_nearest v.sharesTotal amountN P
          v.wf.sharesTotal_norm hannorm hP hPm
      rw [abs_of_nonneg (mul_nonneg hSTnn hann)] at hb
      have hab := abs_le.mp hb
      nlinarith [mul_nonneg hSTnn hann]
    have hPNnn : 0 ≤ P.toRat / navN.toRat := div_nonneg hPnn (le_of_lt hnavpos)
    have hT0nn : 0 ≤ T0.toRat := by
      have hb : |T0.toRat - P.toRat / navN.toRat|
          ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) :=
        operator_div_rounds_to_nearest P navN T0 hPnorm hnavnorm hT0 hT0m
      rw [abs_of_nonneg hPNnn] at hb
      have hab := abs_le.mp hb
      nlinarith [hPNnn]
    have hT0pos : 0 < T0.toRat :=
      lt_of_le_of_ne hT0nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T0 hT0m))
    obtain ⟨hTval, hTnorm⟩ :=
      Number.truncate_floor T0 T hT0norm (Number.negative_false_of_pos T0 hT0pos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
        (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
    rw [hshval, hTval]
    exact_mod_cast Int.floor_nonneg.mpr hT0nn

/-- The shares a deposit mints are a nonnegative canonical MPT amount: the shares the charge
buys, or none for a donation. -/
lemma computeDeposit_shares_form (v : Vault) (roundedAmount : STAmount) (isDonation : Bool)
    (amounts : VaultAmounts) (hra : roundedAmount.Canonical) (hpos : 0 < roundedAmount.toRat)
    (hcomp : (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts)) :
    amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧ 0 ≤ amounts.shares.toRat := by
  cases isDonation
  · obtain ⟨_, _, ha2s, hz, _⟩ := computeDeposit_success_reduces v roundedAmount amounts hcomp
    obtain ⟨hic, hint⟩ := assetsToSharesDeposit_int64_canonical v roundedAmount amounts.shares ha2s
    exact ⟨hic, hint, le_of_lt (assetsToSharesDeposit_pos v roundedAmount amounts.shares hra hpos ha2s hz)⟩
  · obtain ⟨_, hsh, _⟩ := computeDeposit_donation_reduces v roundedAmount amounts hcomp
    rw [hsh]
    exact ⟨zero_int64_IntegralCanonical, STAmount.zero_mNumericType _, (STAmount.zero_toRat _).ge⟩

/-- A vault whose computed total is nonzero holds at least one whole share. -/
lemma Vault.sharesTotal_one_le (v : Vault) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hmz : navN.mantissa_ ≠ 0) : 1 ≤ v.sharesTotal.toRat := by
  have hApos : 0 < v.toExact.assetsTotal :=
    lt_of_lt_of_le (Vault.assetsTotal_pos v navN hat hmz).2 (Vault.assetsTotal_le_exact v navN hat)
  have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
    absurd (Vault.exact_assetsTotal_eq_zero v h0) (ne_of_gt hApos)
  rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne

end XRPL.Model.SingleAssetVault
