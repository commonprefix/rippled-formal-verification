import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultDepositPricing
import XRPL.Properties.Lending.Ledger.Common.CoverGridInv
import XRPL.Properties.Lending.Ledger.Common.IntegralPrecision
import XRPL.Properties.Lending.Ledger.Common.ShareSum
import XRPL.Properties.Lending.Ledger.Common.SharesNonneg
import XRPL.Properties.Lending.Ledger.Common.WrapLedger
import XRPL.Properties.Lending.Loan.Common.PayoffSettle
import XRPL.Properties.Vault.Proofs.DepositAccuracy

/-! # VaultDeposit, VaultSet, VaultDelete and a ledger close never end in an exception

On a reachable ledger each of these transactions returns a result code. A model `Error` is a C++ exception that
leaves the transaction as `tefEXCEPTION`. A VaultDeposit needs AssetsTotal plus the amount within the largest amount
of the asset: past it the Open limit check builds an amount the asset cannot hold and throws (FV_M4_52 for XRP).
The other three need nothing. -/

namespace XRPL.Model.SingleAssetVault.VaultDepositNoException

open XRPL.Model.Protocol
open XRPL.Model.Protocol.VaultDepositNoException
open XRPL.Model.Protocol.ErrorKinds
open XRPL.Model.Lending (Vault.HoldsAsset)

open private STAmount.roundToNumericType_none_exp from XRPL.Properties.Lending.Loan.Common.PayoffSettle

/-- A sum toward zero of a nonnegative exact sum stays between zero and that sum. -/
lemma add_towards_zero_bounds (x y n : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .towards_zero = .ok n) (h0 : 0 ≤ x.toRat + y.toRat) :
    0 ≤ n.toRat ∧ n.toRat ≤ x.toRat + y.toRat := by
  obtain ⟨m, hm, hv⟩ := Number.operator_add_rounded_towards_zero x y n hx hy hok
  rw [if_pos h0] at hm
  rw [hv]
  refine ⟨?_, Number.lower_le _ m hm⟩
  have := Number.lower_tight _ m hm Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact h0)
  rwa [Number.toRat_zero] at this

/-- The computed total of a lawful vault is normalized, at least zero and at most the exact total. -/
lemma assetsTotal_facts (v : Vault) (A : Number) (hA : v.assetsTotal = .ok A) :
    A.isNormalized ∧ 0 ≤ A.toRat ∧ A.toRat ≤ v.toExact.assetsTotal := by
  obtain ⟨hAn, hAD⟩ := Vault.assetsTotal_ge_deployed v A hA
  exact ⟨hAn, le_trans v.exact.assetsDeployed_nonneg hAD, Vault.assetsTotal_le_exact v A hA⟩

/-- The deposit rounding computes while AssetsTotal plus the amount is within the largest amount of the asset. -/
lemma roundedDepositAmount_computes (v : Vault) (amount : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (hty : amount.mNumericType = v.numericType)
    (hR : v.toExact.assetsTotal + amount.toRat ≤ v.numericType.maxAmount) :
    ∃ r, (v.roundedDepositAmount amount).run = .ok r := by
  obtain ⟨A, hA⟩ := assetsTotal_computes v
  obtain ⟨hAn, hA0, hAle⟩ := assetsTotal_facts v A hA
  obtain ⟨ra, hra⟩ := clampToSumExponent_computes A amount v.baseExponent hAn hA0 (Or.inl hc) hpos.le
    v.baseExponent_range (fun hfr => by
      have hnt : v.numericType = .fractional := by
        rw [← hty]
        exact NumericType.eq_fractional_of_not_integral (by simpa [STAmount.integral] using hfr)
      rw [← hnt]
      linarith)
  rw [roundedDepositAmount_ok v amount ra A hA hra]
  split <;> exact ⟨_, rfl⟩

/-- The Open limit check computes while AssetsTotal plus the charge is within the largest amount of the asset and
YieldUnrealized is below `10^96`. -/
lemma checkOpenLimit_computes (v : Vault) (hasset : Vault.HoldsAsset v) (c : STAmount) (hc : c.CanonicalOrZero)
    (hcty : c.mNumericType = v.numericType) (hc0 : 0 ≤ c.toRat)
    (hR : v.toExact.assetsTotal + c.toRat ≤ v.numericType.maxAmount)
    (hyu : v.yieldUnrealized.toRat < 10 ^ 96) : ∃ t, v.checkOpenLimit c = .ok t := by
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  obtain ⟨A, hA⟩ := assetsTotal_computes v
  obtain ⟨hAn, hA0, hAle⟩ := assetsTotal_facts v A hA
  have hfrac : c.integral = false → v.numericType = .fractional := fun hfr => by
    rw [← hcty]
    exact NumericType.eq_fractional_of_not_integral (by simpa [STAmount.integral] using hfr)

  -- the clamp and its Number
  obtain ⟨rounded, hcl⟩ := clampToSumExponent_computes A c v.baseExponent hAn hA0 hc hc0 v.baseExponent_range
    (fun hfr => by rw [← hfrac hfr]; linarith)
  obtain ⟨hrc, hrty, hr0⟩ := clampToSumExponent_canonicalOrZero A c rounded v.baseExponent hc
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hrle := clampToSumExponent_le_abs A c rounded v.baseExponent hc v.baseExponent_range.1
    v.baseExponent_range.2 hcl
  rw [abs_of_nonneg hc0] at hrle
  obtain ⟨an, han⟩ := hrc.toNumber_ok
  obtain ⟨hanv, hann⟩ := hrc.toNumber_exact an han

  -- the exponent after the credit
  obtain ⟨e, he⟩ := postSumExponent_computes v.numericType hasset A an v.baseExponent hAn hann hA0
    (by rw [hanv]; exact hr0) (by rw [hanv]; linarith)

  -- the Open limit comparison
  have hYn := v.wf.yieldUnrealized_norm
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hbig : (10 : ℚ) ^ 96 < 10 ^ 200 := by norm_num
  obtain ⟨s1, hs1⟩ := Number.operator_add_ok_of_abs A v.yieldUnrealized .towards_zero hAn hYn
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_nonneg hY0]; linarith)
  obtain ⟨hs10, hs1le⟩ := add_towards_zero_bounds A v.yieldUnrealized s1 hAn hYn hs1 (by linarith)
  have hs1n := Number.operator_add_isNormalized_any A v.yieldUnrealized s1 .towards_zero hAn hYn hs1
  obtain ⟨s2, hs2⟩ := Number.operator_add_ok_of_abs s1 an .towards_zero hs1n hann
    (by rw [abs_of_nonneg hs10]; linarith [show (10 : ℚ) ^ 96 + 10 ^ 96 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg (by rw [hanv]; exact hr0), hanv]; linarith)
  obtain ⟨L, hL, -, -⟩ := XRPL.Model.Lending.Vault.openLimit_value v
  unfold Vault.checkOpenLimit Vault.exceedsOpenLimit
  simp only [bind, Except.bind, pure, Except.pure, hA, hcl, han, he, hs1, hs2, hL]
  split_ifs <;> exact ⟨_, rfl⟩

/-- A Number between zero and the largest amount of the asset rounds to the asset, to nearest. -/
lemma roundToNumericType_computes (nt : NumericType) (hnt : IsAsset nt) (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) (hle : n.toRat ≤ nt.maxAmount) :
    ∃ r, STAmount.roundToNumericType nt n .to_nearest = .ok r := by
  obtain ⟨st, hst⟩ := ofNumber_computes nt hnt n .to_nearest hn h0 hle
  have hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat := by
    rcases hnt with rfl | rfl | rfl <;> decide
  obtain ⟨hc, -⟩ := STAmount.ofNumber_canonicalOrZero nt n .to_nearest st hmax hst
  obtain ⟨m, hm⟩ := hc.toNumber_ok
  exact ⟨m, by unfold STAmount.roundToNumericType; rw [hst]; exact hm⟩

/-- The balance update of a deposit never fails while AssetsTotal plus the charge is within the largest amount of
the asset. The new total is then an amount of the asset, which C++ `syncAssetsTotal` stores. -/
lemma adjustAssetsAndShares_ne_error (v : Vault) (hasset : Vault.HoldsAsset v) (c shares : STAmount)
    (hc : c.CanonicalOrZero) (hc0 : 0 ≤ c.toRat) (hsh : shares.CanonicalOrZero) (hsh0 : 0 ≤ shares.toRat)
    (hshle : shares.toRat < 10 ^ 96)
    (hR : v.toExact.assetsTotal + c.toRat ≤ v.numericType.maxAmount)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80) {e : Error} :
    (v.adjustAssetsAndShares c shares).run ≠ .error e := by
  have hmaxlt := NumericType.maxAmount_lt v.numericType
  have hbig : (10 : ℚ) ^ 96 < 10 ^ 200 := by norm_num
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hRu : v.assetsAvailable.toRat + v.assetsDeployed.toRat + c.toRat ≤ v.numericType.maxAmount := hR
  obtain ⟨cn, hcn⟩ := hc.toNumber_ok
  obtain ⟨hcnv, hcnn⟩ := hc.toNumber_exact cn hcn
  obtain ⟨sn, hsn⟩ := hsh.toNumber_ok
  obtain ⟨hsnv, hsnn⟩ := hsh.toNumber_exact sn hsn

  -- the new share total
  obtain ⟨st, hst⟩ := Number.operator_add_ok_of_abs v.sharesTotal sn .to_nearest v.wf.sharesTotal_norm hsnn
    (by rw [abs_of_nonneg v.wf.sharesTotal_nonneg]; linarith [Vault.sharesTotal_le_maxRep v])
    (by rw [hsnv, abs_of_nonneg hsh0]; linarith)

  -- the new cash and its stored form
  obtain ⟨s, hs⟩ := Number.operator_add_ok_of_abs v.assetsAvailable cn .to_nearest v.wf.assetsAvailable_norm hcnn
    (by rw [abs_of_nonneg hAA0]; linarith) (by rw [hcnv, abs_of_nonneg hc0]; linarith)
  obtain ⟨w, hw, hwv⟩ := maxAmount_number v.numericType hasset
  obtain ⟨hs0, hsle⟩ := add_nearest_bounds v.assetsAvailable cn s w v.wf.assetsAvailable_norm hcnn hw hs
    (by rw [hcnv]; linarith) (by rw [hcnv, hwv]; linarith)
  have hsn' := Number.operator_add_isNormalized_any v.assetsAvailable cn s .to_nearest v.wf.assetsAvailable_norm
    hcnn hs
  obtain ⟨aa', haa'⟩ := roundToNumericType_computes v.numericType hasset s hsn' hs0 (by rw [← hwv]; exact hsle)

  -- the new total is an amount of the asset
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa'
  have haa'0 := STAmount.roundToNumericType_nonneg _ _ _ hsn' hs0 haa'
  have haa'st := STAmount.isRounded_roundToNumericType _ _ _ hsn' hs0 haa'
  obtain ⟨total, stored, htotal, hstored⟩ : TotalStores v.numericType aa' v.assetsDeployed := by
    refine TotalStores.of_stored_cash_le _ hasset aa' v.assetsDeployed haa'N v.wf.assetsDeployed_norm haa'0 hAD0
      haa'st (fun hi => ?_) (fun hi => hiou (NumericType.eq_fractional_of_not_integral hi))
    -- whole units: the new cash is at most the maximum less AssetsDeployed
    have hmaxrep : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
      intro _
      rcases hasset with h | h | h
      · rw [h] at hi; cases hi
      · rw [h]; decide
      · rw [h]; decide
    obtain ⟨hADd, -⟩ := STAmount.whole_of_stored _ hi _ v.wf.assetsDeployed_norm hAD0
      v.valid.assetsDeployed_representable
    obtain ⟨haa'd, -⟩ := STAmount.whole_of_stored _ hi _ haa'N haa'0 haa'st
    have hma : v.numericType.maxAmount = (v.numericType.maxValue.toNat : ℚ) := by
      unfold NumericType.maxAmount
      rw [if_pos hi]
    have hm63 : (v.numericType.maxValue.toNat : ℚ) ≤ 9223372036854775807 := by
      have hN : v.numericType.maxValue.toNat ≤ 9223372036854775807 := by
        have := hmaxrep hi
        rw [show maxRep.toNat = 9223372036854775807 from rfl] at this
        exact this
      exact_mod_cast hN
    have hroomd : ((v.numericType.maxValue.toNat : ℚ) - v.assetsDeployed.toRat).den = 1 :=
      Rat.den_one_sub _ _ (Rat.den_natCast _) hADd
    obtain ⟨w', hw', hw'v⟩ := Number.exists_of_int ((v.numericType.maxValue.toNat : ℚ) - v.assetsDeployed.toRat)
      hroomd (by linarith) (by linarith [show (9223372036854775807 : ℚ) < 2 ^ 63 by norm_num])
    obtain ⟨-, hsle'⟩ := add_nearest_bounds v.assetsAvailable cn s w' v.wf.assetsAvailable_norm hcnn hw' hs
      (by rw [hcnv]; linarith) (by rw [hcnv, hw'v, ← hma]; linarith)
    have hhalf := STAmount.roundToNumericType_integral_le_half _ hi hmaxrep s aa' hsn' hs0 haa'
    have hw'd : w'.toRat.den = 1 := by rw [hw'v]; exact hroomd
    have hle : aa'.toRat ≤ w'.toRat := Rat.le_of_le_add_half haa'd hw'd (by linarith)
    rw [hw'v] at hle
    linarith

  intro h
  simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
  unfold_ter at h
  simp only [hcn, hsn, hst, hs, haa', Number.operator_add_zero_right, RawVault.assetsTotal, htotal, hstored] at h
  walk_ok

/-- After the balance update of a deposit the new total computes. -/
lemma adjusted_assetsTotal_ne_error (v : Vault) (hasset : Vault.HoldsAsset v) (c shares : STAmount)
    (raw : RawVault) (hadj : (v.adjustAssetsAndShares c shares).run = .ok (.ok raw)) {e : Error} :
    raw.assetsTotal ≠ .error e := by
  obtain ⟨cn, sn, s, aa', st', -, -, -, -, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v c shares raw hadj
  have haan := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  have h1 := STAmount.roundToNumericType_none_exp v.numericType s aa' hasset haa
  have h2 := Number.exponent_le_of_abs_lt_big v.assetsDeployed v.wf.assetsDeployed_norm
    (lt_trans (representable_abs_lt _ _ v.exact.assetsDeployed_representable) (by norm_num))
  obtain ⟨A', hA'⟩ := Number.operator_add_ok_of_exp aa' v.assetsDeployed .downward haan v.wf.assetsDeployed_norm h1
    (by unfold maxExponent; omega)
  intro h
  have h' : aa'.operator_add v.assetsDeployed .downward = .error e := h
  rw [hA'] at h'
  cases h'

/-- The amount a deposit rounds to is canonical, above zero, of the vault's asset and at most the amount. -/
lemma roundedDepositAmount_facts (v : Vault) (amount ra : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (hty : amount.mNumericType = v.numericType)
    (hra : (v.roundedDepositAmount amount).run = .ok (.ok ra)) :
    ra.Canonical ∧ 0 < ra.toRat ∧ ra.mNumericType = v.numericType ∧ ra.toRat ≤ amount.toRat := by
  obtain ⟨hrc, hrp⟩ := DepRnd.Vault.roundedDepositAmount_canonical_pos v amount ra hc hra
  obtain ⟨A, -, hcl, -⟩ := roundedDepositAmount_rounded v amount ra hra
  have hle := clampToSumExponent_le_abs A amount ra v.baseExponent (Or.inl hc) v.baseExponent_range.1
    v.baseExponent_range.2 hcl
  rw [abs_of_pos hpos] at hle
  exact ⟨hrc, hrp, (v.roundedDepositAmount_form amount ra hc hty hra).2.1, hle⟩

/-- The charge of a deposit computation is a canonical or zero amount of the vault's asset, at least zero and at
most the rounded amount. The minted shares are a canonical or zero MPT amount, at least zero. -/
lemma computeDeposit_facts (v : Vault) (hasset : Vault.HoldsAsset v) (ra : STAmount) (isDonation : Bool)
    (amounts : VaultAmounts) (hrc : ra.Canonical) (hrp : 0 < ra.toRat) (hrty : ra.mNumericType = v.numericType)
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts)) :
    amounts.assets.CanonicalOrZero ∧ amounts.assets.mNumericType = v.numericType ∧ 0 ≤ amounts.assets.toRat ∧
      amounts.assets.toRat ≤ ra.toRat ∧ amounts.shares.CanonicalOrZero ∧ 0 ≤ amounts.shares.toRat ∧
      amounts.shares.toRat < 10 ^ 96 := by
  obtain ⟨hac, haty, ha0⟩ := computeDeposit_assets_form v ra isDonation amounts (Or.inl hrc) hrty hasset.maxValue_le
    hcomp
  obtain ⟨hshc, hshty, hsh0⟩ := computeDeposit_shares_form v ra isDonation amounts hrc hrp hcomp
  have hshcan : amounts.shares.Canonical := hshc.canonical (by rw [hshty]; decide)
  have hshlt : amounts.shares.toRat < 10 ^ 96 := by
    have hin := hshc.in_range
    rw [hshty] at hin
    have hm : (amounts.shares.mValue.toNat : ℚ) ≤ 9223372036854775807 := by
      exact_mod_cast (show amounts.shares.mValue.toNat ≤ 9223372036854775807 from hin)
    have hle : amounts.shares.toRat ≤ (amounts.shares.mValue.toNat : ℚ) := by
      rcases hneg : amounts.shares.mIsNegative with _ | _
      · rw [STAmount.toRat_of_nonneg _ hneg, hshc.offset_zero, zpow_zero, mul_one]
      · have hnn : (0 : ℚ) ≤ (amounts.shares.mValue.toNat : ℚ) := by positivity
        rw [STAmount.toRat_of_neg amounts.shares hneg, hshc.offset_zero, zpow_zero, mul_one]
        linarith
    linarith
  refine ⟨hac, haty, ha0, ?_, Or.inl hshcan, hsh0, hshlt⟩
  cases isDonation
  · obtain ⟨priced, A, hs, hsz, hsad, hgt, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
    obtain ⟨hpc, -⟩ := sharesToAssetsDeposit_form v amounts.shares priced hasset.maxValue_le hsad
    have hshpos := assetsToSharesDeposit_pos v ra amounts.shares hrc hrp hs hsz
    have hp0 := sharesToAssetsDeposit_nonneg v amounts.shares priced hshc hshty hshpos hsad
    have hple := (DepAcc.Vault.deposit_priced_le v amounts.shares priced ra hshc hshty hsad hrc hrp hgt).1
    have hle := clampToSumExponent_le_abs A priced amounts.assets v.baseExponent hpc v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [abs_of_nonneg hp0] at hle
    linarith
  · obtain ⟨A, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
    have hle := clampToSumExponent_le_abs A ra amounts.assets v.baseExponent (Or.inl hrc) v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rwa [abs_of_pos hrp] at hle

/-- A step that returns a value does not fail. -/
lemma ne_error_of_ok {α : Type} {x : Except Error α} (h : ∃ r, x = .ok r) {e : Error} : x ≠ .error e := by
  obtain ⟨r, hr⟩ := h
  rw [hr]
  exact nofun

/-- A deposit of a canonical positive amount of the vault's asset fails only with a wrap, while AssetsTotal plus the
amount is within the largest amount of the asset. -/
lemma deposit_error (v : Vault) (hasset : Vault.HoldsAsset v) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hR : v.toExact.assetsTotal + amount.toRat ≤ v.numericType.maxAmount)
    (hyu : v.yieldUnrealized.toRat < 10 ^ 96)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80) {e : Error}
    (h : (v.deposit amount isDonation t hpos).run = .error e) : e = .wrap := by
  have hT0 : 0 ≤ v.toExact.assetsTotal :=
    add_nonneg v.exact.assetsAvailable_nonneg v.exact.assetsDeployed_nonneg
  -- what the first two steps return
  have hfra : ∀ ra, v.roundedDepositAmount amount = .ok (.ok ra) →
      ra.Canonical ∧ 0 < ra.toRat ∧ ra.mNumericType = v.numericType ∧ ra.toRat ≤ amount.toRat :=
    fun ra hra => roundedDepositAmount_facts v amount ra hc hpos hty hra
  have hfam : ∀ ra amounts, v.roundedDepositAmount amount = .ok (.ok ra) →
      computeDeposit v ra isDonation = .ok (.ok amounts) →
      amounts.assets.CanonicalOrZero ∧ amounts.assets.mNumericType = v.numericType ∧ 0 ≤ amounts.assets.toRat ∧
        amounts.assets.toRat ≤ amount.toRat ∧ amounts.shares.CanonicalOrZero ∧ 0 ≤ amounts.shares.toRat ∧
        amounts.shares.toRat < 10 ^ 96 := by
    intro ra amounts hra hcomp
    obtain ⟨hrc, hrp, hrty, hrle⟩ := hfra ra hra
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := computeDeposit_facts v hasset ra isDonation amounts hrc hrp hrty hcomp
    exact ⟨h1, h2, h3, le_trans h4 hrle, h5, h6, h7⟩

  simp only [Vault.deposit] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  · -- the rounding
    exact absurd ‹v.roundedDepositAmount amount = Except.error e›
      (ne_error_of_ok (roundedDepositAmount_computes v amount hc hpos hty hR))
  · -- the pricing
    obtain ⟨hrc, hrp, hrty, hrle⟩ := hfra _ ‹_›
    exact computeDeposit_error v hasset _ isDonation hrc hrp hrty (by linarith) ‹_›
  · -- the Open limit check
    obtain ⟨h1, h2, h3, h4, -, -, -⟩ := hfam _ _ ‹_› ‹_›
    exact absurd ‹Vault.checkOpenLimit v _ = Except.error e›
      (ne_error_of_ok (checkOpenLimit_computes v hasset _ h1 h2 h3 (by linarith) hyu))
  · -- the balance update
    obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hfam _ _ ‹_› ‹_›
    exact absurd ‹Vault.adjustAssetsAndShares v _ _ = Except.error e›
      (adjustAssetsAndShares_ne_error v hasset _ _ h1 h3 h5 h6 h7 (by linarith) hiou)
  · -- the new total
    exact absurd ‹RawVault.assetsTotal _ = Except.error e›
      (adjusted_assetsTotal_ne_error v hasset _ _ _ ‹_›)
  · -- the lawfulness check: the share check before it keeps SharesTotal within the MPT maximum
    exfalso
    have hrounded : (v.roundedDepositAmount amount).run = .ok (.ok _) := ‹v.roundedDepositAmount amount = _›
    have hcomp : (computeDeposit v _ isDonation).run = .ok (.ok _) := ‹computeDeposit v _ isDonation = _›
    have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.ok _) := ‹v.adjustAssetsAndShares _ _ = _›
    have hm : ((maxRep.toNat : ℕ) : ℚ) = 2 ^ 63 - 1 := by
      rw [show maxRep.toNat = 2 ^ 63 - 1 from rfl]; norm_num
    obtain ⟨hwf, hval⟩ := Vault.deposit_success_lawful v amount isDonation t hc hty _ _ _
      ⟨‹_›, ‹_›, ‹_›, ‹_›⟩ hrounded hcomp hadj (by
        rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hm]
        exact not_lt.mp ‹_›)
    obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hwf hval
    have hbad := hv'.symm.trans ‹RawVault.to_lawful _ = Except.error e›
    cases hbad

/-- The shares a successful deposit mints are a canonical or zero MPT amount, at least zero. -/
lemma deposit_shares_facts (v : Vault) (hasset : Vault.HoldsAsset v) (amount : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.shares.CanonicalOrZero ∧ 0 ≤ r.shares.toRat ∧ r.shares.toRat < 10 ^ 96 := by
  obtain ⟨ra, amounts, raw, hra, hcomp, -, -, -, -, hsh⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r hok
  obtain ⟨hrc, hrp, hrty, -⟩ := roundedDepositAmount_facts v amount ra hc hpos hty hra
  obtain ⟨-, -, -, -, h5, h6, h7⟩ := computeDeposit_facts v hasset ra isDonation amounts hrc hrp hrty hcomp
  rw [hsh]
  exact ⟨h5, h6, h7⟩

end XRPL.Model.SingleAssetVault.VaultDepositNoException

namespace XRPL.Model.Lending.VaultDepositNoException

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts)

open private LendingLedger.SharesSum.step from XRPL.Properties.Lending.Ledger.Common.ShareSum

/-- A deposit that succeeds keeps SharesTotal plus the minted shares within the share MPT maximum: the deposit
checks it before it writes the vault. -/
lemma mintFits (l : LendingLedger) : l.MintFits := by
  intro amount isDonation hpos r hok
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  have hm : ((maxRep.toNat : ℕ) : ℚ) = 2 ^ 63 - 1 := by
    rw [show maxRep.toNat = 2 ^ 63 - 1 from rfl]; norm_num
  rw [← hm]
  exact not_lt.mp ‹_›

/-- On a reachable ledger the holders' shares add up to SharesTotal and each holder owns a whole number of
shares. -/
lemma reachable_sharesSum {l : LendingLedger} (hr : l.Reachable) : l.SharesSum := by
  have h := LendingLedger.Reachable.invariant (Inv := fun l => l.Reachable ∧ l.SharesSum)
    (fun g hg => by
      refine ⟨⟨g, [], hg, .refl, fun _ hm => absurd hm List.not_mem_nil⟩, ?_, ?_⟩
      · obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
        have hraw := XRPL.Model.SingleAssetVault.Vault.create_ok_toRawVault hcreate
        rw [hg.no_holders, show g.vault.sharesTotal = g.vault.toRawVault.sharesTotal from rfl, hraw]
        exact Number.toRat_zero.symm
      · intro x hx
        rw [hg.no_holders] at hx
        cases hx)
    (fun l l' tx hi ha => ⟨hi.1.apply ha, LendingLedger.SharesSum.step hi.1 hi.2 (fun _ => mintFits l) ha⟩) hr
  exact h.2

/-- On a reachable ledger a holder owns between zero and `2^63 - 1` shares. -/
lemma reachable_sharesOf_bounds {l : LendingLedger} (hr : l.Reachable) (h : Nat) :
    (l.sharesOf h).isNormalized ∧ 0 ≤ (l.sharesOf h).toRat ∧ (l.sharesOf h).toRat ≤ 2 ^ 63 - 1 := by
  obtain ⟨hn, h0⟩ := hr.sharesNonneg.sharesOf h
  exact ⟨hn, h0, le_trans ((reachable_sharesSum hr).sharesOf_le hr.sharesNonneg h)
    (Vault.sharesTotal_le_maxRep l.vault)⟩


/-- A vault transaction returns a result when its vault operation never fails. -/
lemma apply_ok_of_vault {l : LendingLedger} {tx : LendingTx} (hv : tx.isVault = true)
    (h : tx.preflight l = .tesSUCCESS → l.vaultDeleted = false → ∀ e, (l.applyVault tx).run ≠ .error e) :
    ∃ r, (l.apply tx).run = .ok r := by
  cases hrun : (l.apply tx).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, ha⟩ := LendingLedger.apply_error hrun
    cases tx <;> simp only [LendingTx.isVault, Bool.false_eq_true] at hv <;>
    · simp only [LendingLedger.applyChecked, LendingTx.isVault, ↓reduceIte] at ha
      split at ha
      · cases ha
      · exact h hpre (by simpa using ‹¬ l.vaultDeleted = true›) e (TerExcept.map_error ha)

end XRPL.Model.Lending.VaultDepositNoException

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Protocol.VaultDepositNoException
open XRPL.Model.SingleAssetVault (Vault RawVault)
open XRPL.Model.SingleAssetVault.VaultDepositNoException
open XRPL.Model.Lending.VaultDepositNoException

/-- A ledger close always returns a result. -/
lemma LendingLedger.close_no_exception_proof (l : LendingLedger) (time : UInt32) :
    ∃ r, (l.apply (.close time)).run = .ok r :=
  ⟨_, rfl⟩

/-- A VaultDelete always returns a result. -/
lemma LendingLedger.vaultDelete_no_exception_proof (l : LendingLedger) :
    ∃ r, (l.apply .vaultDelete).run = .ok r := by
  cases hrun : (l.apply .vaultDelete).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨-, ha⟩ := LendingLedger.apply_error hrun
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at ha
    unfold_ter at ha
    walk_ok'
    exact absurd ‹l.vault.canVaultDelete = Except.error e› (ne_error_of_ok (canVaultDelete_computes l.vault))

/-- A VaultSet on a reachable ledger always returns a result. -/
lemma LendingLedger.vaultSet_no_exception_proof (l : LendingLedger) (hr : l.Reachable)
    (assetsMaximum : Option Number) (blockDeposit : Option Bool) :
    ∃ r, (l.apply (.vaultSet assetsMaximum blockDeposit)).run = .ok r := by
  apply apply_ok_of_vault rfl
  intro hpre _ e h
  have hmax : ∀ m ∈ assetsMaximum, m.isNormalized ∧ Number.zero.operator_le m = true := by
    intro m hm
    rw [Option.mem_def] at hm
    subst hm
    have hc : isNonnegativeInput m = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp [LendingTx.preflight, hne] at hpre
    simpa [isNonnegativeInput] using hc
  obtain ⟨t, ht⟩ := canVaultUpdate_computes l.vault hr.holdsAsset assetsMaximum blockDeposit hmax
  simp only [LendingLedger.applyVault] at h
  unfold_ter at h
  rw [ht] at h
  walk_ok'
  have hts : t = .tesSUCCESS := (TER.isTesSuccess_iff t).mp (by simpa using ‹¬ (!t.isTesSuccess) = true›)
  rw [hts] at ht
  obtain ⟨v', hv'⟩ := Vault.update_ok_of_checks l.vault assetsMaximum blockDeposit hmax ht
  have hu : l.vault.update assetsMaximum blockDeposit = .error e := ‹_›
  rw [hv'] at hu
  cases hu

/-- A VaultDeposit on a reachable ledger returns a result while AssetsTotal plus the amount is within the largest
amount of the asset: `10^17` drops, `2^63 - 1` MPT units, `(10^16 - 1)·10^80` for an IOU. -/
lemma LendingLedger.vaultDeposit_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (amount : STAmount) (isDonation : Bool)
    (hrange : l.vault.toExact.assetsTotal + amount.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.vaultDeposit h amount isDonation)).run = .ok r := by
  apply apply_ok_of_vault rfl
  intro hpre _ e hrun
  -- no fixed-width integer wraps
  have hwrap : e ≠ .wrap := fun he => l.applyVault_ne_wrap hr _ hpre (he ▸ hrun)
  obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit_canonical l hr.holdsAsset h amount isDonation hpre
  have hyu : l.vault.yieldUnrealized.toRat < 10 ^ 96 :=
    lt_of_abs_lt (representable_abs_lt _ _ ((STAmount.isRounded_eq_false_iff _ _ l.vault.wf.yieldUnrealized_norm
      l.vault.exact.yieldUnrealized_nonneg).mp hr.yield_isRounded_false))
  -- AssetsDeployed is at most `10^16` base units
  have hdep : l.vault.numericType = .fractional → l.vault.assetsDeployed.toRat < 10 ^ 80 := fun _ => by
    obtain ⟨d, hd, hdv⟩ := hr.deployed_units
    have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (XRPL.Model.Lending.Vault.baseExponent_scale_range l.vault).2
    have hd' : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd
    rw [hdv]
    have h1 : (d : ℚ) * 10 ^ l.vault.baseExponent ≤ (d : ℚ) * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
    linarith [show (10 : ℚ) ^ 16 < 10 ^ 80 by norm_num]
  simp only [LendingLedger.applyVault] at hrun
  split at hrun
  · rename_i hpos
    unfold_ter at hrun
    walk_ok'
    · -- the vault operation
      exact hwrap (deposit_error l.vault hr.holdsAsset amount isDonation l.now hpos hc hty hrange hyu hdep
        (by simpa only [ExceptT.run] using ‹l.vault.deposit amount isDonation l.now hpos = Except.error e›))
    · -- the minted shares as a Number
      obtain ⟨hsc, -, -⟩ := deposit_shares_facts l.vault hr.holdsAsset amount isDonation l.now hpos hc hty _
        (by simpa only [ExceptT.run] using ‹l.vault.deposit amount isDonation l.now hpos = Except.ok _›)
      exact absurd ‹STAmount.toNumber _ _ = Except.error e› (ne_error_of_ok hsc.toNumber_ok)
    · -- the holder's new shares
      obtain ⟨hsc, hs0, hslt⟩ := deposit_shares_facts l.vault hr.holdsAsset amount isDonation l.now hpos hc hty _
        (by simpa only [ExceptT.run] using ‹l.vault.deposit amount isDonation l.now hpos = Except.ok _›)
      obtain ⟨hmv, hmn⟩ := hsc.toNumber_exact _ ‹_›
      obtain ⟨hhn, hh0, hhle⟩ := reachable_sharesOf_bounds hr h
      exact absurd ‹Number.operator_add _ _ _ = Except.error e› (ne_error_of_ok
        (Number.operator_add_ok_of_abs _ _ .to_nearest hhn hmn (by rw [abs_of_nonneg hh0]; linarith)
          (by rw [hmv, abs_of_nonneg hs0]; linarith)))
  · cases hrun

end XRPL.Model.Lending
