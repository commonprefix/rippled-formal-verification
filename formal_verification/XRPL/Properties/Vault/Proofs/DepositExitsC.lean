import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Clamp
import XRPL.Properties.Vault.Proofs.ExitsC.Basic

/-! # `Vault.deposit` exits through the grid clamp

Proof bodies behind `VaultDepositReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault.ExitsC

open XRPL.Model.Protocol

/-- A fractional clamped charge converts exactly. -/
lemma charge_frac_toNumber (v : Vault) (roundedAmount priced c s : STAmount) (cN : Number)
    (hcomp : computeDeposit v roundedAmount = .ok (.success priced s))
    (hclamp : clampToSumExponent v.assetsTotal priced = .ok c)
    (hcfr : c.integral = false)
    (hcN : c.toNumber .to_nearest = .ok cN) :
    cN.toRat = c.toRat ∧ cN.isNormalized := by
  obtain ⟨shares, hats, -, hsad, -, -⟩ := computeDeposit_success_reduces v roundedAmount priced s hcomp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v roundedAmount shares hats
  have hpnt := sharesToAssetsDeposit_mNumericType v shares priced hsad
  have hpfr : priced.integral = false := by
    by_contra hpi
    have hpi' : priced.integral = true := by simpa using hpi
    have := (clampToSumExponent_integral_fields v.assetsTotal priced c hpi' hclamp).1
    have hci : c.integral = true := by
      show c.mNumericType.isIntegral = true; rw [this]; exact hpi'
    rw [hci] at hcfr; exact absurd hcfr (by decide)
  have hpf : STAmount.FracCanonZero priced := by
    refine ⟨frac_of_not_integral priced hpfr, ?_⟩
    by_cases hpz : priced.mValue = 0
    · exact Or.inr hpz
    · rcases sharesToAssetsDeposit_disj_canonical v shares priced hshc hshnt hsad hpz with h | h
      · exact Or.inl h
      · exfalso
        have := h.is_integral
        have h2 : priced.integral = true := this
        rw [hpfr] at h2; exact absurd h2 (by decide)
  have hcf := WdAcc.clamp_frac_shape _ _ _ hpf hclamp
  rcases hcf.2 with h | h
  · obtain ⟨sn, hok, hval, hnorm⟩ := STAmount.toNumber_iou_exact c .to_nearest h
    rw [show cN = sn from Except.ok.inj (hcN.symm.trans hok)]
    exact ⟨hval, hnorm⟩
  · exact STAmount.toNumber_zero_facts c .to_nearest cN h hcN

/-- The shares side of a deposit that issues positive shares. -/
lemma shares_update (v : Vault) (s : STAmount) (sN st' : Number)
    (hSc : s.IntegralCanonical) (hspos : 0 < s.toRat)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hSsz : (v.toExact.sharesTotal : ℚ) + s.toRat ≤ 2 ^ 63 - 1) :
    st'.isNormalized ∧ 0 ≤ st'.toRat ∧ st'.toRat.den = 1 ∧ st'.toRat ≠ 0 := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSsz' : v.sharesTotal.toRat + s.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hSsz
  have hST_nn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hs_den : s.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one s hSc
  have hs_mval : ((s.mValue.toNat : ℕ) : ℚ) = s.toRat :=
    STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg s hSc hspos.le
  have hsz : s.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have h1 : ((s.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [hs_mval]
      calc s.toRat ≤ v.sharesTotal.toRat + s.toRat := by linarith
        _ ≤ 2 ^ 63 - 1 := hSsz'
        _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
    exact_mod_cast h1
  obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
    STAmount.toNumber_integral_small_exact s .to_nearest hSc hsz
  obtain rfl : sN0 = sN := Except.ok.inj (hsN0.symm.trans hsN)
  have hsN_den : sN0.toRat.den = 1 := by rw [hsN_val0]; exact hs_den
  have hsum_den : (v.sharesTotal.toRat + sN0.toRat).den = 1 :=
    Rat.den_one_add _ _ v.wf.sharesTotal_int hsN_den
  have hsum_nn : 0 ≤ v.sharesTotal.toRat + sN0.toRat := by rw [hsN_val0]; linarith
  have hsum_bound : (v.sharesTotal.toRat + sN0.toRat).num.natAbs < 2 ^ 63 :=
    Rat.num_natAbs_lt_of_abs_le _ hsum_den
      (by rw [abs_of_nonneg hsum_nn, hsN_val0]; exact hSsz')
  obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int v.sharesTotal sN0 st'
    v.wf.sharesTotal_norm hsN_norm0 v.wf.sharesTotal_int hsN_den hsum_bound hst
  refine ⟨operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm hsN_norm0 hst,
    by rw [hst_val]; exact hsum_nn, hst_den, ?_⟩
  rw [hst_val, hsN_val0]
  exact ne_of_gt (by linarith)

/-- Adding one charge to both asset totals and a share count re-validates. -/
lemma add_lawful (v : Vault) (cN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcN_norm : cN.isNormalized) (hcN_nn : 0 ≤ cN.toRat)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hshares : st'.isNormalized ∧ 0 ≤ st'.toRat ∧ st'.toRat.den = 1 ∧ st'.toRat ≠ 0)
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hat_norm : at'.isNormalized :=
    operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm hcN_norm hat
  have hat_nn : 0 ≤ at'.toRat :=
    operator_add_nonneg _ _ _ v.wf.assetsTotal_norm hcN_norm hat (by linarith)
  rw [hAV, hat] at hav
  obtain rfl : at' = av' := Except.ok.inj hav
  obtain ⟨hst_norm, hst_nn, hst_den, hst_ne⟩ := hshares
  have hwfE : ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
    ⟨hat_norm, hat_norm, v.wf.assetsMaximum_norm, hst_norm,
      v.wf.lossUnrealized_norm, hst_nn, hst_den,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hat_nn, hat_nn, le_refl _, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
  · intro h0
    exfalso
    have h0' : st'.toRat.num.toNat = 0 := h0
    have := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
    rw [h0'] at this
    exact hst_ne (by exact_mod_cast this.symm)
  · intro mq hm
    have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
    rw [Option.mem_map] at hm'
    obtain ⟨n, hn, rfl⟩ := hm'
    have hn' : v.assetsMaximum = some n := hn
    rw [hn'] at hmax
    have hnpos : 0 < n.toRat :=
      v.exact.assetsMaximum_pos n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
    have hne0 : n.operator_ne Number.zero = true :=
      (operator_ne_iff n Number.zero (v.wf.assetsMaximum_norm n hn) (Or.inl rfl)).mpr
        (by rw [Number.toRat_zero]; exact ne_of_gt hnpos)
    have hgt : at'.operator_gt n = false := by
      simp only [Option.getD_some, hne0, Bool.true_and] at hmax; exact hmax
    have := (operator_gt_iff at' n hat_norm (v.wf.assetsMaximum_norm n hn)).not.mp
      (by rw [hgt]; simp)
    exact le_of_not_gt (fun hc => this hc)
  · exact le_of_eq hL.symm
  · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]
    linarith
  · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]
    linarith

end XRPL.Model.SingleAssetVault.ExitsC

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.deposit_maximum_exceeded_proof (v : Vault) (amountDeposit roundedAmount c cl s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success c s))
    (hclamp : clampToSumExponent v.assetsTotal c = .ok cl)
    (hcN : cl.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hfnp : cl.isFractionalNonPositive = .ok false := by
    by_cases hint : cl.integral = true
    · exact ExitsC.fnp_false cl (Or.inl hint)
    refine ExitsC.fnp_false cl (Or.inr ?_)
    by_contra hle
    push Not at hle
    obtain ⟨hcv, hcn⟩ := ExitsC.charge_frac_toNumber v roundedAmount c cl s cN hcomp hclamp
      (by simpa using hint) hcN
    have hr := operator_add_rounded_to_nearest _ _ _ v.wf.assetsTotal_norm hcn hat
    have hle' := Number.RoundsToRepresentable.le_of_le_normalized at' _ hr v.assetsTotal
      v.wf.assetsTotal_norm (by rw [hcv]; linarith)
    exact ExitsC.not_over_cap v at'
      (operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm hcn hat) hle' hmax
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure, hround, hnz, hins, hcomp,
    hclamp, hfnp, hcN, hsN, hat, hav, hst, hmax]
  rfl

lemma Vault.deposit_success_proof (v : Vault) (amountDeposit roundedAmount priced c s : STAmount)
    (cN sN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success priced s))
    (hclamp : clampToSumExponent v.assetsTotal priced = .ok c)
    (hcpos : c.integral = true ∨ 0 < c.toRat)
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + s.toRat ≤ 2 ^ 63 - 1)
    (hpos : 0 < amountDeposit.toRat) :
    ∃ v' : Vault, v.deposit amountDeposit false hpos = .ok ⟨none, v', c, s⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hfnp := ExitsC.fnp_false c hcpos
  obtain ⟨_, hats, hshz, hsad, -, rfl⟩ :=
    computeDeposit_success_reduces v roundedAmount priced s hcomp
  have hamCanon : roundedAmount.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit roundedAmount v.assetsTotal
      hcanonA hround with hc | hz
    · exact hc
    · rw [hz] at hnz; exact absurd hnz (by decide)
  have ham_nn : 0 ≤ roundedAmount.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit roundedAmount v.assetsTotal hcanonA
      hpos.le hround
  have ham_pos : 0 < roundedAmount.toRat :=
    lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero roundedAmount
      (by unfold STAmount.isZero at hnz; exact ne_of_beq_false hnz)))
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v roundedAmount s hats
  have hshpos : 0 < s.toRat :=
    assetsToSharesDeposit_pos v roundedAmount s hamCanon ham_pos hats hshz
  obtain ⟨hcv, hcn⟩ :=
    Vault.deposit_charge_toNumber_facts v s priced c cN hshc hshnt hshpos hsad hclamp hcN
  have hc_nn := DepAcc.Vault.deposit_charge_nonneg v s priced c hshc hshnt hshpos hsad hclamp hfnp
  obtain ⟨v', htl, hlv'eq⟩ := ExitsC.add_lawful v cN at' av' st' hL hAV hcn
    (by rw [hcv]; exact hc_nn) hat hav
    (ExitsC.shares_update v s sN st' hshc hshpos hsN hst hSsz) hmax
  refine ⟨v', ?_, hlv'eq⟩
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure, hround, hnz, hins, hcomp,
    hclamp, hfnp, hcN, hsN, hat, hav, hst, hmax, htl]
  rfl

lemma Vault.deposit_clamp_precision_loss_proof (v : Vault) (amountDeposit roundedAmount priced c s : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success priced s))
    (hclamp : clampToSumExponent v.assetsTotal priced = .ok c)
    (hvanish : c.integral = false ∧ c.toRat ≤ 0)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecPRECISION_LOSS) := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hfnp := ExitsC.fnp_true c hvanish
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure, hround, hnz, hins, hcomp,
    hclamp, hfnp]
  rfl

lemma Vault.deposit_donation_success_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (_hSsz : (v.toExact.sharesTotal : ℚ) + (STAmount.zero .int64).toRat ≤ 2 ^ 63 - 1)
    (hpos : 0 < amountDeposit.toRat) :
    ∃ v' : Vault, v.deposit amountDeposit true hpos = .ok ⟨none, v', roundedAmount, STAmount.zero .int64⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hamCanon : roundedAmount.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit roundedAmount v.assetsTotal
      hcanonA hround with hc | hz
    · exact hc
    · rw [hz] at hnz; exact absurd hnz (by decide)
  have ham_nn : 0 ≤ roundedAmount.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit roundedAmount v.assetsTotal hcanonA
      hnnA hround
  obtain ⟨aN0, haN0, hval0, hnorm0⟩ := STAmount.toNumber_exact_canonical roundedAmount .to_nearest
    (STAmount.Canonical.exactCanonical roundedAmount hamCanon)
  obtain rfl : aN0 = aN := Except.ok.inj (haN0.symm.trans haN)
  have hzN0 : zN = Number.zero := by
    rw [zero_int64_toNumber] at hzN; exact (Except.ok.inj hzN).symm
  subst hzN0
  rw [Number.operator_add_zero_right] at hst
  obtain rfl : v.sharesTotal = st' := Except.ok.inj hst
  have hshares : v.sharesTotal.isNormalized ∧ 0 ≤ v.sharesTotal.toRat ∧
      v.sharesTotal.toRat.den = 1 ∧ v.sharesTotal.toRat ≠ 0 :=
    ⟨v.wf.sharesTotal_norm, v.wf.sharesTotal_nonneg, v.wf.sharesTotal_int,
      Number.toRat_ne_zero_of_mantissa_ne_zero _ hsh⟩
  obtain ⟨v', htl, hlv'eq⟩ := ExitsC.add_lawful v aN0 at' av' v.sharesTotal hL hAV hnorm0
    (by rw [hval0]; exact ham_nn) hat hav hshares hmax
  refine ⟨v', ?_, hlv'eq⟩
  have hsh' : (v.sharesTotal.mantissa_ == 0) = false := by simpa using hsh
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure, hround, hnz, hsh', haN, hzN,
    hat, hav, hmax, htl, Number.operator_add_zero_right, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    Bool.and_false]

end XRPL.Model.SingleAssetVault
