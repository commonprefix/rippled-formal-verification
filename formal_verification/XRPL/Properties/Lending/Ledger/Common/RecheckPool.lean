import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Properties.Vault.Proofs.Support.Errors

/-! # The vault re-check after a balance update

A loan operation updates the vault with `adjustBalances`, which rejects a negative balance and a LossUnrealized
above AssetsDeployed. The vault it writes passes its re-check when the asset stores the new AssetsDeployed,
AssetsReserved stays within it, and a vault without shares holds nothing. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The change fields a balance update adds to the stored balances are normalized. -/
structure PoolBalanceChange.Normalized (c : PoolBalanceChange) : Prop where
  deployed : c.deployed.isNormalized
  loss : c.loss.isNormalized
  reserved : c.reserved.isNormalized
  yield : c.yield.isNormalized

/-- What a balance update that passed its checks wrote. The five new balances are normalized and not
negative, LossUnrealized stays within AssetsDeployed, and every other field is the old vault's. -/
lemma Vault.adjustBalances_ok_facts (v : Vault) (c : PoolBalanceChange) (raw : RawVault) (hc : c.Normalized)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw)) :
    raw = { v.toRawVault with
      assetsAvailable := raw.assetsAvailable
      assetsDeployed := raw.assetsDeployed
      assetsReserved := raw.assetsReserved
      lossUnrealized := raw.lossUnrealized
      yieldUnrealized := raw.yieldUnrealized } ∧
    raw.assetsAvailable.isNormalized ∧ raw.assetsDeployed.isNormalized ∧ raw.assetsReserved.isNormalized ∧
    raw.lossUnrealized.isNormalized ∧ raw.yieldUnrealized.isNormalized ∧
    0 ≤ raw.assetsAvailable.toRat ∧ 0 ≤ raw.assetsDeployed.toRat ∧ 0 ≤ raw.assetsReserved.toRat ∧
    0 ≤ raw.lossUnrealized.toRat ∧ 0 ≤ raw.yieldUnrealized.toRat ∧
    raw.lossUnrealized.toRat ≤ raw.assetsDeployed.toRat := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at hadj
  unfold_ter at hadj
  walk_ok
  rename_i hsign hgt
  have hAAn := STAmount.roundToNumericType_isNormalized _ _ _ _ _
    ‹STAmount.roundToNumericType v.numericType _ .to_nearest = .ok _›
  have hADn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsDeployed_norm hc.deployed
    ‹v.assetsDeployed.operator_add c.deployed .to_nearest = .ok _›
  have hLUn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm hc.loss
    ‹v.lossUnrealized.operator_add c.loss .to_nearest = .ok _›
  have hARn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsReserved_norm hc.reserved
    ‹v.assetsReserved.operator_add c.reserved .to_nearest = .ok _›
  have hYUn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.yieldUnrealized_norm hc.yield
    ‹v.yieldUnrealized.operator_add c.yield .to_nearest = .ok _›
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hsign
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hsign
  unfold Number.operator_gt at hgt
  have hle := (operator_lt_eq_false_iff _ _ hADn hLUn).mp (by simpa using hgt)
  exact ⟨rfl, hAAn, hADn, hARn, hLUn, hYUn, Number.toRat_nonneg_of_not_signum_neg _ hAAn h1,
    Number.toRat_nonneg_of_not_signum_neg _ hADn h2, Number.toRat_nonneg_of_not_signum_neg _ hARn h5,
    Number.toRat_nonneg_of_not_signum_neg _ hLUn h3, Number.toRat_nonneg_of_not_signum_neg _ hYUn h4, hle⟩

/-- A balance update that passed its checks writes a lawful vault when the asset stores the new AssetsDeployed and
AssetsAvailable, AssetsReserved fits in AssetsDeployed, AssetsAvailable is on the grid, and no shares, no assets. -/
lemma Vault.adjustBalances_to_lawful (v : Vault) (c : PoolBalanceChange) (raw : RawVault) (hc : c.Normalized)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw))
    (hrep : STAmount.Representable v.numericType raw.assetsDeployed.toRat)
    (har : raw.assetsReserved.toRat ≤ raw.assetsDeployed.toRat)
    (hempty : v.sharesTotal = Number.zero → raw.assetsAvailable.toRat = 0 ∧ raw.assetsDeployed.toRat = 0)
    (haar : STAmount.isRounded v.numericType raw.assetsAvailable = false)
    (haag : ∃ k : ℤ, raw.assetsAvailable.toRat = k * 10 ^ v.baseExponent) :
    ∃ v', raw.to_lawful = .ok v' := by
  obtain ⟨hraw, hAAn, hADn, hARn, hLUn, hYUn, hAA0, hAD0, hAR0, hLU0, hYU0, hle⟩ :=
    Vault.adjustBalances_ok_facts v c raw hc hadj
  have hwf : raw.WF := by
    rw [hraw]
    exact { v.wf with
      assetsAvailable_norm := hAAn
      assetsDeployed_norm := hADn
      assetsReserved_norm := hARn
      lossUnrealized_norm := hLUn
      yieldUnrealized_norm := hYUn }
  have hex := v.exact
  have hvalid : raw.toExact.Valid := by
    rw [hraw]
    exact { hex with
      assetsAvailable_nonneg := hAA0
      assetsDeployed_nonneg := hAD0
      assetsReserved_nonneg := hAR0
      lossUnrealized_nonneg := hLU0
      yieldUnrealized_nonneg := hYU0
      empty_shares := fun h0 => by
        have hs0 : v.sharesTotal.toRat = 0 := by
          rw [← RawVault.WF.toExact_sharesTotal _ v.wf]; exact_mod_cast h0
        exact hempty ((Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp hs0)
      lossUnrealized_le := hle
      assetsDeployed_representable := hrep
      assetsReserved_le := har
      assetsAvailable_representable := (STAmount.isRounded_eq_false_iff _ _ hAAn hAA0).mp haar
      assetsAvailable_onGrid := haag }
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of hwf ((RawVault.valid_iff_exact raw hwf).mpr hvalid)
  exact ⟨v', hv'⟩

/-- A vault balance update never fails its re-check when every vault it could write has AssetsDeployed stored
exactly, AssetsReserved within it, no assets without shares, and AssetsAvailable stored exactly on the base grid. -/
lemma Vault.poolAdjust_ne_notLawful (v : Vault) (c : PoolBalanceChange) (hc : c.Normalized)
    (hgood : ∀ raw, (v.adjustBalances c).run = .ok (.ok raw) →
      STAmount.Representable v.numericType raw.assetsDeployed.toRat ∧
      raw.assetsReserved.toRat ≤ raw.assetsDeployed.toRat ∧
      (v.sharesTotal = Number.zero → raw.assetsAvailable.toRat = 0 ∧ raw.assetsDeployed.toRat = 0) ∧
      STAmount.isRounded v.numericType raw.assetsAvailable = false ∧
      ∃ k : ℤ, raw.assetsAvailable.toRat = k * 10 ^ v.baseExponent) :
    AssetPool.adjustBalances v c ≠ .error .notLawful := by
  rw [Vault.pool_adjustBalances]
  intro h
  unfold_ter at h
  walk_ok
  · exact Vault.adjustBalances_ne_notLawful v c (by simp only [ExceptT.run]; assumption)
  · rename_i hlaw
    have hadj' : (v.adjustBalances c).run = .ok (.ok _) := ‹v.adjustBalances c = .ok (.ok _)›
    obtain ⟨h1, h2, h3, h4, h5⟩ := hgood _ hadj'
    obtain ⟨v', hv'⟩ := Vault.adjustBalances_to_lawful v c _ hc hadj' h1 h2 h3 h4 h5
    rw [hv'] at hlaw
    cases hlaw

lemma powerMinusOneLoop_ne_notLawful (rate : Number) (n i : Nat) (term sum : Number) :
    powerMinusOneLoop rate n i term sum ≠ .error .notLawful := by
  fun_induction powerMinusOneLoop rate n i term sum with
  | case1 _ _ _ _ ih =>
    simp only [bind, Except.bind, pure, Except.pure]
    split_ne_notLawful [Number.operator_mul_ne_notLawful, Number.operator_div_ne_notLawful,
      Number.operator_add_ne_notLawful, ih]
  | case2 => simp [pure, Except.pure]

lemma computePowerMinusOne_ne_notLawful (rate n : Number) (pr : UInt32) :
    computePowerMinusOne rate n pr ≠ .error .notLawful := by
  unfold computePowerMinusOne
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_mul_ne_notLawful, powerMinusOneLoop_ne_notLawful]

lemma computePowerMinusOneHybrid_ne_notLawful (rate n : Number) (pr : UInt32) :
    computePowerMinusOneHybrid rate n pr ≠ .error .notLawful := by
  unfold computePowerMinusOneHybrid
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_mul_ne_notLawful, Number.from_rep_ne_notLawful,
    Number.operator_add_ne_notLawful, Number.power_ne_notLawful, Number.operator_sub_ne_notLawful,
    computePowerMinusOne_ne_notLawful]

lemma computePaymentFactor_ne_notLawful (rate n : Number) (pr : UInt32) :
    computePaymentFactor rate n pr ≠ .error .notLawful := by
  unfold computePaymentFactor
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_div_ne_notLawful, computePowerMinusOneHybrid_ne_notLawful,
    Number.operator_add_ne_notLawful, Number.operator_mul_ne_notLawful]

lemma loanPeriodicPayment_ne_notLawful (principal rate : Number) (pr : UInt32) :
    loanPeriodicPayment principal rate pr ≠ .error .notLawful := by
  unfold loanPeriodicPayment
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_div_ne_notLawful, computePaymentFactor_ne_notLawful,
    Number.operator_mul_ne_notLawful]

lemma loanPrincipalFromPeriodicPayment_ne_notLawful (pp rate : Number) (pr : UInt32) :
    loanPrincipalFromPeriodicPayment pp rate pr ≠ .error .notLawful := by
  unfold loanPrincipalFromPeriodicPayment
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_div_ne_notLawful, computePaymentFactor_ne_notLawful,
    Number.operator_mul_ne_notLawful]

lemma loanPeriodicRate_ne_notLawful (rate : TenthBips32) (interval : UInt32) :
    loanPeriodicRate rate interval ≠ .error .notLawful := by
  unfold loanPeriodicRate
  simp only [bind, Except.bind]
  split_ne_notLawful [tenthBipsOfValue_ne_notLawful, Number.operator_div_ne_notLawful]

lemma computeManagementFee_ne_notLawful (nt : NumericType) (value : Number) (rate : TenthBips16) (e : Int) :
    computeManagementFee nt value rate e ≠ .error .notLawful := by
  unfold computeManagementFee
  simp only [bind, Except.bind]
  split_ne_notLawful [tenthBipsOfValue_ne_notLawful, STAmount.roundToNumericType_ne_notLawful]

lemma computeLoanPropertiesFromPeriodicRate_ne_notLawful (principal rate : Number) (pr : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) :
    computeLoanPropertiesFromPeriodicRate principal rate pr mgmt nt minScale ≠ .error .notLawful := by
  unfold computeLoanPropertiesFromPeriodicRate
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [loanPeriodicPayment_ne_notLawful, Number.operator_mul_ne_notLawful,
    STAmount.ofNumber_ne_notLawful, STAmount.roundToNumericType_ne_notLawful, Number.operator_sub_ne_notLawful,
    computeManagementFee_ne_notLawful, loanPrincipalFromPeriodicPayment_ne_notLawful]

lemma LoanState.build_ne_notLawful (a b c : Number) : LoanState.build a b c ≠ .error .notLawful := by
  unfold LoanState.build
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Number.operator_sub_ne_notLawful]

lemma RawLoanBroker.hasMinimumCover_ne_notLawful (rb : RawLoanBroker) (e : Int) :
    rb.hasMinimumCover e ≠ .error .notLawful := by
  intro h
  unfold RawLoanBroker.hasMinimumCover minimumBrokerCover at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all [tenthBipsOfValue_ne_notLawful, STAmount.roundToNumericType_ne_notLawful]

/-- The interest a loan computes comes from two subtractions, which never raise `notLawful`. -/
lemma RawLoan.interestDue_ne_notLawful (rl : RawLoan) : rl.interestDue ≠ .error .notLawful := by
  unfold RawLoan.interestDue
  simp only [bind, Except.bind]
  split_ne_notLawful [Number.operator_sub_ne_notLawful]

end XRPL.Model.Lending
