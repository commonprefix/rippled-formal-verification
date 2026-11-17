import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Protocol.STAmount.Common.Representable

/-! # Proof bodies for `Vault.canCreate`, `Vault.create` and `Vault.update` -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A raw state that is not well-formed and valid fails the re-validation with `notLawful`. -/
lemma RawVault.to_lawful_not_lawful {rv : RawVault} (h : ¬ (rv.WF ∧ rv.Valid)) :
    rv.to_lawful = .error .notLawful := by
  unfold RawVault.to_lawful; rw [dif_neg h]

/-- Proof body of the expired exit of `Vault.canCreate_exits`. -/
lemma Vault.canCreate_expired_proof (scale : Option UInt8) (assetsMaximum : Option Number) (s : VaultSchedule)
    (t : UInt32) (nt : NumericType) (hexp : (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = true) :
    Vault.canCreate scale assetsMaximum (some s) t nt = .ok .tecEXPIRED := by
  simp only [Vault.canCreate, bind, Except.bind, pure, Except.pure]
  rw [if_pos hexp]

/-- On a schedule whose dates are both ahead, `canCreate` is the maximum's grid check. -/
private lemma canCreate_live (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType)
    (hlive : ∀ s ∈ schedule, (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = false) :
    Vault.canCreate scale assetsMaximum schedule t nt = Vault.canCreate scale assetsMaximum none t nt := by
  cases schedule with
  | none => rfl
  | some s =>
    have h := hlive s rfl
    simp only [Vault.canCreate, bind, Except.bind, pure, Except.pure]
    rw [if_neg (by simp only [h]; decide)]

/-- Proof body of the precision-loss exit of `Vault.canCreate_exits`. -/
lemma Vault.canCreate_precision_loss_proof (scale : Option UInt8) (m : Number) (schedule : Option VaultSchedule)
    (t : UInt32) (nt : NumericType)
    (hlive : ∀ s ∈ schedule, (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = false)
    (hgrid : m.isOnExponentGrid (nt.baseExponent (scale.getD vaultDefaultIOUScale)) nt = .ok false) :
    Vault.canCreate scale (some m) schedule t nt = .ok .tecPRECISION_LOSS := by
  rw [canCreate_live scale _ schedule t nt hlive]
  simp [Vault.canCreate, bind, Except.bind, pure, Except.pure, hgrid]

/-- Proof body of the success exit of `Vault.canCreate_exits`. -/
lemma Vault.canCreate_success_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType)
    (hlive : ∀ s ∈ schedule, (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = false)
    (hgrid : ∀ m ∈ assetsMaximum,
      m.isOnExponentGrid (nt.baseExponent (scale.getD vaultDefaultIOUScale)) nt = .ok true) :
    Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS := by
  rw [canCreate_live scale _ schedule t nt hlive]
  cases assetsMaximum with
  | none => rfl
  | some m => simp [Vault.canCreate, bind, Except.bind, pure, Except.pure, hgrid m rfl]

lemma Vault.canCreate_error_codes_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType) (ter : TER)
    (hok : Vault.canCreate scale assetsMaximum schedule t nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecEXPIRED ∨ ter = .tecPRECISION_LOSS := by
  simp only [Vault.canCreate, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals simp

/-- Proof body of the stored-maximum line of `Vault.create_success`. -/
lemma Vault.canCreate_assetsMaximum_not_rounded_proof (scale : Option UInt8) (m : Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType)
    (hcan : Vault.canCreate scale (some m) schedule t nt = .ok .tesSUCCESS) :
    STAmount.isRounded nt m = false :=
  Number.isRounded_eq_false_of_isOnExponentGrid m _ nt
    (Vault.canCreate_assetsMaximum scale (some m) schedule t nt hcan m rfl)

/-- Proof body of the creation line of `Vault.create_success`. -/
lemma Vault.create_success_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool)
    (nt : NumericType)
    (hscale : nt.isIntegral = false → scale.getD vaultDefaultIOUScale ≤ vaultMaximumIOUScale)
    (hmax : ∀ m ∈ assetsMaximum, m.operator_ne Number.zero = true →
      m.isNormalized ∧ Number.zero.operator_lt m = true)
    (hgap : ∀ s ∈ schedule, s.hasValidGap = true)
    (hfee : ∀ s ∈ schedule, ∀ r ∈ earlyExitFeeRate, r ≤ maxEarlyExitFeeRate) :
    ∃ v, Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v := by
  -- the stored maximum is a requested one that is not zero
  have hmax' : ∀ m ∈ assetsMaximum.filter (·.operator_ne Number.zero),
      m.isNormalized ∧ Number.zero.operator_lt m = true := by
    intro m hm
    cases assetsMaximum with
    | none => simp at hm
    | some m' =>
      by_cases hne : m'.operator_ne Number.zero = true
      · simp only [Option.filter, hne, Option.mem_def, Option.some.injEq, if_true] at hm
        subst hm
        exact hmax _ rfl hne
      · simp [Option.filter, hne] at hm
  unfold Vault.create
  dsimp only
  obtain ⟨v, hv, -⟩ := RawVault.to_lawful_ok_of (rv := {
      assetsAvailable := Number.zero
      assetsDeployed := Number.zero
      assetsReserved := Number.zero
      assetsMaximum := assetsMaximum.filter (·.operator_ne Number.zero)
      numericType := nt
      scale := if nt.isIntegral then 0 else scale.getD vaultDefaultIOUScale
      sharesTotal := Number.zero
      lossUnrealized := Number.zero
      yieldUnrealized := Number.zero
      schedule
      earlyExitFeeRate := if schedule.isSome then earlyExitFeeRate else none
      ownerCanBlockDeposit
      depositBlocked := false })
    { assetsAvailable_norm := Number.zero_isNormalized
      assetsDeployed_norm := Number.zero_isNormalized
      assetsReserved_norm := Number.zero_isNormalized
      assetsMaximum_norm := fun m hm => (hmax' m hm).1
      sharesTotal_norm := Number.zero_isNormalized
      lossUnrealized_norm := Number.zero_isNormalized
      yieldUnrealized_norm := Number.zero_isNormalized
      sharesTotal_nonneg := by simp [Number.toRat_zero]
      sharesTotal_int := by simp [Number.toRat_zero]
      scale_integral := fun h => by simp [h]
      scale_le := by
        show (if nt.isIntegral = true then 0 else scale.getD vaultDefaultIOUScale) ≤ vaultMaximumIOUScale
        cases hi : nt.isIntegral
        · rw [if_neg (by simp)]; exact hscale hi
        · rw [if_pos rfl]; decide }
    { assetsAvailable_nonneg := (by decide : Number.zero.operator_le Number.zero = true)
      assetsDeployed_nonneg := (by decide : Number.zero.operator_le Number.zero = true)
      assetsReserved_nonneg := (by decide : Number.zero.operator_le Number.zero = true)
      lossUnrealized_nonneg := (by decide : Number.zero.operator_le Number.zero = true)
      yieldUnrealized_nonneg := (by decide : Number.zero.operator_le Number.zero = true)
      assetsMaximum_pos := fun m hm => (hmax' m hm).2
      empty_shares := fun _ => ⟨rfl, rfl⟩
      lossUnrealized_le := (by decide : Number.zero.operator_le Number.zero = true)
      assetsDeployed_representable := STAmount.isRounded_zero nt
      assetsReserved_le := (by decide : Number.zero.operator_le Number.zero = true)
      sharesTotal_representable := STAmount.isRounded_zero .int64
      depositBlocked_owner := fun h => by simp at h
      schedule_gap := hgap
      earlyExitFeeRate_closedEnded := fun h => by
        cases hs : schedule.isSome
        · simp [hs] at h
        · rfl
      earlyExitFeeRate_le := fun r hr => by
        cases hs : schedule.isSome
        · simp [hs] at hr
        · simp only [hs, if_true] at hr
          obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hs
          exact hfee s hs' r hr
      assetsAvailable_representable := STAmount.isRounded_zero nt
      assetsAvailable_onGrid := Or.inl rfl }
  exact ⟨v, hv⟩

/-- Proof body of the empty-vault line of `Vault.create_success`. -/
lemma Vault.create_empty_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool)
    (nt : NumericType) (v : Vault)
    (hok : Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v) :
    v.assetsAvailable = Number.zero ∧ v.assetsDeployed = Number.zero ∧ v.assetsReserved = Number.zero ∧
      v.sharesTotal = Number.zero ∧ v.lossUnrealized = Number.zero ∧ v.yieldUnrealized = Number.zero := by
  have h := Vault.create_ok_toRawVault hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · first
    | exact congrArg RawVault.assetsAvailable h
    | exact congrArg RawVault.assetsDeployed h
    | exact congrArg RawVault.assetsReserved h
    | exact congrArg RawVault.sharesTotal h
    | exact congrArg RawVault.lossUnrealized h
    | exact congrArg RawVault.yieldUnrealized h

/-- Proof body of the scale line of `Vault.create_not_lawful`. -/
lemma Vault.create_scale_out_of_range_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool)
    (nt : NumericType) (hiou : nt.isIntegral = false)
    (hbad : vaultMaximumIOUScale < scale.getD vaultDefaultIOUScale) :
    Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful := by
  unfold Vault.create
  apply RawVault.to_lawful_not_lawful
  rintro ⟨hwf, -⟩
  have h := hwf.scale_le
  simp only [hiou] at h
  exact absurd h (UInt8.not_le.mpr hbad)

/-- Proof body of the maximum line of `Vault.create_not_lawful`. -/
lemma Vault.create_assetsMaximum_out_of_range_proof (scale : Option UInt8) (m : Number)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool)
    (nt : NumericType) (hne : m.operator_ne Number.zero = true)
    (hbad : ¬ m.isNormalized ∨ Number.zero.operator_lt m = false) :
    Vault.create scale (some m) schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful := by
  unfold Vault.create
  apply RawVault.to_lawful_not_lawful
  rintro ⟨hwf, hv⟩
  have hm : m ∈ (some m).filter (·.operator_ne Number.zero) := by simp [Option.filter, hne]
  rcases hbad with hn | hneg
  · exact hn (hwf.assetsMaximum_norm m hm)
  · have h1 := hv.assetsMaximum_pos m hm
    simp [h1] at hneg

/-- Proof body of the schedule line of `Vault.create_not_lawful`. -/
lemma Vault.create_schedule_gap_proof (scale : Option UInt8) (assetsMaximum : Option Number) (s : VaultSchedule)
    (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType)
    (hbad : s.hasValidGap = false) :
    Vault.create scale assetsMaximum (some s) earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful := by
  unfold Vault.create
  apply RawVault.to_lawful_not_lawful
  rintro ⟨-, hv⟩
  have h := hv.schedule_gap s rfl
  simp [h] at hbad

/-- Proof body of the fee line of `Vault.create_not_lawful`. -/
lemma Vault.create_fee_above_maximum_proof (scale : Option UInt8) (assetsMaximum : Option Number)
    (s : VaultSchedule) (r : TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType)
    (hbad : maxEarlyExitFeeRate < r) :
    Vault.create scale assetsMaximum (some s) (some r) ownerCanBlockDeposit nt = .error .notLawful := by
  unfold Vault.create
  apply RawVault.to_lawful_not_lawful
  rintro ⟨-, hv⟩
  exact UInt32.not_le.mpr hbad (hv.earlyExitFeeRate_le r rfl)

/-- `update` re-checks the vault with only `assetsMaximum` and `depositBlocked` replaced. -/
lemma Vault.update_eq (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool) :
    v.update assetsMaximum blockDeposit =
      ({ v.toRawVault with
        assetsMaximum := match assetsMaximum with
          | none => v.assetsMaximum
          | some m => if m.operator_eq Number.zero then none else some m
        depositBlocked := blockDeposit.getD v.depositBlocked } :
        RawVault).to_lawful := rfl

/-- Proof body of the update line of `Vault.update_success`. -/
lemma Vault.update_success_proof (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    (hmax : ∀ m ∈ assetsMaximum, m.operator_eq Number.zero = false →
      m.isNormalized ∧ Number.zero.operator_lt m = true)
    (hblock : blockDeposit = some true → v.ownerCanBlockDeposit = true) :
    ∃ v', v.update assetsMaximum blockDeposit = .ok v' := by
  -- the stored maximum is the old one, or a requested one that is not zero
  have hmax' : ∀ m ∈ (match assetsMaximum with
      | none => v.assetsMaximum
      | some m => if m.operator_eq Number.zero then none else some m),
      m.isNormalized ∧ Number.zero.operator_lt m = true := by
    intro m hm
    cases assetsMaximum with
    | none => exact ⟨v.wf.assetsMaximum_norm m hm, v.valid.assetsMaximum_pos m hm⟩
    | some m' =>
      cases heq : m'.operator_eq Number.zero
      · simp only [heq, Bool.false_eq_true, if_false, Option.mem_def, Option.some.injEq] at hm
        subst hm
        exact hmax _ rfl heq
      · simp [heq] at hm
  rw [Vault.update_eq]
  obtain ⟨v', hv', -⟩ := RawVault.to_lawful_ok_of (rv := { v.toRawVault with
      assetsMaximum := match assetsMaximum with
        | none => v.assetsMaximum
        | some m => if m.operator_eq Number.zero then none else some m
      depositBlocked := blockDeposit.getD v.depositBlocked })
    { v.wf with assetsMaximum_norm := fun m hm => (hmax' m hm).1 }
    { v.valid with
      assetsMaximum_pos := fun m hm => (hmax' m hm).2
      depositBlocked_owner := fun h => by
        cases hb : blockDeposit with
        | none => simp only [hb, Option.getD_none] at h; exact v.valid.depositBlocked_owner h
        | some b => simp only [hb, Option.getD_some] at h; exact hblock (by rw [hb, h]) }
  exact ⟨v', hv'⟩

/-- Proof body of the stored-maximum line of `Vault.update_success`. -/
lemma Vault.canVaultUpdate_assetsMaximum_not_rounded_proof (v : Vault) (m : Number) (blockDeposit : Option Bool)
    (hcan : v.canVaultUpdate (some m) blockDeposit = .ok .tesSUCCESS) :
    STAmount.isRounded v.numericType m = false := by
  apply Number.isRounded_eq_false_of_isOnExponentGrid m v.baseExponent
  simp only [Vault.canVaultUpdate, bind, Except.bind, pure, Except.pure] at hcan
  walk_ok
  all_goals simp_all

/-- Proof body of the no-change line of `Vault.update_success`. -/
lemma Vault.update_none_proof (v : Vault) : v.update none none = .ok v := by
  rw [Vault.update_eq]
  unfold RawVault.to_lawful
  rw [dif_pos ⟨v.wf, v.valid⟩]
  rfl

/-- Proof body of the maximum line of `Vault.update_not_lawful`. -/
lemma Vault.update_assetsMaximum_out_of_range_proof (v : Vault) (m : Number) (blockDeposit : Option Bool)
    (hne : m.operator_eq Number.zero = false) (hbad : ¬ m.isNormalized ∨ Number.zero.operator_lt m = false) :
    v.update (some m) blockDeposit = .error .notLawful := by
  rw [Vault.update_eq]
  apply RawVault.to_lawful_not_lawful
  rintro ⟨hwf, hv⟩
  have hm : m ∈ (if m.operator_eq Number.zero then none else some m) := by simp [hne]
  rcases hbad with hn | hneg
  · exact hn (hwf.assetsMaximum_norm m hm)
  · have h1 := hv.assetsMaximum_pos m hm
    simp [h1] at hneg

/-- Proof body of the deposit-block line of `Vault.update_not_lawful`. -/
lemma Vault.update_block_not_permitted_proof (v : Vault) (assetsMaximum : Option Number)
    (hocb : v.ownerCanBlockDeposit = false) :
    v.update assetsMaximum (some true) = .error .notLawful := by
  rw [Vault.update_eq]
  apply RawVault.to_lawful_not_lawful
  rintro ⟨-, hv⟩
  have h := hv.depositBlocked_owner (by simp)
  simp [hocb] at h

end XRPL.Model.SingleAssetVault
