import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.Common.SetDefs
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # Proof bodies for the Loan guard theorems

Proofs for the `canCreate`, `canAccept`, `canPay`, `canManage` and `canDelete` exits. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultSchedule)

open private checkPrecisionFields canFundLoan from XRPL.Model.Lending.Loan.LoanSet

private lemma exponent_eq (v : Vault) (nt : NumericType) (assetsTotal : Number) (e : Int)
    (hat : v.assetsTotal = .ok assetsTotal) (hexp : numberExponent assetsTotal v.baseExponent nt = .ok e) :
    AssetPool.exponent v nt = .ok e := by
  show (do let a ← v.assetsTotal; numberExponent a v.baseExponent nt) = _
  rw [hat]; exact hexp

/-! ## The vault check -/

private lemma canFundLoan_subscription (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (h : v.phase t = .subscription) :
    canFundLoan v schedule t nt = .ok .tecTOO_SOON := by
  unfold canFundLoan
  simp only [Vault.pool_phase, h]
  rfl

private lemma canFundLoan_redemption (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (h : v.phase t = .redemption) :
    canFundLoan v schedule t nt = .ok .tecEXPIRED := by
  unfold canFundLoan
  simp only [Vault.pool_phase, h]
  rfl

private lemma canFundLoan_ends_late (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (s : VaultSchedule) (h : v.phase t = .investment) (hs : v.schedule = some s)
    (hlate : s.redemptionDate.toNat <
      schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat + loanRedemptionBuffer) :
    canFundLoan v schedule t nt = .ok .tecNO_PERMISSION := by
  unfold canFundLoan
  simp only [Vault.pool_phase, h, Vault.pool_redemptionDate, hs]
  simp [hlate]

/-- A vault that lends for the schedule leaves only the scale check. -/
private lemma canFundLoan_open (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType) (e : Int)
    (hopen : schedule.FitsVault v t) (hexp : AssetPool.exponent v nt = .ok e) :
    canFundLoan v schedule t nt = .ok (if e != v.baseExponent then .tecLIMIT_EXCEEDED else .tesSUCCESS) := by
  unfold canFundLoan
  rcases hopen with h | ⟨h, hs⟩
  · simp only [Vault.pool_phase, h, hexp, bind, Except.bind, pure, Except.pure]
    show (if (e != v.baseExponent) = true then Except.ok TER.tecLIMIT_EXCEEDED else Except.ok TER.tesSUCCESS) = _
    split <;> rfl
  · simp only [Vault.pool_phase, h, hexp, bind, Except.bind, pure, Except.pure,
      Vault.pool_baseExponent v]
    cases hsch : v.schedule with
    | none => simp [XRPL.Model.SingleAssetVault.Vault.phase, hsch] at h
    | some s =>
      have hb := hs s hsch
      simp only [Vault.pool_redemptionDate, hsch, Option.map_some, Option.getD_some]
      rw [if_neg (by simp; omega)]
      show (if (e != v.baseExponent) = true then Except.ok TER.tecLIMIT_EXCEEDED else Except.ok TER.tesSUCCESS) = _
      split <;> rfl

/-- The vault check passes exactly when the vault lends for the schedule at its base scale. -/
private lemma canFundLoan_success_iff (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (e : Int) (hexp : AssetPool.exponent v nt = .ok e) :
    canFundLoan v schedule t nt = .ok .tesSUCCESS ↔ schedule.FitsVault v t ∧ e = v.baseExponent := by
  constructor
  · intro h
    have hopen : schedule.FitsVault v t := by
      cases hp : v.phase t with
      | noPhase => exact Or.inl hp
      | subscription => rw [canFundLoan_subscription v schedule t nt hp] at h; exact absurd h (by decide)
      | redemption => rw [canFundLoan_redemption v schedule t nt hp] at h; exact absurd h (by decide)
      | investment =>
        refine Or.inr ⟨hp, fun s hs => ?_⟩
        by_contra hlate
        rw [canFundLoan_ends_late v schedule t nt s hp hs (by omega)] at h
        exact absurd h (by decide)
    refine ⟨hopen, ?_⟩
    rw [canFundLoan_open v schedule t nt e hopen hexp] at h
    by_contra hne
    rw [if_pos (by simpa using hne)] at h
    exact absurd h (by decide)
  · rintro ⟨hopen, he⟩
    rw [canFundLoan_open v schedule t nt e hopen hexp, he]
    simp

/-- The vault check returns success, tecTOO_SOON, tecEXPIRED, tecNO_PERMISSION or tecLIMIT_EXCEEDED. -/
private lemma canFundLoan_codes (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (ter : TER) (h : canFundLoan v schedule t nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecTOO_SOON ∨ ter = .tecEXPIRED ∨ ter = .tecNO_PERMISSION ∨
      ter = .tecLIMIT_EXCEEDED := by
  cases hp : v.phase t with
  | subscription => rw [canFundLoan_subscription v schedule t nt hp] at h; cases h; simp
  | redemption => rw [canFundLoan_redemption v schedule t nt hp] at h; cases h; simp
  | noPhase =>
    cases hexp : AssetPool.exponent v nt with
    | error err =>
      unfold canFundLoan at h
      simp only [Vault.pool_phase, hp, hexp, bind, Except.bind] at h
      exact absurd h (by simp)
    | ok e =>
      rw [canFundLoan_open v schedule t nt e (Or.inl hp) hexp] at h
      split at h <;> cases h <;> simp
  | investment =>
    cases hsch : v.schedule with
    | none => simp [XRPL.Model.SingleAssetVault.Vault.phase, hsch] at hp
    | some s =>
      by_cases hlate : s.redemptionDate.toNat <
          schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat +
            loanRedemptionBuffer
      · rw [canFundLoan_ends_late v schedule t nt s hp hsch hlate] at h; cases h; simp
      · have hopen : schedule.FitsVault v t :=
          Or.inr ⟨hp, fun s' hs' => by rw [hsch, Option.mem_def, Option.some.injEq] at hs'; subst hs'; omega⟩
        cases hexp : AssetPool.exponent v nt with
        | error err =>
          unfold canFundLoan at h
          simp only [Vault.pool_phase, hp, hexp, bind, Except.bind, Vault.pool_redemptionDate, hsch] at h
          simp only [Option.map_some, Option.getD_some, gt_iff_lt, pure_eq] at h
          rw [if_neg (by omega)] at h
          exact absurd h (by simp)
        | ok e =>
          rw [canFundLoan_open v schedule t nt e hopen hexp] at h
          split at h <;> cases h <;> simp

/-- `canCreate` once the schedule and the start date pass: the vault check, then the precision check. -/
private lemma canCreate_reduce (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (hfits : schedule.Fits)
    (hstart : twoStep = false ∨ t < schedule.startDate) :
    Loan.canCreate broker v p fees schedule t twoStep =
      match canFundLoan v schedule t broker.numericType with
      | .error e => .error e
      | .ok vt => if !vt.isTesSuccess then .ok vt else
          .ok (if (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) then
            .tesSUCCESS else .tecPRECISION_LOSS) := by
  have hst : (twoStep && decide (t ≥ schedule.startDate)) = false := by
    rcases hstart with h | h
    · simp [h]
    · simp [UInt32.not_le.mpr h]
  simp only [Loan.canCreate, schedule.checkTimeAvailability_success hfits, hst, bind, Except.bind, pure,
    Except.pure, Bool.false_eq_true, ↓reduceIte]
  cases canFundLoan v schedule t broker.numericType with
  | error e => rfl
  | ok vt =>
    simp only [checkPrecisionFields_pure]
    by_cases hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = true <;>
      simp only [hall, ↓reduceIte, Bool.false_eq_true, show TER.tesSUCCESS.isTesSuccess = true from rfl,
        show TER.tecPRECISION_LOSS.isTesSuccess = false from rfl, Bool.not_true, Bool.not_false]

private lemma canCreate_killed (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (hk : schedule.checkTimeAvailability = .ok .tecKILLED) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecKILLED := by
  simp only [Loan.canCreate, hk, bind, Except.bind]
  rfl

/-- Proof body of the tecKILLED line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_schedule_too_long_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (hlong : maxTime.toNat < schedule.startDate.toNat + schedule.gracePeriod.toNat +
      schedule.paymentTotal.toNat * schedule.paymentInterval.toNat) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecKILLED :=
  canCreate_killed broker v p fees schedule t twoStep (schedule.checkTimeAvailability_killed hlong)

/-- Proof body of the StartDate line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_start_passed_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (hfits : schedule.Fits) (hpassed : schedule.startDate ≤ t) :
    Loan.canCreate broker v p fees schedule t true = .ok .tecEXPIRED := by
  simp only [Loan.canCreate, schedule.checkTimeAvailability_success hfits, bind, Except.bind]
  simp [hpassed]
  rfl

/-- Proof body of the subscription phase line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_subscription_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (hfits : schedule.Fits)
    (hstart : twoStep = false ∨ t < schedule.startDate) (hphase : v.phase t = .subscription) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecTOO_SOON := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_subscription v schedule t _ hphase]
  rfl

/-- Proof body of the redemption phase line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_redemption_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (hfits : schedule.Fits)
    (hstart : twoStep = false ∨ t < schedule.startDate) (hphase : v.phase t = .redemption) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecEXPIRED := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_redemption v schedule t _ hphase]
  rfl

/-- Proof body of the RedemptionDate line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_ends_late_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (s : VaultSchedule) (hfits : schedule.Fits)
    (hstart : twoStep = false ∨ t < schedule.startDate) (hphase : v.phase t = .investment)
    (hs : v.schedule = some s)
    (hlate : s.redemptionDate.toNat <
      schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat + loanRedemptionBuffer) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecNO_PERMISSION := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_ends_late v schedule t _ s hphase hs hlate]
  rfl

/-- Proof body of the base scale line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_base_scale_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (assetsTotal : Number) (e : Int)
    (hfits : schedule.Fits) (hstart : twoStep = false ∨ t < schedule.startDate)
    (hopen : schedule.FitsVault v t) (hat : v.assetsTotal = .ok assetsTotal)
    (hexp : numberExponent assetsTotal v.baseExponent broker.numericType = .ok e) (hgt : v.baseExponent < e) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecLIMIT_EXCEEDED := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_open v schedule t _ e hopen (exponent_eq v _ assetsTotal e hat hexp),
    if_pos (by simp; omega)]
  rfl

/-- Proof body of the precision line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_precision_loss_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (assetsTotal : Number)
    (hfits : schedule.Fits) (hstart : twoStep = false ∨ t < schedule.startDate)
    (hopen : schedule.FitsVault v t) (hat : v.assetsTotal = .ok assetsTotal)
    (hexp : numberExponent assetsTotal v.baseExponent broker.numericType = .ok v.baseExponent)
    (hround : ∃ x ∈ p :: fees.amountFields, STAmount.isRounded broker.numericType x = true) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tecPRECISION_LOSS := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_open v schedule t _ _ hopen (exponent_eq v _ assetsTotal _ hat hexp)]
  have hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = false := by
    obtain ⟨x, hx, hr⟩ := hround
    rw [Bool.eq_false_iff]
    intro h
    have := List.all_eq_true.mp h x hx
    simp [hr] at this
  simp [hall]
  rfl

/-- Proof body of the success line of `Loan.canCreate_exits`. -/
lemma Loan.canCreate_success_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (assetsTotal : Number)
    (hfits : schedule.Fits) (hstart : twoStep = false ∨ t < schedule.startDate)
    (hopen : schedule.FitsVault v t) (hat : v.assetsTotal = .ok assetsTotal)
    (hexp : numberExponent assetsTotal v.baseExponent broker.numericType = .ok v.baseExponent)
    (hexact : ∀ x ∈ p :: fees.amountFields, STAmount.isRounded broker.numericType x = false) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS := by
  rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart,
    canFundLoan_open v schedule t _ _ hopen (exponent_eq v _ assetsTotal _ hat hexp)]
  have hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = true :=
    List.all_eq_true.mpr (fun x hx => by simp [hexact x hx])
  simp [hall]

/-- Proof body of `canCreate_error_codes`. -/
lemma Loan.canCreate_error_codes_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (ter : TER)
    (hok : Loan.canCreate broker v p fees schedule t twoStep = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecKILLED ∨ ter = .tecTOO_SOON ∨ ter = .tecEXPIRED ∨
      ter = .tecNO_PERMISSION ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS := by
  have hst : schedule.checkTimeAvailability = .ok .tecKILLED ∨ schedule.checkTimeAvailability = .ok .tesSUCCESS := by
    rw [LoanSchedule.checkTimeAvailability_eq]; split <;> simp
  unfold Loan.canCreate at hok
  rcases hst with h | h <;> rw [h] at hok
  · simp only [bind, Except.bind, pure, Except.pure, show TER.tecKILLED.isTesSuccess = false from rfl,
      Bool.not_false, ↓reduceIte, Except.ok.injEq] at hok
    simp [← hok]
  · simp only [bind, Except.bind, pure, Except.pure, show TER.tesSUCCESS.isTesSuccess = true from rfl,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
    by_cases hexp : (twoStep && decide (t ≥ schedule.startDate)) = true
    · simp only [hexp, ↓reduceIte, Except.ok.injEq] at hok
      simp [← hok]
    · simp only [hexp, Bool.false_eq_true, ↓reduceIte] at hok
      cases hf : canFundLoan v schedule t broker.numericType with
      | error err => rw [hf] at hok; exact absurd hok (by simp)
      | ok vt =>
        rw [hf] at hok
        simp only [checkPrecisionFields_pure] at hok
        by_cases hvt : vt.isTesSuccess = true
        · simp only [hvt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
          by_cases hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = true <;>
            simp only [hall, ↓reduceIte, Bool.false_eq_true, show TER.tesSUCCESS.isTesSuccess = true from rfl,
              show TER.tecPRECISION_LOSS.isTesSuccess = false from rfl, Bool.not_true, Bool.not_false,
              Except.ok.injEq] at hok <;> simp [← hok]
        · simp only [hvt, Bool.not_false, ↓reduceIte, Except.ok.injEq] at hok
          rcases canFundLoan_codes v schedule t _ vt hf with h | h | h | h | h <;> simp [← hok, h]

/-- Proof body of `canCreate_lawful_iff`. -/
lemma Loan.canCreate_lawful_iff_proof (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool) (assetsTotal : Number) (e : Int)
    (hn : 0 < schedule.paymentTotal) (hi : 0 < schedule.paymentInterval)
    (hat : v.assetsTotal = .ok assetsTotal)
    (hexp : numberExponent assetsTotal v.baseExponent broker.numericType = .ok e) :
    Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS ↔
      schedule.Fits ∧ (twoStep = false ∨ t < schedule.startDate) ∧ schedule.FitsVault v t ∧
        e = v.baseExponent ∧ ∀ x ∈ p :: fees.amountFields, STAmount.isRounded broker.numericType x = false := by
  have hexp' := exponent_eq v _ assetsTotal e hat hexp
  constructor
  · intro h
    have hfits : schedule.Fits := by
      by_contra hc
      have hk : schedule.checkTimeAvailability = .ok .tecKILLED := by
        have := LoanSchedule.checkTimeAvailability_eq schedule
        split at this
        · exact this
        · exact absurd ((schedule.checkTimeAvailability_success_iff hn hi).mp this) hc
      rw [canCreate_killed broker v p fees schedule t twoStep hk] at h
      exact absurd h (by decide)
    have hstart : twoStep = false ∨ t < schedule.startDate := by
      cases htwo : twoStep
      · exact Or.inl rfl
      · by_contra hc
        simp only [Bool.true_eq_false, false_or, UInt32.not_lt] at hc
        rw [htwo, Loan.canCreate_start_passed_proof broker v p fees schedule t hfits hc] at h
        exact absurd h (by decide)
    rw [canCreate_reduce broker v p fees schedule t twoStep hfits hstart] at h
    cases hf : canFundLoan v schedule t broker.numericType with
    | error err => rw [hf] at h; exact absurd h (by simp)
    | ok vt =>
      rw [hf] at h
      simp only at h
      by_cases hvt : vt = .tesSUCCESS
      · subst hvt
        obtain ⟨hopen, he⟩ := (canFundLoan_success_iff v schedule t _ e hexp').mp hf
        refine ⟨hfits, hstart, hopen, he, fun x hx => ?_⟩
        by_cases hall : (p :: fees.amountFields).all (fun x => !STAmount.isRounded broker.numericType x) = true
        · simpa using List.all_eq_true.mp hall x hx
        · simp only [hall, show TER.tesSUCCESS.isTesSuccess = true from rfl, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
          exact absurd h (by decide)
      · rw [if_pos (by rw [TER.isTesSuccess_eq_false vt hvt]; rfl)] at h
        exact absurd (Except.ok.inj h) hvt
  · rintro ⟨hfits, hstart, hopen, he, hexact⟩
    subst he
    exact Loan.canCreate_success_proof broker v p fees schedule t twoStep assetsTotal hfits hstart hopen hat hexp
      hexact

/-- Proof body of the not pending line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_not_pending_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = false) :
    loan.canAccept v t = .ok .tecNO_PERMISSION := by
  simp only [Loan.canAccept, hp]
  rfl

/-- A pending loan past its StartDate, or in the redemption phase, can't be accepted. -/
lemma Loan.canAccept_expired_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (hexp : loan.schedule.startDate ≤ t ∨ v.phase t = .redemption) :
    loan.canAccept v t = .ok .tecEXPIRED := by
  by_cases ht : loan.schedule.startDate ≤ t
  · simp only [Loan.canAccept, hp]
    simp [ht]
  · have hr := hexp.resolve_left ht
    simp only [Loan.canAccept, hp, Vault.pool_phase, hr]
    simp [ht]

/-- A loan is never accepted in the redemption phase. -/
lemma Loan.canAccept_not_redemption (loan : Loan) (v : Vault) (t : UInt32) (hred : v.phase t = .redemption)
    (h : loan.canAccept v t = .ok .tesSUCCESS) : False := by
  unfold Loan.canAccept at h
  simp only [Vault.pool_phase, hred] at h
  split at h
  · cases h
  split at h
  · cases h
  · cases h

/-- Proof body of the StartDate line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_start_passed_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (ht : loan.schedule.startDate ≤ t) : loan.canAccept v t = .ok .tecEXPIRED :=
  Loan.canAccept_expired_proof loan v t hp (Or.inl ht)

/-- Proof body of the redemption phase line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_redemption_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (hphase : v.phase t = .redemption) : loan.canAccept v t = .ok .tecEXPIRED :=
  Loan.canAccept_expired_proof loan v t hp (Or.inr hphase)

/-- Proof body of the subscription phase line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_subscription_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (ht : t < loan.schedule.startDate) (hphase : v.phase t = .subscription) :
    loan.canAccept v t = .ok .tecTOO_SOON := by
  simp only [Loan.canAccept, hp, Vault.pool_phase, hphase]
  simp [UInt32.not_le.mpr ht]

/-- `canAccept` once the loan is pending, the start date is ahead and the phase allows it. -/
private lemma canAccept_reduce (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (ht : t < loan.schedule.startDate) (hphase : v.phase t = .noPhase ∨ v.phase t = .investment)
    (i : Number) (hi : loan.interestDue = .ok i) (b : Bool) (hb : v.exceedsOpenLimit i = .ok b) :
    loan.canAccept v t = .ok (if b then .tecLIMIT_EXCEEDED else .tesSUCCESS) := by
  rcases hphase with hph | hph <;>
  · simp only [Loan.canAccept, hp, Vault.pool_phase, hph, Vault.pool_exceedsOpenLimit, hi]
    simp [UInt32.not_le.mpr ht, hb]
    cases b <;> rfl

/-- Proof body of the Open limit line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_open_zone_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (ht : t < loan.schedule.startDate) (hphase : v.phase t = .noPhase ∨ v.phase t = .investment)
    (i : Number) (hi : loan.interestDue = .ok i) (hopen : v.exceedsOpenLimit i = .ok true) :
    loan.canAccept v t = .ok .tecLIMIT_EXCEEDED := by
  rw [canAccept_reduce loan v t hp ht hphase i hi true hopen]
  rfl

/-- Proof body of the success line of `Loan.canAccept_exits`. -/
lemma Loan.canAccept_success_proof (loan : Loan) (v : Vault) (t : UInt32) (hp : loan.isPending = true)
    (ht : t < loan.schedule.startDate) (hphase : v.phase t = .noPhase ∨ v.phase t = .investment)
    (i : Number) (hi : loan.interestDue = .ok i) (hopen : v.exceedsOpenLimit i = .ok false) :
    loan.canAccept v t = .ok .tesSUCCESS := by
  rw [canAccept_reduce loan v t hp ht hphase i hi false hopen]
  rfl

/-- Proof body of `canAccept_error_codes`. -/
lemma Loan.canAccept_error_codes_proof (loan : Loan) (v : Vault) (t : UInt32) (ter : TER)
    (hok : loan.canAccept v t = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecEXPIRED ∨ ter = .tecTOO_SOON ∨
      ter = .tecLIMIT_EXCEEDED := by
  cases hp : loan.isPending
  · rw [Loan.canAccept_not_pending_proof loan v t hp] at hok; cases hok; simp
  by_cases ht : loan.schedule.startDate ≤ t
  · rw [Loan.canAccept_expired_proof loan v t hp (Or.inl ht)] at hok; cases hok; simp
  have ht' : t < loan.schedule.startDate := UInt32.not_le.mp ht
  cases hph : v.phase t with
  | subscription => rw [Loan.canAccept_subscription_proof loan v t hp ht' hph] at hok; cases hok; simp
  | redemption => rw [Loan.canAccept_expired_proof loan v t hp (Or.inr hph)] at hok; cases hok; simp
  | noPhase | investment =>
    cases hi : loan.interestDue with
    | error e =>
      simp only [Loan.canAccept, hp, Vault.pool_phase, hph, hi] at hok
      simp [ht] at hok
    | ok i =>
      cases hb : v.exceedsOpenLimit i with
      | error e =>
        simp only [Loan.canAccept, hp, Vault.pool_phase, hph, hi, Vault.pool_exceedsOpenLimit] at hok
        simp [ht, hb] at hok
      | ok b =>
        first
        | rw [canAccept_reduce loan v t hp ht' (Or.inl hph) i hi b hb] at hok
        | rw [canAccept_reduce loan v t hp ht' (Or.inr hph) i hi b hb] at hok
        cases b <;> cases hok <;> simp

/-- Proof body of `canAccept_lawful_iff`. -/
lemma Loan.canAccept_lawful_iff_proof (loan : Loan) (v : Vault) (t : UInt32) (i : Number)
    (hi : loan.interestDue = .ok i) (b : Bool) (hb : v.exceedsOpenLimit i = .ok b) :
    loan.canAccept v t = .ok .tesSUCCESS ↔
      loan.isPending = true ∧ t < loan.schedule.startDate ∧
        (v.phase t = .noPhase ∨ v.phase t = .investment) ∧ b = false := by
  constructor
  · intro hok
    cases hp : loan.isPending
    · rw [Loan.canAccept_not_pending_proof loan v t hp] at hok; exact absurd hok (by decide)
    by_cases ht : loan.schedule.startDate ≤ t
    · rw [Loan.canAccept_expired_proof loan v t hp (Or.inl ht)] at hok; exact absurd hok (by decide)
    have ht' : t < loan.schedule.startDate := UInt32.not_le.mp ht
    have hph : v.phase t = .noPhase ∨ v.phase t = .investment := by
      cases hph : v.phase t with
      | subscription =>
        rw [Loan.canAccept_subscription_proof loan v t hp ht' hph] at hok; exact absurd hok (by decide)
      | redemption =>
        rw [Loan.canAccept_expired_proof loan v t hp (Or.inr hph)] at hok; exact absurd hok (by decide)
      | noPhase => exact Or.inl rfl
      | investment => exact Or.inr rfl
    rw [canAccept_reduce loan v t hp ht' hph i hi b hb] at hok
    refine ⟨rfl, ht', hph, ?_⟩
    cases b
    · rfl
    · exact absurd hok (by decide)
  · rintro ⟨hp, ht, hph, rfl⟩
    exact Loan.canAccept_success_proof loan v t hp ht hph i hi hb

/-- Proof body of the pending line of `Loan.canPay_exits`. -/
lemma Loan.canPay_pending_proof (loan : Loan) (paymentType : LoanPaymentType) (hp : loan.isPending = true) :
    loan.canPay paymentType = .tecNO_PERMISSION := by
  simp [Loan.canPay, hp]

/-- Proof body of the overpayment line of `Loan.canPay_exits`. -/
lemma Loan.canPay_overpayment_not_allowed_proof (loan : Loan) (hp : loan.isPending = false)
    (ha : loan.allowsOverpayment = false) :
    loan.canPay .overpayment = .tecNO_PERMISSION := by
  simp [Loan.canPay, hp, ha]

/-- Proof body of the paid-off line of `Loan.canPay_exits`. -/
lemma Loan.canPay_paid_off_proof (loan : Loan) (paymentType : LoanPaymentType) (hp : loan.isPending = false)
    (ha : paymentType = .overpayment → loan.allowsOverpayment = true)
    (hpaid : loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero) :
    loan.canPay paymentType = .tecKILLED := by
  have hz0 : Number.zero.operator_eq Number.zero = true := rfl
  rcases hpaid with h | h <;> cases paymentType <;> simp_all [Loan.canPay]

/-- Proof body of the success line of `Loan.canPay_exits`. -/
lemma Loan.canPay_success_proof (loan : Loan) (paymentType : LoanPaymentType) (hp : loan.isPending = false)
    (ha : paymentType = .overpayment → loan.allowsOverpayment = true)
    (hr : loan.paymentRemaining ≠ 0) (hpo : loan.principalOutstanding ≠ Number.zero) :
    loan.canPay paymentType = .tesSUCCESS := by
  have hz : loan.principalOutstanding.operator_eq Number.zero = false := by
    rw [Bool.eq_false_iff]
    intro h
    apply hpo
    have := (operator_eq_iff _ _ loan.wf.principalOutstanding_norm Number.zero_isNormalized).mp h
    rw [Number.toRat_zero] at this
    exact (Number.toRat_eq_zero_iff_eq_zero loan.wf.principalOutstanding_norm).mp this
  cases paymentType <;> simp_all [Loan.canPay]

/-- Proof body of `canPay_error_codes`. -/
lemma Loan.canPay_error_codes_proof (loan : Loan) (paymentType : LoanPaymentType) :
    loan.canPay paymentType = .tesSUCCESS ∨ loan.canPay paymentType = .tecNO_PERMISSION ∨
      loan.canPay paymentType = .tecKILLED := by
  cases paymentType <;> simp only [Loan.canPay] <;> split_ifs <;> simp

/-- Proof body of `canPay_lawful_iff`. -/
lemma Loan.canPay_lawful_iff_proof (loan : Loan) (paymentType : LoanPaymentType) :
    loan.canPay paymentType = .tesSUCCESS ↔
      loan.isPending = false ∧ (paymentType = .overpayment → loan.allowsOverpayment = true) ∧
        loan.paymentRemaining ≠ 0 ∧ loan.principalOutstanding ≠ Number.zero := by
  constructor
  · intro h
    cases hp : loan.isPending
    · have ha : paymentType = .overpayment → loan.allowsOverpayment = true := by
        intro hpt
        cases ha : loan.allowsOverpayment
        · subst hpt; rw [Loan.canPay_overpayment_not_allowed_proof loan hp ha] at h; exact absurd h (by decide)
        · rfl
      refine ⟨rfl, ha, ?_, ?_⟩
      · intro hr
        rw [Loan.canPay_paid_off_proof loan paymentType hp ha (Or.inl hr)] at h; exact absurd h (by decide)
      · intro hpo
        rw [Loan.canPay_paid_off_proof loan paymentType hp ha (Or.inr hpo)] at h; exact absurd h (by decide)
    · rw [Loan.canPay_pending_proof loan paymentType hp] at h; exact absurd h (by decide)
  · rintro ⟨hp, ha, hr, hpo⟩
    exact Loan.canPay_success_proof loan paymentType hp ha hr hpo

/-- A pending, defaulted or paid-off loan can't be managed. -/
lemma Loan.canManage_closed_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hclosed : loan.isPending = true ∨ loan.isDefault = true ∨ loan.paymentRemaining = 0) :
    loan.canManage action now = .ok .tecNO_PERMISSION := by
  unfold Loan.canManage
  rcases hclosed with h | h | h <;> split_ifs <;> simp_all

/-- An impair of an impaired loan, or an unimpair of a loan that isn't impaired, is not permitted. -/
lemma Loan.canManage_wrong_flag_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hflag : (loan.isImpaired = true ∧ action = .impair) ∨ (loan.isImpaired = false ∧ action = .unimpair)) :
    loan.canManage action now = .ok .tecNO_PERMISSION := by
  unfold Loan.canManage
  rcases hflag with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> split_ifs <;> simp_all

/-- Proof body of the pending exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_pending_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hp : loan.isPending = true) : loan.canManage action now = .ok .tecNO_PERMISSION :=
  Loan.canManage_closed_proof loan action now (Or.inl hp)

/-- Proof body of the defaulted exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_defaulted_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hd : loan.isDefault = true) : loan.canManage action now = .ok .tecNO_PERMISSION :=
  Loan.canManage_closed_proof loan action now (Or.inr (Or.inl hd))

/-- Proof body of the paid-off exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_paid_off_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hr : loan.paymentRemaining = 0) : loan.canManage action now = .ok .tecNO_PERMISSION :=
  Loan.canManage_closed_proof loan action now (Or.inr (Or.inr hr))

/-- Proof body of the already-impaired exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_already_impaired_proof (loan : Loan) (now : UInt32) (h : loan.isImpaired = true) :
    loan.canManage .impair now = .ok .tecNO_PERMISSION :=
  Loan.canManage_wrong_flag_proof loan .impair now (Or.inl ⟨h, rfl⟩)

/-- Proof body of the not-impaired exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_not_impaired_proof (loan : Loan) (now : UInt32) (h : loan.isImpaired = false) :
    loan.canManage .unimpair now = .ok .tecNO_PERMISSION :=
  Loan.canManage_wrong_flag_proof loan .unimpair now (Or.inr ⟨h, rfl⟩)

/-- Proof body of the too-soon exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_default_too_soon_proof (loan : Loan) (now : UInt32)
    (hp : loan.isPending = false) (hd : loan.isDefault = false) (hr : loan.paymentRemaining ≠ 0)
    (hfit : loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat)
    (hsoon : now.toNat ≤ loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat) :
    loan.canManage .default now = .ok .tecTOO_SOON := by
  have hsum : (loan.nextPaymentDueDate + loan.schedule.gracePeriod).toNat =
      loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by simp [maxTime] at hfit; omega)
  have hle : ¬ now > loan.nextPaymentDueDate + loan.schedule.gracePeriod := by
    rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum]; omega
  simp [Loan.canManage, hp, hd, hr, hle, UInt32.addChecked_of_lt loan.gracePeriodEnd_lt, bind, Except.bind]

/-- Proof body of the success exit of `Loan.canManage_exits`. -/
lemma Loan.canManage_success_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hp : loan.isPending = false) (hd : loan.isDefault = false) (hr : loan.paymentRemaining ≠ 0)
    (himp : action = .impair → loan.isImpaired = false) (hunimp : action = .unimpair → loan.isImpaired = true)
    (hfit : loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat)
    (hlate : action = .default → loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < now.toNat) :
    loan.canManage action now = .ok .tesSUCCESS := by
  have hsum : (loan.nextPaymentDueDate + loan.schedule.gracePeriod).toNat =
      loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by simp [maxTime] at hfit; omega)
  cases action with
  | impair => simp [Loan.canManage, hp, hd, hr, himp rfl]
  | unimpair => simp [Loan.canManage, hp, hd, hr, hunimp rfl]
  | default =>
    have hgt : now > loan.nextPaymentDueDate + loan.schedule.gracePeriod := by
      rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum]; exact hlate rfl
    simp [Loan.canManage, hp, hd, hr, hgt, UInt32.addChecked_of_lt loan.gracePeriodEnd_lt, bind, Except.bind]

/-- Proof body of `canManage_error_codes`. -/
lemma Loan.canManage_error_codes_proof (loan : Loan) (action : LoanManageAction) (now : UInt32) :
    loan.canManage action now = .ok .tesSUCCESS ∨ loan.canManage action now = .ok .tecNO_PERMISSION ∨
      loan.canManage action now = .ok .tecTOO_SOON := by
  generalize hr : loan.canManage action now = r
  unfold Loan.canManage at hr
  simp only [bind, Except.bind, pure, Except.pure, UInt32.addChecked_of_lt loan.gracePeriodEnd_lt] at hr
  split_ifs at hr <;> subst hr <;> simp

/-- Proof body of `canManage_lawful_iff`. -/
lemma Loan.canManage_lawful_iff_proof (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (hfit : loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat) :
    loan.canManage action now = .ok .tesSUCCESS ↔
      loan.isPending = false ∧ loan.isDefault = false ∧ loan.paymentRemaining ≠ 0 ∧
        (action = .impair → loan.isImpaired = false) ∧ (action = .unimpair → loan.isImpaired = true) ∧
        (action = .default → loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < now.toNat) := by
  constructor
  · intro h
    have hclosed : ¬ (loan.isPending = true ∨ loan.isDefault = true ∨ loan.paymentRemaining = 0) := by
      intro hc; rw [Loan.canManage_closed_proof loan action now hc] at h; exact absurd h (by decide)
    push Not at hclosed
    obtain ⟨hp, hd, hr⟩ := hclosed
    have hp' : loan.isPending = false := by simpa using hp
    have hd' : loan.isDefault = false := by simpa using hd
    refine ⟨hp', hd', hr, fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
    · by_contra hc
      rw [Loan.canManage_wrong_flag_proof loan action now (Or.inl ⟨by simpa using hc, ha⟩)] at h
      exact absurd h (by decide)
    · by_contra hc
      rw [Loan.canManage_wrong_flag_proof loan action now (Or.inr ⟨by simpa using hc, ha⟩)] at h
      exact absurd h (by decide)
    · subst ha
      by_contra hc
      rw [Loan.canManage_default_too_soon_proof loan now hp' hd' hr hfit (by omega)] at h
      exact absurd h (by decide)
  · rintro ⟨hp, hd, hr, himp, hunimp, hlate⟩
    exact Loan.canManage_success_proof loan action now hp hd hr himp hunimp hfit hlate

/-- Proof body of the has-obligations exit of `Loan.canDelete_exits`. -/
lemma Loan.canDelete_has_obligations_proof (loan : Loan) (hp : loan.isPending = false)
    (hr : 0 < loan.paymentRemaining) :
    loan.canDelete = .tecHAS_OBLIGATIONS := by
  simp [Loan.canDelete, hp, hr]

/-- Proof body of the success exit of `Loan.canDelete_exits`. -/
lemma Loan.canDelete_success_proof (loan : Loan) (h : loan.isPending = true ∨ loan.paymentRemaining = 0) :
    loan.canDelete = .tesSUCCESS := by
  rcases h with h | h <;> simp [Loan.canDelete, h]

/-- Proof body of `canDelete_error_codes`. -/
lemma Loan.canDelete_error_codes_proof (loan : Loan) :
    loan.canDelete = .tesSUCCESS ∨ loan.canDelete = .tecHAS_OBLIGATIONS := by
  unfold Loan.canDelete
  split <;> simp

/-- Proof body of `canDelete_lawful_iff`. -/
lemma Loan.canDelete_lawful_iff_proof (loan : Loan) :
    loan.canDelete = .tesSUCCESS ↔ loan.isPending = true ∨ loan.paymentRemaining = 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hp : loan.isPending = false := by simpa using hc.1
    rw [Loan.canDelete_has_obligations_proof loan hp (by
      rw [UInt32.lt_iff_toNat_lt]; have := hc.2; rw [ne_eq, ← UInt32.toNat_inj] at this; simp at this ⊢; omega)] at h
    exact absurd h (by decide)
  · exact Loan.canDelete_success_proof loan

/-- Guards that pass in LoanSet passed the amortization guards. -/
lemma LoanProperties.checkGuards_amortization (props : LoanProperties) (principal : Number)
    (ir : TenthBips32) (n : UInt32) (nt : NumericType) (h : props.checkGuards principal ir n nt = .ok .tesSUCCESS) :
    props.amortizationGuards principal (ir != 0) n nt = .ok .tesSUCCESS := by
  unfold LoanProperties.checkGuards at h
  cases hg : props.amortizationGuards principal (ir != 0) n nt with
  | error e => rw [hg] at h; exact absurd h (by simp [bind, Except.bind])
  | ok g =>
    rw [hg] at h
    simp only [bind, Except.bind] at h
    by_cases hgs : g.isTesSuccess = true
    · rw [(TER.isTesSuccess_iff g).mp hgs]
    · simp only [Bool.not_eq_true] at hgs
      simp only [hgs, Bool.not_false, if_true, pure, Except.pure, Except.ok.injEq] at h
      rw [h] at hgs; exact absurd hgs (by decide)

end XRPL.Model.Lending
