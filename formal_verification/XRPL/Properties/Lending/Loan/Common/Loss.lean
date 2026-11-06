import XRPL.Properties.Lending.Loan.Common.Impaired
import XRPL.Properties.Lending.Loan.Common.PayMonotone
import XRPL.Properties.Lending.Loan.Common.Reserved

/-! # What loan operations do to LossUnrealized

Impair adds PrincipalOutstanding to LossUnrealized, unimpair takes it off again, and so do a default and
a payment of an impaired loan. Only a LoanSet raises AssetsDeployed, and only inside the Open zone. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.payInstalments_below UnsettledPayment.PaidOk from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- A vault update without a loss change keeps LossUnrealized. -/
private lemma Vault.poolAdjust_loss_zero (v v' : Vault) (c : PoolBalanceChange) (hc : c.loss = Number.zero)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.lossUnrealized = v.lossUnrealized := by
  have hr := (Vault.poolAdjust_adjustSums v c v' h).loss
  rw [hc, Number.operator_add_zero_right] at hr
  exact (Except.ok.inj hr).symm

/-- A vault update without a deployed change keeps AssetsDeployed. -/
lemma Vault.poolAdjust_deployed_zero (v v' : Vault) (c : PoolBalanceChange) (hc : c.deployed = Number.zero)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.assetsDeployed = v.assetsDeployed := by
  have hr := (Vault.poolAdjust_adjustSums v c v' h).deployed
  rw [hc, Number.operator_add_zero_right] at hr
  exact (Except.ok.inj hr).symm

/-- A new loan keeps LossUnrealized. As it fits the Open zone, AssetsDeployed after it and the principal are each
at most `10^16` base units. -/
lemma Loan.create_lossStep (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.lossUnrealized = v.lossUnrealized ∧
      r.pool'.assetsDeployed.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ v.baseExponent ∧
      principal.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨hzone, hfunds⟩ := Loan.create_inside_open_zone broker v principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hok
  obtain ⟨_, loanState, _, principal', _, hchecks, -, hpool, -, -⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  have hbase := Vault.baseExponent_scale_range v
  have hb10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hlim : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent := by
    have h2 : (10 : ℚ) ^ (v.baseExponent - 1) = 10 ^ v.baseExponent / 10 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    rw [h2] at hzone
    push_cast at hzone
    nlinarith
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) v.baseExponent
    (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
  have hsums := Vault.poolAdjust_adjustSums v _ _ hpool
  refine ⟨Vault.poolAdjust_loss_zero v r.pool' _ rfl hpool, ?_, by linarith⟩
  have hd := operator_add_le_of_le_normalized _ _ _ w v.wf.assetsDeployed_norm hp hsums.deployed hw
    (by rw [hwv]; push_cast; linarith)
  rw [hwv] at hd
  push_cast at hd
  exact hd

/-- An accept keeps LossUnrealized and AssetsDeployed. -/
lemma Loan.accept_lossStep (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) :
    r.pool'.lossUnrealized = v.lossUnrealized ∧ r.pool'.assetsDeployed = v.assetsDeployed := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hpool := ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›
  exact ⟨Vault.poolAdjust_loss_zero v _ _ rfl hpool, Vault.poolAdjust_deployed_zero v _ _ rfl hpool⟩

/-- A delete keeps LossUnrealized and never raises AssetsDeployed. -/
lemma Loan.delete_lossStep (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) :
    r.pool'.lossUnrealized = v.lossUnrealized ∧ r.pool'.assetsDeployed.toRat ≤ v.assetsDeployed.toRat := by
  cases hp : loan.isPending
  · rw [Loan.delete_active_vault loan v r hp h]
    exact ⟨rfl, le_refl _⟩
  · obtain ⟨principal', raw, _, -, hadj, hv', -, -⟩ := Loan.delete_pending_ok_inv loan v r hp h
    obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
    have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1
    have hl := hs.loss
    rw [show (loan.deleteChange principal').loss = Number.zero from rfl, Number.operator_add_zero_right] at hl
    have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    refine ⟨?_, ?_⟩
    · rw [show r.pool'.lossUnrealized = r.pool'.toRawVault.lossUnrealized from rfl, hraw, heq]
      exact (Except.ok.inj hl).symm
    · rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw, heq]
      exact Number.operator_add_le_self v.wf.assetsDeployed_norm
        (Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm)
        (by rw [Number.toRat_neg]; linarith) hs.deployed

/-- Deleting an active loan needs a loan with no payments left. -/
lemma Loan.canDelete_active_paid (loan : Loan) (h : loan.canDelete = .tesSUCCESS) (hp : loan.isPending = false) :
    loan.paymentRemaining = 0 := by
  unfold Loan.canDelete at h
  rw [hp] at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, gt_iff_lt] at hc
    by_contra hne
    apply hc
    rw [UInt32.lt_iff_toNat_lt]
    have : loan.paymentRemaining.toNat ≠ 0 := fun h0 => hne (UInt32.toNat_inj.mp (by rw [h0]; rfl))
    show 0 < loan.paymentRemaining.toNat
    omega

/-- Setting the impaired flag adds PrincipalOutstanding to LossUnrealized, clearing it takes it off.
AssetsDeployed and PrincipalOutstanding stay the same. -/
private lemma Loan.changeImpairment_lossStep (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    v.lossUnrealized.operator_add (if b then loan.principalOutstanding else loan.principalOutstanding.operator_neg)
        .to_nearest = .ok r.pool'.lossUnrealized ∧
      r.pool'.assetsDeployed = v.assetsDeployed ∧ r.loan'.isImpaired = b ∧
      r.loan'.principalOutstanding = loan.principalOutstanding := by
  have hflag := Loan.changeImpairment_flag loan v b r h
  cases b <;>
  · simp only [Loan.changeImpairment, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold_ter at h
    walk_ok
    all_goals
      have hpool := ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›
      have hl := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
      exact ⟨(Vault.poolAdjust_adjustSums v _ _ hpool).loss, Vault.poolAdjust_deployed_zero v _ _ rfl hpool, hflag,
        (congrArg RawLoan.principalOutstanding hl :)⟩

/-- Impair adds PrincipalOutstanding to LossUnrealized and marks the loan impaired. -/
lemma Loan.manageImpair_lossStep (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) :
    v.lossUnrealized.operator_add loan.principalOutstanding .to_nearest = .ok r.pool'.lossUnrealized ∧
      r.pool'.assetsDeployed = v.assetsDeployed ∧ r.loan'.isImpaired = true ∧
      r.loan'.principalOutstanding = loan.principalOutstanding := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_lossStep loan v true r ‹_›

/-- Unimpair takes PrincipalOutstanding off LossUnrealized and clears the impaired flag. -/
lemma Loan.manageUnimpair_lossStep (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) :
    v.lossUnrealized.operator_add loan.principalOutstanding.operator_neg .to_nearest = .ok r.pool'.lossUnrealized ∧
      r.pool'.assetsDeployed = v.assetsDeployed ∧ r.loan'.isImpaired = false ∧
      r.loan'.principalOutstanding = loan.principalOutstanding :=
  Loan.changeImpairment_lossStep loan v false r h

/-- A default releases an impaired loan's paper loss, never raises AssetsDeployed and leaves PrincipalOutstanding
at zero. The impaired flag stays as it was. -/
lemma Loan.manageDefault_lossStep (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    v.lossUnrealized.operator_add
        (if loan.isImpaired then loan.principalOutstanding.operator_neg else Number.zero) .to_nearest =
        .ok r.pool'.lossUnrealized ∧
      r.pool'.assetsDeployed.toRat ≤ v.assetsDeployed.toRat ∧
      r.loan'.principalOutstanding = Number.zero ∧ r.loan'.isImpaired = loan.isImpaired := by
  obtain ⟨_, _, _, raw, _, -, -, hadj, hraw, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show r.pool'.lossUnrealized = r.pool'.toRawVault.lossUnrealized from rfl, hraw, heq]
    exact hs.loss
  · rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw, heq]
    exact Number.operator_add_le_self v.wf.assetsDeployed_norm
      (Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm)
      (by rw [Number.toRat_neg]; linarith) hs.deployed
  · show r.loan'.toRawLoan.principalOutstanding = _; rw [hloan]; rfl
  · show r.loan'.toRawLoan.isImpaired = _; rw [hloan]; rfl

/-- Impair needs a loan that is not impaired. -/
lemma Loan.canManage_impair_not_impaired (loan : Loan) (now : UInt32)
    (h : loan.canManage .impair now = .ok .tesSUCCESS) :
    loan.isImpaired = false := by
  cases hi : loan.isImpaired
  · rfl
  · unfold Loan.canManage at h
    split at h
    · cases h
    split at h
    · cases h
    rw [if_pos (by simp [hi])] at h
    cases h

/-- Unimpair needs an impaired loan. -/
lemma Loan.canManage_unimpair_impaired (loan : Loan) (now : UInt32)
    (h : loan.canManage .unimpair now = .ok .tesSUCCESS) :
    loan.isImpaired = true := by
  cases hi : loan.isImpaired
  · unfold Loan.canManage at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hd
    rw [if_neg (by simp [hi]), if_pos (by simp [hi, hd])] at h
    cases h
  · rfl

/-- A payment of an impaired loan releases its paper loss. A payment of any other loan keeps
LossUnrealized, and no payment raises AssetsDeployed. -/
lemma Loan.pay_lossStep (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    (loan.isImpaired = true →
        v.lossUnrealized.operator_add loan.principalOutstanding.operator_neg .to_nearest =
          .ok r.pool'.lossUnrealized) ∧
      (loan.isImpaired = false → r.pool'.lossUnrealized = v.lossUnrealized) ∧
      r.pool'.assetsDeployed.toRat ≤ v.assetsDeployed.toRat := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, -, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨-, -, -, -, hpaid⟩ := Loan.payInstalments_below loan v pt amount now p hp
  obtain ⟨_, _, _, _, _, raw, _, -, hadj, hv', -, -, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpool := Vault.poolAdjust_ok _ _ raw r.pool' hadj hv'
  have hLU : r.pool'.lossUnrealized = p.pool.lossUnrealized := Vault.poolAdjust_loss_zero _ _ _ rfl hpool
  have hAD : r.pool'.assetsDeployed.toRat ≤ p.pool.assetsDeployed.toRat :=
    Number.operator_add_le_self p.pool.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpaid.1)
      (by rw [Number.toRat_neg]; linarith [hpaid.2]) (Vault.poolAdjust_adjustSums _ _ _ hpool).deployed
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
    obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
    exact ⟨fun h => absurd h (by simp), fun _ => hLU, hAD⟩
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
    split at hu
    · cases hu
    · cases hu
    · rename_i v1 hadj1
      obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
      refine ⟨fun _ => ?_, fun h => absurd h (by simp), ?_⟩
      · rw [hLU]; exact (Vault.poolAdjust_adjustSums v _ _ hadj1).loss
      · rw [Vault.poolAdjust_deployed_zero v _ _ rfl hadj1] at hAD; exact hAD

/-- A payment leaves the loan not impaired. -/
lemma Loan.pay_isImpaired (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) : r.loan'.isImpaired = false :=
  Loan.payment_unimpaired loan v pt amount now r h

end XRPL.Model.Lending
