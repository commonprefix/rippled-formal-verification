import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.ClosedLoans
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.VaultPrecision
import XRPL.Properties.Lending.Loan.Common.DeleteExits
import XRPL.Properties.Lending.Loan.Common.ManageTotal

/-! # A pending loan can be deleted

On a reachable ledger, LoanDelete of a pending loan succeeds when AssetsAvailable plus its principal fits the
asset. The principal goes back to AssetsAvailable and leaves AssetsDeployed, AssetsReserved and DebtTotal. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Vault.isRounded_false_of_units from XRPL.Properties.Lending.Ledger.Common.VaultPrecision

/-- A stored loan's PrincipalOutstanding is at most the sum over its broker's loans. -/
private lemma LendingLedger.principalOn_le_brokerPrincipal (l : LendingLedger) (i : Nat) {e : LoanEntry}
    (he : l.loan? i = some e) : e.loan.principalOutstanding.toRat ≤ l.brokerPrincipal e.brokerIndex := by
  obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
  have hnn : ∀ x ∈ l.loans.map (LoanEntry.principalOn e.brokerIndex), 0 ≤ x := fun _ hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    exact LoanEntry.principalOn_nonneg _ o
  have := List.single_le_sum hnn _ (List.mem_map_of_mem (f := LoanEntry.principalOn e.brokerIndex)
    (List.getElem_mem hi))
  rw [hei] at this
  simpa [LoanEntry.principalOn] using this

/-- On a reachable ledger the vault update of a pending delete succeeds and passes its re-check, when
AssetsAvailable plus the principal fits the asset. -/
private lemma LendingLedger.pending_delete_vault (l : LendingLedger) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) (hp : e.loan.isPending = true) (loan : Loan)
    (hpo : loan.principalOutstanding = e.loan.principalOutstanding)
    (hnt : loan.broker.numericType = l.vault.numericType) (principal' : Number)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hfit : STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat)) :
    ∃ raw v', (l.vault.adjustBalances (loan.deleteChange principal')).run = .ok (.ok raw) ∧
      raw.to_lawful = .ok v' := by
  have hsc := hr.scaleInv
  have hres := hr.reservedInv
  have hloss := hr.lossInv
  have hdebt := hr.debtInv
  have hbase := Vault.baseExponent_scale_range l.vault
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hb1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hunits : ∀ x : ℚ, x ≤ 10 ^ 16 * 10 ^ l.vault.baseExponent → x < 2 ^ 63 * 10 ^ l.vault.baseExponent ∧
      x < 10 ^ 96 := fun x hx => by
    have h1 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
      mul_lt_mul_of_pos_right (by norm_num) hb10
    have h2 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 := by
      calc (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ 10 ^ 16 * 1 :=
            mul_le_mul_of_nonneg_left hb1 (by norm_num)
        _ = 10 ^ 16 := by ring
    exact ⟨lt_of_le_of_lt hx h1, by linarith [show (10 : ℚ) ^ 16 < 10 ^ 96 by norm_num]⟩
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hpN : loan.principalOutstanding.isNormalized := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat :=
    (loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)
  have hprep : STAmount.Representable l.vault.numericType loan.principalOutstanding.toRat := by
    rw [hpo]; exact hres.exact i e he hp
  have hpR : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false := by
    rw [hnt]; exact (STAmount.isRounded_eq_false_iff _ _ hpN hp0).mpr hprep
  have hp'v := STAmount.roundToNumericType_of_isRounded_false _ _ _ hpN hpR hround
  have hp'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  obtain ⟨mp, hmp⟩ := hsc.principal_grid he
  have hpg : loan.principalOutstanding.toRat = (mp : ℚ) * 10 ^ l.vault.baseExponent := by rw [hpo]; exact hmp
  have hplt := STAmount.Representable.lt_pow _ _ hprep
  have hAAN := l.vault.wf.assetsAvailable_norm
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat :=
    (l.vault.exact.assetsAvailable_nonneg : 0 ≤ l.vault.assetsAvailable.toRat)
  have hAArep : STAmount.Representable l.vault.numericType l.vault.assetsAvailable.toRat :=
    (STAmount.isRounded_eq_false_iff _ _ hAAN hAA0).mp (hr.storesAvailable hmax)
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_lt l.vault.assetsAvailable principal' .to_nearest hAAN hp'N hAA0
    (STAmount.Representable.lt_pow _ _ hAArep) (by rw [hp'v]; exact hp0) (by rw [hp'v]; exact hplt)
  have haav : aa.toRat = l.vault.assetsAvailable.toRat + loan.principalOutstanding.toRat := by
    rw [Number.operator_add_exact_of_fits hAAN hp'N haa
      (by rw [hp'v, hpo]; exact STAmount.Representable.number hfit), hp'v]
  have haaN := operator_add_isNormalized_to_nearest_sz _ _ _ hAAN hp'N haa
  have haa0 : 0 ≤ aa.toRat := by rw [haav]; linarith
  have haaR : STAmount.isRounded l.vault.numericType aa = false :=
    (STAmount.isRounded_eq_false_iff _ _ haaN haa0).mpr (by rw [haav, hpo]; exact hfit)
  obtain ⟨aa', haa'⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ haaR
  have haa'v := STAmount.roundToNumericType_of_isRounded_false _ _ _ haaN haaR haa'
  have hADN := l.vault.wf.assetsDeployed_norm
  have hADs : l.vault.assetsDeployed.toRat = l.principalSum (fun _ => true) := hdebt.deployed
  obtain ⟨nd, hnd⟩ := hsc.principalSum_grid (fun _ => true)
  have hPOle : loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
    have := l.principalIf_le_sum (fun _ => true) i
    rw [he] at this
    simp only [LoanEntry.principalIf, if_true] at this
    rw [hADs, hpo]; exact this
  have hADlt := hunits _ hloss.deployed
  obtain ⟨ad', had'⟩ := Number.operator_add_ok_of_small l.vault.assetsDeployed loan.principalOutstanding.operator_neg
    .to_nearest hADN (Number.operator_neg_isNormalized _ hpN)
    ((l.vault.exact.assetsDeployed_nonneg : 0 ≤ l.vault.assetsDeployed.toRat)) hADlt.2
    (by rw [Number.toRat_neg, abs_neg, abs_of_nonneg hp0]; exact hplt)
  have had'v : ad'.toRat = l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat :=
    Number.operator_add_neg_toRat_of_grid _ _ _ _ hADN hpN ⟨nd, by rw [hADs, hnd]⟩ ⟨mp, hpg⟩ hPOle hADlt.1 hsb had'
  have hARN := l.vault.wf.assetsReserved_norm
  obtain ⟨nr, hnr⟩ := hres.grid
  have hPOar : loan.principalOutstanding.toRat ≤ l.vault.assetsReserved.toRat := by
    have := l.principalIf_le_sum (·.isPending) i
    rw [he] at this
    simp only [LoanEntry.principalIf, hp, if_true] at this
    rw [hres.sum, hpo]; exact this
  have hARlt := hunits _ hres.bound
  obtain ⟨ar', har'⟩ := Number.operator_add_ok_of_small l.vault.assetsReserved principal'.operator_neg .to_nearest
    hARN (Number.operator_neg_isNormalized _ hp'N)
    ((l.vault.exact.assetsReserved_nonneg : 0 ≤ l.vault.assetsReserved.toRat)) hARlt.2
    (by rw [Number.toRat_neg, abs_neg, hp'v, abs_of_nonneg hp0]; exact hplt)
  have har'v : ar'.toRat = l.vault.assetsReserved.toRat - loan.principalOutstanding.toRat := by
    rw [Number.operator_add_neg_toRat_of_grid _ _ _ _ hARN hp'N ⟨nr, hnr⟩ ⟨mp, by rw [hp'v, hpg]⟩
      (by rw [hp'v]; exact hPOar) hARlt.1 hsb har', hp'v]
  have hs : Vault.AdjustSums l.vault (loan.deleteChange principal') aa' ad' l.vault.lossUnrealized ar'
      l.vault.yieldUnrealized :=
    ⟨⟨aa, haa, haa'⟩, had', Number.operator_add_zero_right _ _, har', Number.operator_add_zero_right _ _⟩
  have hLU0 : 0 ≤ l.vault.lossUnrealized.toRat := l.vault.exact.lossUnrealized_nonneg
  have hYU0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
  have had'N := operator_add_isNormalized_to_nearest_sz _ _ _ hADN (Number.operator_neg_isNormalized _ hpN) had'
  have har'N := operator_add_isNormalized_to_nearest_sz _ _ _ hARN (Number.operator_neg_isNormalized _ hp'N) har'
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa'
  have hT81 := LendingLedger.loss_reserved_deployed_proof l hr
  have hadj := Vault.adjustBalances_ok l.vault _ _ _ _ _ _ hs
    ⟨Number.signum_nonneg_of_toRat _ haa'N (by rw [haa'v]; exact haa0),
      Number.signum_nonneg_of_toRat _ had'N (by rw [had'v]; linarith),
      Number.signum_nonneg_of_toRat _ l.vault.wf.lossUnrealized_norm hLU0,
      Number.signum_nonneg_of_toRat _ l.vault.wf.yieldUnrealized_norm hYU0,
      Number.signum_nonneg_of_toRat _ har'N (by rw [har'v]; linarith)⟩
    (by
      cases hgt : l.vault.lossUnrealized.operator_gt ad'
      · rfl
      · have := (operator_gt_iff _ _ l.vault.wf.lossUnrealized_norm had'N).mp hgt
        rw [had'v] at this
        linarith)
  have hadrep : STAmount.Representable l.vault.numericType
      (l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat) := by
    rw [← had'v]
    refine (STAmount.isRounded_eq_false_iff _ _ had'N (by rw [had'v]; linarith)).mp ?_
    refine Vault.isRounded_false_of_units l.vault ad' had'N (by rw [had'v]; linarith) ?_ ?_ ?_
    · refine ⟨nd - mp, ?_⟩
      have hle : (mp : ℚ) ≤ nd := by
        have : (mp : ℚ) * 10 ^ l.vault.baseExponent ≤ (nd : ℚ) * 10 ^ l.vault.baseExponent := by
          rw [← hpg, ← hnd, ← hADs]; exact hPOle
        exact le_of_mul_le_mul_right this hb10
      have hle' : mp ≤ nd := by exact_mod_cast hle
      rw [had'v, hADs, hnd, hpg]; push_cast [hle']; ring
    · rw [had'v]; have := hloss.deployed; linarith
    · rw [had'v]; linarith
  obtain ⟨v', hv', -⟩ := Loan.delete_vault_lawful loan l.vault principal' _ hround hadj hpR hadrep
    hr.holdsAsset.maxValue_le ⟨hpN, mp, by rw [hpg]; push_cast; ring⟩
  exact ⟨_, v', hadj, hv'⟩

/-- A pending loan can be deleted now when its principal fits beside AssetsAvailable. -/
lemma LendingLedger.pending_resolvable_proof (l : LendingLedger) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hnd : l.vaultDeleted = false) (i : Nat) (e : LoanEntry) (he : l.loan? i = some e)
    (hp : e.loan.isPending = true)
    (hfit : STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat)) :
    ∃ l', (l.apply (.loanDelete i)).run = .ok (.ok l') := by
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  have hs := hr.scaleInv
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (by rw [hs.brokers _ b hb, hs.loanBroker i e he])
  have hraw := Loan.withBroker_eq hw
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hp' : loan.isPending = true := by rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw]; exact hp
  have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hnt : loan.broker.numericType = l.vault.numericType := by rw [hlb]; exact hs.brokers _ b hb
  have hc : loan.canDelete = .tesSUCCESS := by unfold Loan.canDelete; simp [hp']
  have hpN : loan.principalOutstanding.isNormalized := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat :=
    (loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)
  have hpR : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false := by
    rw [hnt]
    exact (STAmount.isRounded_eq_false_iff _ _ hpN hp0).mpr (by rw [hpo]; exact hr.reservedInv.exact i e he hp)
  obtain ⟨principal', hround⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ hpR
  obtain ⟨raw, v', hadj, hv'⟩ := l.pending_delete_vault hr hmax i e he hp loan hpo hnt principal' hround hfit
  have hdebt := hr.debtInv
  have hDT : b.debtTotal.toRat = l.brokerPrincipal e.brokerIndex := hdebt.debt _ b hb
  have hPOle : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat := by
    rw [hlb, hDT, hpo]; exact l.principalOn_le_brokerPrincipal i he
  have hDTlt : loan.broker.debtTotal.toRat < 10 ^ 96 := by
    have h1 := l.brokerPrincipal_le e.brokerIndex
    have h2 := hr.lossInv.deployed
    have hb1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (Vault.baseExponent_scale_range l.vault).2
    rw [hlb, hDT]
    rw [hdebt.deployed] at h2
    nlinarith
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_lt loan.broker.debtTotal loan.principalOutstanding .to_nearest
    loan.broker.wf.debtTotal_norm hpN (le_trans hp0 hPOle) hDTlt hp0 (lt_of_le_of_lt hPOle hDTlt)
  obtain ⟨broker', hbroker⟩ := Loan.delete_broker_lawful loan d hd (Or.inr hPOle)
  have hdel := Loan.delete_success_proof loan l.vault principal' d raw v' broker' hp' hround hadj hv' hd hbroker
  let u : LoanEffect := { vault := v', brokerIndex := e.brokerIndex, broker := broker', loanIndex := i, loan := none }
  refine ⟨l.commitLoan u, ?_⟩
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  simp only [ExceptT.run] at hdel
  rw [hc, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdel]
  rfl

end XRPL.Model.Lending
