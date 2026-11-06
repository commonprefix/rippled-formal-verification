import XRPL.Properties.Lending.Loan.Common.DeleteExits
import XRPL.Properties.Lending.Loan.Common.AcceptProofs

/-! # Proof bodies for the `Loan.delete` properties

What a delete moves between the vault and the broker, and a pending create then delete. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Number.toRat_nonneg_of_le from XRPL.Properties.Lending.Loan.Common.AcceptExits
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs

/-- A broker that released a loan holds one loan less, and DebtTotal is the given amount, or zero
once no loan is left. -/
private lemma LoanBroker.releaseLoan_ok_inv (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.loanCount = lb.loanCount - 1 ∧ lb'.debtTotal = if lb.loanCount - 1 == 0 then Number.zero else d := by
  unfold LoanBroker.releaseLoan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i _ hc
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
  have h' := (RawLoanBroker.to_lawful_ok h).1
  exact ⟨congrArg RawLoanBroker.loanCount h', congrArg RawLoanBroker.debtTotal h'⟩

/-- One loan less is none exactly for the broker's last loan. -/
private lemma loanCount_sub_one_eq_zero (n : UInt32) : n - 1 = 0 ↔ n = 1 := by
  constructor
  · intro h
    have := congrArg (· + 1) h
    simpa using this
  · rintro rfl; rfl

variable (loan : Loan) (v : Vault)

/-- A pending delete moves exactly PrincipalOutstanding when the asset stores it and each new balance exactly, and
a last loan carries all of DebtTotal. `deletePending_principal_attained` shows the AssetsAvailable fit is needed. -/
lemma Loan.deletePending_principal_of_exact (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = true) (hok : (loan.delete v).run = .ok (.ok r))
    (hpo : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false)
    (haa : STAmount.Representable v.numericType (v.assetsAvailable.toRat + loan.principalOutstanding.toRat))
    (har : STAmount.Representable v.numericType (v.assetsReserved.toRat - loan.principalOutstanding.toRat))
    (had : STAmount.Representable v.numericType (v.assetsDeployed.toRat - loan.principalOutstanding.toRat))
    (hdt : STAmount.Representable loan.broker.numericType
      (loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat))
    (hlast : loan.broker.loanCount = 1 → loan.broker.debtTotal.toRat = loan.principalOutstanding.toRat) :
    r.pool'.assetsAvailable.toRat - v.assetsAvailable.toRat = loan.principalOutstanding.toRat ∧
      v.assetsReserved.toRat - r.pool'.assetsReserved.toRat = loan.principalOutstanding.toRat ∧
      v.assetsDeployed.toRat - r.pool'.assetsDeployed.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.toRat - r.broker'.debtTotal.toRat = loan.principalOutstanding.toRat := by
  obtain ⟨principal', raw, debtTotal', hround, hadj, hv', hdebt, hb⟩ :=
    Loan.delete_pending_ok_inv loan v r hp hok
  have hraw := (RawVault.to_lawful_ok hv').1
  obtain ⟨hcount, hdt'⟩ := LoanBroker.releaseLoan_ok_inv _ _ _ hb
  obtain ⟨aa', ad', lu', ar', yu', hs, -, -, hrawEq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  obtain ⟨aa, h1, h2⟩ := hs.cash
  have hd := hs.deployed
  have hr := hs.reserved
  simp only [Loan.deleteChange] at h1 hd hr
  have hpn := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hneg := Number.operator_neg_isNormalized _ hpn

  -- the asset stores the principal exactly, so the rounded principal is the principal
  have hp' : principal' = loan.principalOutstanding :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround) hpn
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ hpn hpo hround)
  subst hp'

  -- AssetsAvailable: the sum is exact, and the asset stores it, so the rounding keeps it
  have haan : aa.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hpn h1
  have haav : aa.toRat = v.assetsAvailable.toRat + loan.principalOutstanding.toRat :=
    Number.operator_add_exact_of_fits v.wf.assetsAvailable_norm hpn h1 (STAmount.Representable.number haa)
  have haa0 : 0 ≤ aa.toRat := by
    rw [haav]; linarith [(show 0 ≤ v.assetsAvailable.toRat from v.exact.assetsAvailable_nonneg)]
  have haa' : aa'.toRat = aa.toRat := STAmount.roundToNumericType_of_isRounded_false _ _ _ haan
    ((STAmount.isRounded_eq_false_iff _ _ haan haa0).mpr (by rw [haav]; exact haa)) h2

  have harv : ar'.toRat = v.assetsReserved.toRat - loan.principalOutstanding.toRat := by
    have h := Number.operator_add_exact_of_fits v.wf.assetsReserved_norm hneg hr
      (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number har)
    rw [h, Number.toRat_neg, ← sub_eq_add_neg]
  have hadv : ad'.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat := by
    have h := Number.operator_add_exact_of_fits v.wf.assetsDeployed_norm hneg hd
      (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number had)
    rw [h, Number.toRat_neg, ← sub_eq_add_neg]

  -- DebtTotal: the exact difference, or zero for the broker's last loan, which carries all the debt
  have hdtv : loan.broker.debtTotal.toRat - r.broker'.debtTotal.toRat = loan.principalOutstanding.toRat := by
    rw [hdt']
    by_cases hc : loan.broker.loanCount - 1 = 0
    · rw [if_pos (by rw [hc]; rfl), Number.toRat_zero, sub_zero]
      exact hlast ((loanCount_sub_one_eq_zero _).mp hc)
    · rw [if_neg (by simpa using hc)]
      have h := Number.operator_add_exact_of_fits loan.broker.wf.debtTotal_norm hneg hdebt
        (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number hdt)
      rw [h, Number.toRat_neg]; ring

  rw [hraw, hrawEq]
  refine ⟨?_, ?_, ?_, hdtv⟩
  · show aa'.toRat - _ = _
    rw [haa', haav]; ring
  · show _ - ar'.toRat = _
    rw [harv]; ring
  · show _ - ad'.toRat = _
    rw [hadv]; ring

/-- Proof body of the last loan part of `Lending.deleteActive_settled`. -/
lemma Loan.deleteActive_last_proof (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = false) (hclosed : loan.paymentRemaining = 0) (hlast : loan.broker.loanCount = 1)
    (hdebt : loan.broker.debtTotal.toRat = loan.principalOutstanding.toRat)
    (hok : (loan.delete v).run = .ok (.ok r)) :
    loan.broker.debtTotal = Number.zero ∧ r.broker'.debtTotal = loan.broker.debtTotal := by
  -- a closed loan carries no principal, so the last loan leaves no debt
  have hP : loan.principalOutstanding.toRat = 0 := (loan.exact.paid_zeroed hclosed).2.1
  have hD : loan.broker.debtTotal = Number.zero := by
    apply (Number.toRat_eq_zero_iff_eq_zero loan.broker.wf.debtTotal_norm).mp
    rw [hdebt, hP]
  refine ⟨hD, ?_⟩
  have hbv := Loan.deleteActive_raw _ _ (Loan.delete_active_ok_inv loan v r hp hok).1
  have h := congrArg RawLoanBroker.debtTotal hbv
  simp only [hlast] at h
  rw [hD]
  exact h

variable (broker : LoanBroker) (principal : Number) (rates : LoanRates) (fees : LoanFees)
  (schedule : LoanSchedule) (allowsOverpayment : Bool)

/-- Proof body of `createPending_deletePending_restores`. -/
lemma Loan.createPending_deletePending_restores_proof (r : LoanWithPool Vault) (r' : LoanBrokerWithPool Vault)
    (hpn : principal.isNormalized) (hp0 : 0 ≤ principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (haa' : STAmount.Representable v.numericType (v.assetsAvailable.toRat - principal.toRat))
    (har : STAmount.Representable v.numericType (v.assetsReserved.toRat + principal.toRat))
    (hdt : STAmount.Representable broker.numericType (broker.debtTotal.toRat + principal.toRat))
    (hcreate : (Loan.create broker v principal rates fees schedule allowsOverpayment true).run = .ok (.ok r))
    (hdelete : (r.loan'.delete r.pool').run = .ok (.ok r')) :
    r'.pool'.assetsAvailable = v.assetsAvailable ∧ r'.pool'.assetsReserved = v.assetsReserved ∧
      r'.broker'.debtTotal = broker.debtTotal ∧ r'.broker'.loanCount = broker.loanCount := by
  obtain ⟨props, loanState, debtTotal', principal', broker', hchecks, hround, hpool, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment true r hcreate
  have hPO := Loan.create_principalOutstanding broker v principal rates fees schedule allowsOverpayment true r
    hpn hp0 hst hcreate
  have hp' : principal' = principal :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround) hpn
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ hpn hst hround)
  subst hp'
  have hl := (RawLoan.to_lawful_ok hloan).1
  have hb := (RawLoanBroker.to_lawful_ok hbroker).1
  have hbr : r.loan'.broker = broker' := (congrArg RawLoan.broker hl :)
  have hpend : r.loan'.isPending = true := (congrArg RawLoan.isPending hl :)
  obtain ⟨principal'', rawD, debtTotal'', hround'', hadjD, hvD, hdebtD, hbD⟩ :=
    Loan.delete_pending_ok_inv r.loan' r.pool' r' hpend hdelete
  rw [hbr, hPO] at hround''
  rw [hbr, hPO] at hdebtD
  rw [hbr] at hbD
  have hnt : broker'.numericType = broker.numericType := (congrArg RawLoanBroker.numericType hb :)
  rw [hnt] at hround''
  rw [hround, Except.ok.injEq] at hround''
  subst hround''
  have hneg := Number.operator_neg_isNormalized _ hpn

  obtain ⟨rawP, hadjP, hvP⟩ := Vault.poolAdjust_ok_inv v _ r.pool' hpool
  obtain ⟨aaP, adP, luP, arP, yuP, hsP, -, -, hrawPeq⟩ := Vault.adjustBalances_ok_parts v _ rawP hadjP
  have hpf := (RawVault.to_lawful_ok hvP).1.trans hrawPeq
  obtain ⟨aaD, adD, luD, arD, yuD, hsD, -, -, hrawDeq⟩ := Vault.adjustBalances_ok_parts r.pool' _ rawD hadjD
  have hdf := (RawVault.to_lawful_ok hvD).1.trans hrawDeq
  obtain ⟨aa, h1P, h2P⟩ := hsP.cash
  have hrP := hsP.reserved
  obtain ⟨aa', h1D, h2D⟩ := hsD.cash
  have hrD := hsD.reserved
  simp only [Loan.createChange, Loan.deleteChange, if_true] at h1P hrP h1D hrD
  rw [show r.pool'.assetsAvailable = aaP from (congrArg RawVault.assetsAvailable hpf :)] at h1D
  rw [show r.pool'.assetsReserved = arP from (congrArg RawVault.assetsReserved hpf :)] at hrD
  rw [show r.pool'.numericType = v.numericType from (congrArg RawVault.numericType hpf :)] at h2D

  -- AssetsAvailable: the create's debit is exact and stored, and the delete's credit undoes it
  have haan : aa.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hneg h1P
  have haav : aa.toRat = v.assetsAvailable.toRat - principal'.toRat := by
    have h := Number.operator_add_exact_of_fits v.wf.assetsAvailable_norm hneg h1P
      (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number haa')
    rw [h, Number.toRat_neg, ← sub_eq_add_neg]
  have haa0 : 0 ≤ aa.toRat := by
    have hle := (operator_lt_eq_false_iff _ _ v.wf.assetsAvailable_norm hpn).mp hchecks.funds
    rw [haav]; linarith
  have haaP : aaP.toRat = aa.toRat := STAmount.roundToNumericType_of_isRounded_false _ _ _ haan
    ((STAmount.isRounded_eq_false_iff _ _ haan haa0).mpr (by rw [haav]; exact haa')) h2P
  have haaPn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2P
  have haa' : aa' = v.assetsAvailable := by
    have h := Number.operator_add_exact_of_fits haaPn hpn h1D
      ⟨v.assetsAvailable, v.wf.assetsAvailable_norm, by rw [haaP, haav]; ring⟩
    exact Number.isNormalized.toRat_inj (operator_add_isNormalized_to_nearest_sz _ _ _ haaPn hpn h1D)
      v.wf.assetsAvailable_norm (by rw [h, haaP, haav]; ring)
  subst haa'
  have haaD : aaD = v.assetsAvailable :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2D) v.wf.assetsAvailable_norm
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm haa h2D)

  have harPn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsReserved_norm hpn hrP
  have harPv := Number.operator_add_exact_of_fits v.wf.assetsReserved_norm hpn hrP
    (STAmount.Representable.number har)
  have harD : arD = v.assetsReserved := by
    have h := Number.operator_add_exact_of_fits harPn hneg hrD
      ⟨v.assetsReserved, v.wf.assetsReserved_norm, by rw [harPv, Number.toRat_neg]; ring⟩
    exact Number.isNormalized.toRat_inj (operator_add_isNormalized_to_nearest_sz _ _ _ harPn hneg hrD)
      v.wf.assetsReserved_norm (by rw [h, harPv, Number.toRat_neg]; ring)

  have hdtb : broker'.debtTotal = debtTotal' := (congrArg RawLoanBroker.debtTotal hb :)
  have hlcb : broker'.loanCount = broker.loanCount + 1 := (congrArg RawLoanBroker.loanCount hb :)
  rw [hdtb] at hdebtD
  have hdn := broker.wf.debtTotal_norm
  have hdt'n := operator_add_isNormalized_to_nearest_sz _ _ _ hdn hpn hchecks.debt
  have hdt'v := Number.operator_add_exact_of_fits hdn hpn hchecks.debt (STAmount.Representable.number hdt)
  have hdt'' : debtTotal'' = broker.debtTotal := by
    have h := Number.operator_add_exact_of_fits hdt'n hneg hdebtD
      ⟨broker.debtTotal, hdn, by rw [hdt'v, Number.toRat_neg]; ring⟩
    exact Number.isNormalized.toRat_inj (operator_sub_isNormalized_to_nearest_sz _ _ _ hdt'n hpn hdebtD) hdn
      (by rw [h, hdt'v, Number.toRat_neg]; ring)
  obtain ⟨hcount, hdebt'⟩ := LoanBroker.releaseLoan_ok_inv _ _ _ hbD
  have hlc : broker'.loanCount - 1 = broker.loanCount := by rw [hlcb]; simp

  refine ⟨?_, ?_, ?_, by rw [hcount, hlc]⟩
  · rw [show r'.pool'.assetsAvailable = aaD from (congrArg RawVault.assetsAvailable hdf :), haaD]
  · rw [show r'.pool'.assetsReserved = arD from (congrArg RawVault.assetsReserved hdf :), harD]
  · rw [hdebt', hlc, hdt'']
    by_cases h0 : broker.loanCount = 0
    · rw [if_pos (by rw [h0]; rfl)]
      have h : broker.debtTotal.toRat = 0 := broker.exact.empty_broker (by
        show broker.loanCount.toNat = 0; rw [h0]; rfl)
      exact ((Number.toRat_eq_zero_iff_eq_zero broker.wf.debtTotal_norm).mp h).symm
    · rw [if_neg (by simpa using h0)]

end XRPL.Model.Lending
