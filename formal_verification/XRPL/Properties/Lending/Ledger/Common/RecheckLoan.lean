import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Lending.Ledger.Common.RecheckPool
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Loan.Common.ManageDefs
import XRPL.Properties.Lending.Loan.Common.ManageCover
import XRPL.Properties.Lending.Loan.Common.AcceptExits
import XRPL.Properties.Lending.Ledger.Common.PendingDelete
import XRPL.Properties.Lending.Ledger.Common.LoansInv

/-! # Loan transactions pass their lawfulness re-check

LoanAccept, LoanDelete and LoanManage on a reachable ledger never fail the model with `notLawful`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.accept_reduce from XRPL.Properties.Lending.Loan.Common.AcceptExits
open private Vault.isRounded_false_of_units from XRPL.Properties.Lending.Ledger.Common.VaultPrecision
open private LendingLedger.principalSum_add_le_all from XRPL.Properties.Lending.Ledger.Common.ManageTotal
open private Loan.delete_pending_reduce from XRPL.Properties.Lending.Loan.Common.DeleteExits

/-- A vault record with no shares has a zero share count in its exact reading. -/
private lemma Vault.toExact_sharesTotal_zero (v : Vault) (h : v.sharesTotal = Number.zero) :
    v.toExact.sharesTotal = 0 := by
  show v.sharesTotal.toRat.num.toNat = 0
  rw [h, Number.toRat_zero]; rfl

/-- A balance update that moves no cash and nothing deployed passes the vault re-check, when the asset
stores AssetsAvailable exactly and the reserve can only shrink. Impair, unimpair and accept are such updates. -/
lemma Vault.poolAdjust_frame_ne_notLawful (v : Vault) (c : PoolBalanceChange) (hc : c.Normalized)
    (hcash : c.cash = Number.zero) (hdep : c.deployed = Number.zero)
    (hres : ∀ ar', v.assetsReserved.operator_add c.reserved .to_nearest = .ok ar' →
      ar'.toRat ≤ v.assetsReserved.toRat)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    AssetPool.adjustBalances v c ≠ .error .notLawful := by
  refine Vault.poolAdjust_ne_notLawful v c hc fun raw hadj => ?_
  obtain ⟨aa', ad', lu', ar', yu', hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts v c raw hadj
  have hex := v.exact
  obtain ⟨aa, haa1, haa2⟩ := hs.cash
  rw [hcash] at haa1
  have haaeq := Number.eq_of_add_zero haa1
  subst haaeq
  have hd := hs.deployed
  rw [hdep] at hd
  have hadeq := Number.eq_of_add_zero hd
  subst hadeq
  have haa' := STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm haa haa2
  refine ⟨hex.assetsDeployed_representable, le_trans (hres ar' hs.reserved) hex.assetsReserved_le, fun h0 => ?_,
    (Vault.round_cash_valid v _ haa2).1, (Vault.round_cash_valid v _ haa2).2⟩
  obtain ⟨h1, h2⟩ := hex.empty_shares (Vault.toExact_sharesTotal_zero v h0)
  exact ⟨by rw [haa']; exact h1, h2⟩

/-- An update with no reserve change keeps AssetsReserved. -/
private lemma reserved_zero_le (v : Vault) (ar' : Number)
    (h : v.assetsReserved.operator_add Number.zero .to_nearest = .ok ar') : ar'.toRat ≤ v.assetsReserved.toRat := by
  rw [Number.eq_of_add_zero h]

/-- An impair never fails its re-checks when the asset stores AssetsAvailable exactly. -/
lemma Loan.manageImpair_ne_notLawful (loan : Loan) (v : Vault) (now : UInt32)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    (loan.manageImpair v now).run ≠ .error .notLawful := by
  intro h
  by_cases hlate : loan.nextPaymentDueDate < now
  · rw [Loan.manageImpair_run loan v now hlate] at h
    have hvault := Vault.poolAdjust_frame_ne_notLawful v { loss := loan.principalOutstanding }
      ⟨Number.zero_isNormalized, loan.wf.principalOutstanding_norm, Number.zero_isNormalized,
        Number.zero_isNormalized⟩ rfl rfl (reserved_zero_le v) haa
    obtain ⟨loan', hl', -⟩ := Loan.withImpaired_lawful loan true
    split at h
    · rename_i e he
      cases h
      exact hvault he
    · cases h
    · simp only [Loan.withImpaired, hl'] at h
      cases h
  · have hl : loan.isPaymentLate now = false := by
      unfold Loan.isPaymentLate; exact decide_eq_false hlate
    simp only [Loan.manageImpair, hl] at h
    unfold_ter at h
    simp at h

/-- An unimpair never fails its re-checks when the asset stores AssetsAvailable exactly. -/
lemma Loan.manageUnimpair_ne_notLawful (loan : Loan) (v : Vault)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    (loan.manageUnimpair v).run ≠ .error .notLawful := by
  intro h
  rw [Loan.manageUnimpair_run loan v] at h
  have hvault := Vault.poolAdjust_frame_ne_notLawful v { loss := loan.principalOutstanding.operator_neg }
    ⟨Number.zero_isNormalized, Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm,
      Number.zero_isNormalized, Number.zero_isNormalized⟩ rfl rfl (reserved_zero_le v) haa
  obtain ⟨loan', hl', -⟩ := Loan.withImpaired_lawful loan false
  split at h
  · rename_i e he
    cases h
    exact hvault he
  · cases h
  · simp only [Loan.withImpaired, hl'] at h
    cases h

/-- A balance change that passes the vault update passes the vault re-check when every update the change could
compute writes a lawful vault. -/
private lemma Vault.poolAdjust_ne_notLawful_of_lawful (v : Vault) (c : PoolBalanceChange)
    (h : ∀ raw, (v.adjustBalances c).run = .ok (.ok raw) → ∃ v', raw.to_lawful = .ok v') :
    AssetPool.adjustBalances v c ≠ .error .notLawful := by
  rw [Vault.pool_adjustBalances]
  intro he
  unfold_ter at he
  walk_ok
  · exact Vault.adjustBalances_ne_notLawful v c (by simp only [ExceptT.run]; assumption)
  · rename_i hlaw
    obtain ⟨v', hv'⟩ := h _ ‹v.adjustBalances c = .ok (.ok _)›
    rw [hv'] at hlaw
    cases hlaw

/-- An accept never fails its re-checks. The loan only loses its pending flag, and the vault keeps
AssetsDeployed and LossUnrealized while AssetsReserved falls. -/
lemma Loan.accept_ne_notLawful (loan : Loan) (v : Vault) : (loan.accept v).run ≠ .error .notLawful := by
  intro h
  cases hi : loan.interestDue with
  | error e =>
    have : (loan.accept v).run = .error e := by
      simp only [Loan.accept]
      unfold_ter
      simp [hi]
    rw [this] at h
    cases h
    exact RawLoan.interestDue_ne_notLawful _ hi
  | ok interestDue =>
    rw [Loan.accept_reduce loan v interestDue hi] at h
    have hvault := Vault.poolAdjust_ne_notLawful_of_lawful v (loan.acceptChange interestDue) fun raw hadj => by
      obtain ⟨v', hv', -⟩ := Loan.accept_vault_lawful loan v interestDue raw hi hadj
      exact ⟨v', hv'⟩
    obtain ⟨loan', hl', -⟩ := Loan.accept_loan_lawful loan
    split at h
    · rename_i e he
      cases h
      exact hvault he
    · cases h
    · simp only [hl'] at h
      cases h

lemma Loan.defaultCover_ne_notLawful (loan : Loan) (v : Vault) : loan.defaultCover v ≠ .error .notLawful := by
  unfold Loan.defaultCover
  simp only [bind, Except.bind]
  split_ne_notLawful [tenthBipsOfValue_ne_notLawful, STAmount.roundToNumericType_ne_notLawful,
    sumRoundAndSubtract_ne_notLawful, STAmount.toNumber_ne_notLawful]

/-- A floored credit of nothing onto an empty balance is nothing. -/
private lemma sumRoundAndSubtract_zero_zero (b : Int) (nt : NumericType) (st : STAmount)
    (h : sumRoundAndSubtract Number.zero Number.zero b nt .downward = .ok st) : st.toRat = 0 := by
  unfold sumRoundAndSubtract at h
  split at h
  · cases nt with
    | fractional => simp [NumericType.isIntegral] at *
    | integral mv mo ms msh =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      have h1 : STAmount.ofNumber (.integral mv mo ms msh) Number.zero .downward =
          .ok ⟨.integral mv mo ms msh, 0, 0, false⟩ := rfl
      rw [h1] at h
      cases h
      rfl
  · have hfr : nt = .fractional := by cases nt <;> simp_all [NumericType.isIntegral]
    subst hfr
    dsimp only at h
    rw [pure_bind] at h
    obtain ⟨e, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
    rw [Number.operator_add_zero_right, Except.ok.injEq] at hsum
    subst hsum
    obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
    have h3 : STAmount.roundToNumericType .fractional Number.zero .downward (some e) = .ok Number.zero := by
      have h2 : (⟨.fractional, 0, -100, false⟩ : STAmount).toNumber .downward = .ok Number.zero :=
        STAmount.toNumber_zero_fractional _ _ rfl rfl
      simp [STAmount.roundToNumericType, STAmount.ofNumber_fractional_zero, STAmount.roundToExponent,
        STAmount.integral, STAmount.isZero, NumericType.isIntegral, h2]
    rw [h3, Except.ok.injEq] at hsum'
    subst hsum'
    obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
    rw [Number.operator_sub_zero, Except.ok.injEq] at hd
    subst hd
    rw [STAmount.ofNumber_fractional_zero, Except.ok.injEq] at h
    rw [← h]
    unfold STAmount.toRat
    rw [if_pos rfl]

/-- The cover a default of a loan without principal pays an empty vault is zero. -/
private lemma Loan.defaultCover_zero (loan : Loan) (v : Vault) (dc : Number) (h : loan.defaultCover v = .ok dc)
    (hpo : loan.principalOutstanding.toRat = 0) (haa : v.assetsAvailable.toRat = 0) : dc = Number.zero := by
  obtain ⟨mc, liq, c, st, hmc, hliq, hc, hst, hdc⟩ := Loan.defaultCover_parts loan v dc h
  have hb := loan.broker.exact
  obtain ⟨hmcn, hmc0⟩ := tenthBipsOfValue_upward_facts _ _ _ loan.broker.wf.debtTotal_norm hb.debtTotal_nonneg hmc
  obtain ⟨hliqn, hliq0⟩ := tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq
  obtain ⟨hm1, hm1n⟩ := Number.min_toRat _ _ hliqn loan.wf.principalOutstanding_norm
  obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ _ hm1n loan.broker.wf.coverAvailable_norm
  have hcap : (Number.min (Number.min liq loan.principalOutstanding) loan.broker.coverAvailable).toRat = 0 := by
    rw [hm2, hm1, hpo]
    have hca : (0 : ℚ) ≤ loan.broker.coverAvailable.toRat := hb.coverAvailable_nonneg
    rw [min_eq_right hliq0, min_eq_left hca]
  obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n (le_of_eq hcap.symm) hc
  have hcz : c = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hcn).mp (by linarith)
  have hAz : v.assetsAvailable = Number.zero := (Number.toRat_eq_zero_iff_eq_zero v.wf.assetsAvailable_norm).mp haa
  rw [hcz, hAz] at hst
  have hst0 := sumRoundAndSubtract_zero_zero _ _ _ hst
  obtain ⟨-, hex⟩ := sumRoundAndSubtract_downward_le _ _ _ _ _ Number.zero_isNormalized
    (by rw [Number.toRat_zero]) Number.zero_isNormalized (by rw [Number.toRat_zero]) (Vault.baseExponent_range v) hst
  obtain ⟨hv, hn⟩ := hex dc hdc
  exact (Number.toRat_eq_zero_iff_eq_zero hn).mp (by rw [hv, hst0])

/-- A to-nearest difference of a value at most the balance stays between zero and the balance. -/
private lemma Number.operator_sub_between (x y d : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hy0 : 0 ≤ y.toRat) (hyx : y.toRat ≤ x.toRat) (h : x.operator_sub y .to_nearest = .ok d) :
    0 ≤ d.toRat ∧ d.toRat ≤ x.toRat ∧ d.isNormalized := by
  have hneg := Number.operator_neg_isNormalized _ hy
  have h' : x.operator_add y.operator_neg .to_nearest = .ok d := h
  refine ⟨operator_add_nonneg _ _ _ hx hneg h' (by rw [Number.toRat_neg]; linarith),
    operator_add_le_of_le_normalized _ _ _ _ hx hneg h' hx (by rw [Number.toRat_neg]; linarith),
    operator_sub_isNormalized_to_nearest_sz _ _ _ hx hy h⟩

/-- The broker a default writes is lawful: DebtTotal loses a principal it holds, and CoverAvailable a cover
no larger than itself. -/
private lemma Loan.defaultedBroker_lawful (loan : Loan) (dc dt' ca' : Number) (hdcn : dc.isNormalized)
    (hdc : dc.toRat ≤ loan.broker.coverAvailable.toRat)
    (hpo : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat)
    (hdt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok dt')
    (hca : loan.broker.coverAvailable.operator_sub dc .to_nearest = .ok ca') :
    ∃ b, (loan.defaultedBroker dt' ca').to_lawful = .ok b := by
  have hb := loan.broker.exact
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨hdt0, hdtle, hdtn⟩ := Number.operator_sub_between _ _ _ loan.broker.wf.debtTotal_norm
    loan.wf.principalOutstanding_norm hp0 hpo hdt
  have hcan := operator_sub_isNormalized_to_nearest_sz _ _ _ loan.broker.wf.coverAvailable_norm hdcn hca
  have hca0 : 0 ≤ ca'.toRat := operator_add_nonneg _ _ _ loan.broker.wf.coverAvailable_norm
    (Number.operator_neg_isNormalized _ hdcn) hca (by rw [Number.toRat_neg]; linarith)
  have hwf : (loan.defaultedBroker dt' ca').WF := ⟨hdtn, loan.broker.wf.debtMaximum_norm, hcan⟩
  have hex : (loan.defaultedBroker dt' ca').toExact.Valid :=
    { hb with
      debtTotal_nonneg := hdt0
      coverAvailable_nonneg := hca0
      debt_within_cap := fun hm => le_trans hdtle (hb.debt_within_cap hm)
      empty_broker := fun h0 => by
        have hdt00 : loan.broker.debtTotal.toRat = 0 := hb.empty_broker h0
        have hfit : ∃ w : Number, w.isNormalized ∧
            w.toRat = loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat :=
          ⟨Number.zero, Number.zero_isNormalized, by rw [Number.toRat_zero]; linarith⟩
        show dt'.toRat = 0
        rw [Number.operator_sub_exact_of_fits loan.broker.wf.debtTotal_norm loan.wf.principalOutstanding_norm hdt
          hfit]
        linarith }
  obtain ⟨b, hb', -⟩ := RawLoanBroker.to_lawful_ok_of hwf ((RawLoanBroker.valid_iff_exact _ hwf).mpr hex)
  exact ⟨b, hb'⟩

/-- A default never fails its re-checks when the loan's principal sits in its broker's DebtTotal, the asset
stores AssetsDeployed less the principal, and AssetsReserved stays within what is left. -/
lemma Loan.manageDefault_ne_notLawful (loan : Loan) (v : Vault)
    (hpo : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat)
    (hrep : STAmount.Representable v.numericType (v.assetsDeployed.toRat - loan.principalOutstanding.toRat))
    (hres : v.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat)
    (hnt : loan.broker.numericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) :
    (loan.manageDefault v).run ≠ .error .notLawful := by
  intro h
  rw [Loan.manageDefault_run] at h
  have hpn := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hex := v.exact
  split at h
  · rename_i e he; cases h; exact RawLoan.interestDue_ne_notLawful _ he
  rename_i interestDue hi
  split at h
  · rename_i e he; cases h; exact Loan.defaultCover_ne_notLawful _ _ he
  rename_i dc hdc
  have hdcn := Loan.defaultCover_isNormalized loan v dc hdc
  obtain ⟨mc, liq, -, -, hmc, hliq, -, -, -⟩ := Loan.defaultCover_parts loan v dc hdc
  have hdcle := Loan.defaultCover_le loan v dc mc liq hdc hmc hliq
  have hcN : (loan.defaultChange interestDue dc).Normalized :=
    ⟨Number.operator_neg_isNormalized _ hpn, by
      show Number.isNormalized (if loan.isImpaired then loan.principalOutstanding.operator_neg else Number.zero)
      split
      · exact Number.operator_neg_isNormalized _ hpn
      · exact Number.zero_isNormalized, Number.zero_isNormalized,
      Number.operator_neg_isNormalized _ (RawLoan.interestDue_isNormalized loan interestDue hi)⟩
  -- the cover the default adds is floored onto a grid at or above the base, so the new cash stays on the base grid
  have hdcg : Number.OnGrid v.baseExponent dc := by
    obtain ⟨_, _, _, st, _, _, _, hsr, htn⟩ := Loan.defaultCover_parts loan v dc hdc
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ st _ (Vault.assetsAvailable_onGrid v)
      ⟨v.baseExponent_bounds.1, v.baseExponent_bounds.2.1⟩ (fun hi => v.baseExponent_bounds.2.2 (hnt ▸ hi)) hsr htn
  have hvault := Vault.poolAdjust_ne_notLawful v (loan.defaultChange interestDue dc) hcN fun raw hadj => by
    have hcv := Vault.adjustBalances_cash_valid v _ raw hmax hdcg hadj
      (Vault.adjustBalances_ok_facts v _ raw hcN hadj).2.2.2.2.2.2.1
    obtain ⟨aa', ad', lu', ar', yu', hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
    have hfit := STAmount.Representable.number hrep
    have hadv : ad'.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat := by
      have h1 := Number.operator_add_exact_of_fits v.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpn)
        hs.deployed (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact hfit)
      show ad'.toRat = _
      rw [h1, Number.toRat_neg, ← sub_eq_add_neg]
    have harv : ar' = v.assetsReserved := Number.eq_of_add_zero hs.reserved
    refine ⟨by show STAmount.Representable v.numericType ad'.toRat; rw [hadv]; exact hrep,
      by show ar'.toRat ≤ ad'.toRat; rw [harv, hadv]; linarith, fun h0 => ?_, hcv.1, hcv.2⟩
    -- a vault without shares holds nothing, so the loan has no principal and the cover is zero
    obtain ⟨hA0, hD0⟩ := hex.empty_shares (Vault.toExact_sharesTotal_zero v h0)
    have hD0' : v.assetsDeployed.toRat = 0 := hD0
    have hP0 : loan.principalOutstanding.toRat = 0 := by
      have := hex.assetsReserved_nonneg
      have : (0 : ℚ) ≤ v.assetsReserved.toRat := this
      linarith
    have hdcz := Loan.defaultCover_zero loan v dc hdc hP0 hA0
    obtain ⟨aa, h1, h2⟩ := hs.cash
    have h1' : v.assetsAvailable.operator_add Number.zero .to_nearest = .ok aa := by
      rw [← hdcz]; exact h1
    have haae := Number.eq_of_add_zero h1'
    have hAz : v.assetsAvailable = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero v.wf.assetsAvailable_norm).mp hA0
    rw [haae, hAz] at h2
    have h3 : STAmount.roundToNumericType v.numericType Number.zero .to_nearest = .ok Number.zero := by
      cases v.numericType <;> rfl
    rw [h3, Except.ok.injEq] at h2
    exact ⟨by show aa'.toRat = 0; rw [← h2, Number.toRat_zero], by show ad'.toRat = 0; rw [hadv]; linarith⟩
  split at h
  · rename_i e he; cases h; exact hvault he
  · cases h
  split at h
  · rename_i e he; cases h; exact Number.operator_sub_ne_notLawful _ _ _ he
  rename_i dt' hdt
  split at h
  · rename_i e he; cases h; exact Number.operator_sub_ne_notLawful _ _ _ he
  rename_i ca' hca
  have hdcca : dc.toRat ≤ loan.broker.coverAvailable.toRat := le_trans hdcle (min_le_right _ _)
  obtain ⟨b, hb⟩ := Loan.defaultedBroker_lawful loan dc dt' ca' hdcn hdcca hpo hdt hca
  split at h
  · rename_i e he; rw [hb] at he; cases he
  rename_i broker' hb'
  obtain ⟨loan', hl', -⟩ := Loan.defaultedLoan_lawful loan broker'
  split at h
  · rename_i e he; rw [hl'] at he; cases he
  · cases h

/-- Reading a stored loan with the ledger's copy of its broker never fails the lawfulness re-check. -/
lemma LendingLedger.Reachable.withBroker_ne_notLawful {l : LendingLedger} (hr : l.Reachable) {i : Nat}
    {e : LoanEntry} {b : LoanBroker} (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) :
    e.loan.withBroker b ≠ .error .notLawful := by
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (hr.scaleInv.broker_asset he hb)
  rw [hw]; exact nofun

/-- AssetsDeployed less the principal of a stored loan is an amount the asset stores: a whole number of base
units, at most `10^16` of them. -/
lemma LendingLedger.Reachable.deployed_sub_representable {l : LendingLedger} (hr : l.Reachable) {i : Nat}
    {loan : Loan} (hat : l.LoanAt i loan) :
    STAmount.Representable l.vault.numericType (l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat) := by
  obtain ⟨w, hw, hwv⟩ := hr.deployed_fits hat
  obtain ⟨d, -, hdv⟩ := hr.deployed_units
  obtain ⟨p, -, hpv, hle, -⟩ := hr.loanAt_principal hat
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hw0 : 0 ≤ w.toRat := by rw [hwv]; linarith
  rw [← hwv]
  refine (STAmount.isRounded_eq_false_iff _ _ hw hw0).mp ?_
  have hpd : p ≤ d := by
    have : (p : ℚ) * 10 ^ l.vault.baseExponent ≤ (d : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hpv, ← hdv]; exact hle
    exact_mod_cast le_of_mul_le_mul_right this hb10
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  refine Vault.isRounded_false_of_units l.vault w hw hw0 ⟨d - p, ?_⟩ ?_ ?_
  · rw [hwv, hdv, hpv]; push_cast [hpd]; ring
  · rw [hwv]; have := hr.lossInv.deployed; linarith
  · rw [hwv]; linarith

/-- The management checks never raise `notLawful`. -/
lemma Loan.canManage_ne_notLawful (loan : Loan) (action : LoanManageAction) (now : UInt32) :
    loan.canManage action now ≠ .error .notLawful := by
  unfold Loan.canManage
  simp only [bind, Except.bind, pure, Except.pure, UInt32.addChecked_of_lt loan.gracePeriodEnd_lt]
  split_ifs <;> exact nofun

/-- A LoanManage on a reachable ledger never fails its lawfulness re-check. -/
lemma LendingLedger.loanManage_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (action : LoanManageAction) : (l.apply (.loanManage i action)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_loan rfl
  intro _ _ h
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok'
  · exact hr.withBroker_ne_notLawful ‹_› ‹_› ‹_›
  · exact Loan.canManage_ne_notLawful _ _ _ ‹_›
  rename_i _ e he _ b hb _ _ loan hw _ _ _ ter hct _ hc _ hm
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have haa : STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false := hr.availableStored
  cases action with
  | impair => exact Loan.manageImpair_ne_notLawful loan l.vault l.now haa hm
  | unimpair => exact Loan.manageUnimpair_ne_notLawful loan l.vault haa hm
  | default =>
    have hter : ter = .tesSUCCESS := (TER.isTesSuccess_iff ter).mp (by simpa using hc)
    have hp := Loan.canManage_not_pending loan .default l.now (by rw [hct, hter])
    have hraw := Loan.withBroker_eq hw
    have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hp' : e.loan.isPending = false := by
      rw [← hp, show loan.isPending = loan.toRawLoan.isPending from rfl, hraw]
    obtain ⟨-, -, -, -, hdt⟩ := hr.loanAt_principal hat
    have hres : l.vault.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
      rw [hr.reservedInv.sum, hr.debtInv.deployed, hpo]
      exact LendingLedger.principalSum_add_le_all l (·.isPending) he hp'
    simp only [Loan.manage] at hm
    unfold_ter at hm
    walk_ok'
    exact Loan.manageDefault_ne_notLawful loan l.vault hdt (hr.deployed_sub_representable hat) hres
      (hr.loanAt_scale hat).2 hr.holdsAsset.maxValue_le ‹_›

/-- The LoanAccept checks never raise `notLawful`. -/
lemma Loan.canAccept_ne_notLawful (loan : Loan) (v : Vault) (now : UInt32) :
    loan.canAccept v now ≠ .error .notLawful := by
  unfold Loan.canAccept
  simp only [bind, Except.bind, pure, Except.pure, Vault.pool_exceedsOpenLimit]
  split_ne_notLawful [RawLoan.interestDue_ne_notLawful, Vault.exceedsOpenLimit_ne_notLawful]

/-- A LoanAccept on a reachable ledger never fails its lawfulness re-check. -/
lemma LendingLedger.loanAccept_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat) :
    (l.apply (.loanAccept i)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_loan rfl
  intro _ _ h
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok'
  · exact hr.withBroker_ne_notLawful ‹_› ‹_› ‹_›
  · exact Loan.canAccept_ne_notLawful _ _ _ ‹_›
  · exact Loan.accept_ne_notLawful _ _ ‹_›

/-- A delete never fails its re-checks when a pending loan's principal is stored exactly, sits in its broker's
DebtTotal, and the asset stores AssetsDeployed less it. -/
lemma Loan.delete_ne_notLawful (loan : Loan) (v : Vault)
    (hpo : loan.isPending = true → STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false)
    (had : loan.isPending = true →
      STAmount.Representable v.numericType (v.assetsDeployed.toRat - loan.principalOutstanding.toRat))
    (hdt : loan.isPending = true → loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpg : loan.isPending = true → Number.OnGrid v.baseExponent loan.principalOutstanding)
    (hc0 : loan.broker.loanCount ≠ 0) :
    (loan.delete v).run ≠ .error .notLawful := by
  intro h
  cases hp : loan.isPending
  · rw [Loan.delete_active_reduce loan v hp] at h
    obtain ⟨b, hb, -⟩ := Loan.deleteActive_ok loan.broker hc0
    rw [hb] at h
    cases h
  · cases hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest with
    | error e =>
      have : (loan.delete v).run = .error e := by
        simp only [Loan.delete, hp, if_true, Loan.deletePending]
        unfold_ter
        simp [hround]
      rw [this] at h
      cases h
      exact STAmount.roundToNumericType_ne_notLawful _ _ _ _ hround
    | ok principal' =>
      rw [Loan.delete_pending_reduce loan v principal' hp hround] at h
      have hpn := loan.wf.principalOutstanding_norm
      have hp'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
      have hcN : (loan.deleteChange principal').Normalized :=
        ⟨Number.operator_neg_isNormalized _ hpn, Number.zero_isNormalized,
          Number.operator_neg_isNormalized _ hp'n, Number.zero_isNormalized⟩
      have hvault := Vault.poolAdjust_ne_notLawful_of_lawful v (loan.deleteChange principal') fun raw hadj => by
        obtain ⟨v', hv', -⟩ := Loan.delete_vault_lawful loan v principal' raw hround hadj (hpo hp) (had hp) hmax
          (hpg hp)
        exact ⟨v', hv'⟩
      split at h
      · rename_i e he; cases h; exact hvault he
      · cases h
      split at h
      · rename_i e he; cases h; exact Number.operator_sub_ne_notLawful _ _ _ he
      rename_i d hd
      obtain ⟨b, hb⟩ := Loan.delete_broker_lawful loan d hd hc0 (Or.inr (hdt hp))
      rw [hb] at h
      cases h

/-- A LoanDelete on a reachable ledger never fails its lawfulness re-check. -/
lemma LendingLedger.loanDelete_ne_notLawful (l : LendingLedger) (hr : l.Reachable) (i : Nat) :
    (l.apply (.loanDelete i)).run ≠ .error .notLawful := by
  apply LendingLedger.apply_ne_notLawful_of_loan rfl
  intro _ _ h
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok'
  · exact hr.withBroker_ne_notLawful ‹_› ‹_› ‹_›
  rename_i e he _ b hb _ _ loan hw _ _ _ hd
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hraw := Loan.withBroker_eq hw
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  obtain ⟨-, -, -, -, hdt⟩ := hr.loanAt_principal hat
  have hnt := (hr.loanAt_scale hat).2
  refine Loan.delete_ne_notLawful loan l.vault (fun hp => ?_) (fun _ => hr.deployed_sub_representable hat)
    (fun _ => hdt) hr.holdsAsset.maxValue_le (fun _ => (hr.loanAt_scale hat).1 ▸ (Loan.principal_onGrid loan).1)
    (by rw [show loan.broker = b from (congrArg RawLoan.broker hraw :)]; exact hr.loanCountInv.loanCount_ne_zero he hb)
    hd
  have hp' : e.loan.isPending = true := by
    rw [← hp, show loan.isPending = loan.toRawLoan.isPending from rfl, hraw]
  rw [hnt]
  exact (STAmount.isRounded_eq_false_iff _ _ loan.wf.principalOutstanding_norm
    loan.exact.principalOutstanding_nonneg).mpr (by rw [hpo]; exact hr.reservedInv.exact i e he hp')

end XRPL.Model.Lending
