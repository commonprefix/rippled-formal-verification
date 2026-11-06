import XRPL.Properties.Lending.Loan.Common.AcceptExits
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Model.Lending.Loan.LoanDelete

/-! # Proof bodies for the `Loan.delete` exits

The exits of the vault update a pending delete runs, and its success path. A closed loan's delete
always succeeds. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Vault.adjustBalances_codes Number.zero_le_of_signum Number.toRat_nonneg_of_le Number.operator_sub_toRat_le
  from XRPL.Properties.Lending.Loan.Common.AcceptExits

/-- Releasing a loan from a broker passes the re-check when the new DebtTotal is a normalized
amount between zero and DebtMaximum, or the broker has no loan left. -/
private lemma LoanBroker.releaseLoan_ok (lb : LoanBroker) (d : Number) (hc0 : lb.loanCount ≠ 0) (hn : d.isNormalized)
    (h0 : lb.loanCount - 1 ≠ 0 → 0 ≤ d.toRat)
    (hle : lb.loanCount - 1 ≠ 0 → lb.debtMaximum ≠ Number.zero → d.toRat ≤ lb.debtMaximum.toRat) :
    ∃ lb', lb.releaseLoan d = .ok lb' ∧ lb'.toRawLoanBroker = { lb.toRawLoanBroker with
      loanCount := lb.loanCount - 1
      debtTotal := if lb.loanCount - 1 == 0 then Number.zero else d } := by
  unfold LoanBroker.releaseLoan
  rw [UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hc0)]
  simp only [bind, Except.bind]
  apply RawLoanBroker.to_lawful_ok_of
  · refine { lb.wf with debtTotal_norm := ?_ }
    dsimp only
    split
    · exact Number.zero_isNormalized
    · exact hn
  · by_cases hc : lb.loanCount - 1 = 0
    · have hb : (lb.loanCount - 1 == 0) = true := by rw [hc]; rfl
      refine { lb.valid with debtTotal_nonneg := ?_, debt_within_cap := ?_, empty_broker := ?_ } <;>
        dsimp only <;> rw [if_pos hb]
      · decide
      · exact fun _ => lb.valid.debtMaximum_nonneg
      · exact fun _ => rfl
    · have hb : (lb.loanCount - 1 == 0) = false := by simpa using hc
      refine { lb.valid with debtTotal_nonneg := ?_, debt_within_cap := ?_, empty_broker := ?_ } <;>
        dsimp only <;> rw [hb, if_neg Bool.false_ne_true]
      · exact (operator_le_iff _ _ Number.zero_isNormalized hn).mpr (by rw [Number.toRat_zero]; exact h0 hc)
      · exact fun hm => (operator_le_iff _ _ hn lb.wf.debtMaximum_norm).mpr (hle hc hm)
      · exact fun h => absurd h hc

/-- The balance change a pending delete makes to the vault: the rounded principal returns from
AssetsReserved to AssetsAvailable and the principal leaves AssetsDeployed. -/
def Loan.deleteChange (loan : Loan) (principal' : Number) : PoolBalanceChange :=
  { cash := principal'
    deployed := loan.principalOutstanding.operator_neg
    reserved := principal'.operator_neg }

/-- The run of a pending delete: the vault update, then the new DebtTotal and the re-check of the
broker. -/
private lemma Loan.delete_pending_reduce (loan : Loan) (v : Vault) (principal' : Number)
    (hp : loan.isPending = true)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal') :
    (loan.delete v).run =
      match AssetPool.adjustBalances v (loan.deleteChange principal') with
      | .error e => .error e
      | .ok (.error ter) => .ok (.error ter)
      | .ok (.ok v') =>
        match loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with
        | .error e => .error e
        | .ok debtTotal' =>
          match loan.broker.releaseLoan debtTotal' with
          | .error e => .error e
          | .ok broker' => .ok (.ok { broker' := broker', pool' := v' }) := by
  simp only [Loan.delete, hp, if_true, Loan.deletePending]
  unfold_ter
  simp only [hround, Loan.deleteChange]
  rcases AssetPool.adjustBalances v
      { cash := principal', deployed := loan.principalOutstanding.operator_neg,
        reserved := principal'.operator_neg } with e | (ter | v') <;> try rfl
  rcases loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with e | d <;> try rfl
  dsimp only
  cases loan.broker.releaseLoan d <;> rfl

/-- The run of a closed loan's delete: the broker releases the loan and the vault is untouched. -/
lemma Loan.delete_active_reduce (loan : Loan) (v : Vault) (hp : loan.isPending = false) :
    (loan.delete v).run =
      match Loan.deleteActive loan.broker with
      | .error e => .error e
      | .ok broker' => .ok (.ok { broker' := broker', pool' := v }) := by
  simp only [Loan.delete, hp, Bool.false_eq_true, if_false]
  unfold_ter
  cases Loan.deleteActive loan.broker <;> rfl

/-- Releasing a closed loan always passes the broker's re-check: DebtTotal keeps its value, or drops
to zero with the last loan. -/
lemma Loan.deleteActive_ok (broker : LoanBroker) (hc0 : broker.loanCount ≠ 0) :
    ∃ broker', Loan.deleteActive broker = .ok broker' ∧ broker'.toRawLoanBroker = { broker.toRawLoanBroker with
      loanCount := broker.loanCount - 1
      debtTotal := if broker.loanCount - 1 == 0 then Number.zero else broker.debtTotal } :=
  LoanBroker.releaseLoan_ok broker broker.debtTotal hc0 broker.wf.debtTotal_norm
    (fun _ => (show 0 ≤ broker.debtTotal.toRat from broker.exact.debtTotal_nonneg))
    (fun _ hm => (operator_le_iff _ _ broker.wf.debtTotal_norm broker.wf.debtMaximum_norm).mp
      (broker.valid.debt_within_cap hm))

/-- A release that passed: the broker with one loan less, and DebtTotal kept or dropped to zero with the last
loan. -/
lemma Loan.deleteActive_raw (broker broker' : LoanBroker) (h : Loan.deleteActive broker = .ok broker') :
    broker'.toRawLoanBroker = { broker.toRawLoanBroker with
      loanCount := broker.loanCount - 1
      debtTotal := if broker.loanCount - 1 == 0 then Number.zero else broker.debtTotal } := by
  unfold Loan.deleteActive LoanBroker.releaseLoan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i c hc
    obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
    exact (RawLoanBroker.to_lawful_ok h).1

/-- A successful delete of a closed loan released it from the broker and left the vault as it was. -/
lemma Loan.delete_active_ok_inv (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = false) (hok : (loan.delete v).run = .ok (.ok r)) :
    Loan.deleteActive loan.broker = .ok r.broker' ∧ r.pool' = v := by
  rw [Loan.delete_active_reduce loan v hp] at hok
  cases hb : Loan.deleteActive loan.broker with
  | error e => rw [hb] at hok; cases hok
  | ok b =>
    rw [hb] at hok
    injection hok with hok
    injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

/-- A successful pending delete rounded the principal, ran a successful vault update, and released
the loan from the broker. -/
lemma Loan.delete_pending_ok_inv (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hp : loan.isPending = true) (hok : (loan.delete v).run = .ok (.ok r)) :
    ∃ principal' raw debtTotal',
      STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
        .ok principal' ∧
      (v.adjustBalances (loan.deleteChange principal')).run = .ok (.ok raw) ∧ raw.to_lawful = .ok r.pool' ∧
      loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal' ∧
      loan.broker.releaseLoan debtTotal' = .ok r.broker' := by
  cases hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest with
  | error e =>
    simp only [Loan.delete, hp, if_true, Loan.deletePending] at hok
    unfold_ter at hok
    simp [hround] at hok
  | ok principal' =>
    rw [Loan.delete_pending_reduce loan v principal' hp hround] at hok
    revert hok
    rcases hpool : AssetPool.adjustBalances v (loan.deleteChange principal') with e | (t | v')
    · intro hok; cases hok
    · intro hok; injection hok with hok; cases hok
    · intro hok; dsimp only at hok
      obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ v' hpool
      cases hdebt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with
      | error e => rw [hdebt] at hok; dsimp only at hok; cases hok
      | ok d =>
        rw [hdebt] at hok; dsimp only at hok
        cases hb : loan.broker.releaseLoan d with
        | error e => rw [hb] at hok; dsimp only at hok; cases hok
        | ok b =>
          rw [hb] at hok; dsimp only at hok; injection hok with hok; injection hok with hok; subst hok
          exact ⟨principal', raw, d, rfl, hadj, hv', rfl, hb⟩

/-- The broker a pending delete writes passes its re-check while the loan's principal is within
DebtTotal, or when it is the broker's last loan. -/
lemma Loan.delete_broker_lawful (loan : Loan) (debtTotal' : Number)
    (hdebt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal')
    (hc0 : loan.broker.loanCount ≠ 0)
    (h : loan.broker.loanCount = 1 ∨ loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat) :
    ∃ broker', loan.broker.releaseLoan debtTotal' = .ok broker' := by
  have hdn := loan.broker.wf.debtTotal_norm
  have hpn := loan.wf.principalOutstanding_norm
  have hn : debtTotal'.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ _ hdn hpn hdebt
  rcases h with h1 | hle
  · obtain ⟨b, hb, -⟩ := LoanBroker.releaseLoan_ok loan.broker debtTotal' hc0 hn
      (fun hc => absurd (by rw [h1]; rfl) hc) (fun hc => absurd (by rw [h1]; rfl) hc)
    exact ⟨b, hb⟩
  · -- the new DebtTotal is the rounded difference, between zero and the old DebtTotal
    have hR := operator_sub_rounded_to_nearest _ _ _ hdn hpn hdebt
    have h0 : 0 ≤ debtTotal'.toRat := by
      have := Number.roundsToRepresentable_ge _ _ hR Number.zero Number.zero_isNormalized
        (by rw [Number.toRat_zero]; linarith)
      rwa [Number.toRat_zero] at this
    have hup : debtTotal'.toRat ≤ loan.broker.debtTotal.toRat :=
      Number.operator_sub_toRat_le _ _ _ hdn hpn
        (show 0 ≤ loan.principalOutstanding.toRat from loan.exact.principalOutstanding_nonneg) hdebt
    obtain ⟨b, hb, -⟩ := LoanBroker.releaseLoan_ok loan.broker debtTotal' hc0 hn (fun _ => h0)
      (fun _ hm => hup.trans ((operator_le_iff _ _ hdn loan.broker.wf.debtMaximum_norm).mp
        (loan.broker.valid.debt_within_cap hm)))
    exact ⟨b, hb⟩

/-- The vault a pending delete writes passes its re-check when the asset stores PrincipalOutstanding and
AssetsDeployed − PrincipalOutstanding exactly. The second can fail when AssetsDeployed is coarser than the principal. -/
lemma Loan.delete_vault_lawful (loan : Loan) (v : Vault) (principal' : Number) (raw : RawVault)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hadj : (v.adjustBalances (loan.deleteChange principal')).run = .ok (.ok raw))
    (hpo : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false)
    (had : STAmount.Representable v.numericType (v.assetsDeployed.toRat - loan.principalOutstanding.toRat))
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hpg : Number.OnGrid v.baseExponent loan.principalOutstanding) :
    ∃ v', raw.to_lawful = .ok v' ∧ v'.toRawVault = raw := by
  obtain ⟨aa', ad', lu', ar', yu', hs, ⟨haa, hadn, -, -, har⟩, hle, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  obtain ⟨aa, h1, h2⟩ := hs.cash
  have hd := hs.deployed
  have hl := hs.loss
  have hr := hs.reserved
  have hy := hs.yield
  simp only [Loan.deleteChange, Number.operator_add_zero_right, Except.ok.injEq] at h1 hd hl hr hy
  subst hl hy
  have hpn := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  -- the asset stores the principal exactly, so the rounded principal is the principal
  have hp' : principal' = loan.principalOutstanding :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround) hpn
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ hpn hpo hround)
  subst hp'
  have haan : aa.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hpn h1
  have haan' : aa'.isNormalized := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2
  have hadn' : ad'.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsDeployed_norm
    (Number.operator_neg_isNormalized _ hpn) hd
  have harn : ar'.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsReserved_norm
    (Number.operator_neg_isNormalized _ hpn) hr
  have hadv : ad'.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat := by
    have h := Number.operator_add_exact_of_fits v.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpn) hd
      (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number had)
    rw [h, Number.toRat_neg, ← sub_eq_add_neg]
  have had0 := Number.toRat_nonneg_of_le hadn' (Number.zero_le_of_signum _ hadn' hadn)
  -- the principal returns to the cash as whole base units
  have haa0 := Number.toRat_nonneg_of_le haan' (Number.zero_le_of_signum _ haan' haa)
  have hcv := Vault.adjustBalances_cash_valid v _ _ hmax hpg hadj haa0
  apply RawVault.to_lawful_ok_of
  · exact { v.wf with assetsAvailable_norm := haan', assetsDeployed_norm := hadn', assetsReserved_norm := harn }
  · refine { v.valid with
      assetsAvailable_nonneg := Number.zero_le_of_signum _ haan' haa
      assetsDeployed_nonneg := Number.zero_le_of_signum _ hadn' hadn
      assetsReserved_nonneg := Number.zero_le_of_signum _ harn har
      empty_shares := ?_
      lossUnrealized_le := ?_
      assetsDeployed_representable := ?_
      assetsReserved_le := ?_
      assetsAvailable_representable := hcv.1
      assetsAvailable_onGrid := Vault.onGrid_clause v aa' haan' haa0 hcv.2 }
    · -- an empty vault deploys nothing, so the deleted loan carried no principal
      intro h0
      obtain ⟨hA, hD⟩ := v.valid.empty_shares h0
      have hP0 : loan.principalOutstanding.toRat = 0 := by
        rw [hadv, hD, Number.toRat_zero] at had0; linarith
      have hP : loan.principalOutstanding = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hpn).mp hP0
      rw [hA, hP, Number.operator_add_zero_right, Except.ok.injEq] at h1
      rw [← h1, STAmount.roundToNumericType_zero_to_nearest, Except.ok.injEq] at h2
      refine ⟨h2.symm, (Number.toRat_eq_zero_iff_eq_zero hadn').mp ?_⟩
      rw [hadv, hD, hP0, Number.toRat_zero]; ring
    · unfold Number.operator_le; unfold Number.operator_gt at hle; simpa using hle
    · exact (STAmount.isRounded_eq_false_iff _ _ hadn' had0).mpr (by rw [hadv]; exact had)
    · -- AssetsReserved and AssetsDeployed both lose the principal
      have hR := operator_add_rounded_to_nearest _ _ _ v.wf.assetsReserved_norm
        (Number.operator_neg_isNormalized _ hpn) hr
      have hrd := (operator_le_iff _ _ v.wf.assetsReserved_norm v.wf.assetsDeployed_norm).mp
        v.valid.assetsReserved_le
      have hle' := Number.roundsToRepresentable_le _ _ hR ad' hadn'
        (by rw [hadv, Number.toRat_neg]; linarith)
      exact (operator_le_iff _ _ harn hadn').mpr hle'

variable (loan : Loan) (v : Vault)

/-- Proof body of the AssetsDeployed bad-ledger exit of `Loan.delete_exits`. -/
lemma Loan.delete_deployed_bad_ledger_proof (principal' aa' ad' lu' ar' yu' : Number)
    (hp : loan.isPending = true)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hs : Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu')
    (hneg : ad'.signum < 0) :
    (loan.delete v).run = .ok (.error .tefBAD_LEDGER) := by
  have hadj := Vault.adjustBalances_bad_ledger v _ aa' ad' lu' ar' yu' hs (Or.inr (Or.inl hneg))
  rw [Loan.delete_pending_reduce loan v principal' hp hround, Vault.poolAdjust_rejected v _ _ hadj]

/-- Proof body of the AssetsReserved bad-ledger exit of `Loan.delete_exits`. -/
lemma Loan.delete_reserved_bad_ledger_proof (principal' aa' ad' lu' ar' yu' : Number)
    (hp : loan.isPending = true)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hs : Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu')
    (hneg : ar'.signum < 0) :
    (loan.delete v).run = .ok (.error .tefBAD_LEDGER) := by
  have hadj := Vault.adjustBalances_bad_ledger v _ aa' ad' lu' ar' yu' hs
    (Or.inr (Or.inr (Or.inr (Or.inr hneg))))
  rw [Loan.delete_pending_reduce loan v principal' hp hround, Vault.poolAdjust_rejected v _ _ hadj]

/-- Proof body of the limit exit of `Loan.delete_exits`. -/
lemma Loan.delete_limit_exceeded_proof (principal' aa' ad' lu' ar' yu' : Number)
    (hp : loan.isPending = true)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hs : Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hgt : lu'.operator_gt ad' = true) :
    (loan.delete v).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  have hadj := Vault.adjustBalances_limit_exceeded v _ aa' ad' lu' ar' yu' hs hnn hgt
  rw [Loan.delete_pending_reduce loan v principal' hp hround, Vault.poolAdjust_rejected v _ _ hadj]

/-- Proof body of the pending success exit of `Loan.delete_exits`. -/
lemma Loan.delete_success_proof (principal' debtTotal' : Number) (raw : RawVault) (v' : Vault)
    (broker' : LoanBroker) (hp : loan.isPending = true)
    (hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest =
      .ok principal')
    (hadj : (v.adjustBalances (loan.deleteChange principal')).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hdebt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal')
    (hbroker : loan.broker.releaseLoan debtTotal' = .ok broker') :
    (loan.delete v).run = .ok (.ok { broker' := broker', pool' := v' }) := by
  rw [Loan.delete_pending_reduce loan v principal' hp hround, Vault.poolAdjust_ok v _ raw v' hadj hv']
  simp only [hdebt, hbroker]

/-- Proof body of the active success exit of `Loan.delete_exits`. -/
lemma Loan.deleteActive_success_proof (broker' : LoanBroker) (hp : loan.isPending = false)
    (hbroker : loan.broker.releaseLoan loan.broker.debtTotal = .ok broker') :
    (loan.delete v).run = .ok (.ok { broker' := broker', pool' := v }) := by
  rw [Loan.delete_active_reduce loan v hp]
  simp only [Loan.deleteActive, hbroker]

/-- Proof body of `delete_error_codes`. -/
lemma Loan.delete_error_codes_proof (ter : TER) (hok : (loan.delete v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED := by
  cases hp : loan.isPending with
  | false =>
    rw [Loan.delete_active_reduce loan v hp] at hok
    cases hb : Loan.deleteActive loan.broker <;> rw [hb] at hok <;> dsimp only at hok <;> cases hok
  | true =>
    cases hround : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest with
    | error e =>
      simp only [Loan.delete, hp, if_true, Loan.deletePending] at hok
      unfold_ter at hok
      simp [hround] at hok
    | ok principal' =>
      rw [Loan.delete_pending_reduce loan v principal' hp hround] at hok
      revert hok
      rcases hpool : AssetPool.adjustBalances v (loan.deleteChange principal') with e | (t | v')
      · intro hok; cases hok
      · intro hok; injection hok with hok; injection hok with hok; subst hok
        exact Vault.adjustBalances_codes v _ t (Vault.poolAdjust_rejected_parts v _ t hpool)
      · intro hok; dsimp only at hok
        cases hdebt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with
        | error e => rw [hdebt] at hok; dsimp only at hok; cases hok
        | ok d =>
          rw [hdebt] at hok; dsimp only at hok
          cases hb : loan.broker.releaseLoan d <;> rw [hb] at hok <;> dsimp only at hok <;> cases hok

end XRPL.Model.Lending
