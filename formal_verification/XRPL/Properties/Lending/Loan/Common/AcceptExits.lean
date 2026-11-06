import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.LoanValid
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Properties.Vault.Proofs.Support.CashGrid

/-! # Proof bodies for the `Loan.accept` exits

The exits of the vault update an accept runs, and its success path. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A vault update rejects only with tefBAD_LEDGER or tecLIMIT_EXCEEDED. -/
private lemma Vault.adjustBalances_codes (v : Vault) (c : PoolBalanceChange) (ter : TER)
    (h : (v.adjustBalances c).run = .ok (.error ter)) : ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

/-- A lawful vault never has LossUnrealized above AssetsDeployed. -/
private lemma Vault.lossUnrealized_gt_false (v : Vault) :
    v.lossUnrealized.operator_gt v.assetsDeployed = false := by
  have h := v.valid.lossUnrealized_le
  unfold Number.operator_le at h; unfold Number.operator_gt; simpa using h

/-- A normalized `Number` with a nonnegative sign is at least zero. -/
private lemma Number.zero_le_of_signum (n : Number) (hn : n.isNormalized) (h : 0 ≤ n.signum) :
    Number.zero.operator_le n = true := by
  rw [operator_le_iff _ _ Number.zero_isNormalized hn, Number.toRat_zero]
  rw [signum_eq n hn] at h
  by_contra hlt
  push Not at hlt
  rw [if_neg (by linarith), if_pos hlt] at h
  omega

/-- A `Number` at least zero, read exactly. -/
private lemma Number.toRat_nonneg_of_le {n : Number} (hn : n.isNormalized)
    (h : Number.zero.operator_le n = true) : 0 ≤ n.toRat := by
  have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp h
  rwa [Number.toRat_zero] at this

/-- Taking a nonnegative amount off a balance never leaves it above the balance. -/
private lemma Number.operator_sub_toRat_le (x y d : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hy0 : 0 ≤ y.toRat) (hok : x.operator_add y.operator_neg .to_nearest = .ok d) : d.toRat ≤ x.toRat := by
  have hR := operator_add_rounded_to_nearest x y.operator_neg d hx (Number.operator_neg_isNormalized _ hy) hok
  exact Number.roundsToRepresentable_le d _ hR x hx (by rw [Number.toRat_neg]; linarith)

/-- A normalized `Number` at least zero has a nonnegative sign. -/
private lemma Number.signum_nonneg_of_le (n : Number) (hn : n.isNormalized)
    (h : Number.zero.operator_le n = true) : 0 ≤ n.signum := by
  have h0 := Number.toRat_nonneg_of_le hn h
  rw [signum_eq n hn]
  split_ifs <;> first | omega | linarith

/-- The balance change an accept makes to the vault: the principal leaves AssetsReserved and the
interest joins YieldUnrealized. -/
def Loan.acceptChange (loan : Loan) (interestDue : Number) : PoolBalanceChange :=
  { yield := interestDue
    reserved := loan.principalOutstanding.operator_neg }

/-- The run of an accept: the pool update with the accept change, then the re-check of the loan. -/
private lemma Loan.accept_reduce (loan : Loan) (v : Vault) (interestDue : Number)
    (hi : loan.interestDue = .ok interestDue) :
    (loan.accept v).run =
      match AssetPool.adjustBalances v (loan.acceptChange interestDue) with
      | .error e => .error e
      | .ok (.error ter) => .ok (.error ter)
      | .ok (.ok v') =>
        match ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful with
        | .error e => .error e
        | .ok loan' => .ok (.ok { loan' := loan', pool' := v' }) := by
  simp only [Loan.accept]
  unfold_ter
  simp only [hi, Loan.acceptChange]
  rcases AssetPool.adjustBalances v { yield := interestDue, reserved := loan.principalOutstanding.operator_neg }
    with e | (ter | v') <;> try rfl
  cases ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful <;> rfl

/-- A successful accept ran a successful vault update, and its loan is the re-checked active loan. -/
lemma Loan.accept_ok_inv (loan : Loan) (v : Vault) (interestDue : Number) (r : LoanWithPool Vault)
    (hi : loan.interestDue = .ok interestDue) (hok : (loan.accept v).run = .ok (.ok r)) :
    ∃ raw, (v.adjustBalances (loan.acceptChange interestDue)).run = .ok (.ok raw) ∧
      raw.to_lawful = .ok r.pool' ∧
      ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful = .ok r.loan' := by
  rw [Loan.accept_reduce loan v interestDue hi] at hok
  revert hok
  rcases hp : AssetPool.adjustBalances v (loan.acceptChange interestDue) with e | (t | v')
  · intro hok; cases hok
  · intro hok; injection hok with hok; cases hok
  · intro hok; dsimp only at hok
    obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ v' hp
    cases hl : ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful with
    | error e => rw [hl] at hok; dsimp only at hok; cases hok
    | ok loan' =>
      rw [hl] at hok; dsimp only at hok; injection hok with hok; injection hok with hok; subst hok
      exact ⟨raw, hadj, hv', rfl⟩

/-- An accept keeps the broker. -/
lemma Loan.accept_broker (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.broker = loan.broker := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact (congrArg RawLoan.broker (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :)

/-- The vault update of an accept rejects only with tefBAD_LEDGER: it moves nothing into
LossUnrealized or out of AssetsDeployed. -/
private lemma accept_adjust_codes (loan : Loan) (v : Vault) (interestDue : Number) (ter : TER)
    (h : (v.adjustBalances (loan.acceptChange interestDue)).run = .ok (.error ter)) : ter = .tefBAD_LEDGER := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances, Loan.acceptChange] at h
  unfold_ter at h
  simp only [Number.operator_add_zero_right] at h
  walk_ok
  · rfl
  · rename_i hgt
    rw [Vault.lossUnrealized_gt_false] at hgt
    exact absurd hgt (by decide)

/-- The active loan passes its re-check: no loan invariant reads the pending flag. -/
lemma Loan.accept_loan_lawful (loan : Loan) :
    ∃ loan', ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful = .ok loan' ∧
      loan'.toRawLoan = { loan.toRawLoan with isPending := false } :=
  RawLoan.to_lawful_ok_of { loan.wf with } { loan.valid with }

/-- The vault an accept writes passes its re-check: AssetsDeployed and LossUnrealized keep their
values and AssetsReserved only falls. -/
lemma Loan.accept_vault_lawful (loan : Loan) (v : Vault) (interestDue : Number) (raw : RawVault)
    (hi : loan.interestDue = .ok interestDue)
    (hadj : (v.adjustBalances (loan.acceptChange interestDue)).run = .ok (.ok raw)) :
    ∃ v', raw.to_lawful = .ok v' ∧ v'.toRawVault = raw := by
  obtain ⟨aa', ad', lu', ar', yu', hs, ⟨haa, -, -, hyu, har⟩, -, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  obtain ⟨aa, h1, h2⟩ := hs.cash
  have hd := hs.deployed
  have hl := hs.loss
  have hr := hs.reserved
  have hy := hs.yield
  simp only [Loan.acceptChange, Number.operator_add_zero_right, Except.ok.injEq] at h1 hd hl hr hy
  subst h1 hd hl
  have hpn := loan.wf.principalOutstanding_norm
  have harn : ar'.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsReserved_norm
    (Number.operator_neg_isNormalized _ hpn) hr
  have hyun : yu'.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.yieldUnrealized_norm
    (RawLoan.interestDue_isNormalized loan _ hi) hy
  have haan : aa'.isNormalized := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2
  apply RawVault.to_lawful_ok_of
  · exact { v.wf with assetsAvailable_norm := haan, assetsReserved_norm := harn, yieldUnrealized_norm := hyun }
  · refine { v.valid with
      assetsAvailable_nonneg := Number.zero_le_of_signum _ haan haa
      assetsReserved_nonneg := Number.zero_le_of_signum _ harn har
      yieldUnrealized_nonneg := Number.zero_le_of_signum _ hyun hyu
      empty_shares := ?_
      assetsReserved_le := ?_
      assetsAvailable_representable := (Vault.round_cash_valid v aa' h2).1
      assetsAvailable_onGrid := Vault.onGrid_clause v aa' haan (by
        have := Number.zero_le_of_signum _ haan haa
        rwa [operator_le_iff _ _ Number.zero_isNormalized haan, Number.toRat_zero] at this)
        (Vault.round_cash_valid v aa' h2).2 }
    · intro h0
      obtain ⟨hA, hD⟩ := v.valid.empty_shares h0
      rw [hA, STAmount.roundToNumericType_zero_to_nearest, Except.ok.injEq] at h2
      exact ⟨h2.symm, hD⟩
    · -- the release keeps AssetsReserved at most its old value, so at most AssetsDeployed
      have hle := Number.operator_sub_toRat_le _ _ _ v.wf.assetsReserved_norm hpn
        ((show 0 ≤ loan.principalOutstanding.toRat from loan.exact.principalOutstanding_nonneg)) hr
      have hrd := (operator_le_iff _ _ v.wf.assetsReserved_norm v.wf.assetsDeployed_norm).mp
        v.valid.assetsReserved_le
      exact (operator_le_iff _ _ harn v.wf.assetsDeployed_norm).mpr (le_trans hle hrd)

variable (loan : Loan) (v : Vault)

/-- Proof body of the tefBAD_LEDGER line of `Loan.accept_exits`. -/
lemma Loan.accept_bad_ledger_proof (interestDue aa' ad' lu' ar' yu' : Number)
    (hi : loan.interestDue = .ok interestDue)
    (hs : Vault.AdjustSums v (loan.acceptChange interestDue) aa' ad' lu' ar' yu')
    (hneg : ar'.signum < 0) :
    (loan.accept v).run = .ok (.error .tefBAD_LEDGER) := by
  have hadj := Vault.adjustBalances_bad_ledger v _ aa' ad' lu' ar' yu' hs
    (Or.inr (Or.inr (Or.inr (Or.inr hneg))))
  rw [Loan.accept_reduce loan v interestDue hi, Vault.poolAdjust_rejected v _ _ hadj]

/-- Proof body of the success line of `Loan.accept_exits`. -/
lemma Loan.accept_success_proof (interestDue : Number) (raw : RawVault) (v' : Vault) (loan' : Loan)
    (hi : loan.interestDue = .ok interestDue)
    (hadj : (v.adjustBalances (loan.acceptChange interestDue)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hloan : ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful = .ok loan') :
    (loan.accept v).run = .ok (.ok { loan' := loan', pool' := v' }) := by
  rw [Loan.accept_reduce loan v interestDue hi, Vault.poolAdjust_ok v _ raw v' hadj hv']
  simp only [hloan]

/-- Proof body of `accept_error_codes`. -/
lemma Loan.accept_error_codes_proof (ter : TER) (hok : (loan.accept v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER := by
  cases hi : loan.interestDue with
  | error e =>
    simp only [Loan.accept] at hok
    unfold_ter at hok
    simp [hi] at hok
  | ok interestDue =>
    rw [Loan.accept_reduce loan v interestDue hi] at hok
    revert hok
    rcases hp : AssetPool.adjustBalances v (loan.acceptChange interestDue) with e | (t | v')
    · intro hok; cases hok
    · intro hok; injection hok with hok; injection hok with hok; subst hok
      exact accept_adjust_codes loan v interestDue t (Vault.poolAdjust_rejected_parts v _ t hp)
    · intro hok; dsimp only at hok
      cases hl : ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful <;> rw [hl] at hok <;>
        dsimp only at hok <;> cases hok

end XRPL.Model.Lending
