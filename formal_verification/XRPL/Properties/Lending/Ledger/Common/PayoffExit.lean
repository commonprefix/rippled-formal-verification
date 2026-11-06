import XRPL.Properties.Lending.Ledger.Common.SettledVault
import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.RecheckVault
import XRPL.Properties.Lending.Ledger.Common.SharesNonneg
import XRPL.Properties.Lending.Ledger.Common.SumFacts
import XRPL.Properties.Lending.Ledger.Common.ReachableFromIn
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # Paying out the sole holder once every loan is closed

A closed loan owes no principal, so the vault has nothing lent out and nothing lost. Its cash is whole base units
stored exactly, and one withdrawal of every share pays out all of it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

/-- With every stored loan paid off, no stored loan owes principal. -/
private lemma LendingLedger.principalSum_closed (l : LendingLedger)
    (hclosed : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0)
    (p : Loan → Bool) : l.principalSum p = 0 := by
  unfold LendingLedger.principalSum
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  cases o with
  | none => rfl
  | some e =>
    obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem ho
    have he : l.loan? j = some e := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_getElem hj, hjo]; rfl
    have hpo := (e.loan.valid.paid_zeroed (hclosed j e he)).2.1
    have hpo' : e.loan.principalOutstanding = Number.zero := hpo
    simp [LoanEntry.principalIf, hpo', Number.toRat_zero]

/-- With every loan closed, the vault is settled, for an MPT cash below `2.5·10^17` units. XRP stores at most
`10^17` drops. -/
lemma LendingLedger.Reachable.settled {l : LendingLedger} (hr : l.Reachable)
    (hclosed : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0)
    (hmpt : l.vault.numericType = NumericType.int64 → l.vault.assetsAvailable.toRat < 25 * 10 ^ 16) :
    l.vault.Settled := by
  have hsum := l.principalSum_closed hclosed
  have hAD : l.vault.assetsDeployed = Number.zero :=
    (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.assetsDeployed_norm).mp (by rw [hr.debtInv.deployed, hsum])
  have hLU : l.vault.lossUnrealized = Number.zero :=
    (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.lossUnrealized_norm).mp
      (by rw [LendingLedger.loss_impaired_proof l hr, hsum])
  have hst := hr.storesAvailable hr.holdsAsset.maxValue_le
  refine ⟨hAD, hLU, hr.assetsAvailable_units hr.holdsAsset, hst, fun hint => ?_⟩
  rcases hr.holdsAsset with hfr | hnat | hint64
  · rw [hfr] at hint; cases hint
  · -- XRP: the asset stores at most `10^17` drops
    have hrep := (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm
      l.vault.exact.assetsAvailable_nonneg).mp hst
    rcases hrep with h0 | hrep
    · rw [h0]; norm_num
    · rw [hnat] at hrep
      simp only [NumericType.native] at hrep
      obtain ⟨-, k, hk, -, hkv⟩ := hrep
      have hk' : (k : ℚ) ≤ 10 ^ 17 := by exact_mod_cast (show k ≤ 10 ^ 17 from hk)
      rw [hkv]; linarith
  · exact hmpt hint64

/-- Proof body of `Lending.payoff_exit`. -/
lemma LendingLedger.payoff_exit_settled_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hph : l.vault.phase l.now = .redemption)
    (hclosed : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0)
    (h : Nat) (hsole : l.isSoleShareholder h = true)
    (hmpt : l.vault.numericType = NumericType.int64 → l.vault.assetsAvailable.toRat < 25 * 10 ^ 16) :
    ∃ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') ∧
      l'.vault.assetsAvailable = Number.zero ∧ l'.vault.sharesTotal = Number.zero := by
  have hz := hr.settled hclosed hmpt
  have hmax := hr.holdsAsset.maxValue_le
  have hSTn := l.vault.wf.sharesTotal_norm
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  obtain ⟨hheldn, hheld0⟩ := hr.sharesNonneg.sharesOf h
  unfold LendingLedger.isSoleShareholder at hsole
  rw [Bool.and_eq_true, operator_ne_iff _ _ hheldn Number.zero_isNormalized,
    operator_eq_iff _ _ hheldn hSTn, Number.toRat_zero] at hsole
  obtain ⟨hne0, heq⟩ := hsole
  have hSTpos : 0 < l.vault.sharesTotal.toRat := by rw [← heq]; exact lt_of_le_of_ne hheld0 (Ne.symm hne0)
  -- the share total as an int64 amount, which the preflight accepts
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok l.vault.sharesTotal .to_nearest hSTn
    (Number.negative_false_of_pos _ hSTpos) (Vault.sharesTotal_le_maxRep l.vault)
  obtain ⟨hsic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ S (by decide) hS
  have hSv : S.toRat = l.vault.sharesTotal.toRat :=
    STAmount.ofNumber_integral_exact .int64 _ _ S (by decide) hSTn l.vault.wf.sharesTotal_int hS
  have hSpos : 0 < S.toRat := by rw [hSv]; exact hSTpos
  have hSm : S.mValue ≠ 0 := fun h0 => by rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hSpos; exact lt_irrefl _ hSpos
  have hSneg : S.mIsNegative = false := by
    cases hn : S.mIsNegative
    · rfl
    · have := STAmount.toRat_nonpos_of S hn; linarith
  have hcan : isCanonicalAmount S .int64 = true := by
    unfold isCanonicalAmount
    have hint : NumericType.int64.isIntegral = true := by decide
    rw [hint, if_pos rfl]
    have hr' := hsic.in_range
    rw [hty] at hr'
    simp [hty, hsic.offset_zero, hr']
  have hpre : (LendingTx.vaultWithdraw h (.vaultShares S)).preflight l = .tesSUCCESS := by
    simp [LendingTx.preflight, hcan, isPositiveAmount, hSneg, hSm]
  obtain ⟨hc, -⟩ := isCanonicalAmount_canonical S .int64 (fun _ => by decide) hcan hSm
  have hpos : 0 < (WithdrawAmount.vaultShares S).amount.toRat := hSpos
  have hopen : (l.vault.earlyExitFeeRate.isNone && l.vault.phase l.now == .investment) = false := by
    rw [hph]; simp
  obtain ⟨r, hw, hrs, -, hAA', hST'⟩ := Vault.Settled.withdraw_all l.vault l.now hz hmax (l.isSoleShareholder h)
    hopen S hc hty (by rw [hSv, hcast]) hpos
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical S .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hlt : (l.sharesOf h).operator_lt sn = false := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff _ _ hheldn hsnn, hsnv, hSv, heq]
    exact lt_irrefl _
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_normalized_cap (l.sharesOf h) sn .to_nearest hheldn hsnn
    (Number.negative_false_of_nonneg _ hheldn hheld0)
    (Number.negative_false_of_pos _ (by rw [hsnv]; exact hSpos))
    (by rw [heq]; exact Vault.sharesTotal_le_maxRep l.vault)
    (by rw [hsnv, hSv]; exact Vault.sharesTotal_le_maxRep l.vault)
  refine ⟨S, l.commitVault { vault := r.vault', holderShares := some (h, d) }, by rw [hSv, heq], ?_, ?_, ?_⟩
  · rw [LendingLedger.apply_of_preflight hpre]
    simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, Bool.false_eq_true, ↓reduceIte,
      LendingLedger.applyVault, hpos, ↓reduceDIte]
    unfold_ter
    have hwh := Vault.withdraw_holder_of_ok _ _ _ _ _ _ _ hw sn (by rw [hrs]; exact hsn) hlt
    simp only [ExceptT.run] at hwh
    rw [hwh]
    simp only [hrs, hsn, hd]
    rfl
  · simp only [LendingLedger.commitVault, LendingLedger.setShares]
    exact hAA'
  · simp only [LendingLedger.commitVault, LendingLedger.setShares]
    exact hST'

end XRPL.Model.Lending
