import XRPL.Properties.Lending.Ledger.Common.BrokerSteps
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Vault.Proofs.Support.IOUTotality

/-! # Brokers on the lending ledger

No transaction changes the vault's base exponent. A broker without loans can always be deleted, and a cover the
asset stores exactly comes back unchanged. -/

namespace XRPL.Model.Protocol

/-- The largest amount of an asset: its maximum for XRP or MPT, `cMaxValue·10^cMaxOffset` for an IOU. -/
def NumericType.maxAmount (nt : NumericType) : ℚ :=
  if nt.isIntegral then nt.maxValue.toNat else cMaxValue.toNat * 10 ^ cMaxOffset

/-- The largest IOU amount is `(10^16 - 1)·10^80`. -/
lemma NumericType.maxAmount_fractional : NumericType.fractional.maxAmount = (10 ^ 16 - 1) * 10 ^ 80 := by
  unfold NumericType.maxAmount
  rw [if_neg (by decide), show cMaxOffset = 80 from rfl, show cMaxValue.toNat = 9999999999999999 from rfl]
  norm_num

/-- Every asset's maximum is below `10^96`. -/
lemma NumericType.maxAmount_lt (nt : NumericType) : nt.maxAmount < 10 ^ 96 := by
  cases hint : nt.isIntegral
  · rw [NumericType.eq_fractional_of_not_integral hint, NumericType.maxAmount_fractional]
    norm_num
  · unfold NumericType.maxAmount
    rw [if_pos hint]
    have h : (nt.maxValue.toNat : ℚ) < 2 ^ 64 := by exact_mod_cast UInt64.toNat_lt_size nt.maxValue
    linarith [show (2 : ℚ) ^ 64 < 10 ^ 96 by norm_num]

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private STAmount.roundtrip_of_isRounded_false from XRPL.Properties.Protocol.STAmount.Common.Representable

/-- Every transaction keeps the vault's base exponent. -/
lemma LendingLedger.apply_baseExponent {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.vault.baseExponent = l.vault.baseExponent := by
  have hbe : ∀ v v' : Vault, v'.numericType = v.numericType → v'.scale = v.scale →
      v'.baseExponent = v.baseExponent := fun v v' h1 h2 => by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [h1, h2]
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]; exact hbe _ _ hk.numericType hk.scale
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    exact hbe _ _ hs.numericType hs.scale
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    rfl

/-- A broker without loans can be deleted. -/
private lemma LoanBroker.canDelete_empty (lb : LoanBroker) (v : Vault) (h0 : lb.loanCount = 0) :
    lb.canDelete v = .ok .tesSUCCESS := by
  have hd := lb.valid.empty_broker h0
  unfold LoanBroker.canDelete
  rw [h0, show lb.debtTotal = Number.zero from hd]
  rfl

/-- A broker without loans whose cover converts to the asset is deleted. -/
private lemma LendingLedger.broker_delete_ok (l : LendingLedger) (hnd : l.vaultDeleted = false) (j : Nat)
    (b : LoanBroker) (hb : l.broker? j = some b) (h0 : b.loanCount = 0) (c : STAmount)
    (hc : b.roundedCoverAvailable = .ok c) :
    (l.apply (.loanBrokerDelete j)).run = .ok (.ok (l.commitBroker { index := j, broker := none })) := by
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyBroker, hb]
  unfold_ter
  rw [LoanBroker.canDelete_empty b l.vault h0]
  simp only [hc]
  rfl

/-- A cover the asset stores exactly comes back unchanged. The delete converts it to the asset without
rounding. -/
lemma LoanBroker.roundedCoverAvailable_of_representable (lb : LoanBroker)
    (hrep : STAmount.Representable lb.numericType lb.coverAvailable.toRat) :
    ∃ c, lb.roundedCoverAvailable = .ok c ∧ c.toRat = lb.coverAvailable.toRat := by
  have hn := lb.wf.coverAvailable_norm
  have h0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  obtain ⟨st, n, hst, hnum, hval⟩ := STAmount.roundtrip_of_isRounded_false _ _ hn
    ((STAmount.isRounded_eq_false_iff _ _ hn h0).mpr hrep)
  refine ⟨st, hst, ?_⟩
  rw [← hval]
  by_cases hz : st.mValue = 0
  · -- a zero amount reads back as zero
    rw [STAmount.toRat_eq_zero_of_mValue_zero st hz]
    by_cases hint : lb.numericType.isIntegral = true
    · have hic := (STAmount.ofNumber_integral_canonical _ _ _ st hint hst).1
      rw [(STAmount.toNumber_exact_of st n (Or.inr ⟨hic, by rw [hz]; decide⟩) hnum).1,
        STAmount.toRat_eq_zero_of_mValue_zero st hz]
    · have hfr : st.integral = false := by
        unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ st hst]; simpa using hint
      rw [STAmount.toNumber_zero_fractional st _ hfr hz, Except.ok.injEq] at hnum
      rw [← hnum, Number.toRat_zero]
  · exact (STAmount.toNumber_exact_of st n (STAmount.ofNumber_exactCanonical _ _ _ st hn h0 hst hz) hnum).1.symm

/-- A cover within the asset's maximum converts to the asset, so LoanBrokerDelete can send it to the owner. -/
lemma LendingLedger.Reachable.roundedCoverAvailable_ok {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {b : LoanBroker} (hb : l.broker? j = some b) (hmax : b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ c, b.roundedCoverAvailable = .ok c := by
  have hnt : b.numericType = l.vault.numericType := hr.scaleInv.brokers j b hb
  cases hint : l.vault.numericType.isIntegral
  · -- an IOU cover is zero, or positive and below the largest IOU amount
    have hfr := NumericType.eq_fractional_of_not_integral hint
    rw [hfr, NumericType.maxAmount_fractional] at hmax
    have hn := b.wf.coverAvailable_norm
    unfold LoanBroker.roundedCoverAvailable
    rw [hnt, hfr]
    rcases b.exact.coverAvailable_nonneg.lt_or_eq with hpos | h0
    · exact STAmount.ofNumber_fractional_ok_below _ hn hpos (by linarith)
    · rw [(Number.toRat_eq_zero_iff_eq_zero hn).mp h0.symm, STAmount.ofNumber_fractional_zero]
      exact ⟨_, rfl⟩
  · unfold NumericType.maxAmount at hmax
    rw [if_pos hint] at hmax
    obtain ⟨c, hc, -⟩ := LoanBroker.roundedCoverAvailable_of_representable b
      (by rw [hnt]; exact hr.cover_representable_integral hint hb hmax)
    exact ⟨c, hc⟩

/-- Proof body of `Lending.broker_exit`. -/
lemma LendingLedger.broker_exit_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (j : Nat) (b : LoanBroker) (hb : l.broker? j = some b) (h0 : b.loanCount = 0)
    (hcap : l.vault.numericType.isIntegral = true → b.coverAvailable.toRat ≤ l.vault.numericType.maxValue.toNat)
    (c : STAmount) (hc : b.roundedCoverAvailable = .ok c) :
    (l.apply (.loanBrokerDelete j)).run = .ok (.ok (l.commitBroker { index := j, broker := none })) ∧
      (l.vault.numericType.isIntegral = true ∨ b.coverAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
        c.toRat = b.coverAvailable.toRat) := by
  refine ⟨LendingLedger.broker_delete_ok l hnd j b hb h0 c hc, fun hcase => ?_⟩
  suffices hrep : STAmount.Representable b.numericType b.coverAvailable.toRat by
    obtain ⟨c', hc', hval⟩ := LoanBroker.roundedCoverAvailable_of_representable b hrep
    obtain rfl := Except.ok.inj (hc.symm.trans hc')
    exact hval
  rw [hr.scaleInv.brokers j b hb]
  cases hint : l.vault.numericType.isIntegral
  · -- an IOU cover is whole base units, so below `10^16` of them it fits 16 digits
    have hlt := hcase.resolve_left (by rw [hint]; decide)
    have hfr := NumericType.eq_fractional_of_not_integral hint
    obtain ⟨n, hn⟩ := (hr.cover_onGrid hb).nat b.exact.coverAvailable_nonneg
    have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    have hn16 : n < 10 ^ 16 := by
      have : (n : ℚ) < 10 ^ 16 := lt_of_mul_lt_mul_right (by rw [← hn]; exact hlt) hp.le
      exact_mod_cast this
    obtain ⟨hlo, hhi, -⟩ := l.vault.baseExponent_bounds
    rw [hfr, hn]
    exact STAmount.representable_fractional_of_units n _ hn16 (by omega) (by omega)
  · exact hr.cover_representable_integral hint hb (hcap hint)

end XRPL.Model.Lending
