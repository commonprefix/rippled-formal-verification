import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder
import XRPL.Properties.Vault.Proofs.TotalStored

/-! # What a withdrawal or a clawback takes from the vault

Both pay a nonnegative amount of the asset out of AssetsAvailable and leave the lent-out balances alone.
The asset stores AssetsAvailable exactly, so the rounded new value never rises above the old one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault WithdrawAmount VaultWithAmounts computeClawback_success_reduces)

/-- Rounding a value to an asset never lands above an amount the asset stores exactly and that bounds the
value. -/
private lemma STAmount.roundToNumericType_le_stored (nt : NumericType) (w x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (hw : w.isNormalized) (hw0 : 0 ≤ w.toRat)
    (hst : STAmount.isRounded nt w = false) (hx : x.isNormalized) (hxw : x.toRat ≤ w.toRat)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.toRat ≤ w.toRat :=
  XRPL.Model.Protocol.STAmount.roundToNumericType_le_of_stored nt w x y hmax hw hw0 hst hx hxw hok

/-- A debit of a nonnegative amount of the asset leaves AssetsAvailable at most what it was, when the asset
stores AssetsAvailable exactly. -/
private lemma Vault.debit_le (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false) (hc : assets.CanonicalOrZero)
    (h0 : 0 ≤ assets.toRat) (hadj : (v.adjustAssetsAndShares assets.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ := hc.operator_neg.toNumber_exact assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hv
  have hsn := Number.operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.roundsToRepresentable_le s _ (Number.operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hnorm
      hs)
      _ v.wf.assetsAvailable_norm (by rw [hv]; linarith)
  exact STAmount.roundToNumericType_le_stored _ _ _ _ hmax v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg
    hst hsn hsle haa

/-- A withdrawal pays a nonnegative amount of the asset, and its update of AssetsAvailable debits that
amount. -/
private lemma Vault.withdraw_payout_nonneg (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ 0 ≤ r.assets.toRat ∧ ∃ raw : RawVault,
      (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
        r.vault'.toRawVault = raw := by
  simp only [XRPL.Model.SingleAssetVault.Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a 100% fee pays nothing
  all_goals try
    have hz := STAmount.zero_canonicalOrZero v.numericType
    exact ⟨hz.1, by rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)], _, ‹_›,
      (RawVault.to_lawful_ok ‹_›).1⟩
  -- the final withdrawal pays all of AssetsAvailable
  all_goals try
    have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
    exact ⟨(STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1,
      STAmount.ofNumber_nonneg _ _ _ _ v.wf.assetsAvailable_norm
        (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg) hp,
      _, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩
  -- the fee path pays the payout clamped onto the grid of AssetsAvailable
  all_goals try
    have hp : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    have hpc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1
    obtain ⟨hcf, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    exact ⟨hcf, hc0, _, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩
  -- a zero payout skips the fee
  all_goals
    have hnf : STAmount.operator_eq _ _ = false := ‹_›
    have hzs : ¬ (STAmount.operator_eq _ _ = false ∧ STAmount.isZero _ = false) := ‹_›
    have hz0 := Bool.of_not_eq_false (fun h => hzs ⟨hnf, h⟩)
    exact ⟨Or.inr hz0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz0)], _, ‹_›,
      (RawVault.to_lawful_ok ‹_›).1⟩

/-- A clawback recovers a nonnegative amount of the asset, and its update of AssetsAvailable debits that
amount. -/
private lemma Vault.clawback_payout_nonneg (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ 0 ≤ r.assets.toRat ∧ ∃ raw : RawVault,
      (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
        r.vault'.toRawVault = raw := by
  obtain ⟨amounts, raw, hcomp, hadj, hraw, hras, hrs⟩ :=
    Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  rw [hras, hrs]
  refine ⟨?_, ?_, raw, hadj, hraw⟩ <;>
  · obtain ⟨recovered, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
    have hrc : recovered.CanonicalOrZero := by
      cases hpr with
      | direct _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
      | capped _ _ _ _ _ _ _ _ _ _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
    rcases hrec with ⟨hz, heq⟩ | ⟨-, hcl, -⟩
    · first
        | exact heq ▸ Or.inr hz
        | rw [heq, (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]
    · obtain ⟨hcf, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg v.baseExponent_range.1
        v.baseExponent_range.2 hcl
      first
        | exact hcf
        | exact hc0

/-- Proof body of `Lending.lent_out_protected`. -/
lemma LendingLedger.lent_out_protected_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (htx : (∃ holder amount, tx = .vaultWithdraw holder amount) ∨ ∃ holder assets, tx = .vaultClawback holder assets)
    (h : (l.apply tx).run = .ok (.ok l')) :
    0 ≤ l'.vault.assetsAvailable.toRat ∧ l'.vault.assetsAvailable.toRat ≤ l.vault.assetsAvailable.toRat ∧
      l'.vault.assetsDeployed = l.vault.assetsDeployed := by
  have hv : tx.isVault = true := by
    rcases htx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
  have hvault : (l.commitVault u).vault = u.vault := by
    unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
  rw [hvault]
  have hk := l.applyVault_keepsLending tx u hu
  have hst := hr.storesAvailable hmax
  refine ⟨u.vault.exact.assetsAvailable_nonneg, ?_, hk.assetsDeployed⟩
  rcases htx with ⟨holder, amount, rfl⟩ | ⟨holder, assets, rfl⟩
  · simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      all_goals
        obtain ⟨hc, h0, raw, hadj, hraw⟩ := Vault.withdraw_payout_nonneg _ _ _ _ _ hmax _
          (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
        calc _ = raw.assetsAvailable.toRat := by rw [← hraw]
          _ ≤ _ := Vault.debit_le _ _ _ raw hmax hst hc h0 hadj
    · cases hu
  · simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      all_goals
        obtain ⟨hc, h0, raw, hadj, hraw⟩ := Vault.clawback_payout_nonneg _ _ _ _ _ hmax _ ‹_›
        calc _ = raw.assetsAvailable.toRat := by rw [← hraw]
          _ ≤ _ := Vault.debit_le _ _ _ raw hmax hst hc h0 hadj
    · cases hu

end XRPL.Model.Lending
