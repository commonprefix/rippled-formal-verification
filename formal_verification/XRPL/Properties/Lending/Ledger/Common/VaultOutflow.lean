import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # What a withdrawal or a clawback takes from the vault

Both pay a nonnegative amount of the asset out of AssetsAvailable and leave the lent-out balances alone.
The asset stores AssetsAvailable exactly, so the rounded new value never rises above the old one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault WithdrawAmount VaultWithAmounts computeClawback_success_reduces)

/-- Rounding a negative value to an asset gives at most zero. -/
private lemma STAmount.roundToNumericType_nonpos (nt : NumericType) (x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (hx : x.isNormalized) (hx0 : x.toRat < 0)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.toRat ≤ 0 := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, -⟩ := STAmount.ofNumber_canonicalOrZero nt x _ st hmax hof
    rw [(hcz.toNumber_exact y hok).1]
    have hneg : x.negative_ = true := by
      by_contra h
      have := Number.toRat_nonneg_of_nonnegative x (by simpa using h)
      linarith
    cases hint : nt.isIntegral
    · exact STAmount.ofNumber_signtrue_nonpos nt x _ st hint hx hneg hof
    · exact STAmount.ofNumber_integral_negative_nonpos nt x _ st hint hneg hof

/-- Rounding a value to an asset never lands above an amount the asset stores exactly and that bounds the
value. -/
private lemma STAmount.roundToNumericType_le_stored (nt : NumericType) (w x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (hw : w.isNormalized) (hw0 : 0 ≤ w.toRat)
    (hst : STAmount.isRounded nt w = false) (hx : x.isNormalized) (hxw : x.toRat ≤ w.toRat)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.toRat ≤ w.toRat := by
  by_cases hx0 : x.toRat < 0
  · exact (STAmount.roundToNumericType_nonpos nt x y hmax hx hx0 hok).trans hw0
  push Not at hx0
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero nt x _ st hmax hof
    rw [(hcz.toNumber_exact y hok).1]
    by_cases hz : st.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hz]; exact hw0
    unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hst
    cases ha : STAmount.ofNumber nt w .to_nearest with
    | error e => rw [ha] at hst; exact absurd hst (by simp)
    | ok a =>
      rw [ha] at hst
      simp only [bind, Except.bind, pure, Except.pure] at hst
      cases hn : a.toNumber .to_nearest with
      | error e => rw [hn] at hst; exact absurd hst (by simp)
      | ok n =>
        rw [hn] at hst
        have heq : n.operator_eq w = true := by simpa using hst
        obtain ⟨hnv, hnn⟩ := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ha).1.toNumber_exact n hn
        have hav : a.toRat = w.toRat := by rw [← hnv]; exact (operator_eq_iff _ _ hnn hw).mp heq
        by_cases ha0 : a.mValue = 0
        · -- a zero bound leaves only a zero value, which converts to zero
          have hw0' : w.toRat = 0 := by rw [← hav, STAmount.toRat_eq_zero_of_mValue_zero _ ha0]
          have hxz : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp (by linarith)
          subst hxz
          exact absurd (STAmount.ofNumber_source_ne_zero nt _ _ st hof hz) (by decide)
        have hac := STAmount.ofNumber_exactCanonical nt w .to_nearest a hw hw0 ha ha0
        have hat := STAmount.ofNumber_mNumericType nt w .to_nearest a ha
        rw [← hav]
        exact STAmount.ofNumber_to_nearest_le_of_canonical nt x st a hx hx0 hac hat (by rw [hav]; exact hxw) hof hz

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
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.roundsToRepresentable_le s _ (operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hnorm hs)
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
