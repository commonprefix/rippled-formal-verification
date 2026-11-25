import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Walk

/-! # Share supply limit of a deposit

A deposit fails when its new shares take the shares outstanding past `2^63 - 1`, tested on two integers as in C++
`isMPTOverflow`. These lemmas restate the test on the exact totals. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The overflow test in whole numbers: the shares outstanding plus the new ones pass `2^63 - 1`. -/
lemma isMPTOverflow_iff (sendAmount outstandingAmount : UInt64) :
    isMPTOverflow sendAmount outstandingAmount = true ↔
      2 ^ 63 - 1 < outstandingAmount.toNat + sendAmount.toNat := by
  have hmax : maxRep.toNat = 2 ^ 63 - 1 := rfl
  unfold isMPTOverflow
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, gt_iff_lt, gt_iff_lt, UInt64.lt_iff_toNat_lt,
    UInt64.lt_iff_toNat_lt, hmax]
  by_cases hs : sendAmount.toNat ≤ 2 ^ 63 - 1
  · have hle : sendAmount ≤ maxRep := UInt64.le_iff_toNat_le.mpr (by rw [hmax]; exact hs)
    rw [UInt64.toNat_sub_of_le _ _ hle, hmax]
    omega
  · constructor
    · intro _; omega
    · intro _; exact Or.inl (by omega)

/-- An amount with offset 0 that is not below zero has its mantissa as value. -/
lemma STAmount.toRat_eq_mValue_of_nonneg (s : STAmount) (hoff : s.mOffset = 0) (h0 : 0 ≤ s.toRat) :
    s.toRat = (s.mValue.toNat : ℚ) := by
  by_cases hz : s.mValue = 0
  · rw [(STAmount.toRat_eq_zero_iff s).mpr hz, hz]; rfl
  · have hpos : 0 < s.mValue.toNat := by
      rcases Nat.eq_zero_or_pos s.mValue.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hz
      · exact h
    unfold STAmount.toRat at h0 ⊢
    rw [ite_eq_right hz] at h0 ⊢
    simp only [hoff, ge_iff_le, le_refl, ite_true, Int.toNat_zero, pow_zero, mul_one] at h0 ⊢
    cases hneg : s.mIsNegative
    · simp [Rat.mkRat_one]
    · rw [hneg] at h0
      simp only [ite_true, Rat.mkRat_one] at h0
      have : ((-1 * (s.mValue.toNat : ℤ) : ℤ) : ℚ) < 0 := by
        have hp : (0 : ℚ) < (s.mValue.toNat : ℚ) := by exact_mod_cast hpos
        push_cast; linarith
      exact absurd h0 (not_le.mpr this)

/-- The share total of a lawful vault converts into a share amount whose mantissa is the total. -/
lemma Vault.sharesTotal_amount_mValue (v : Vault) (sharesTotalAmount : STAmount)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    ((sharesTotalAmount.mValue.toNat : ℕ) : ℚ) = v.sharesTotal.toRat :=
  (STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest sharesTotalAmount v.wf.sharesTotal_norm
    v.wf.sharesTotal_nonneg v.wf.sharesTotal_int (Vault.sharesTotal_le_maxRep v) hst).2.2.2.1

/-- The share total of a lawful vault always converts into a share amount. -/
lemma Vault.sharesTotal_amount_ok (v : Vault) :
    ∃ sharesTotalAmount, STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount :=
  STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg)
    (Vault.sharesTotal_le_maxRep v)

/-- The deposit's share supply test on the exact totals: it fires when SharesTotal plus the new shares pass
`2^63 - 1`. -/
lemma Vault.shareSupply_overflow_iff (v : Vault) (shares sharesTotalAmount : STAmount)
    (hoff : shares.mOffset = 0) (h0 : 0 ≤ shares.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    isMPTOverflow shares.mValue sharesTotalAmount.mValue = true ↔
      (2 ^ 63 - 1 : ℚ) < v.sharesTotal.toRat + shares.toRat := by
  rw [isMPTOverflow_iff, ← Vault.sharesTotal_amount_mValue v sharesTotalAmount hst,
    STAmount.toRat_eq_mValue_of_nonneg shares hoff h0]
  constructor
  · intro h
    have : ((2 ^ 63 - 1 : ℕ) : ℚ) < ((sharesTotalAmount.mValue.toNat + shares.mValue.toNat : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  · intro h
    have : ((2 ^ 63 - 1 : ℕ) : ℚ) < ((sharesTotalAmount.mValue.toNat + shares.mValue.toNat : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- The shares a deposit computes have offset 0: an MPT amount, or none for a donation. -/
lemma computeDeposit_shares_offset (v : Vault) (roundedAmount : STAmount) (isDonation : Bool)
    (amounts : VaultAmounts) (hcomp : (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts)) :
    amounts.shares.mOffset = 0 := by
  cases isDonation
  · obtain ⟨_, _, ha2s, -⟩ := computeDeposit_success_reduces v roundedAmount amounts hcomp
    exact (assetsToSharesDeposit_int64_canonical v roundedAmount amounts.shares ha2s).1.offset_zero
  · obtain ⟨_, hsh, -⟩ := computeDeposit_donation_reduces v roundedAmount amounts hcomp
    rw [hsh]
    exact zero_int64_IntegralCanonical.offset_zero

/-- A share amount that passed the supply test keeps SharesTotal plus it within `2^63 - 1`. -/
lemma Vault.shareSupply_le (v : Vault) (shares sharesTotalAmount : STAmount) (hoff : shares.mOffset = 0)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfit : isMPTOverflow shares.mValue sharesTotalAmount.mValue = false) :
    v.sharesTotal.toRat + shares.toRat ≤ 2 ^ 63 - 1 := by
  rcases le_or_gt 0 shares.toRat with h0 | hneg
  · by_contra hlt
    have hov := (Vault.shareSupply_overflow_iff v shares sharesTotalAmount hoff h0 hst).mpr (not_le.mp hlt)
    rw [hfit] at hov
    exact absurd hov (by decide)
  · linarith [Vault.sharesTotal_le_maxRep v]

/-- The shares a deposit mints are a whole amount that is not below zero. -/
lemma Vault.deposit_minted_shares_form (v : Vault) (amountDeposit ra : STAmount) (isDonation : Bool)
    (amounts : VaultAmounts) (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts)) :
    amounts.shares.mOffset = 0 ∧ 0 ≤ amounts.shares.toRat := by
  obtain ⟨hrcz, -, hr0⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hrounded
  obtain ⟨_, -, -, hrz⟩ := roundedDepositAmount_rounded v amountDeposit ra hrounded
  have hrm : ra.mValue ≠ 0 := by simpa [STAmount.isZero] using hrz
  have hrc : ra.Canonical := hrcz.resolve_right (by simpa using hrz)
  have hrp : 0 < ra.toRat := lt_of_le_of_ne hr0 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
  obtain ⟨hic, -, h0⟩ := computeDeposit_shares_form v ra isDonation amounts hrc hrp hcomp
  exact ⟨hic.offset_zero, h0⟩

/-- A successful deposit keeps SharesTotal plus the minted shares within the share MPT maximum. -/
lemma Vault.deposit_ok_shareSupply (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    v.sharesTotal.toRat + r.shares.toRat ≤ 2 ^ 63 - 1 := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  have hcomp : (computeDeposit v _ isDonation).run = .ok (.ok _) := ‹computeDeposit v _ isDonation = _›
  exact Vault.shareSupply_le v _ _ (computeDeposit_shares_offset v _ isDonation _ hcomp) ‹_›
    (Bool.eq_false_iff.mpr ‹_›)

/-- The same bound on the exact share total. -/
lemma Vault.deposit_ok_shareSupply_exact (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 := by
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  exact Vault.deposit_ok_shareSupply v amountDeposit isDonation t hpos r hok

end XRPL.Model.SingleAssetVault
