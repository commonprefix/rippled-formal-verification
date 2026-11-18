import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve
import XRPL.Properties.Vault.Proofs.Support.GridFloor
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # The vault update a withdrawal makes

A withdrawal subtracts its payout from the cash and its burned shares from the share total. A final
withdrawal pays out all the cash. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A non-final withdrawal pays nothing, or pays through the fee: it prices the burned shares, takes
the fee from that rounding up, rounds the rest down into the asset and clamps it onto the grid of the cash left. -/
lemma Vault.withdraw_payout_cases (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      ((r.assets.toRat = 0 ∧ (v.earlyExitFeeRateAt t = maxEarlyExitFeeRate ∨ priced.toRat = 0)) ∨
        ∃ (pricedNumber fee payoutNumber paidNumber : Number) (payout : STAmount),
          v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
          priced.toNumber .to_nearest = .ok pricedNumber ∧
          tenthBipsOfValue pricedNumber (v.earlyExitFeeRateAt t) .upward = .ok fee ∧
          pricedNumber.operator_sub fee .downward = .ok payoutNumber ∧
          STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout ∧
          payout.isZero = false ∧
          clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok r.assets ∧
          r.assets.isFractionalNonPositive = .ok false ∧
          r.assets.toNumber .to_nearest = .ok paidNumber ∧
          v.assetsAvailable.operator_lt paidNumber = false) := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals dsimp only at hlt hsic hs64 hspos ⊢
  -- the run is not final
  all_goals
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hnf : ¬ STAmount.operator_eq _ _ = true :=
      (Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).not.mpr (ne_of_lt hlt)
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok _) := ‹_›
    refine ⟨_, computeWithdraw_ok_priced v amount waive _ hcomp, ?_⟩
  · -- a 100% fee pays nothing
    have hmaxr : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = true := ‹_›
    exact Or.inl ⟨STAmount.zero_toRat _, Or.inl (beq_iff_eq.mp hmaxr)⟩
  · -- the last check passed: the clamped payout is not a nonpositive fractional amount
    have hfnp0 : STAmount.isFractionalNonPositive _ = .ok _ := ‹_›
    have hfnp := hfnp0.trans (congrArg Except.ok (show _ = false by assumption))
    have hlow : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false := ‹_›
    exact Or.inr ⟨_, _, _, _, _, fun h => by rw [h] at hlow; exact absurd hlow (by decide),
      ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hfnp, ‹_›, ‹_›⟩
  · -- a zero priced amount pays nothing
    have hnz : ¬ (_ = false ∧ STAmount.isZero _ = false) := ‹_›
    simp only [hnf, true_and, Bool.not_eq_false] at hnz
    unfold STAmount.isZero at hnz
    have h0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa using hnz)
    exact Or.inl ⟨h0, Or.inr h0⟩

/-- A nonzero fractional clamp floors the amount onto the grid of the cash it leaves, a grid no
finer than the base grid. -/
lemma Vault.clamp_floor (v : Vault) (X clamped : STAmount) (hX : X.CanonicalOrZero)
    (hXt : X.mNumericType = .fractional) (hX0 : 0 ≤ X.toRat) (hnz : clamped.mValue ≠ 0)
    (hcl : clampToSumExponent v.assetsAvailable X.operator_neg v.baseExponent = .ok clamped) :
    ∃ (dN : Number) (e : ℤ), X.operator_neg.toNumber .to_nearest = .ok dN ∧
      postSumExponent v.assetsAvailable dN v.baseExponent .fractional = .ok e ∧ v.baseExponent ≤ e ∧
      clamped.toRat = (⌊X.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e := by
  have hpf : X.operator_neg.FracCanonZero :=
    STAmount.operator_neg_fczr _ (hX.fracCanonZero (by unfold STAmount.integral; rw [hXt]; rfl))
  obtain ⟨dN, e, hdN, hps, hge, hfl⟩ := clampToSumExponent_frac_floor _ _ _ _ hpf
    v.baseExponent_range.1 v.baseExponent_range.2 hnz hcl
  have hnt : X.operator_neg.numericType = .fractional := by
    show X.operator_neg.mNumericType = _
    rw [(STAmount.operator_neg_fields X).1, hXt]
  rw [hnt] at hps
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hX0] at hfl
  exact ⟨dN, e, hdN, hps, hge, hfl⟩

/-- Proof of `Vault.withdraw_final_iff`. -/
lemma Vault.withdraw_final_iff_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.shares.toRat = v.toExact.sharesTotal ↔
      r.vault'.toRawVault = { v.toRawVault with assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  have hST := Vault.withdraw_sharesTotal v amount waive t hpos hc hty r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨aa', st', hfr⟩ := Vault.withdraw_frame v amount waive t hpos r hok
  have hAA : r.vault'.assetsAvailable = aa' := (congrArg RawVault.assetsAvailable hfr).trans rfl
  have hSTv : r.vault'.sharesTotal = st' := (congrArg RawVault.sharesTotal hfr).trans rfl
  constructor
  · intro hfin
    have hst0 : r.vault'.sharesTotal = Number.zero :=
      Number.eq_zero_of_mantissa_zero _ r.vault'.wf.sharesTotal_norm
        (Number.toRat_eq_zero_iff.mp (by rw [hST, ← hcast, hfin]; ring))
    have haa0 := (r.vault'.valid.empty_shares hst0).1
    rw [hfr, ← hAA, ← hSTv, haa0, hst0]
  · intro h
    have hst0 : r.vault'.sharesTotal = Number.zero := congrArg RawVault.sharesTotal h
    rw [hst0, Number.toRat_zero] at hST
    rw [hcast]
    linarith

/-- A reachable vault stores its cash exactly and deploys nothing, so the final payout is all the cash and the whole
share total is worth exactly that. -/
lemma Vault.withdraw_final_payout_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.idealAssetsWithdraw waive r.shares.toRat := by
  obtain ⟨hpay, -, -⟩ := Vault.withdraw_final_proof v amount waive t t0 hpos hr hc hty hmax r hok hfinal
  obtain ⟨-, -, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  obtain ⟨atot, nav, hat, hnav, hq⟩ := Vault.Reachable.withdrawNavExact_proof v t0 hr waive
  have hsub : v.assetsTotalForWithdrawal waive = .ok nav := by
    simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, hat]; exact hnav
  have hST : (v.toExact.sharesTotal : ℚ) ≠ 0 := by rw [← hfinal]; exact ne_of_gt hspos
  rw [hpay]
  unfold RawVault.idealAssetsWithdraw
  rw [hfinal, mul_div_assoc, div_self hST, mul_one, ← hq]
  exact (Vault.Reachable.nav_eq_cash v t0 hr waive nav hsub).symm

end XRPL.Model.SingleAssetVault
