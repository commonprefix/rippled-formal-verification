import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.WithdrawExits

/-! # A withdrawal that checks the holder's shares

The ledger passes the holder's shares to `Vault.withdraw`, which rejects a holder who owns fewer than it redeems
(C++ VaultWithdraw.cpp:432). When the check passes, the withdrawal is the one the vault lemmas describe. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

set_option maxHeartbeats 400000 in
-- the proof goes through every path of the withdrawal and the holder check, about twice the default limit
/-- A withdrawal that checks the holder's shares succeeds only as the unchecked one does, and the holder owns the
shares it redeems. -/
lemma Vault.withdraw_holder_ok (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (held : Number) (r : VaultWithAmounts)
    (h : (v.withdraw amount waive t hpos (some held)).run = .ok (.ok r)) :
    (v.withdraw amount waive t hpos).run = .ok (.ok r) ∧
      ∀ s, r.shares.toNumber .to_nearest = .ok s → held.operator_lt s = false := by
  simp only [Vault.withdraw] at h ⊢
  unfold_ter at h ⊢
  walk_ok
  all_goals
    refine ⟨?_, fun s hs => ?_⟩
    · simp_all only [↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, not_false_eq_true]
    · simp_all only [Except.ok.injEq, Bool.not_eq_true]

/-- A holder who owns the shares the withdrawal redeems passes the check, so the checked withdrawal is the
unchecked one. -/
lemma Vault.withdraw_holder_eq (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (held : Number)
    (hpass : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      ∃ s, amounts.shares.toNumber .to_nearest = .ok s ∧ held.operator_lt s = false) :
    (v.withdraw amount waive t hpos (some held)).run = (v.withdraw amount waive t hpos).run := by
  simp only [Vault.withdraw]
  unfold_ter
  simp only [ExceptT.run] at hpass
  rcases hc : computeWithdraw v amount waive with _ | _ | amounts
  · rfl
  · rfl
  · obtain ⟨s, hs, hlt⟩ := hpass amounts hc
    simp only [hs, hlt, Bool.false_eq_true, ↓reduceIte]

/-- A final withdrawal while AssetsDeployed ≠ 0 is rejected with tecHAS_OBLIGATIONS before the holder check. -/
lemma Vault.withdraw_has_obligations_holder (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (holderShares : Option Number) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount)
    (hsoon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hcomp : (computeWithdraw v amount waive).run = .ok (.ok amounts))
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : amounts.shares.operator_eq sharesTotalAmount = true)
    (hdeployed : v.assetsDeployed.operator_ne Number.zero = true) :
    (v.withdraw amount waive t hpos holderShares).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  simp only [Vault.withdraw]
  unfold_ter
  simp only [ExceptT.run] at hcomp
  simp [hsoon, hcomp, hst, hfinal, hdeployed]

set_option maxHeartbeats 400000 in
-- the proof goes through every path of the withdrawal and the holder check, about twice the default limit
/-- A withdrawal that checks the holder's shares never ends in `notLawful` when the holder owns at most
SharesTotal and a final withdrawal finds the cash stored exactly. -/
lemma Vault.withdraw_holder_ne_notLawful (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (held : Number)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hn : held.isNormalized) (hbal : held.toRat ≤ v.toExact.sharesTotal)
    (hexact : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toRat = v.toExact.sharesTotal → STAmount.isRounded v.numericType v.assetsAvailable = false) :
    (v.withdraw amount waive t hpos (some held)).run ≠ .error .notLawful := by
  by_cases hpass : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      ∃ s, amounts.shares.toNumber .to_nearest = .ok s ∧ held.operator_lt s = false
  · rw [Vault.withdraw_holder_eq v amount waive t hpos held hpass]
    refine Vault.withdraw_lawful v amount waive t hpos hc hty hmax (fun a ha => ?_) hexact
    obtain ⟨s, hs, hlt⟩ := hpass a ha
    obtain ⟨hsic, hs64, -⟩ := computeWithdraw_shares_form v amount waive a hc hty hpos ha
    obtain ⟨sn, hsn, hv, hsnorm, -⟩ :=
      STAmount.toNumber_integral_exact a.shares .to_nearest hsic (by rw [hs64]; decide)
    rw [hs, Except.ok.injEq] at hsn
    subst hsn
    rw [← hv]
    exact le_trans ((operator_lt_eq_false_iff _ _ hn hsnorm).mp hlt) hbal
  · intro h
    push Not at hpass
    obtain ⟨a, ha, hfail⟩ := hpass
    simp only [Vault.withdraw] at h
    unfold_ter at h
    simp only [ExceptT.run] at ha
    simp only [ha] at h
    walk_ok
    -- a helper never returns `notLawful`, and a path past the holder check contradicts `hfail`
    all_goals first
      | (simp only [STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful,
          Vault.assetsTotalForWithdrawal_ne_notLawful, Vault.checkDebitNotDust_ne_notLawful,
          tenthBipsOfValue_ne_notLawful, Number.operator_sub_ne_notLawful, clampToSumExponent_ne_notLawful,
          STAmount.isFractionalNonPositive_ne_notLawful] at *; done)
      | exact absurd (Bool.eq_false_iff.mpr ‹¬ held.operator_lt _ = true›) (hfail _ ‹_›)

set_option maxHeartbeats 400000 in
-- the proof goes through every path of the withdrawal and the holder check, about twice the default limit
/-- A holder who owns the shares a successful withdrawal redeems passes the check, with the same result. -/
lemma Vault.withdraw_holder_of_ok (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (held : Number) (r : VaultWithAmounts)
    (h : (v.withdraw amount waive t hpos).run = .ok (.ok r)) (s : Number)
    (hs : r.shares.toNumber .to_nearest = .ok s) (hlt : held.operator_lt s = false) :
    (v.withdraw amount waive t hpos (some held)).run = .ok (.ok r) := by
  simp only [Vault.withdraw] at h ⊢
  unfold_ter at h ⊢
  walk_ok
  all_goals simp_all only [↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, not_false_eq_true]

end XRPL.Model.SingleAssetVault
