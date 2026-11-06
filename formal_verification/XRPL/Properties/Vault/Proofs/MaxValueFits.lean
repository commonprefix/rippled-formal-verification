import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.OpenZone
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.WithdrawUpdates
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.Support.Errors
import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.WithdrawExchange
import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout
import XRPL.Properties.Vault.Proofs.Support.ComputeClawback
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Protocol.Number.Signum.Signum

/-! # The asset of a reachable vault with shares fits an `int64` amount

A vault's asset never changes along a history, and every vault with shares took a deposit of a
canonical amount in that asset, which bounds an integral asset's maximum by `maxRep`. A reachable
vault without shares holds no cash. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A lawful vault with no shares holds no cash. -/
lemma Vault.assetsAvailable_eq_zero_of_no_shares (v : Vault) (hS : (v.toExact.sharesTotal : ℚ) = 0) :
    v.assetsAvailable = Number.zero :=
  (Number.toRat_eq_zero_iff_eq_zero v.wf.assetsAvailable_norm).mp
    (v.exact.empty_shares (by exact_mod_cast hS)).1

/-- A lawful vault with no shares stores the zero `Number` as its share total. -/
lemma Vault.sharesTotal_eq_zero_of_no_shares (v : Vault) (hS : (v.toExact.sharesTotal : ℚ) = 0) :
    v.sharesTotal = Number.zero := by
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf] at hS
  exact (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp hS

/-- A reachable vault with no shares is in the Open zone: nothing is lent out and there is no cash. -/
lemma Vault.Reachable.openZone_of_no_shares (v : Vault) (t : UInt32) (hr : Vault.Reachable v t)
    (hS : (v.toExact.sharesTotal : ℚ) = 0) : v.OpenZone := by
  obtain ⟨hAD, hLU, hYU⟩ := Vault.Reachable.noLending_proof v t hr
  have hAA := Vault.assetsAvailable_eq_zero_of_no_shares v hS
  exact ⟨hAD, hLU, hYU, ⟨0, by norm_num, by rw [hAA, Number.toRat_zero]; simp⟩,
    by rw [hAA]; exact STAmount.isRounded_zero _⟩

/-- A successful withdrawal burns a positive amount of shares, so the vault had shares. -/
lemma Vault.withdraw_sharesTotal_pos (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  have h := Vault.withdraw_exact_sharesTotal v amount waive t hpos hc hty r hok
  have hs := (Vault.withdraw_shares_form v amount waive t hpos hc hty r hok).2.2
  have h0 : (0 : ℚ) ≤ r.vault'.toExact.sharesTotal := Nat.cast_nonneg _
  linarith

/-- A burn the vault allows reads an insolvent vault, which has shares. -/
lemma Vault.canBurnShares_sharesTotal_pos (v : Vault) (amount holderShares sharesTotalAmount : STAmount)
    (hok : (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount)) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  have hins := (Vault.canBurnShares_ok_reduces v amount holderShares sharesTotalAmount hok).1
  simp only [Vault.isInsolvent, Bool.and_eq_true, decide_eq_true_eq] at hins
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  exact (signum_eq_one_iff _ v.wf.sharesTotal_norm).mp hins.2

/-- On a reachable vault with no shares, the clawback pricing accepts only a zero amount that names
the holder's balance: there is no cash, so every other request prices to no shares. -/
private lemma Vault.Reachable.clawback_no_shares_names_holder (v : Vault) (t0 : UInt32)
    (hr : Vault.Reachable v t0) (hS : (v.toExact.sharesTotal : ℚ) = 0) (assets holderShares : STAmount)
    (waive : Bool) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    assets.isZero = true ∧ r.shares = holderShares ∧ holderShares.isZero = false := by
  have hAA := Vault.assetsAvailable_eq_zero_of_no_shares v hS
  have hST := Vault.sharesTotal_eq_zero_of_no_shares v hS
  have hnav : v.assetsTotalForWithdrawal waive = .ok Number.zero := by
    rw [(Vault.Reachable.openZone_of_no_shares v t0 hr hS).assetsTotalForWithdrawal_eq waive, hAA]
  obtain ⟨amounts, -, hcomp, -, -, -, hrsh⟩ :=
    Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  have hnz : amounts.shares.isZero = false := by
    by_contra h
    have := Vault.clawback_zero_shares_proof v assets holderShares waive hnn
      (Vault.clawback_ok_not_native v assets holderShares waive hnn r hok) amounts hcomp
      (Bool.of_not_eq_false h)
    rw [hok] at this
    exact absurd this (by simp)
  -- the shares a request names, when they are not zero
  have hnamed : ∀ shares, assetsToSharesClawback v assets holderShares waive = .ok shares →
      shares.isZero = false → assets.isZero = true ∧ shares = holderShares := by
    intro shares ha2s hsz
    simp only [assetsToSharesClawback, bind, Except.bind, pure, Except.pure] at ha2s
    walk_ok
    · -- the share total, which is zero
      exfalso
      obtain ⟨-, -, -, -, hval⟩ := STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest shares
        v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg v.wf.sharesTotal_int v.sharesTotal_le_maxRep ‹_›
      rw [hST, Number.toRat_zero] at hval
      exact (STAmount.isZero_eq_false_iff _).mp hsz ((STAmount.toRat_eq_zero_iff _).mp hval)
    · exact ⟨‹_›, rfl⟩
    · -- the shares the assets are worth: nothing
      exfalso
      have h : assetsToSharesWithdraw v assets true waive = .ok shares := ‹_›
      simp only [assetsToSharesWithdraw, hnav, bind, Except.bind, pure, Except.pure,
        show (Number.zero.mantissa_ == 0) = true from rfl, if_true, Except.ok.injEq] at h
      subst h
      exact (STAmount.isZero_eq_false_iff _).mp hsz (STAmount.zero_mValue _)
  obtain ⟨recovered, -, hpr, -, -, -⟩ :=
    computeClawback_success_reduces v assets holderShares waive amounts hcomp
  cases hpr with
  | direct shares recovered n ha2s hs2a hn hgt =>
    obtain ⟨hz, heq⟩ := hnamed _ ha2s hnz
    exact ⟨hz, hrsh.trans heq, heq ▸ hnz⟩
  | capped shares0 recovered0 cash shares recovered n0 n ha2s0 hs2a0 hn0 hgt0 hcash ha2s hs2a hn hgt =>
    -- the first recovery is zero, which never exceeds the cash
    exfalso
    rw [Vault.sharesToAssetsWithdraw_zero_nav_proof v shares0 waive Number.zero hnav rfl,
      Except.ok.injEq] at hs2a0
    subst hs2a0
    obtain ⟨hn0v, hn0n⟩ := STAmount.CanonicalOrZero.toNumber_exact (STAmount.zero_canonicalOrZero _).1 n0 hn0
    rw [STAmount.zero_toRat] at hn0v
    rw [(Number.toRat_eq_zero_iff_eq_zero hn0n).mp hn0v, hAA] at hgt0
    exact absurd hgt0 (by decide)

/-- A successful clawback of a nonzero amount from a reachable vault finds shares: with no shares
there is no cash, and the amount is worth no shares. -/
lemma Vault.Reachable.clawback_sharesTotal_pos_of_nonzero (v : Vault) (t0 : UInt32)
    (hr : Vault.Reachable v t0) (assets holderShares : STAmount) (waive : Bool)
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  by_contra hS
  have hS0 : (v.toExact.sharesTotal : ℚ) = 0 := le_antisymm (not_lt.mp hS) (Nat.cast_nonneg _)
  have := (Vault.Reachable.clawback_no_shares_names_holder v t0 hr hS0 assets holderShares waive hnn r hok).1
  rw [hznz] at this
  exact Bool.false_ne_true this

/-- A successful clawback from a reachable vault finds shares: with no shares there is no cash, and
the only request that prices to shares names the holder's balance, which the vault cannot burn. -/
lemma Vault.Reachable.clawback_sharesTotal_pos (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hhs : holderShares.ShareBalance)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  by_contra hS
  have hS0 : (v.toExact.sharesTotal : ℚ) = 0 := le_antisymm (not_lt.mp hS) (Nat.cast_nonneg _)
  obtain ⟨-, hrs, hnz⟩ :=
    Vault.Reachable.clawback_no_shares_names_holder v t0 hr hS0 assets holderShares waive hnn r hok
  -- the vault burns the holder's shares from a zero total, which no lawful vault survives
  obtain ⟨amounts, raw, -, hadj, hraw, -, hrsh⟩ :=
    Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  rw [hrsh] at hrs
  rw [hrs] at hadj
  have hic : holderShares.IntegralCanonical :=
    (hhs.canonical.1 (by simp only [STAmount.integral, hhs.int64]; decide)).1
  have hb := abs_le.mp (hic.abs_le_int64 hhs.int64)
  have hST : v.sharesTotal.toRat = 0 := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; exact hS0
  have hst := Vault.adjustAssetsAndShares_sharesTotal v _ _ raw
    (STAmount.CanonicalOrZero.operator_neg (Or.inl hhs.canonical))
    (by rw [STAmount.operator_neg_toRat, Rat.neg_den]; exact hic.den_eq_one)
    (by rw [STAmount.operator_neg_toRat, hST]; linarith)
    (by rw [STAmount.operator_neg_toRat, hST]; linarith) hadj
  rw [STAmount.operator_neg_toRat, hST] at hst
  have h0 : 0 ≤ raw.sharesTotal.toRat := by rw [← hraw]; exact r.vault'.wf.sharesTotal_nonneg
  have hhs0 := STAmount.toRat_nonneg_of _ hhs.nonneg
  exact (STAmount.isZero_eq_false_iff _).mp hnz ((STAmount.toRat_eq_zero_iff _).mp (by linarith))

/-- A reachable vault with shares has an asset whose integral maximum fits an `int64` amount. The
asset never changes along the history, and the shares came from a deposit of a canonical amount in it. -/
lemma Vault.Reachable.maxValue_fits (v : Vault) (t : UInt32) (hr : Vault.Reachable v t)
    (hs : 0 < (v.toExact.sharesTotal : ℚ)) :
    v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
  revert hs
  induction hr with
  | create _ _ _ _ _ _ _ w _ hcr =>
    intro hs
    have hST : w.sharesTotal = Number.zero := (congrArg RawVault.sharesTotal (Vault.create_ok_toRawVault hcr)).trans rfl
    rw [RawVault.WF.toExact_sharesTotal w.toRawVault w.wf, hST, Number.toRat_zero] at hs
    exact absurd hs (lt_irrefl 0)
  | deposit u _ _ _ _ r _ _ hc hty _ hok _ _ =>
    intro _
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    rw [hnt]
    exact Vault.maxValue_fits_of_canonical u _ hc hty
  | withdraw u _ _ amount _ _ r _ _ hc hty _ _ hpos hok _ ih =>
    intro _
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    rw [hnt]
    exact ih (Vault.withdraw_sharesTotal_pos u amount _ _ hpos hc hty r hok)
  | clawback u _ _ assets holderShares waive r hru _ _ _ hhs _ hnn hok _ ih =>
    intro _
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    rw [hnt]
    exact ih (Vault.Reachable.clawback_sharesTotal_pos u _ hru assets holderShares waive hhs hnn r hok)
  | burnShares u _ _ amount holderShares sharesTotalAmount u' _ _ _ hcan hok ih =>
    intro _
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    rw [hnt]
    exact ih (Vault.canBurnShares_sharesTotal_pos u amount holderShares sharesTotalAmount hcan)
  | update u _ _ _ _ _ u' _ _ _ hok ih =>
    intro hs
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hST : u'.sharesTotal = u.sharesTotal := (congrArg RawVault.sharesTotal hv).trans rfl
    rw [hnt]
    refine ih ?_
    rwa [RawVault.WF.toExact_sharesTotal u'.toRawVault u'.wf, hST,
      ← RawVault.WF.toExact_sharesTotal u.toRawVault u.wf] at hs

/-- Every reachable vault has an asset whose integral maximum fits an `int64` amount, or no shares. -/
lemma Vault.Reachable.maxValue_fits_or_no_shares (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∨
      (v.toExact.sharesTotal : ℚ) = 0 := by
  rcases (Nat.cast_nonneg v.toExact.sharesTotal : (0 : ℚ) ≤ _).lt_or_eq with h | h
  · exact Or.inl (Vault.Reachable.maxValue_fits v t hr h)
  · exact Or.inr h.symm

/-- Every reachable vault is in the Open zone. A vault with shares has an asset that fits, and a
vault without shares has no cash. -/
lemma Vault.Reachable.openZone (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) : v.OpenZone := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t hr with hmax | hS
  · exact Vault.Reachable.openZone_proof v t hr hmax
  · exact Vault.Reachable.openZone_of_no_shares v t hr hS

lemma Vault.Reachable.assetsAvailable_exact_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    STAmount.isRounded v.numericType v.assetsAvailable = false :=
  (Vault.Reachable.openZone v t hr).cashExact

lemma Vault.Reachable.assetsAvailable_le_openLimit_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) :=
  (Vault.Reachable.openZone v t hr).assetsAvailable_le_openLimit

/-- A withdrawal the model rejects as unlawful priced its shares: the rejection comes from the cash
update. -/
lemma Vault.withdraw_notLawful_reduces (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (h : (v.withdraw amount waive t hpos).run = .error .notLawful) :
    ∃ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) := by
  simp only [Vault.withdraw] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a helper never returns `notLawful`
  all_goals try first
    | exact (computeWithdraw_ne_notLawful _ _ _ ‹_›).elim
    | exact (Vault.adjustAssetsAndShares_ne_notLawful _ _ _ ‹_›).elim
    | (simp only [STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful,
        Vault.assetsTotalForWithdrawal_ne_notLawful, Vault.checkDebitNotDust_ne_notLawful,
        tenthBipsOfValue_ne_notLawful, Number.operator_sub_ne_notLawful, clampToSumExponent_ne_notLawful,
        STAmount.isFractionalNonPositive_ne_notLawful] at *)
  all_goals exact ⟨_, ‹_›⟩

/-- A clawback the model rejects as unlawful priced its shares, a nonzero amount: the rejection comes
from the cash update. -/
lemma Vault.clawback_notLawful_reduces (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (h : (v.clawback assets holderShares waive hnn).run = .error .notLawful) :
    ∃ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) ∧
      amounts.shares.isZero = false := by
  simp only [Vault.clawback] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  -- a helper never returns `notLawful`
  all_goals try first
    | exact (computeClawback_ne_notLawful _ _ _ _ ‹_›).elim
    | exact (Vault.adjustAssetsAndShares_ne_notLawful _ _ _ ‹_›).elim
    | (simp only [STAmount.toNumber_ne_notLawful, Vault.checkDebitNotDust_ne_notLawful] at *)
  all_goals exact ⟨_, ‹_›, ‹_›⟩

/-- Proof of the final success line of `Vault.withdraw_exits`. With shares the asset fits and the final payout is the
cash, stored exactly. Without shares the pricing burns a positive amount, so it cannot burn every share. -/
lemma Vault.withdraw_final_success_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hfinal : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toRat = v.toExact.sharesTotal) :
    (v.withdraw amount waive t hpos).run ≠ .error .notLawful := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t0 hr with hmax | hS
  · exact Vault.withdraw_lawful v amount waive t hpos hc hty hmax (fun a h => le_of_eq (hfinal a h))
      (fun _ _ _ => (Vault.Reachable.openZone_proof v t0 hr hmax).cashExact)
  · intro h
    obtain ⟨amounts, hcomp⟩ := Vault.withdraw_notLawful_reduces v amount waive t hpos h
    have hs := (computeWithdraw_shares_form v amount waive amounts hc hty hpos hcomp).2.2
    rw [hfinal amounts hcomp, hS] at hs
    exact lt_irrefl _ hs

/-- Proof of the final success line of `Vault.clawback_exits`. With shares the asset fits and a clawback of every share
recovers all the cash. Without shares the pricing names a nonzero amount, so it cannot name every share. -/
lemma Vault.clawback_final_success_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (t0 : UInt32) (hnn : 0 ≤ assets.toRat) (hr : Vault.Reachable v t0) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.ShareBalance)
    (hfinal : ∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.toRat = v.toExact.sharesTotal) :
    (v.clawback assets holderShares waive hnn).run ≠ .error .notLawful := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t0 hr with hmax | hS
  · exact Vault.clawback_lawful v assets holderShares waive hnn hc hhs hmax (fun a h => le_of_eq (hfinal a h))
      (fun a h heq => by
        rw [STAmount.operator_neg_toRat,
          Vault.Reachable.computeClawback_final v t0 hr hmax assets holderShares waive hc hnn hhs a h heq]
        ring)
  · intro h
    obtain ⟨amounts, hcomp, hnz⟩ := Vault.clawback_notLawful_reduces v assets holderShares waive hnn h
    have h0 := hfinal amounts hcomp
    rw [hS] at h0
    exact (STAmount.isZero_eq_false_iff _).mp hnz ((STAmount.toRat_eq_zero_iff _).mp h0)

/-- Per-share value is never negative: the net asset value and the share count are nonnegative. -/
lemma Vault.perShareValue_nonneg (v : Vault) : 0 ≤ v.withdrawNav / (v.toExact.sharesTotal : ℚ) := by
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  show 0 ≤ v.toExact.assetsTotal - v.toExact.lossUnrealized
  have := v.exact.lossUnrealized_le
  have := v.exact.assetsAvailable_nonneg
  unfold RawVault.Exact.assetsTotal
  linarith

/-- `ReachableFromIn.no_dilution` from a vault without shares: its per-share value is `0`, so nothing can be lost. -/
lemma Vault.ReachableFromIn.no_dilution_of_no_shares (v : Vault) (hS : (v.toExact.sharesTotal : ℚ) = 0) (w : Vault) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥ v.withdrawNav / (v.toExact.sharesTotal : ℚ) := by
  rw [hS, div_zero]
  exact Vault.perShareValue_nonneg w

end XRPL.Model.SingleAssetVault
