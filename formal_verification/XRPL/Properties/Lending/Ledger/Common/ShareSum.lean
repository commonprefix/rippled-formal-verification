import XRPL.Properties.Lending.Ledger.Common.SharesNonneg
import XRPL.Properties.Lending.Ledger.Common.RecheckVault
import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.WithdrawUpdates

/-! # Holder shares add up to SharesTotal

A deposit adds the shares it mints to the holder and to SharesTotal, a withdrawal or a clawback takes the same
shares off both, and a burn takes the holding off SharesTotal. While deposits keep SharesTotal within the share MPT
maximum every amount is a whole number below `2^63`, so nothing rounds. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultWithAmounts)

/-- The holders' shares add up to SharesTotal, and each holder owns a whole number of shares. -/
structure LendingLedger.SharesSum (l : LendingLedger) : Prop where
  sum : (l.shares.map Number.toRat).sum = l.vault.sharesTotal.toRat
  whole : ∀ x ∈ l.shares, x.toRat.den = 1

/-- Every deposit on the ledger keeps SharesTotal plus the shares it mints within the share MPT maximum. -/
def LendingLedger.MintFits (l : LendingLedger) : Prop :=
  ∀ (amount : STAmount) (isDonation : Bool) (hpos : 0 < amount.toRat) (r : VaultWithAmounts),
    (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok r) →
    l.vault.sharesTotal.toRat + r.shares.toRat ≤ 2 ^ 63 - 1

/-- A holder's shares are a whole number, zero for a holder the ledger doesn't list. -/
lemma LendingLedger.SharesSum.sharesOf_whole {l : LendingLedger} (hl : l.SharesSum) (h : Nat) :
    (l.sharesOf h).toRat.den = 1 := by
  unfold LendingLedger.sharesOf
  rw [List.getD_eq_getElem?_getD]
  cases hx : l.shares[h]? with
  | none => rw [Option.getD_none, Number.toRat_zero]; rfl
  | some x => exact hl.whole x (List.mem_of_getElem? hx)

/-- A holder owns at most SharesTotal when no holder owns less than zero. -/
lemma LendingLedger.SharesSum.sharesOf_le {l : LendingLedger} (hl : l.SharesSum) (hn : l.SharesNonneg) (h : Nat) :
    (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat := by
  rw [← hl.sum]
  have hall : ∀ q ∈ l.shares.map Number.toRat, 0 ≤ q := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact (hn x hx).2
  unfold LendingLedger.sharesOf
  rw [List.getD_eq_getElem?_getD]
  cases hx : l.shares[h]? with
  | none => rw [Option.getD_none, Number.toRat_zero]; exact List.sum_nonneg hall
  | some x => exact List.single_le_sum hall _ (List.mem_map_of_mem (List.mem_of_getElem? hx))

/-- Replacing one entry of a list of rationals changes its sum by the new entry less the old one. -/
private lemma List.sum_set_rat (L : List ℚ) (i : Nat) (a : ℚ) (hi : i < L.length) :
    (L.set i a).sum = L.sum - L[i] + a := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero, List.sum_cons, List.getElem_cons_zero]; ring
    | succ i =>
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      rw [ih i (by simpa using hi)]
      ring

/-- Setting holder `h` to `n` changes the sum of the holdings by `n` less the old holding. -/
private lemma LendingLedger.setShares_sum (l : LendingLedger) (h : Nat) (n : Number) :
    ((l.setShares h n).shares.map Number.toRat).sum =
      (l.shares.map Number.toRat).sum - (l.sharesOf h).toRat + n.toRat := by
  unfold LendingLedger.setShares LendingLedger.sharesOf
  dsimp only
  have hlen : h < (l.shares ++ List.replicate (h + 1 - l.shares.length) Number.zero).length := by
    simp only [List.length_append, List.length_replicate]; omega
  have hpsum : ((l.shares ++ List.replicate (h + 1 - l.shares.length) Number.zero).map Number.toRat).sum =
      (l.shares.map Number.toRat).sum := by
    simp [List.map_replicate, Number.toRat_zero]
  have hget : (l.shares ++ List.replicate (h + 1 - l.shares.length) Number.zero)[h] = l.shares.getD h Number.zero := by
    by_cases hh : h < l.shares.length
    · rw [List.getElem_append_left hh, List.getD_eq_getElem _ _ hh]
    · rw [List.getElem_append_right (by omega), List.getElem_replicate, List.getD_eq_default _ _ (by omega)]
  rw [List.map_set, List.sum_set_rat _ h _ (by simpa using hlen), hpsum, List.getElem_map, hget]

/-- Setting one holder keeps the sum when SharesTotal moves by the change in that holding. -/
private lemma LendingLedger.SharesSum.setShares {l : LendingLedger} (hl : l.SharesSum) (v' : Vault) (h : Nat)
    (n : Number) (hn : n.toRat.den = 1)
    (hST : v'.sharesTotal.toRat = l.vault.sharesTotal.toRat - (l.sharesOf h).toRat + n.toRat) :
    ({ l with vault := v' }.setShares h n).SharesSum where
  sum := by
    rw [LendingLedger.setShares_sum]
    show (l.shares.map Number.toRat).sum - (l.sharesOf h).toRat + n.toRat = v'.sharesTotal.toRat
    rw [hl.sum, hST]
  whole := by
    intro x hx
    unfold LendingLedger.setShares at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · rcases List.mem_append.mp hx with hx | hx
      · exact hl.whole x hx
      · rw [List.eq_of_mem_replicate hx, Number.toRat_zero]; rfl
    · exact hn

open XRPL.Model.SingleAssetVault in
/-- A deposit mints a whole number of shares of at least zero. -/
private lemma Vault.deposit_shares_whole (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (r : VaultWithAmounts)
    (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.shares.CanonicalOrZero ∧ r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat := by
  obtain ⟨ra, amounts, -, hra, hcomp, -, -, -, -, hrs⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r h
  obtain ⟨hrc, hrp⟩ := DepRnd.Vault.roundedDepositAmount_canonical_pos v amount ra hc hra
  rw [hrs]
  obtain ⟨hic, hty, h0⟩ := computeDeposit_shares_form v ra isDonation amounts hrc hrp hcomp
  exact ⟨Or.inl (hic.canonical (by rw [hty]; decide)), hic.den_eq_one, h0⟩

/-- The holder's shares as an amount of shares: a canonical MPT amount of at least zero, of the same value. -/
private lemma LendingLedger.holder_shareBalance (l : LendingLedger) (hr : l.Reachable) (hl : l.SharesSum) (h : Nat)
    (hs : STAmount) (hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs) :
    hs.ShareBalance ∧ hs.IntegralCanonical ∧ hs.toRat = (l.sharesOf h).toRat := by
  obtain ⟨hn, h0⟩ := hr.sharesNonneg.sharesOf h
  obtain ⟨hty, -, hneg, -, hval⟩ := STAmount.ofNumber_int64_shape _ _ _ hn h0 (hl.sharesOf_whole h)
    (le_trans (hl.sharesOf_le hr.sharesNonneg h) l.vault.sharesTotal_le_maxRep) hof
  have hic := (STAmount.ofNumber_integral_canonical _ _ _ _ (by decide) hof).1
  exact ⟨⟨hty, hic.canonical (by rw [hty]; decide), hneg⟩, hic, hval⟩

/-- Taking `burned` whole shares off the holding and off SharesTotal moves SharesTotal by the change in the
holding. The new SharesTotal is at least zero, so `burned` is within SharesTotal and nothing rounds. -/
private lemma LendingLedger.holder_sub_exact (l : LendingLedger) (hr : l.Reachable) (hl : l.SharesSum) (h : Nat)
    (burned shares' : Number) (v' : Vault) (hb : burned.isNormalized) (hbd : burned.toRat.den = 1)
    (hb0 : 0 ≤ burned.toRat) (hST : v'.sharesTotal.toRat = l.vault.sharesTotal.toRat - burned.toRat)
    (hsub : (l.sharesOf h).operator_sub burned .to_nearest = .ok shares') :
    shares'.toRat.den = 1 ∧
      v'.sharesTotal.toRat = l.vault.sharesTotal.toRat - (l.sharesOf h).toRat + shares'.toRat := by
  obtain ⟨hn, h0⟩ := hr.sharesNonneg.sharesOf h
  have hle := hl.sharesOf_le hr.sharesNonneg h
  have hmax := l.vault.sharesTotal_le_maxRep
  have hd := hl.sharesOf_whole h
  have hv0 := v'.wf.sharesTotal_nonneg
  obtain ⟨hv, hvd⟩ := operator_sub_exact_int _ _ _ hn hb hd hbd
    (Rat.num_natAbs_lt (Rat.den_one_sub _ _ hd hbd) (by linarith) (by linarith)) hsub
  exact ⟨hvd, by rw [hST, hv]; ring⟩

open XRPL.Model.SingleAssetVault in
/-- A vault transaction moves SharesTotal by the change in the holding it writes. -/
private lemma LendingLedger.applyVault_sharesSum (l : LendingLedger) (hr : l.Reachable) (hl : l.SharesSum)
    (tx : LendingTx) (hfit : (∃ h amount isDonation, tx = .vaultDeposit h amount isDonation) → l.MintFits)
    (hpre : (tx.preflight l).isTesSuccess = true)
    (u : VaultEffect) (hu : (l.applyVault tx).run = .ok (.ok u)) :
    (∀ p ∈ u.holderShares, p.2.toRat.den = 1 ∧
      u.vault.sharesTotal.toRat = l.vault.sharesTotal.toRat - (l.sharesOf p.1).toRat + p.2.toRat) ∧
    (u.holderShares = none → u.vault.sharesTotal.toRat = l.vault.sharesTotal.toRat) := by
  have hpre' := (TER.isTesSuccess_iff _).mp hpre
  cases tx with
  | vaultDeposit h amount isDonation =>
    obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit_canonical l hr.holdsAsset h amount isDonation hpre'
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · rename_i hpos
      unfold_ter at hu
      walk_ok
      refine ⟨fun p hp => ?_, fun hn => by cases hn⟩
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hdep : (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok _) := ‹_›
      obtain ⟨hsc, hsd, hs0⟩ := Vault.deposit_shares_whole _ _ _ _ _ hc _ hdep
      have hmn : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      obtain ⟨hmv, hmn'⟩ := hsc.toNumber_exact _ hmn
      have hfit' := hfit ⟨h, amount, isDonation, rfl⟩ amount isDonation hpos _ hdep
      have hcast := RawVault.WF.toExact_sharesTotal _ l.vault.wf
      have hST := Vault.deposit_exact_sharesTotal _ _ _ _ hpos hc hty _ hdep (by rw [hcast]; exact hfit')
      rw [RawVault.WF.toExact_sharesTotal _ (VaultWithAmounts.vault' _).wf, hcast] at hST
      obtain ⟨hn, h0⟩ := hr.sharesNonneg.sharesOf h
      have hle := hl.sharesOf_le hr.sharesNonneg h
      have hd := hl.sharesOf_whole h
      have hmd := hsd
      rw [← hmv] at hmd
      obtain ⟨hv, hvd⟩ := operator_add_exact_int _ _ _ hn hmn' hd hmd
        (Rat.num_natAbs_lt (Rat.den_one_add _ _ hd hmd) (by linarith) (by linarith)) ‹_›
      exact ⟨hvd, by rw [hST, hv, hmv]; ring⟩
    · cases hu
  | vaultWithdraw h amount =>
    obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset h amount hpre'
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · rename_i hpos
      unfold_ter at hu
      walk_ok
      refine ⟨fun p hp => ?_, fun hn => by cases hn⟩
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hw := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
      obtain ⟨hsc, hs64, hspos⟩ := Vault.withdraw_shares_form _ _ _ _ hpos hc hty _ hw
      have hST := Vault.withdraw_sharesTotal _ _ _ _ hpos hc hty _ hw
      have hburn : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      obtain ⟨hbv, hbn⟩ := STAmount.CanonicalOrZero.toNumber_exact
        (Or.inl (hsc.canonical (by rw [hs64]; decide))) _ hburn
      have hbd := hsc.den_eq_one
      have hb0 := le_of_lt hspos
      rw [← hbv] at hbd hST hb0
      exact l.holder_sub_exact hr hl h _ _ _ hbn hbd hb0 hST ‹_›
    · cases hu
  | vaultClawback h assets =>
    have hc := LendingTx.preflight_vaultClawback_canonical l hr.holdsAsset h assets hpre'
    have hmax := hr.holdsAsset.maxValue_le
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · rename_i hnn
      unfold_ter at hu
      walk_ok
      refine ⟨fun p hp => ?_, fun hn => by cases hn⟩
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
      obtain ⟨hhs, -, -⟩ := l.holder_shareBalance hr hl h _ hof
      have hcl : (l.vault.clawback assets _ (l.isSoleShareholder h) hnn).run = .ok (.ok _) := ‹_›
      have hST := Vault.clawback_exact_sharesTotal _ _ _ _ hnn hc hhs hmax _ hcl
      rw [RawVault.WF.toExact_sharesTotal _ (VaultWithAmounts.vault' _).wf,
        RawVault.WF.toExact_sharesTotal _ l.vault.wf] at hST
      obtain ⟨amounts, raw, hcomp, -, -, -, hrsh⟩ := Vault.clawback_ok_reduces _ _ _ _ hnn _ hcl
      obtain ⟨hic, h64, h0, -, -⟩ := computeClawback_amounts_form _ _ _ _ _ hc hnn hhs hmax hcomp
      rw [← hrsh] at hic h64 h0
      have hdes : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      obtain ⟨hdv, hdn⟩ := STAmount.CanonicalOrZero.toNumber_exact
        (Or.inl (hic.canonical (by rw [h64]; decide))) _ hdes
      have hdd := hic.den_eq_one
      rw [← hdv] at hdd hST h0
      exact l.holder_sub_exact hr hl h _ _ _ hdn hdd h0 hST ‹_›
    · cases hu
  | vaultBurnShares h amount =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    refine ⟨fun p hp => ?_, fun hn => by cases hn⟩
    simp only [Option.mem_def, Option.some.injEq] at hp
    subst hp
    have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
    obtain ⟨hhs, hic, hval⟩ := l.holder_shareBalance hr hl h _ hof
    have hb : (l.vault.burnShares _).run = .ok (.ok _) := ‹_›
    have hST := Vault.burnShares_sharesTotal_exact_proof _ _ _ hb hic hhs.nonneg (by
      rw [hval, RawVault.WF.toExact_sharesTotal _ l.vault.wf]; exact hl.sharesOf_le hr.sharesNonneg h)
    rw [RawVault.WF.toExact_sharesTotal _ (Vault.wf _), RawVault.WF.toExact_sharesTotal _ l.vault.wf, hval] at hST
    refine ⟨by rw [Number.toRat_zero]; rfl, ?_⟩
    rw [hST, Number.toRat_zero]
    ring
  | vaultSet assetsMaximum blockDeposit unblockDeposit =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    refine ⟨fun p hp => (by cases hp), fun _ => ?_⟩
    have hupd : l.vault.update assetsMaximum blockDeposit unblockDeposit = .ok _ := ‹_›
    unfold Vault.update at hupd
    have hraw := congrArg RawVault.sharesTotal (RawVault.to_lawful_ok hupd).1
    exact congrArg Number.toRat hraw
  | _ => simp only [LendingLedger.applyVault] at hu; cases hu

/-- Every transaction keeps the holders' shares adding up to SharesTotal, given that a deposit fits. -/
private lemma LendingLedger.SharesSum.step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (hl : l.SharesSum) (hfit : (∃ h amount isDonation, tx = .vaultDeposit h amount isDonation) → l.MintFits)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.SharesSum := by
  by_cases hv : tx.isVault = true
  · have hpre := (LendingLedger.apply_checked h).1
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    obtain ⟨hsome, hnone⟩ := l.applyVault_sharesSum hr hl tx hfit hpre u hu
    unfold LendingLedger.commitVault
    cases hs : u.holderShares with
    | none => exact ⟨by rw [hnone hs]; exact hl.sum, hl.whole⟩
    | some p =>
      obtain ⟨i, n⟩ := p
      obtain ⟨hn, hST⟩ := hsome (i, n) hs
      exact hl.setShares u.vault i n hn hST
  by_cases hb : tx.isBroker = true
  · obtain ⟨-, hsh, hvault, -⟩ := LendingLedger.broker_ops_scope_proof l l' tx hb h
    exact ⟨by rw [hsh, hvault]; exact hl.sum, by rw [hsh]; exact hl.whole⟩
  by_cases hlo : tx.isLoan = true
  · obtain ⟨-, -, hsh, hST, -⟩ := LendingLedger.loan_ops_scope_proof l l' tx hlo h
    exact ⟨by rw [hsh, hST]; exact hl.sum, by rw [hsh]; exact hl.whole⟩
  have h' := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, not_true_eq_false] at hv hb hlo
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h'
    unfold_ter at h'
    walk_ok
    exact ⟨hl.sum, hl.whole⟩
  · simp only [LendingLedger.applyChecked] at h'
    unfold_ter at h'
    walk_ok
    exact ⟨hl.sum, hl.whole⟩

/-- A transaction other than a deposit keeps the holders' shares adding up to SharesTotal. -/
lemma LendingLedger.SharesSum.step_of_not_deposit {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (hl : l.SharesSum) (hnd : ∀ h amount isDonation, tx ≠ .vaultDeposit h amount isDonation)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.SharesSum :=
  hl.step hr (fun ⟨h, amount, isDonation, he⟩ => absurd he (hnd h amount isDonation)) h

/-- While shares exist and the holders' shares add up to SharesTotal, some holder owns some. -/
lemma LendingLedger.SharesSum.exists_holder {l : LendingLedger} (hl : l.SharesSum)
    (hS : 0 < l.vault.sharesTotal.toRat) : ∃ h, 0 < (l.sharesOf h).toRat := by
  rw [← hl.sum] at hS
  by_contra hne
  push Not at hne
  have hle : (l.shares.map Number.toRat).sum ≤ 0 := by
    refine le_trans (List.sum_le_card_nsmul _ 0 fun q hq => ?_) (by simp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hne i
    unfold LendingLedger.sharesOf at this
    rwa [List.getD_eq_getElem _ _ hi] at this
  linarith

end XRPL.Model.Lending
