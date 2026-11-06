import XRPL.Properties.Lending.Ledger.Common.WindDownLoans
import XRPL.Properties.Lending.Ledger.Common.HolderRedeemIntegral
import XRPL.Properties.Lending.Ledger.Common.ShareSum
import XRPL.Properties.Lending.Ledger.Common.PayoffExit
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Ledger.Common.WindDownProofs

/-! # Winding a vault down to its deletion

Once every loan is closed, the brokers leave, each holder but the last redeems all its shares, the last holder
takes all the cash, and VaultDelete finds nothing left. On an MPT vault of `2.5·10^17` units or more the last holder
first redeems all but a few shares, then the rest. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule VaultWithAmounts WithdrawAmount)

open private LendingLedger.broker_delete_ok from XRPL.Properties.Lending.Ledger.Common.BrokerProofs

/-- A whole number of shares, positive and at most `2^63 - 1`, as the int64 amount a VaultWithdraw names. The
amount keeps its value and passes the preflight. -/
private lemma LendingLedger.sharesAmount (l : LendingLedger) (h : Nat) (x : Number) (hx : x.isNormalized)
    (hpos : 0 < x.toRat) (hwhole : x.toRat.den = 1) (hcap : x.toRat ≤ 2 ^ 63 - 1) :
    ∃ S : STAmount, S.toRat = x.toRat ∧ S.Canonical ∧ S.mNumericType = .int64 ∧
      (LendingTx.vaultWithdraw h (.vaultShares S)).preflight l = .tesSUCCESS := by
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok x .to_nearest hx (Number.negative_false_of_pos _ hpos) hcap
  obtain ⟨hsic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ S (by decide) hS
  have hSv : S.toRat = x.toRat := STAmount.ofNumber_integral_exact .int64 _ _ S (by decide) hx hwhole hS
  have hSpos : 0 < S.toRat := by rw [hSv]; exact hpos
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
  obtain ⟨hc, -⟩ := isCanonicalAmount_canonical S .int64 (fun _ => by decide) hcan hSm
  exact ⟨S, hSv, hc, hty, by simp [LendingTx.preflight, hcan, isPositiveAmount, hSneg, hSm]⟩

/-- A holder written by a vault transaction holds the shares it was written. -/
private lemma LendingLedger.sharesOf_commit_self (l : LendingLedger) (v : Vault) (h : Nat) (d : Number) :
    (l.commitVault { vault := v, holderShares := some (h, d) }).sharesOf h = d := by
  unfold LendingLedger.commitVault LendingLedger.setShares LendingLedger.sharesOf
  simp only
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_set_self]

/-- A redemption the vault accepts from a holder who owns the shares is the ledger's. The holder keeps its
shares less the redeemed ones. -/
private lemma LendingLedger.apply_redeem (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (h : Nat) (hwhole : (l.sharesOf h).toRat.den = 1) (hheldcap : (l.sharesOf h).toRat ≤ 2 ^ 63 - 1)
    (S : STAmount) (hc : S.Canonical) (hty : S.mNumericType = .int64)
    (hpre : (LendingTx.vaultWithdraw h (.vaultShares S)).preflight l = .tesSUCCESS)
    (hpos : 0 < (WithdrawAmount.vaultShares S).amount.toRat) (r : VaultWithAmounts)
    (hw : (l.vault.withdraw (.vaultShares S) (l.isSoleShareholder h) l.now hpos).run = .ok (.ok r))
    (hrs : r.shares = S) (hcover : S.toRat ≤ (l.sharesOf h).toRat) :
    ∃ d : Number, (l.apply (.vaultWithdraw h (.vaultShares S))).run =
        .ok (.ok (l.commitVault { vault := r.vault', holderShares := some (h, d) })) ∧
      d.toRat = (l.sharesOf h).toRat - S.toRat := by
  obtain ⟨hheldn, -⟩ := hr.sharesNonneg.sharesOf h
  have hSpos : 0 < S.toRat := hpos
  have hsic : S.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hcap : S.toRat ≤ 2 ^ 63 - 1 := by
    have := STAmount.IntegralCanonical.abs_le_int64 hsic hty
    rw [abs_of_pos hSpos] at this
    exact this
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical S .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  have hlt' : (l.sharesOf h).operator_lt sn = false := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff _ _ hheldn hsnn, hsnv]
    exact not_lt.mpr hcover
  have hheld0 : 0 ≤ (l.sharesOf h).toRat := le_trans hSpos.le hcover
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_normalized_cap (l.sharesOf h) sn .to_nearest hheldn hsnn
    (Number.negative_false_of_nonneg _ hheldn hheld0) (Number.negative_false_of_pos _ (by rw [hsnv]; exact hSpos))
    hheldcap (by rw [hsnv]; exact hcap)
  have hsnd : sn.toRat.den = 1 := by rw [hsnv]; exact hsic.den_eq_one
  have hdiff : ((l.sharesOf h).toRat - sn.toRat).den = 1 := by
    have h' : (l.sharesOf h).toRat - sn.toRat = (((l.sharesOf h).toRat.num - sn.toRat.num : ℤ) : ℚ) := by
      rw [Int.cast_sub, Rat.coe_int_num_of_den_eq_one hwhole, Rat.coe_int_num_of_den_eq_one hsnd]
    rw [h']; exact Rat.den_intCast _
  obtain ⟨hdv, -⟩ := operator_sub_exact_int _ _ _ hheldn hsnn hwhole hsnd
    (Rat.num_natAbs_lt hdiff (by rw [hsnv]; linarith) (by rw [hsnv]; linarith)) hd
  refine ⟨d, ?_, by rw [hdv, hsnv]⟩
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, Bool.false_eq_true, ↓reduceIte,
    LendingLedger.applyVault, hpos, ↓reduceDIte]
  unfold_ter
  have hwh := Vault.withdraw_holder_of_ok _ _ _ _ _ _ _ hw sn (by rw [hrs]; exact hsn) hlt'
  simp only [ExceptT.run] at hwh
  rw [hwh]
  simp only [hrs, hsn, hd]
  rfl

/-- The redemption phase charges no early-exit fee and lets withdrawals run. -/
private lemma Vault.redemption_open {v : Vault} {t : UInt32} (hph : v.phase t = .redemption) :
    (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false ∧ v.earlyExitFeeRateAt t = 0 := by
  refine ⟨by rw [hph]; simp, ?_⟩
  unfold Vault.earlyExitFeeRateAt
  rw [hph]
  cases v.earlyExitFeeRate <;> rfl

/-- A holder redeems all its shares while others hold some, on a reachable ledger with a settled vault in its
redemption phase, when the shares are worth at least one unit at the scale of the cash or the vault has no cash. -/
lemma LendingLedger.redeem_part (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hph : l.vault.phase l.now = .redemption) (hz : l.vault.Settled) (h : Nat)
    (hwhole : (l.sharesOf h).toRat.den = 1) (hpos : 0 < (l.sharesOf h).toRat)
    (hlt : (l.sharesOf h).toRat < l.vault.sharesTotal.toRat)
    (hworth : 0 < l.vault.assetsAvailable.toRat →
      ∀ E, numberExponent l.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok E →
        (10 : ℚ) ^ E ≤ (l.sharesOf h).toRat * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal) :
    ∃ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') ∧
      (l'.vault.toExact.sharesTotal : ℚ) = l.vault.toExact.sharesTotal - (l.sharesOf h).toRat ∧
      l'.vault.assetsAvailable.toRat ≤ l.vault.assetsAvailable.toRat := by
  have hmax := hr.holdsAsset.maxValue_le
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  have hSTle := Vault.sharesTotal_le_maxRep l.vault
  obtain ⟨hheldn, -⟩ := hr.sharesNonneg.sharesOf h
  obtain ⟨S, hSv, hc, hty, hpre⟩ := l.sharesAmount h _ hheldn hpos hwhole (by linarith)
  have hpos' : 0 < (WithdrawAmount.vaultShares S).amount.toRat := by show 0 < S.toRat; rw [hSv]; exact hpos
  obtain ⟨hopen, hfee⟩ := Vault.redemption_open hph
  obtain ⟨r, hw, hrs, haa⟩ := Vault.Settled.withdraw_part_ok l.vault l.now hz hmax (l.isSoleShareholder h) hopen hfee
    S hc hty hpos' (by rw [hSv, hcast]; exact hlt) (fun hA E hE => by rw [hSv]; exact hworth hA E hE)
  obtain ⟨d, hok, -⟩ := l.apply_redeem hr hnd h hwhole (by linarith) S hc hty hpre hpos' r hw hrs (le_of_eq hSv)
  have hST' := Vault.withdraw_exact_sharesTotal l.vault _ _ _ hpos' hc (by exact hty) r hw
  exact ⟨S, _, hSv, hok, by show (r.vault'.toExact.sharesTotal : ℚ) = _; rw [hST', hrs, hSv], haa⟩

/-- In redemption, on an XRP or MPT vault with nothing lent or lost, a holder redeems `n` shares worth at least one
unit while the shares left are worth at least 20. The cash drops by at least their worth less 20. -/
lemma LendingLedger.redeem_some_integral (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hph : l.vault.phase l.now = .redemption) (hint : l.vault.numericType.isIntegral = true)
    (hAD : l.vault.assetsDeployed = Number.zero) (hLU : l.vault.lossUnrealized = Number.zero) (h n : Nat)
    (hwhole : (l.sharesOf h).toRat.den = 1) (hheldcap : (l.sharesOf h).toRat ≤ 2 ^ 63 - 1) (hn1 : 1 ≤ n)
    (hle : (n : ℚ) ≤ (l.sharesOf h).toRat) (hlt : (n : ℚ) < l.vault.toExact.sharesTotal)
    (hworth : 1 ≤ n * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal)
    (hkeep : 20 ≤ (l.vault.toExact.sharesTotal - n) * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal) :
    ∃ (shares : STAmount) (l' : LendingLedger), shares.toRat = n ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') ∧
      (l'.vault.toExact.sharesTotal : ℚ) = l.vault.toExact.sharesTotal - n ∧
      l'.vault.assetsAvailable.toRat ≤
        l.vault.assetsAvailable.toRat - n * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal + 20 ∧
      (l'.sharesOf h).toRat = (l.sharesOf h).toRat - n := by
  have hmax := hr.holdsAsset.maxValue_le
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  have hSTle := Vault.sharesTotal_le_maxRep l.vault
  have hn63 : (n : ℚ) ≤ 2 ^ 63 - 1 := by rw [hcast] at hlt; linarith
  obtain ⟨x, hx, hxv⟩ := Number.exists_normalized_of_int (n : ℤ) (by
    have h1 : (n : ℚ) < 2 ^ 63 := by linarith
    have h2 : n < 2 ^ 63 := by exact_mod_cast h1
    simpa using h2)
  have hxv' : x.toRat = n := by rw [hxv]; push_cast; rfl
  obtain ⟨S, hSv, hc, hty, hpre⟩ := l.sharesAmount h x hx (by rw [hxv']; exact_mod_cast hn1)
    (by rw [hxv']; exact Rat.den_natCast _) (by rw [hxv']; exact hn63)
  rw [hxv'] at hSv
  have hpos' : 0 < (WithdrawAmount.vaultShares S).amount.toRat := by
    show 0 < S.toRat; rw [hSv]; exact_mod_cast hn1
  obtain ⟨hopen, hfee⟩ := Vault.redemption_open hph
  obtain ⟨r, hw, hrs, haa, hpay⟩ := Vault.withdraw_part_ok_integral l.vault l.now hint hmax hAD hLU
    hr.availableStored (l.isSoleShareholder h) hopen hfee S hc hty hpos' (by rw [hSv]; exact hlt)
    (by rw [hSv]; exact hworth) (by rw [hSv]; exact hkeep)
  obtain ⟨d, hok, hdv⟩ := l.apply_redeem hr hnd h hwhole hheldcap S hc hty hpre hpos' r hw hrs
    (by rw [hSv]; exact hle)
  have hST' := Vault.withdraw_exact_sharesTotal l.vault _ _ _ hpos' hc (by exact hty) r hw
  refine ⟨S, _, hSv, hok, by show (r.vault'.toExact.sharesTotal : ℚ) = _; rw [hST', hrs, hSv], ?_, ?_⟩
  · show r.vault'.assetsAvailable.toRat ≤ _
    have := (abs_le.mp hpay).1
    rw [hSv] at this
    rw [haa]
    linarith
  · rw [LendingLedger.sharesOf_commit_self, hdv, hSv]

/-- The last holder redeems its single share on an XRP or MPT vault with nothing lent or lost, in the redemption
phase. It takes all the cash and leaves no cash and no shares. -/
lemma LendingLedger.redeem_one_share (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hph : l.vault.phase l.now = .redemption) (hint : l.vault.numericType.isIntegral = true)
    (hAD : l.vault.assetsDeployed = Number.zero) (hLU : l.vault.lossUnrealized = Number.zero) (h : Nat)
    (hS : l.vault.toExact.sharesTotal = 1) (hheld : (l.sharesOf h).toRat = 1) :
    ∃ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') ∧
      l'.vault.assetsAvailable = Number.zero ∧ l'.vault.sharesTotal = Number.zero := by
  have hmax := hr.holdsAsset.maxValue_le
  obtain ⟨hheldn, -⟩ := hr.sharesNonneg.sharesOf h
  obtain ⟨S, hSv, hc, hty, hpre⟩ := l.sharesAmount h _ hheldn (by rw [hheld]; norm_num)
    (by rw [hheld]; rfl) (by rw [hheld]; norm_num)
  have hpos' : 0 < (WithdrawAmount.vaultShares S).amount.toRat := by
    show 0 < S.toRat; rw [hSv, hheld]; norm_num
  obtain ⟨hopen, -⟩ := Vault.redemption_open hph
  obtain ⟨r, hw, hrs, hAA', hST'⟩ := Vault.withdraw_one_share_ok l.vault l.now hint hmax hAD hLU hr.availableStored
    (l.isSoleShareholder h) hopen hS S hc hty (by rw [hSv, hheld]) hpos'
  obtain ⟨d, hok, -⟩ := l.apply_redeem hr hnd h (by rw [hheld]; rfl) (by rw [hheld]; norm_num) S hc hty hpre
    hpos' r hw hrs (le_of_eq hSv)
  exact ⟨S, _, hSv, hok, hAA', hST'⟩

/-- What the wind-down keeps once every loan is closed: a reachable ledger, not deleted, in the redemption phase,
with no loan, and holders' shares that add up to SharesTotal. -/
structure LendingLedger.HolderPhase (l : LendingLedger) : Prop where
  reachable : l.Reachable
  notDeleted : l.vaultDeleted = false
  redemption : l.vault.phase l.now = .redemption
  noLoans : ∀ i, l.loan? i = none
  sum : l.SharesSum

/-- A wind-down makes no deposit, so it keeps the holders' shares adding up to SharesTotal. -/
private lemma LendingLedger.WindsDownWhole.sharesSum {l l' : LendingLedger} {txs : List LendingTx} (hr : l.Reachable)
    (hl : l.SharesSum) (h : l.WindsDownWhole txs l') : l'.SharesSum := by
  induction h with
  | refl => exact hl
  | step tx hprev hw ha ih =>
    refine ih.step_of_not_deposit (hprev.reachable hr) (fun h amount isDonation he => ?_) ha
    subst he
    exact hw

/-- With no loan left nothing is lent and nothing is lost. -/
private lemma LendingLedger.HolderPhase.idle {l : LendingLedger} (hP : l.HolderPhase) :
    l.vault.assetsDeployed = Number.zero ∧ l.vault.lossUnrealized = Number.zero := by
  have hr := hP.reachable
  have hz : ∀ p : Loan → Bool, l.principalSum p = 0 := fun p =>
    l.principalSum_eq_zero p fun j e he => by rw [hP.noLoans j] at he; cases he
  exact ⟨(Number.toRat_eq_zero_iff_eq_zero l.vault.wf.assetsDeployed_norm).mp (by rw [hr.debtInv.deployed, hz]),
    (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.lossUnrealized_norm).mp
      (by rw [LendingLedger.loss_impaired_proof l hr, hz])⟩

/-- With no loan left the vault is settled, once an MPT cash is below `2.5·10^17` units. -/
private lemma LendingLedger.HolderPhase.settled {l : LendingLedger} (hP : l.HolderPhase)
    (hsmall : l.vault.numericType = NumericType.int64 → l.vault.assetsAvailable.toRat < 25 * 10 ^ 16) :
    l.vault.Settled :=
  hP.reachable.settled (fun i e he => by rw [hP.noLoans i] at he; cases he) hsmall

/-- With no loan left a holder's shares are worth their part of the cash. -/
private lemma LendingLedger.HolderPhase.worth {l : LendingLedger} (hP : l.HolderPhase) (h : Nat) :
    (l.sharesOf h).toRat * l.vault.shareValue =
      (l.sharesOf h).toRat * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal := by
  obtain ⟨hAD, hLU⟩ := hP.idle
  have hnav : l.vault.withdrawNav = l.vault.assetsAvailable.toRat := by
    show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat - l.vault.lossUnrealized.toRat = _
    rw [hAD, hLU, Number.toRat_zero]
    ring
  show (l.sharesOf h).toRat * (l.vault.withdrawNav / l.vault.toExact.sharesTotal) = _
  rw [hnav, mul_div_assoc]

/-- A vault transaction keeps the redemption phase, the loans and the brokers, and does not delete the vault. -/
private lemma LendingLedger.vault_step_frame {l l' : LendingLedger} {tx : LendingTx} (hv : tx.isVault = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    l'.vaultDeleted = l.vaultDeleted ∧ l'.now = l.now ∧ l'.vault.schedule = l.vault.schedule ∧
      l'.vault.numericType = l.vault.numericType ∧ l'.loans = l.loans ∧ l'.brokers = l.brokers := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
  have hk := l.applyVault_keepsLending tx u hu
  unfold LendingLedger.commitVault
  split <;> exact ⟨rfl, rfl, hk.schedule, hk.numericType, rfl, rfl⟩

/-- The redemption phase depends on the vault only through its schedule. -/
private lemma Vault.phase_of_schedule {v v' : Vault} (h : v'.schedule = v.schedule) (t : UInt32) :
    v'.phase t = v.phase t := by
  unfold Vault.phase; rw [h]

/-- A redemption keeps the wind-down's holder phase. -/
private lemma LendingLedger.HolderPhase.step {l l' : LendingLedger} {h : Nat} {amount : WithdrawAmount}
    (hP : l.HolderPhase) (hok : (l.apply (.vaultWithdraw h amount)).run = .ok (.ok l')) :
    l'.HolderPhase ∧ l'.brokers = l.brokers ∧ l'.vault.numericType = l.vault.numericType := by
  obtain ⟨hnd', hnow', hsch', hnt', hloans', hbr'⟩ := LendingLedger.vault_step_frame rfl hok
  exact ⟨⟨hP.reachable.apply hok, by rw [hnd']; exact hP.notDeleted,
    by rw [Vault.phase_of_schedule hsch', hnow']; exact hP.redemption,
    fun i => by unfold LendingLedger.loan?; rw [hloans']; exact hP.noLoans i,
    hP.sum.step_of_not_deposit hP.reachable (fun _ _ _ he => by cases he) hok⟩, hbr', hnt'⟩

/-- A holder that owns every share is the sole shareholder. -/
private lemma LendingLedger.sole_of_all {l : LendingLedger} (hr : l.Reachable) {h : Nat}
    (hpos : 0 < (l.sharesOf h).toRat) (hall : (l.sharesOf h).toRat = l.vault.sharesTotal.toRat) :
    l.isSoleShareholder h = true := by
  obtain ⟨hn, -⟩ := hr.sharesNonneg.sharesOf h
  unfold LendingLedger.isSoleShareholder
  rw [Bool.and_eq_true, operator_ne_iff _ _ hn Number.zero_isNormalized,
    operator_eq_iff _ _ hn l.vault.wf.sharesTotal_norm, Number.toRat_zero]
  exact ⟨ne_of_gt hpos, hall⟩

/-- In a list of nonnegative values, two different entries add up to at most the sum. -/
private lemma List.getD_add_getD_le_sum (L : List ℚ) (hL : ∀ x ∈ L, 0 ≤ x) {i j : Nat} (hij : i ≠ j) :
    L.getD i 0 + L.getD j 0 ≤ L.sum := by
  have hone : ∀ k, L.getD k 0 ≤ L.sum := fun k => by
    rw [List.getD_eq_getElem?_getD]
    cases hk : L[k]? with
    | none => exact List.sum_nonneg hL
    | some x => exact List.single_le_sum hL x (List.mem_of_getElem? hk)
  induction L generalizing i j with
  | nil => simp
  | cons a L ih =>
    have ha : 0 ≤ a := hL a (by simp)
    have hL' : ∀ x ∈ L, 0 ≤ x := fun x hx => hL x (by simp [hx])
    have hone' : ∀ k, L.getD k 0 ≤ L.sum := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases hk : L[k]? with
      | none => exact List.sum_nonneg hL'
      | some x => exact List.single_le_sum hL' x (List.mem_of_getElem? hk)
    rw [List.sum_cons]
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => simpa using add_le_add_left (hone' j) a
    | succ i =>
      cases j with
      | zero => simpa [add_comm] using add_le_add_left (hone' i) a
      | succ j =>
        have := ih hL' (i := i) (j := j) (fun h => hij (by omega)) hone'
        simp only [List.getD_cons_succ]
        linarith

/-- In a list whose entries other than `i` are at most zero, the sum is at most entry `i`. -/
private lemma List.sum_le_getD (L : List ℚ) {i : Nat} (h : ∀ j, j ≠ i → L.getD j 0 ≤ 0) : L.sum ≤ L.getD i 0 := by
  induction L generalizing i with
  | nil => simp
  | cons a L ih =>
    rw [List.sum_cons]
    cases i with
    | zero =>
      have hL : L.sum ≤ 0 := by
        refine le_trans (List.sum_le_card_nsmul _ 0 fun x hx => ?_) (by simp)
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have := h (k + 1) (by omega)
        rw [List.getD_cons_succ, List.getD_eq_getElem _ _ hk] at this
        exact this
      simpa using hL
    | succ i =>
      have ha : a ≤ 0 := by simpa using h 0 (by omega)
      have := ih (i := i) (fun j hj => by simpa using h (j + 1) (by omega))
      simp only [List.getD_cons_succ]
      linarith

/-- The shares of two different holders add up to at most SharesTotal. -/
private lemma LendingLedger.SharesSum.two_le {l : LendingLedger} (hl : l.SharesSum) (hn : l.SharesNonneg) {h h' : Nat}
    (hne : h ≠ h') : (l.sharesOf h).toRat + (l.sharesOf h').toRat ≤ l.vault.sharesTotal.toRat := by
  rw [← hl.sum]
  have hget : ∀ k, (l.shares.map Number.toRat).getD k 0 = (l.sharesOf k).toRat := fun k => by
    unfold LendingLedger.sharesOf
    rw [← Number.toRat_zero, List.getD_map]
  rw [← hget h, ← hget h']
  refine List.getD_add_getD_le_sum _ (fun x hx => ?_) hne
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (hn y hy).2

/-- A holder other than `h` owns shares when `h` owns fewer than all of them. -/
private lemma LendingLedger.SharesSum.other_holder {l : LendingLedger} (hl : l.SharesSum) {h : Nat}
    (hlt : (l.sharesOf h).toRat < l.vault.sharesTotal.toRat) : ∃ h', h' ≠ h ∧ 0 < (l.sharesOf h').toRat := by
  by_contra hne
  push Not at hne
  have hget : ∀ k, (l.shares.map Number.toRat).getD k 0 = (l.sharesOf k).toRat := fun k => by
    unfold LendingLedger.sharesOf
    rw [← Number.toRat_zero, List.getD_map]
  have := List.sum_le_getD (l.shares.map Number.toRat) (i := h) (fun j hj => by rw [hget j]; exact hne j hj)
  rw [hl.sum, hget h] at this
  linarith

/-- An MPT cash stored exactly is at most `2^63 - 1` and has a scale. -/
private lemma LendingLedger.Reachable.integral_scale {l : LendingLedger} (hr : l.Reachable)
    (hnt : l.vault.numericType = NumericType.int64) :
    l.vault.assetsAvailable.toRat ≤ 2 ^ 63 - 1 ∧
      ∃ E, numberExponent l.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok E := by
  have hA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hrep := (STAmount.isRounded_eq_false_iff _ _ l.vault.wf.assetsAvailable_norm hA0).mp hr.availableStored
  have hcap : l.vault.assetsAvailable.toRat ≤ 2 ^ 63 - 1 := by
    rcases hrep with h0 | hrep
    · rw [h0]; norm_num
    · rw [hnt] at hrep
      obtain ⟨-, k, -, hk, hkv⟩ := hrep
      rw [hkv]
      have h1 : k + 1 ≤ 2 ^ 63 := by omega
      have h2 : ((k + 1 : ℕ) : ℚ) ≤ 2 ^ 63 := by exact_mod_cast h1
      push_cast at h2
      linarith
  refine ⟨hcap, ?_⟩
  unfold numberExponent
  split
  · exact ⟨_, rfl⟩
  · rw [hnt]
    obtain ⟨a, ha⟩ := STAmount.ofNumber_int64_ok l.vault.assetsAvailable .downward l.vault.wf.assetsAvailable_norm
      (Number.negative_false_of_nonneg _ l.vault.wf.assetsAvailable_norm hA0) hcap
    exact ⟨max l.vault.baseExponent a.exponent, by simp [ha]⟩

/-- The last holder of a large MPT vault takes all the cash. It redeems all but a few shares worth at least 20
units, then the rest: a single share prices exactly, and a few shares leave a small, settled vault. -/
private lemma LendingLedger.HolderPhase.sole_exit {l : LendingLedger} (hP : l.HolderPhase)
    (hnt : l.vault.numericType = NumericType.int64) (hbig : 25 * 10 ^ 16 ≤ l.vault.assetsAvailable.toRat)
    {h : Nat} (hh : 0 < (l.sharesOf h).toRat) (hall : (l.sharesOf h).toRat = l.vault.sharesTotal.toRat) :
    ∃ (txs : List LendingTx) (l' : LendingLedger), LendingLedger.Reaches l txs l' ∧
      (∀ tx ∈ txs, tx.isWindDown = true) ∧ l'.HolderPhase ∧ l'.vault.toExact.sharesTotal = 0 ∧
      l'.brokers = l.brokers := by
  have hr := hP.reachable
  have hint : l.vault.numericType.isIntegral = true := by rw [hnt]; rfl
  obtain ⟨hAD, hLU⟩ := hP.idle
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  have hwhole := hP.sum.sharesOf_whole h
  have hSTle := Vault.sharesTotal_le_maxRep l.vault
  set N := l.vault.toExact.sharesTotal with hN
  have hNh : (N : ℚ) = (l.sharesOf h).toRat := by rw [hcast, hall]
  have hN1 : 1 ≤ N := by
    have : (0 : ℚ) < N := by rw [hNh]; exact hh
    exact_mod_cast this
  set A := l.vault.assetsAvailable.toRat with hA
  -- a single share pays out all the cash at once
  by_cases hone : N = 1
  · obtain ⟨shares, l', hsv, hok, hAA', hST'⟩ := l.redeem_one_share hr hP.notDeleted hP.redemption hint hAD hLU h
      hone (by rw [← hNh, hone]; norm_num)
    obtain ⟨hP', hbr', -⟩ := hP.step hok
    refine ⟨[.vaultWithdraw h (.vaultShares shares)], l', LendingLedger.Reaches.single hok,
      fun tx htx => (by rw [List.mem_singleton.mp htx]; rfl), hP', ?_, hbr'⟩
    show l'.vault.sharesTotal.toRat.num.toNat = 0
    rw [hST', Number.toRat_zero]
    rfl
  -- otherwise keep `m` shares worth at least 20 units, and redeem the others
  have hN2 : 2 ≤ N := by omega
  have hNq : (2 : ℚ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℚ) < N := by linarith
  obtain ⟨m, hm1, hmN, hmlo, hmcase⟩ : ∃ m : ℕ, 1 ≤ m ∧ m < N ∧ 20 ≤ m * A / N ∧ (m = 1 ∨ m * A / N < 60) := by
    by_cases hu : 20 ≤ A / N
    · exact ⟨1, le_rfl, by omega, by simpa using hu, Or.inl rfl⟩
    · push Not at hu
      have hc0 : 0 < 20 * N / A := by positivity
      refine ⟨⌈(20 * N / A : ℚ)⌉₊, Nat.ceil_pos.mpr hc0, ?_, ?_, Or.inr ?_⟩
      · have hlt := Nat.ceil_lt_add_one hc0.le
        have : 20 * (N : ℚ) / A + 1 ≤ N := by
          rw [div_add_one (by positivity), div_le_iff₀ (by positivity)]
          nlinarith
        exact_mod_cast lt_of_lt_of_le hlt this
      · have hle := Nat.le_ceil (20 * (N : ℚ) / A)
        have h1 : 20 * (N : ℚ) / A * A / N = 20 := by field_simp
        calc (20 : ℚ) = 20 * (N : ℚ) / A * A / N := h1.symm
          _ ≤ _ := by gcongr
      · have hlt := Nat.ceil_lt_add_one hc0.le
        have h1 : (20 * (N : ℚ) / A + 1) * A / N = 20 + A / N := by field_simp
        calc (⌈(20 * N / A : ℚ)⌉₊ : ℚ) * A / N < (20 * (N : ℚ) / A + 1) * A / N := by gcongr
          _ = 20 + A / N := h1
          _ < 60 := by linarith
  have hmq : (m : ℚ) < N := by exact_mod_cast hmN
  have hm1q : (1 : ℚ) ≤ m := by exact_mod_cast hm1
  have hkq : ((N - m : ℕ) : ℚ) = (N : ℚ) - m := by rw [Nat.cast_sub hmN.le]
  have hkeep : 20 ≤ ((N : ℚ) - ((N - m : ℕ) : ℚ)) * A / N := by rw [hkq]; ring_nf; ring_nf at hmlo; linarith
  have hworth : 1 ≤ ((N - m : ℕ) : ℚ) * A / N := by
    have hsplit : ((N - m : ℕ) : ℚ) * A / N = A - m * A / N := by rw [hkq]; field_simp
    rw [hsplit]
    rcases hmcase with rfl | h60
    · have : A / N ≤ A / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hNq
      simp only [Nat.cast_one, one_mul]
      linarith
    · linarith
  obtain ⟨shares, l₁, hsv, hok, hST₁, hAA₁, hheld₁⟩ := l.redeem_some_integral hr hP.notDeleted hP.redemption hint hAD
    hLU h (N - m) hwhole (by rw [hall]; exact hSTle) (by omega)
    (by rw [hkq, ← hNh]; linarith) (by rw [hkq]; linarith) hworth (by
      have := hkeep; simpa using this)
  obtain ⟨hP₁, hbr₁, hnt₁⟩ := hP.step hok
  have hr₁ := hP₁.reachable
  have hN₁ : (l₁.vault.toExact.sharesTotal : ℚ) = m := by rw [hST₁, hkq]; ring
  have hheld₁' : (l₁.sharesOf h).toRat = m := by rw [hheld₁, hkq, ← hNh]; ring
  have hcast₁ := RawVault.WF.toExact_sharesTotal l₁.vault.toRawVault l₁.vault.wf
  obtain ⟨hAD₁, hLU₁⟩ := hP₁.idle
  have hstep₁ : LendingLedger.Reaches l [.vaultWithdraw h (.vaultShares shares)] l₁ := LendingLedger.Reaches.single hok
  rcases hmcase with rfl | h60
  · -- one share is left: it prices exactly
    obtain ⟨shares₂, l₂, hsv₂, hok₂, hAA₂, hST₂⟩ := l₁.redeem_one_share hr₁ hP₁.notDeleted hP₁.redemption
      (by rw [hnt₁]; exact hint) hAD₁ hLU₁ h (by exact_mod_cast hN₁) hheld₁'
    obtain ⟨hP₂, hbr₂, -⟩ := hP₁.step hok₂
    refine ⟨_, l₂, hstep₁.trans (LendingLedger.Reaches.single hok₂), fun tx htx => ?_, hP₂, ?_, by rw [hbr₂, hbr₁]⟩
    · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at htx
      rcases htx with rfl | rfl <;> rfl
    · show l₂.vault.sharesTotal.toRat.num.toNat = 0
      rw [hST₂, Number.toRat_zero]
      rfl
  · -- a few shares are left on a small vault, which is settled
    have hsmall₁ : l₁.vault.numericType = NumericType.int64 → l₁.vault.assetsAvailable.toRat < 25 * 10 ^ 16 := by
      intro _
      have := hkq
      calc l₁.vault.assetsAvailable.toRat ≤ A - ((N - m : ℕ) : ℚ) * A / N + 20 := hAA₁
        _ = m * A / N + 20 := by rw [hkq]; field_simp; ring
        _ < 25 * 10 ^ 16 := by linarith
    obtain ⟨shares₂, l₂, hsv₂, hok₂, -, hST₂⟩ := LendingLedger.payoff_exit_settled_proof l₁ hr₁ hP₁.notDeleted
      hP₁.redemption (fun i e he => by rw [hP₁.noLoans i] at he; cases he) h
      (LendingLedger.sole_of_all hr₁ (by rw [hheld₁']; linarith) (by rw [hheld₁', ← hN₁, hcast₁])) hsmall₁
    obtain ⟨hP₂, hbr₂, -⟩ := hP₁.step hok₂
    refine ⟨_, l₂, hstep₁.trans (LendingLedger.Reaches.single hok₂), fun tx htx => ?_, hP₂, ?_, by rw [hbr₂, hbr₁]⟩
    · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at htx
      rcases htx with rfl | rfl <;> rfl
    · show l₂.vault.sharesTotal.toRat.num.toNat = 0
      rw [hST₂, Number.toRat_zero]
      rfl

/-- Every holder redeems its shares. Each holder but the last redeems all its shares, the last one takes all
the cash, while no holder on the way holds dust. -/
private lemma LendingLedger.HolderPhase.redeem_all {start : LendingLedger}
    (hdust : ∀ (txs : List LendingTx) (l' : LendingLedger), start.WindsDownWhole txs l' → (∀ i, l'.loan? i = none) →
      l'.NoDust) :
    ∀ (n : Nat) (txs₀ : List LendingTx) (l : LendingLedger), start.WindsDownWhole txs₀ l → l.HolderPhase →
      l.vault.toExact.sharesTotal = n →
      ∃ (txs : List LendingTx) (l' : LendingLedger), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, tx.isWindDown = true) ∧ l'.HolderPhase ∧ l'.vault.toExact.sharesTotal = 0 ∧
        l'.brokers = l.brokers := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro txs₀ l hw₀ hP hn
    have hr := hP.reachable
    have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact ⟨[], l, .refl, fun tx htx => (by cases htx), hP, by rw [hn, h0], rfl⟩
    have hS : 0 < l.vault.sharesTotal.toRat := by
      rw [← hcast, hn]; exact_mod_cast hpos
    have hSTpos : (0 : ℚ) < l.vault.toExact.sharesTotal := by rw [hcast]; exact hS
    have hcont : ∀ (h : Nat) (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat →
        (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') →
        l'.vault.toExact.sharesTotal < n →
        ∃ (txs : List LendingTx) (l'' : LendingLedger), LendingLedger.Reaches l txs l'' ∧
          (∀ tx ∈ txs, tx.isWindDown = true) ∧ l''.HolderPhase ∧ l''.vault.toExact.sharesTotal = 0 ∧
          l''.brokers = l.brokers := by
      intro h shares l' hsv hok hlt'
      obtain ⟨hP', hbr', -⟩ := hP.step hok
      have hstep : l.WindsDownWhole [.vaultWithdraw h (.vaultShares shares)] l' := .single hsv hok
      obtain ⟨txs, l'', hw, hwt, hP'', h0, hb''⟩ := ih _ hlt' (txs₀ ++ _) l' (hw₀.trans hstep) hP' rfl
      refine ⟨_ ++ txs, l'', (LendingLedger.Reaches.single hok).trans hw, fun tx htx => ?_, hP'', h0,
        by rw [hb'', hbr']⟩
      rcases List.mem_append.mp htx with h' | h'
      · rw [List.mem_singleton.mp h']; rfl
      · exact hwt tx h'
    by_cases hsmall : l.vault.numericType = NumericType.int64 → l.vault.assetsAvailable.toRat < 25 * 10 ^ 16
    · -- a settled vault
      have hz := hP.settled hsmall
      obtain ⟨h, hh⟩ := hP.sum.exists_holder hS
      have hle := hP.sum.sharesOf_le hr.sharesNonneg h
      rcases lt_or_eq_of_le hle with hlt | heq
      · -- a holder that does not own every share redeems all of them
        have hworth : 0 < l.vault.assetsAvailable.toRat →
            ∀ E, numberExponent l.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok E →
              (10 : ℚ) ^ E ≤ (l.sharesOf h).toRat * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal := by
          intro hA E hE
          rw [← hP.worth h]
          refine hdust txs₀ l hw₀ hP.noLoans h hh hlt ?_ E hE
          rw [hP.worth h]
          positivity
        obtain ⟨shares, l', hsv, hok, hST', -⟩ :=
          LendingLedger.redeem_part l hr hP.notDeleted hP.redemption hz h (hP.sum.sharesOf_whole h) hh hlt hworth
        refine hcont h shares l' hsv hok ?_
        rw [← hn]
        have : (l'.vault.toExact.sharesTotal : ℚ) < l.vault.toExact.sharesTotal := by rw [hST']; linarith
        exact_mod_cast this
      · -- the holder of every share takes all the cash
        obtain ⟨shares, l', hsv, hok, -, hST'⟩ := LendingLedger.payoff_exit_settled_proof l hr hP.notDeleted
          hP.redemption (fun i e he => by rw [hP.noLoans i] at he; cases he) h (LendingLedger.sole_of_all hr hh heq)
          hsmall
        obtain ⟨hP', hbr', -⟩ := hP.step hok
        refine ⟨[.vaultWithdraw h (.vaultShares shares)], l', LendingLedger.Reaches.single hok,
          fun tx htx => (by rw [List.mem_singleton.mp htx]; rfl), hP', ?_, hbr'⟩
        show l'.vault.sharesTotal.toRat.num.toNat = 0
        rw [hST', Number.toRat_zero]
        rfl
    -- an MPT vault of `2.5·10^17` units or more
    have hnt : l.vault.numericType = NumericType.int64 := by
      by_contra hne; exact hsmall (fun h => absurd h hne)
    have hbig : 25 * 10 ^ 16 ≤ l.vault.assetsAvailable.toRat := by
      by_contra hlt; exact hsmall (fun _ => by push Not at hlt; exact hlt)
    have hint : l.vault.numericType.isIntegral = true := by rw [hnt]; rfl
    obtain ⟨hAD, hLU⟩ := hP.idle
    obtain ⟨hcap, E, hE⟩ := hr.integral_scale hnt
    have hE0 : (1 : ℚ) ≤ 10 ^ E := by
      have hb := (Vault.baseExponent_bounds l.vault).2.2 hint
      have := numberExponent_ge _ _ _ _ hE
      rw [hb] at this
      exact one_le_zpow₀ (by norm_num) this
    by_cases hex : ∃ h, 0 < (l.sharesOf h).toRat ∧ 2 * (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat
    · -- a holder of at most half the shares redeems all of them, the others keep at least half the cash
      obtain ⟨h, hh, h2⟩ := hex
      have hwhole := hP.sum.sharesOf_whole h
      have hlt : (l.sharesOf h).toRat < l.vault.sharesTotal.toRat := by linarith
      set k := (l.sharesOf h).toRat.num.toNat with hk
      have hkq : (k : ℚ) = (l.sharesOf h).toRat := by
        rw [hk]
        have hnum := Rat.coe_int_num_of_den_eq_one hwhole
        have h0 : 0 ≤ (l.sharesOf h).toRat.num := Rat.num_nonneg.mpr hh.le
        rw [← hnum]
        exact_mod_cast Int.toNat_of_nonneg h0
      have hworth : 1 ≤ (l.sharesOf h).toRat * l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal := by
        rw [← hP.worth h]
        refine le_trans hE0 (hdust txs₀ l hw₀ hP.noLoans h hh hlt ?_ E hE)
        rw [hP.worth h]
        positivity
      have hkeep : 20 ≤ ((l.vault.toExact.sharesTotal : ℚ) - (l.sharesOf h).toRat) *
          l.vault.assetsAvailable.toRat / l.vault.toExact.sharesTotal := by
        rw [hcast, le_div_iff₀ hS]
        nlinarith
      obtain ⟨shares, l', hsv, hok, hST', -, -⟩ := l.redeem_some_integral hr hP.notDeleted hP.redemption hint hAD
        hLU h k hwhole (by linarith [hP.sum.sharesOf_le hr.sharesNonneg h, Vault.sharesTotal_le_maxRep l.vault])
        (by have : (0 : ℚ) < k := by rw [hkq]; exact hh
            exact_mod_cast this)
        (le_of_eq hkq) (by rw [hkq, hcast]; exact hlt) (by rw [hkq]; exact hworth) (by rw [hkq]; exact hkeep)
      refine hcont h shares l' (by rw [hsv, hkq]) hok ?_
      rw [← hn]
      have : (l'.vault.toExact.sharesTotal : ℚ) < l.vault.toExact.sharesTotal := by rw [hST', hkq]; linarith
      exact_mod_cast this
    · -- one holder owns every share
      push Not at hex
      obtain ⟨h, hh⟩ := hP.sum.exists_holder hS
      have hall : (l.sharesOf h).toRat = l.vault.sharesTotal.toRat := by
        by_contra hne
        have hlt := lt_of_le_of_ne (hP.sum.sharesOf_le hr.sharesNonneg h) hne
        obtain ⟨h', hne', hh'⟩ := hP.sum.other_holder hlt
        have := hP.sum.two_le hr.sharesNonneg (Ne.symm hne')
        have := hex h hh
        have := hex h' hh'
        linarith
      exact hP.sole_exit hnt hbig hh hall

/-- Every broker leaves. With no loan left each broker has no loans, and LoanBrokerDelete succeeds. -/
private lemma LendingLedger.HolderPhase.delete_brokers :
    ∀ (n : Nat) (l : LendingLedger), l.HolderPhase → l.brokers.countP (·.isSome) = n →
      ∃ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' ∧ l'.HolderPhase ∧
        (∀ j, l'.broker? j = none) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hP hn
    by_cases hex : ∃ j b, l.broker? j = some b
    · obtain ⟨j, b, hb⟩ := hex
      have h0 : b.loanCount = 0 := by
        have hc := hP.reachable.loanCountInv.counted j b hb
        rw [LendingLedger.loansOf_none hP.noLoans j] at hc
        exact UInt32.toNat_inj.mp (by simpa using hc)
      have hok := LendingLedger.broker_delete_ok l hP.notDeleted j b hb h0
      have hjl := LendingLedger.broker?_lt hb
      have hbr : (l.commitBroker { index := j, broker := none }).brokers = l.brokers.set j none := by
        show storeSlot l.brokers j none = _
        unfold storeSlot
        rw [if_pos hjl]
      have hP' : (l.commitBroker { index := j, broker := none }).HolderPhase :=
        ⟨hP.reachable.apply hok, hP.notDeleted, hP.redemption, hP.noLoans,
          hP.sum.step_of_not_deposit hP.reachable (fun _ _ _ he => by cases he) hok⟩
      have hlt : (l.commitBroker { index := j, broker := none }).brokers.countP (·.isSome) < n := by
        rw [hbr, ← hn]
        unfold LendingLedger.broker? at hb
        cases hx : l.brokers[j]? with
        | none => rw [hx] at hb; cases hb
        | some o =>
          rw [hx] at hb
          cases o with
          | none => cases hb
          | some b' => exact List.countP_set_none_lt _ j b' hx
      obtain ⟨txs, l', hw, hP'', hnone⟩ := ih _ hlt _ hP' rfl
      have hstep := LendingLedger.WindsDownWhole.single (show l.WholeWindDownTx (.loanBrokerDelete j) from trivial) hok
      exact ⟨_, l', hstep.trans hw, hP'', hnone⟩
    · push Not at hex
      refine ⟨[], l, .refl, hP, fun j => ?_⟩
      cases h : l.broker? j with
      | none => rfl
      | some b => exact absurd h (hex j b)

/-- VaultDelete succeeds once no broker, loan or share is left. -/
private lemma LendingLedger.HolderPhase.vaultDelete_ok {l : LendingLedger} (hP : l.HolderPhase)
    (hS : l.vault.toExact.sharesTotal = 0) (hb : ∀ j, l.broker? j = none) :
    (l.apply .vaultDelete).run = .ok (.ok { l with vaultDeleted := true }) := by
  have hr := hP.reachable
  have hST : l.vault.sharesTotal = Number.zero := by
    have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
    rw [hS, Nat.cast_zero] at hcast
    exact (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.sharesTotal_norm).mp hcast.symm
  obtain ⟨hAA, hAD⟩ := l.vault.valid.empty_shares hST
  obtain ⟨-, -, -, hAR, -⟩ := LendingLedger.lifecycle_settles_proof l hr (fun j b' hj => by rw [hb j] at hj; cases hj)
  have hcan : l.vault.canVaultDelete = .ok .tesSUCCESS := by
    have htot : l.vault.assetsTotal = .ok Number.zero := by
      unfold RawVault.assetsTotal
      rw [show l.vault.toRawVault.assetsAvailable = l.vault.assetsAvailable from rfl,
        show l.vault.toRawVault.assetsDeployed = l.vault.assetsDeployed from rfl, hAA, hAD,
        Number.operator_add_zero_right]
    unfold Vault.canVaultDelete
    simp only [bind, Except.bind, pure, Except.pure, htot, hAA, hST]
    rfl
  have hany : l.brokers.any Option.isSome = false := by
    rw [List.any_eq_false]
    intro o ho
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
    have hn := hb k
    unfold LendingLedger.broker? at hn
    rw [List.getElem?_eq_getElem hk] at hn
    cases hx : l.brokers[k] with
    | none => simp
    | some b => rw [hx] at hn; simp at hn
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete]
  unfold_ter
  rw [hP.notDeleted, hcan]
  simp only [Bool.false_eq_true, ↓reduceIte, show TER.tesSUCCESS.isTesSuccess = true from rfl, Bool.not_true,
    hany, hAR]
  rfl

/-- Past RedemptionDate a closed-ended vault is in its redemption phase. -/
private lemma Vault.phase_past_redemption (v : Vault) (s : VaultSchedule) (hs : v.schedule = some s) (t : UInt32)
    (ht : s.redemptionDate < t) : v.phase t = .redemption := by
  have hgap := v.valid.schedule_gap s (by rw [hs]; rfl)
  unfold VaultSchedule.hasValidGap at hgap
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgap
  have hmin : XRPL.Model.SingleAssetVault.minInvestmentPeriod = 180 := rfl
  have hsub : s.subscriptionDate < t := by
    rw [UInt32.lt_iff_toNat_lt] at ht ⊢
    omega
  have hle : s.redemptionDate ≤ t := by
    rw [UInt32.le_iff_toNat_le]
    rw [UInt32.lt_iff_toNat_lt] at ht
    omega
  unfold Vault.phase
  rw [hs]
  simp [hsub, hle]

/-- Proof body of `Lending.Reachable.wind_down`. -/
lemma LendingLedger.wind_down_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (s : VaultSchedule) (hs : l.vault.schedule = some s) (hpast : s.redemptionDate < l.now)
    (hgrace : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
      s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat)
    (hpending : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened)
    (hactive : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
      e.loan.paymentRemaining ≠ 0 → l.NotCoarsened)
    (hca : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hsum : l.SharesSum)
    (hdust : ∀ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' → (∀ i, l'.loan? i = none) →
      l'.NoDust) :
    ∃ (txs : List LendingTx) (l' : LendingLedger), LendingLedger.Reaches l txs l' ∧ (∀ tx ∈ txs, tx.isWindDown = true) ∧
      (l'.apply .vaultDelete).run = .ok (.ok { l' with vaultDeleted := true }) := by
  have hP : l.LoanPhase s := ⟨hr, hnd, hs, hpast, hgrace, hpending, hactive, hca⟩
  obtain ⟨txs₁, l₁, hw₁, hP₁, hnone⟩ := LendingLedger.LoanPhase.close_all _ l hP rfl
  have hH₁ : l₁.HolderPhase := ⟨hP₁.reachable, hP₁.notDeleted,
    Vault.phase_past_redemption l₁.vault s hP₁.schedule l₁.now hP₁.past, hnone, hw₁.sharesSum hr hsum⟩
  obtain ⟨txs₂, l₂, hw₂, hH₂, hb₂⟩ := LendingLedger.HolderPhase.delete_brokers _ l₁ hH₁ rfl
  obtain ⟨txs₃, l₃, hw₃, hwt₃, hH₃, hS₃, hbr₃⟩ :=
    LendingLedger.HolderPhase.redeem_all hdust _ (txs₁ ++ txs₂) l₂ (hw₁.trans hw₂) hH₂ rfl
  have hw := hw₁.trans hw₂
  refine ⟨txs₁ ++ txs₂ ++ txs₃, l₃, hw.reaches.trans hw₃, fun tx htx => ?_,
    hH₃.vaultDelete_ok hS₃ (fun j => by unfold LendingLedger.broker?; rw [hbr₃]; exact hb₂ j)⟩
  rcases List.mem_append.mp htx with h' | h'
  · exact hw.isWindDown tx h'
  · exact hwt₃ tx h'

end XRPL.Model.Lending
