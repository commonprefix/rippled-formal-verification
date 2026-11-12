import XRPL.Properties.Lending.Ledger.Common.WindDownLoans
import XRPL.Properties.Lending.Ledger.Common.ShareSum
import XRPL.Properties.Lending.Ledger.Common.DustHolders
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.WithdrawUpdates
import XRPL.Properties.Vault.Proofs.CanEmpty
import XRPL.Properties.Lending.Ledger.Common.RedemptionDefaultWitness

/-! # A vault that no wind-down deletes

A reachable ledger past RedemptionDate with no broker or loan left, one base unit of cash and two holders owning half
the shares each. Each holder's shares are worth half a base unit, so every VaultWithdraw pays nothing and fails, and
VaultDelete finds the shares. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On an IOU vault with one base unit of cash and nothing lent, any amount up to half the shares is priced above
zero and below one base unit. -/
lemma Vault.half_unit_price (v : Vault) (hz : v.OpenZone) (hfr : v.numericType = .fractional)
    (hA : v.assetsAvailable.toRat = 10 ^ v.baseExponent) (shares priced : STAmount) (waive : Bool)
    (hsic : shares.IntegralCanonical) (hs64 : shares.mNumericType = .int64) (hspos : 0 < shares.toRat)
    (hhalf : 2 * shares.toRat ≤ v.toExact.sharesTotal)
    (hpr : v.sharesToAssetsWithdraw shares waive = .ok priced) :
    0 < priced.toRat ∧ priced.toRat < 10 ^ v.baseExponent := by
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    intro h; rw [hfr] at h; cases h
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds v
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAApos : 0 < v.assetsAvailable.toRat := by rw [hA]; exact hp10
  obtain ⟨nav, hnav, -, hcase⟩ := WdPrice.price_cases v shares priced waive hpr
  rw [hz.assetsTotalForWithdrawal_eq waive, Except.ok.injEq] at hnav
  subst hnav
  rcases hcase with ⟨hm0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · exact absurd (Number.toRat_eq_zero_of_mantissa_zero _ hm0) (ne_of_gt hAApos)
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ (hsic.canonical (by rw [hs64]; decide)))
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hS : 2 * sn0.toRat ≤ v.sharesTotal.toRat := by rw [hsnv, ← hcast]; exact hhalf
  have hSpos : 0 < v.sharesTotal.toRat := by rw [hsnv] at hS; linarith
  have hSle := Vault.sharesTotal_le_maxRep v
  have hs1 : (1 : ℚ) ≤ sn0.toRat := by
    rw [hsnv]
    exact rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hS1 : (1 : ℚ) ≤ v.sharesTotal.toRat := by linarith
  -- the worth of the shares, at most half a base unit and well above `10^-50`
  obtain ⟨V, hVdef⟩ : ∃ V : ℚ, V = v.assetsAvailable.toRat * sn0.toRat / v.sharesTotal.toRat := ⟨_, rfl⟩
  have hVhi : V ≤ 10 ^ v.baseExponent / 2 := by
    rw [hVdef, div_le_iff₀ hSpos, hA]
    nlinarith
  have hVlo : (10 : ℚ) ^ (-50 : ℤ) ≤ V := by
    have h10 : (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) hblo
    have hV1 : 10 ^ v.baseExponent / (2 ^ 63 - 1) ≤ V := by
      rw [hVdef, hA, div_le_div_iff₀ (by norm_num) hSpos]
      nlinarith
    have h50 : (10 : ℚ) ^ (-50 : ℤ) ≤ 10 ^ (-10 : ℤ) / (2 ^ 63 - 1) := by norm_num
    calc (10 : ℚ) ^ (-50 : ℤ) ≤ 10 ^ (-10 : ℤ) / (2 ^ 63 - 1) := h50
      _ ≤ 10 ^ v.baseExponent / (2 ^ 63 - 1) := div_le_div_of_nonneg_right h10 (by norm_num)
      _ ≤ V := hV1
  obtain ⟨hann, hanpos, hb⟩ := pipe_large v.assetsAvailable sn0 NS an v.sharesTotal v.wf.assetsAvailable_norm hsnn
    v.wf.sharesTotal_norm hAApos.le (by linarith) hSpos hS1 (by rw [← hVdef]; exact hVlo) hmul hdiv
  rw [← hVdef] at hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hanhi : an.toRat ≤ V * (1 + 2 / 10 ^ 18) := by
    have := (abs_le.mp hb).2
    have hV0 : 0 ≤ V := le_trans (zpow_pos (by norm_num) _).le hVlo
    nlinarith
  have hof' : STAmount.ofNumber .fractional an .to_nearest = .ok priced := by rw [← hfr]; exact hof
  have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ an.toRat := by
    have hab := (abs_le.mp hb).1
    have hV0 : 0 ≤ V := le_trans (zpow_pos (by norm_num) _).le hVlo
    have hε : V * sharesε ≤ V / 2 := by
      have : (sharesε : ℚ) ≤ 1 / 2 := by unfold sharesε; norm_num
      nlinarith
    have h1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-50 : ℤ) / 2 := by norm_num
    have h2 : (10 : ℚ) ^ (-50 : ℤ) / 2 ≤ V / 2 := div_le_div_of_nonneg_right hVlo (by norm_num)
    generalize (10 : ℚ) ^ (-81 : ℤ) = a at h1 ⊢
    generalize (10 : ℚ) ^ (-50 : ℤ) = b at h1 h2
    linarith
  have hpm : priced.mValue ≠ 0 := STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest priced hann h81 hof'
  obtain ⟨hhalfulp, hp0⟩ := WdPrice.ofNumber_half v.numericType an priced hann
    (Number.negative_false_of_pos an hanpos) hof hpm
  have hppos : 0 < priced.toRat := lt_of_le_of_ne hp0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
  obtain ⟨hcz, hpty⟩ := Vault.sharesToAssetsWithdraw_form v shares priced waive hmax hpr
  have hpc : priced.Canonical := hcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  have hPiou : priced.IOUCanonical := hpc.2 (by unfold STAmount.integral; rw [hpty, hfr]; rfl)
  obtain ⟨hP15, -⟩ := STAmount.IOUCanonical.toRat_bounds priced hPiou hppos
  have h15 : (10 : ℚ) ^ (priced.exponent + 15) = 10 ^ priced.exponent * 10 ^ 15 := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  rw [h15] at hP15
  have hulp := (abs_le.mp hhalfulp).2
  refine ⟨hppos, ?_⟩
  have hpe : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
  nlinarith

/-- On an IOU vault with one base unit of cash, nothing lent and no exit fee, a withdrawal of at most half the shares
fails. The shares are priced below one base unit, and a payout is nothing or a whole number of base units above zero. -/
lemma Vault.half_unit_withdraw_fails (v : Vault) (hz : v.OpenZone) (hfr : v.numericType = .fractional)
    (hA : v.assetsAvailable.toRat = 10 ^ v.baseExponent) (t : UInt32) (hfee : v.earlyExitFeeRateAt t = 0)
    (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical)
    (hty : amount.InAsset v.numericType) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hhalf : 2 * r.shares.toRat ≤ v.toExact.sharesTotal) : False := by
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    intro h; rw [hfr] at h; cases h
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hlt : r.shares.toRat < v.toExact.sharesTotal := by linarith
  obtain ⟨priced, hpr, hcases⟩ := Vault.withdraw_payout_cases v amount waive t hpos hc hty r hok hlt
  obtain ⟨hppos, hplt⟩ := Vault.half_unit_price v hz hfr hA r.shares priced waive hsic hs64 hspos hhalf hpr
  rcases hcases with ⟨-, hfm | hp0⟩ | ⟨pN, fee, payN, paidN, payout, -, -, -, -, hp, -, hcl, hnp, -, -⟩
  · rw [hfee] at hfm
    exact absurd hfm (by decide)
  · exact absurd hp0 (ne_of_gt hppos)
  -- the payout is a whole number of base units, at most the priced amount, so it is nothing
  obtain ⟨-, ⟨j, hj⟩, -, -⟩ := Vault.withdraw_payout_units v amount waive t hpos hz hmax r hok
  obtain ⟨priced', hpr', hle⟩ := Vault.withdraw_payout_le_proof v amount waive t hpos hc hty hmax r hok hlt
  rw [hpr, Except.ok.injEq] at hpr'
  subst hpr'
  rw [hfee] at hle
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hj0 : j = 0 := by
    have h1 : (j : ℚ) * 10 ^ v.baseExponent < 1 * 10 ^ v.baseExponent := by
      have hle' : r.assets.toRat ≤ priced.toRat := by simpa using hle
      rw [← hj, one_mul]; linarith
    have : (j : ℚ) < 1 := lt_of_mul_lt_mul_right h1 hp10.le
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
  have hr0 : r.assets.toRat = 0 := by rw [hj, hj0]; simp
  -- a zero IOU payout is reported nonpositive, which the withdrawal rejects
  have hpo := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp
  have hrc := clampToSumExponent_canonicalOrZero _ _ _ _ hpo.1.operator_neg v.baseExponent_range.1
    v.baseExponent_range.2 hcl
  have hrt : r.assets.mNumericType = .fractional := by
    rw [hrc.2.1, (STAmount.operator_neg_fields _).1, hpo.2, hfr]
  rw [STAmount.isFractionalNonPositive_zero _ hrt ((STAmount.toRat_eq_zero_iff _).mp hr0)] at hnp
  exact absurd (Except.ok.inj hnp) (by decide)

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule VaultWithAmounts WithdrawAmount)

open private dhGenesis dhTxs dhGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.DustHolders
open private niGenesis niGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
open private rdTxs from XRPL.Properties.Lending.Ledger.Common.RedemptionDefaultWitness

/-- A property every wind-down transaction keeps holds at the end of every run of them. -/
private lemma LendingLedger.Reaches.keeps {P : LendingLedger → Prop} {start l : LendingLedger}
    {txs : List LendingTx}
    (hstep : ∀ (l₀ : LendingLedger) (tx : LendingTx) (l₁ : LendingLedger), P l₀ → tx.isWindDown = true →
      (l₀.apply tx).run = .ok (.ok l₁) → P l₁)
    (h0 : P start) (h : LendingLedger.Reaches start txs l) (hw : ∀ tx ∈ txs, tx.isWindDown = true) : P l := by
  induction h with
  | refl => exact h0
  | step tx _ ha ih =>
    exact hstep _ tx _ (ih fun t ht => hw t (List.mem_append_left _ ht))
      (hw tx (List.mem_append_right _ (List.mem_singleton_self _))) ha

/-- A management action on an empty loan slot fails. -/
private lemma LendingLedger.manage_empty {l l' : LendingLedger} {i : Nat} {a : LoanManageAction}
    (h0 : l.loan? i = none) : (l.apply (.loanManage i a)).run ≠ .ok (.ok l') := by
  intro h
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_manage_inv u i a hu
  rw [h0] at he
  cases he

/-- A LoanDelete on an empty loan slot fails. -/
private lemma LendingLedger.delete_empty {l l' : LendingLedger} {i : Nat} (h0 : l.loan? i = none) :
    (l.apply (.loanDelete i)).run ≠ .ok (.ok l') := by
  intro h
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_delete_inv u i hu
  rw [h0] at he
  cases he

/-- A LoanBrokerDelete on an empty broker slot fails. -/
private lemma LendingLedger.brokerDelete_empty {l l' : LendingLedger} {j : Nat} (h0 : l.broker? j = none) :
    (l.apply (.loanBrokerDelete j)).run ≠ .ok (.ok l') := by
  intro h
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_broker rfl h
  simp only [LendingLedger.applyBroker, h0] at hu
  cases hu

/-- On an IOU ledger with one base unit of cash, nothing lent and no exit fee, no holder of at most half the shares
can withdraw, by shares or by assets. -/
private lemma LendingLedger.half_unit_withdraw_fails {l l' : LendingLedger} (hr : l.Reachable)
    (hz : l.vault.OpenZone) (hfr : l.vault.numericType = .fractional)
    (hA : l.vault.assetsAvailable.toRat = 10 ^ l.vault.baseExponent) (hfee : l.vault.earlyExitFeeRateAt l.now = 0)
    {h : Nat} (hh : 2 * (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) {amount : WithdrawAmount} :
    (l.apply (.vaultWithdraw h amount)).run ≠ .ok (.ok l') := by
  intro hok
  obtain ⟨hpre, -⟩ := LendingLedger.apply_checked hok
  obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset h amount
    ((TER.isTesSuccess_iff _).mp hpre)
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_vault rfl hok
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  obtain ⟨hheldn, -⟩ := hr.sharesNonneg.sharesOf h
  simp only [LendingLedger.applyVault] at hu
  split at hu
  · rename_i hpos
    unfold_ter at hu
    walk_ok
    have hwith : (l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some (l.sharesOf h))).run =
        .ok (.ok _) := ‹_›
    obtain ⟨hw, hheld⟩ := Vault.withdraw_holder_ok _ _ _ _ _ _ _ hwith
    obtain ⟨hsic, hs64, -⟩ := Vault.withdraw_shares_form _ _ _ _ hpos hc hty _ hw
    obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical _ .to_nearest
      (STAmount.Canonical.exactCanonical _ (hsic.canonical (by rw [hs64]; decide)))
    have hle := (operator_lt_eq_false_iff _ _ hheldn hsnn).mp (hheld sn hsn)
    refine Vault.half_unit_withdraw_fails l.vault hz hfr hA l.now hfee amount _ hpos hc hty _ hw ?_
    rw [← hsnv, hcast]
    linarith
  · cases hu

/-- The dust-holder ledger: no broker and no loan, two holders of half the shares each and no other holder, an IOU
vault in redemption with one base unit of cash and nothing lent, and VaultDelete rejected. -/
private def wdDustCheck : Bool :=
  match dhGenesis.run dhTxs with
  | .ok l =>
    !l.vaultDeleted && decide (l.vault.schedule = some dhSchedule) && decide (dhSchedule.redemptionDate < l.now) &&
      decide (l.vault.phase l.now = .redemption) &&
      l.brokers.all Option.isNone && l.loans.all Option.isNone && l.shares.length == 2 &&
      l.vault.numericType == NumericType.fractional &&
      decide ((l.shares.map Number.toRat).sum = l.vault.sharesTotal.toRat) &&
      l.shares.all (fun x => x.toRat.den == 1) &&
      decide (2 * (l.sharesOf 0).toRat ≤ l.vault.sharesTotal.toRat) &&
      decide (2 * (l.sharesOf 1).toRat ≤ l.vault.sharesTotal.toRat) &&
      l.vault.assetsDeployed == Number.zero && l.vault.lossUnrealized == Number.zero &&
      l.vault.yieldUnrealized == Number.zero &&
      decide (l.vault.assetsAvailable.toRat = 10 ^ l.vault.baseExponent) &&
      !STAmount.isRounded l.vault.numericType l.vault.assetsAvailable &&
      (match (l.apply .vaultDelete).run with
        | .ok (.ok _) => false
        | _ => true)
  | .error _ => false

private lemma wdDustCheck_true : wdDustCheck = true := by native_decide

/-- No loan is stored when every loan slot is empty. -/
private lemma LendingLedger.loan?_of_all_none {l : LendingLedger} (h : l.loans.all Option.isNone = true) (i : Nat) :
    l.loan? i = none := by
  unfold LendingLedger.loan?
  cases hx : l.loans[i]? with
  | none => rfl
  | some o =>
    have := List.all_eq_true.mp h o (List.mem_of_getElem? hx)
    cases o with
    | none => rfl
    | some e => simp at this

/-- No broker is stored when every broker slot is empty. -/
private lemma LendingLedger.broker?_of_all_none {l : LendingLedger} (h : l.brokers.all Option.isNone = true)
    (j : Nat) : l.broker? j = none := by
  unfold LendingLedger.broker?
  cases hx : l.brokers[j]? with
  | none => rfl
  | some o =>
    have := List.all_eq_true.mp h o (List.mem_of_getElem? hx)
    cases o with
    | none => rfl
    | some b => simp at this

/-- No wind-down deletes the dust-holder vault. Past RedemptionDate and loan A's grace period, with no broker or
loan left, every VaultWithdraw by any holder is rejected, and VaultDelete finds the shares. -/
lemma LendingLedger.wind_down_dust_witness :
    ∃ (l : LendingLedger) (s : VaultSchedule), l.Reachable ∧ l.vaultDeleted = false ∧ l.vault.schedule = some s ∧
      s.redemptionDate < l.now ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
        e.loan.paymentRemaining ≠ 0 → l.NotCoarsened) ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) ∧
      l.SharesSum ∧
      ∀ (txs : List LendingTx) (l' l'' : LendingLedger), LendingLedger.Reaches l txs l' →
        (∀ tx ∈ txs, tx.isWindDown = true) → (l'.apply .vaultDelete).run ≠ .ok (.ok l'') := by
  have hc := wdDustCheck_true
  unfold wdDustCheck at hc
  split at hc
  case h_2 => cases hc
  rename_i l hl
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnd, hsch⟩, hpast⟩, hph⟩, hb⟩, hlo⟩, hlen⟩, hnt⟩, hsum⟩, hwhole⟩, h0⟩, h1⟩,
    hAD⟩, hLU⟩, hYU⟩, hA⟩, hcash⟩, hdel⟩ := hc
  have hr : l.Reachable := LendingLedger.Reachable.of_run dhGenesis_genesis hl
  have hnone := LendingLedger.loan?_of_all_none hlo
  have hbnone := LendingLedger.broker?_of_all_none hb
  have hz : l.vault.OpenZone := ⟨hAD, hLU, hYU, ⟨1, by norm_num, by rw [hA]; ring⟩, hcash⟩
  have hfee : l.vault.earlyExitFeeRateAt l.now = 0 := by
    unfold Vault.earlyExitFeeRateAt
    rw [hph]
    cases l.vault.earlyExitFeeRate <;> rfl
  have hhalf : ∀ h, 2 * (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat := by
    intro h
    rcases (by omega : h = 0 ∨ h = 1 ∨ 2 ≤ h) with rfl | rfl | h2
    · exact h0
    · exact h1
    · have hS0 := l.vault.wf.sharesTotal_nonneg
      unfold LendingLedger.sharesOf
      rw [List.getD_eq_default _ _ (by rw [hlen]; exact h2), Number.toRat_zero]
      linarith
  have hstuck : ∀ (tx : LendingTx) (l₁ : LendingLedger), tx.isWindDown = true → (l.apply tx).run ≠ .ok (.ok l₁) := by
    intro tx l₁ hw hok
    cases tx with
    | loanManage i a => exact LendingLedger.manage_empty (hnone i) hok
    | loanDelete i => exact LendingLedger.delete_empty (hnone i) hok
    | loanBrokerDelete j => exact LendingLedger.brokerDelete_empty (hbnone j) hok
    | vaultWithdraw h amount => exact LendingLedger.half_unit_withdraw_fails hr hz hnt hA hfee (hhalf h) hok
    | _ => cases hw
  refine ⟨l, dhSchedule, hr, hnd, hsch, hpast,
    fun i e he => (by rw [hnone i] at he; cases he), fun i e he => (by rw [hnone i] at he; cases he),
    fun i e he => (by rw [hnone i] at he; cases he), fun j b hb' => (by rw [hbnone j] at hb'; cases hb'),
    ⟨hsum, fun x hx => by simpa using List.all_eq_true.mp hwhole x hx⟩,
    fun txs l' l'' hreach hw hdel' => ?_⟩
  have hl' : l' = l := LendingLedger.Reaches.keeps (P := (· = l))
    (fun l₀ tx l₁ h₀ hw₀ ha => by subst h₀; exact absurd ha (hstuck tx l₁ hw₀)) rfl hreach hw
  subst hl'
  rw [hdel'] at hdel
  cases hdel

/-- A LoanBrokerDelete of a broker with loans fails. -/
private lemma LendingLedger.brokerDelete_with_loans {l l' : LendingLedger} {j : Nat} {b : LoanBroker}
    (hb : l.broker? j = some b) (hc : b.loanCount ≠ 0) : (l.apply (.loanBrokerDelete j)).run ≠ .ok (.ok l') := by
  intro h
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_broker rfl h
  have hcan : b.canDelete l.vault = .ok .tecHAS_OBLIGATIONS := by
    simp [LoanBroker.canDelete, hc]
  simp only [LendingLedger.applyBroker, hb] at hu
  unfold_ter at hu
  rw [hcan] at hu
  simp only at hu
  rw [if_pos (show (!TER.tecHAS_OBLIGATIONS.isTesSuccess) = true from rfl)] at hu
  simp at hu

/-- A VaultDelete fails while a broker is left. -/
private lemma LendingLedger.vaultDelete_with_broker {l l' : LendingLedger}
    (hany : l.brokers.any Option.isSome = true) : (l.apply .vaultDelete).run ≠ .ok (.ok l') := by
  intro h
  rw [LendingLedger.apply_of_preflight rfl] at h
  simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h
  unfold_ter at h
  simp only [hany, ite_true] at h
  repeat' split at h
  all_goals simp_all

/-- After `rdTxs`, one second past RedemptionDate: one broker and one active loan whose grace period has not ended,
whose default is too soon and which can't be deleted, a vault that is not coarsened, and holder shares that add up
to SharesTotal. -/
private def wdGraceCheck : Bool :=
  match niGenesis.run rdTxs with
  | .ok l =>
    match l.vault.schedule, l.loan? 0, l.broker? 0 with
    | some s, some e, some b =>
      !l.vaultDeleted && decide (s.redemptionDate < l.now) &&
        decide (l.now.toNat ≤ s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat) &&
        l.loans.length == 1 && l.brokers.length == 1 && e.brokerIndex == 0 && b.loanCount != 0 &&
        !e.loan.isPending &&
        decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
          10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) &&
        decide (b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) &&
        decide ((l.shares.map Number.toRat).sum = l.vault.sharesTotal.toRat) &&
        l.shares.all (fun x => x.toRat.den == 1) &&
        (match e.loan.withBroker b with
          | .ok loan =>
            (match loan.canDelete with
              | .tesSUCCESS => false
              | _ => true) &&
            (match loan.canManage .default l.now with
              | .ok .tesSUCCESS => false
              | _ => true)
          | .error _ => true)
    | _, _, _ => false
  | .error _ => false

private lemma wdGraceCheck_true : wdGraceCheck = true := by native_decide

/-- No wind-down deletes the vault one second past RedemptionDate while a loan's grace period runs on. Its default
is too soon and it can't be deleted, so its broker stays and VaultDelete fails. -/
lemma LendingLedger.wind_down_grace_witness :
    ∃ (l : LendingLedger) (s : VaultSchedule), l.Reachable ∧ l.vaultDeleted = false ∧ l.vault.schedule = some s ∧
      s.redemptionDate < l.now ∧
      (∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
        l.now.toNat ≤ s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
        e.loan.paymentRemaining ≠ 0 → l.NotCoarsened) ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) ∧
      l.SharesSum ∧
      (∀ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' → (∀ i, l'.loan? i = none) →
        l'.NoDust) ∧
      ∀ (txs : List LendingTx) (l' l'' : LendingLedger), LendingLedger.Reaches l txs l' →
        (∀ tx ∈ txs, tx.isWindDown = true) → (l'.apply .vaultDelete).run ≠ .ok (.ok l'') := by
  have hc := wdGraceCheck_true
  unfold wdGraceCheck at hc
  split at hc
  case h_2 => cases hc
  rename_i l hl
  split at hc
  case h_2 => cases hc
  rename_i s e0 b0 hs he0 hb0
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnd, hpast⟩, hgr⟩, hlen⟩, hblen⟩, hbi⟩, hcount⟩, hpend⟩, hnc⟩, hca⟩, hsum⟩, hwhole⟩,
    hmatch⟩ := hc
  have hr : l.Reachable := LendingLedger.Reachable.of_run niGenesis_genesis hl
  -- the loan and the broker are the only ones, and the loan's default and deletion both fail
  have hlone : ∀ (l₀ : LendingLedger) (i : Nat) (e : LoanEntry), l₀.loans = l.loans → l₀.loan? i = some e →
      i = 0 ∧ e = e0 := by
    intro l₀ i e hL he
    unfold LendingLedger.loan? at he he0
    rw [hL] at he
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [he0] at he
      exact ⟨rfl, (Option.some.inj he).symm⟩
    · simp [List.getElem?_eq_none (show l.loans.length ≤ i by omega)] at he
  have hbone : ∀ (l₀ : LendingLedger) (j : Nat) (b : LoanBroker), l₀.brokers = l.brokers → l₀.broker? j = some b →
      j = 0 ∧ b = b0 := by
    intro l₀ j b hB hb
    unfold LendingLedger.broker? at hb hb0
    rw [hB] at hb
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hb0] at hb
      exact ⟨rfl, (Option.some.inj hb).symm⟩
    · simp [List.getElem?_eq_none (show l.brokers.length ≤ j by omega)] at hb
  have hbad : ∀ loan, e0.loan.withBroker b0 = .ok loan →
      loan.canDelete ≠ .tesSUCCESS ∧ loan.canManage .default l.now ≠ .ok .tesSUCCESS := by
    intro loan hw
    rw [hw] at hmatch
    simp only [Bool.and_eq_true] at hmatch
    obtain ⟨h1, h2⟩ := hmatch
    refine ⟨fun hd => ?_, fun hm => ?_⟩
    · rw [hd] at h1
      simp at h1
    · rw [hm] at h2
      simp at h2
  -- every wind-down step keeps the loans, the brokers and the close time
  have hstep : ∀ (l₀ : LendingLedger) (tx : LendingTx) (l₁ : LendingLedger),
      (l₀.loans = l.loans ∧ l₀.brokers = l.brokers ∧ l₀.now = l.now) → tx.isWindDown = true →
      (l₀.apply tx).run = .ok (.ok l₁) → (l₁.loans = l.loans ∧ l₁.brokers = l.brokers ∧ l₁.now = l.now) := by
    rintro l₀ tx l₁ ⟨hL, hB, hN⟩ hw hok
    cases tx with
    | loanManage i a =>
      exfalso
      have ha : a = .default := by cases a <;> simp_all [LendingTx.isWindDown]
      subst ha
      obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hok
      obtain ⟨e, broker, loan, r, he, hb, hwb, hcan, -, -⟩ := l₀.applyLoan_manage_inv u i .default hu
      obtain ⟨rfl, rfl⟩ := hlone l₀ i e hL he
      obtain ⟨-, rfl⟩ := hbone l₀ 0 broker hB (by rw [hbi] at hb; exact hb)
      rw [hN] at hcan
      exact (hbad loan hwb).2 hcan
    | loanDelete i =>
      exfalso
      obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hok
      obtain ⟨e, broker, loan, r, he, hb, hwb, hcan, -, -⟩ := l₀.applyLoan_delete_inv u i hu
      obtain ⟨rfl, rfl⟩ := hlone l₀ i e hL he
      obtain ⟨-, rfl⟩ := hbone l₀ 0 broker hB (by rw [hbi] at hb; exact hb)
      exact (hbad loan hwb).1 hcan
    | loanBrokerDelete j =>
      exfalso
      cases hbj : l₀.broker? j with
      | none => exact LendingLedger.brokerDelete_empty hbj hok
      | some b =>
        obtain ⟨-, rfl⟩ := hbone l₀ j b hB hbj
        exact LendingLedger.brokerDelete_with_loans hbj hcount hok
    | vaultWithdraw h amount =>
      obtain ⟨hL', hB'⟩ := LendingLedger.vault_ops_scope_proof l₀ l₁ _ rfl hok
      obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault rfl hok
      refine ⟨hL'.trans hL, hB'.trans hB, ?_⟩
      rw [← hN]
      unfold LendingLedger.commitVault
      split <;> rfl
    | _ => simp [LendingTx.isWindDown] at hw
  have hkeep : ∀ (txs : List LendingTx) (l' : LendingLedger), LendingLedger.Reaches l txs l' →
      (∀ tx ∈ txs, tx.isWindDown = true) → (l'.loans = l.loans ∧ l'.brokers = l.brokers ∧ l'.now = l.now) :=
    fun txs l' hreach hw => LendingLedger.Reaches.keeps
      (P := fun l₀ => l₀.loans = l.loans ∧ l₀.brokers = l.brokers ∧ l₀.now = l.now) hstep ⟨rfl, rfl, rfl⟩ hreach hw
  refine ⟨l, s, hr, hnd, hs, hpast, ⟨0, e0, he0, hgr⟩,
    fun i e he hp => absurd hp (by obtain ⟨-, rfl⟩ := hlone l i e rfl he; simp [hpend]),
    fun _ _ _ _ _ => hnc, fun j b hb => by obtain ⟨-, rfl⟩ := hbone l j b rfl hb; exact hca,
    ⟨hsum, fun x hx => by simpa using List.all_eq_true.mp hwhole x hx⟩, ?_, ?_⟩
  · intro txs l' hw hnone
    have hall : ∀ tx ∈ txs, tx.isWindDown = true := by
      clear hnone
      induction hw with
      | refl => simp
      | step tx _ hw' _ ih =>
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact ih t ht
        · rw [List.mem_singleton.mp ht]
          exact hw'.isWindDown
    obtain ⟨hL, -, -⟩ := hkeep txs l' hw.reaches hall
    have h0 := hnone 0
    unfold LendingLedger.loan? at h0 he0
    rw [hL, he0] at h0
    cases h0
  · intro txs l' l'' hreach hw hdel
    obtain ⟨-, hB, -⟩ := hkeep txs l' hreach hw
    have hany : l'.brokers.any Option.isSome = true := by
      rw [hB]
      unfold LendingLedger.broker? at hb0
      cases hx : l.brokers[0]? with
      | none => rw [hx] at hb0; cases hb0
      | some x =>
        rw [hx] at hb0
        cases x with
        | none => cases hb0
        | some x => exact List.any_eq_true.mpr ⟨some x, List.mem_of_getElem? hx, rfl⟩
    exact LendingLedger.vaultDelete_with_broker hany hdel

end XRPL.Model.Lending
