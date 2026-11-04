import XRPL.Properties.Lending.Ledger.Common.AssetFlowDefs
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
import XRPL.Properties.Lending.Ledger.Common.DefaultCredit
import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Ledger.Common.SharesNonneg
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # Each transaction moves AssetsTotal by exactly its flow

On a reachable ledger that is not coarsened before or after it, a transaction changes AssetsTotal by exactly the
assets it moves: a deposit adds what it charges, a withdrawal and a clawback take off what they pay, a payment adds
its interest and a default writes off the principal the cover does not pay. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount VaultAmounts
  computeClawback_success_reduces)

open private Vault.cash_update_eq Loan.unimpairIfImpaired_balances vault_credit_cross Loan.create_total_eq
  Loan.accept_total_eq Loan.changeImpairment_total_eq Loan.delete_total_eq
  from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private Vault.assetsTotal_eq_of_grid Vault.assetsTotal_bounds Vault.total_of_raw
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private Loan.unimpairIfImpaired Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay

open XRPL.Model.SingleAssetVault in
/-- A deposit adds exactly what it charges to a vault below `10^16` base units. The inflow check keeps the
charge inside the Open zone, and on the base grid it lands exactly. -/
private lemma Vault.deposit_total_eq (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat + r.vault'.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat + r.assets.toRat := by
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, hadj, hraw, hras, -⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r h
  have hmax := hasset.maxValue_le
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra isDonation amounts hrac hraty hmax hcomp
  have hcharge : ∃ k : ℤ, amounts.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ (sharesToAssetsDeposit_form v amounts.shares assets hmax hsta).1 hcl
    · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ hrac hcl
  obtain ⟨amountNum, hnum, hex⟩ := Vault.checkOpenLimit_ok_inv v _ hin
  obtain ⟨hnv, hnn⟩ := hcf.toNumber_exact amountNum hnum
  obtain ⟨k, hk⟩ := hcharge
  have hex' := hex
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at hex'
  obtain ⟨atot, hat, -⟩ := bind_ok_peel _ _ _ hex'
  have hatv := Vault.assetsTotal_eq_of_grid v atot hv hS hat
  obtain ⟨hatn, -, -⟩ := Vault.assetsTotal_bounds v atot hat
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  obtain ⟨a, ha⟩ := hv.1.2
  obtain ⟨d, hd⟩ := hv.2.2
  have hb := Vault.exceedsOpenLimit_false_total v amountNum atot hnn (by rw [hnv]; exact hc0) hat hatn
    (by rw [hatv]; linarith) ⟨a + d, by rw [hatv, ha, hd]; push_cast; ring⟩ hYg.2 ⟨k, by rw [hnv, hk]⟩ hex
  rw [hatv, hnv] at hb
  obtain ⟨assetsNum, _, s, aa', _, hnum', -, -, hs, haa, hrw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  rw [hnum, Except.ok.injEq] at hnum'
  subst hnum'
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hlim : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent < 10 ^ (16 + v.baseExponent) := by
    rw [open_line_eq]; nlinarith
  have hcash := Vault.cash_update_eq v amountNum s aa' hasset hv.1 ⟨hnn, k, by rw [hnv, hk]⟩
    (by rw [hnv]; linarith) (by rw [hnv]; linarith) hs haa
  rw [hnv] at hcash
  rw [show r.vault'.assetsAvailable = r.vault'.toRawVault.assetsAvailable from rfl,
    show r.vault'.assetsDeployed = r.vault'.toRawVault.assetsDeployed from rfl, hraw, hrw, hras]
  show aa'.toRat + v.assetsDeployed.toRat = _
  linarith

open XRPL.Model.SingleAssetVault in
/-- A withdrawal pays an amount of the asset that is whole base units, at most AssetsAvailable, and debits it. -/
private lemma Vault.withdraw_payout_units' (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (haa : ∃ k : ℕ, v.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ (∃ j : ℕ, r.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      r.assets.toRat ≤ v.assetsAvailable.toRat ∧ ∃ raw : RawVault,
        (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
          r.vault'.toRawVault = raw := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a 100% fee pays nothing
  all_goals try
    have hz := STAmount.zero_canonicalOrZero v.numericType
    exact ⟨hz.1, ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]; simp⟩,
      by rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]; exact v.exact.assetsAvailable_nonneg,
      _, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩
  -- the final withdrawal pays all the cash, which the asset stores exactly
  all_goals try
    have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
    have hpc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1
    have hfe := Vault.final_payout_exact v _ hst hmax hp
    obtain ⟨kA, hAv⟩ := haa
    exact ⟨hpc, ⟨kA, by rw [hfe, hAv]⟩, le_of_eq hfe, _, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩
  -- the fee path pays the payout clamped onto the grid of the cash, which the cash covers
  all_goals try
    have hp : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    obtain ⟨hpc, hpty⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp
    have hcf := (clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl).1
    obtain ⟨j, hj⟩ := clampToSumExponent_units _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 (fun hi => le_of_eq (v.baseExponent_bounds.2.2 (by
        unfold STAmount.integral at hi; rwa [(STAmount.operator_neg_fields _).1, hpty] at hi))) hcl
    have hkeep := Vault.payout_keeps_cash v _ _ hcf ‹_› ‹_›
    rw [STAmount.operator_neg_toRat] at hkeep
    exact ⟨hcf, ⟨j, hj⟩, by linarith, _, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩
  -- a zero payout skips the fee
  all_goals
    have hnf : STAmount.operator_eq _ _ = false := ‹_›
    have hzs : ¬ (STAmount.operator_eq _ _ = false ∧ STAmount.isZero _ = false) := ‹_›
    have hz0 := Bool.of_not_eq_false (fun h => hzs ⟨hnf, h⟩)
    have h0 := (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz0)
    exact ⟨Or.inr hz0, ⟨0, by rw [h0]; simp⟩, by rw [h0]; exact v.exact.assetsAvailable_nonneg, _, ‹_›,
      (RawVault.to_lawful_ok ‹_›).1⟩

open XRPL.Model.SingleAssetVault in
/-- A clawback destroys shares of at least zero, when the holder's shares are. -/
private lemma assetsToSharesClawback_nonneg (v : Vault) (assets holderShares shares : STAmount) (waive : Bool)
    (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hhs : holderShares.CanonicalOrZero ∧ 0 ≤ holderShares.toRat)
    (hok : assetsToSharesClawback v assets holderShares waive = .ok shares) :
    shares.CanonicalOrZero ∧ 0 ≤ shares.toRat := by
  simp only [assetsToSharesClawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  · exact ⟨(STAmount.ofNumber_canonicalOrZero .int64 _ _ _ (fun _ => by decide) ‹_›).1,
      STAmount.ofNumber_nonneg _ _ _ _ v.wf.sharesTotal_norm
        (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) ‹_›⟩
  · exact hhs
  · obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ‹_›
    exact ⟨Or.inl (hic.canonical (by rw [hty]; decide)), assetsToSharesWithdraw_nonneg v _ _ waive hc hnn ‹_›⟩

open XRPL.Model.SingleAssetVault in
/-- A clawback recovers an amount of the asset that is whole base units, at most AssetsAvailable, and debits it. -/
private lemma Vault.clawback_payout_units' (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.CanonicalOrZero ∧ 0 ≤ holderShares.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ (∃ j : ℕ, r.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      r.assets.toRat ≤ v.assetsAvailable.toRat ∧ ∃ raw : RawVault,
        (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
          r.vault'.toRawVault = raw := by
  obtain ⟨amounts, raw, hcomp, hadj, hraw, hras, hrs⟩ :=
    Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  obtain ⟨rec, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  have hcap : ∀ (sd ar : STAmount) (n : Number), sd.CanonicalOrZero → 0 ≤ sd.toRat →
      v.sharesToAssetsWithdraw sd waive = .ok ar → ar.toNumber .to_nearest = .ok n →
      n.operator_gt v.assetsAvailable = false →
      ar.CanonicalOrZero ∧ ar.mNumericType = v.numericType ∧ 0 ≤ ar.toRat ∧ ar.toRat ≤ v.assetsAvailable.toRat := by
    intro sd ar n hsd hsd0 hs2a hn hgt
    obtain ⟨har, hty⟩ := Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a
    obtain ⟨hv, hnorm⟩ := har.toNumber_exact n hn
    have hle : ¬ v.assetsAvailable.toRat < n.toRat := by
      rw [← operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm]
      simpa [Number.operator_gt] using hgt
    exact ⟨har, hty, Vault.sharesToAssetsWithdraw_nonneg v _ _ waive hsd hsd0 hs2a, by rw [← hv]; linarith⟩
  obtain ⟨hrc, hrty, hr0, hrle⟩ : rec.CanonicalOrZero ∧ rec.mNumericType = v.numericType ∧ 0 ≤ rec.toRat ∧
      rec.toRat ≤ v.assetsAvailable.toRat := by
    cases hpr with
    | direct _ _ n ha2s hs2a hn hgt =>
      obtain ⟨hsd, hsd0⟩ := assetsToSharesClawback_nonneg v _ _ _ waive hc hnn hhs ha2s
      exact hcap _ _ n hsd hsd0 hs2a hn hgt
    | capped _ _ cash _ _ _ n _ _ _ _ hcash ha2s hs2a hn hgt =>
      have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
      have hc0 := STAmount.ofNumber_nonneg _ _ _ _ v.wf.assetsAvailable_norm
        (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg) hcash
      obtain ⟨hic, hty⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true waive ha2s
      exact hcap _ _ n (Or.inl (hic.canonical (by rw [hty]; decide)))
        (assetsToSharesWithdraw_nonneg v _ _ waive hcc hc0 ha2s) hs2a hn hgt
  rw [hras, hrs]
  refine ⟨?_, ?_, ?_, raw, hadj, hraw⟩
  all_goals rcases hrec with ⟨hz, heq⟩ | ⟨-, hcl, -⟩
  · rw [heq]; exact hrc
  · exact (clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl).1
  · exact ⟨0, by rw [heq, (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]; simp⟩
  · exact clampToSumExponent_units _ _ _ _ hrc.operator_neg v.baseExponent_range.1 v.baseExponent_range.2
      (fun hi => le_of_eq (v.baseExponent_bounds.2.2 (by
        unfold STAmount.integral at hi; rwa [(STAmount.operator_neg_fields _).1, hrty] at hi))) hcl
  · rw [heq, (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]; exact v.exact.assetsAvailable_nonneg
  · have hle := clampToSumExponent_le_abs _ _ _ _ hrc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl
    rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0] at hle
    linarith

/-- A debit of whole base units, at most AssetsAvailable, lands exactly on a vault below `10^16` base units. -/
private lemma Vault.debit_total_eq (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hc : assets.CanonicalOrZero) (hj : ∃ j : ℕ, assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hle : assets.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares assets.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat + raw.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat - assets.toRat := by
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, hrw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hnv, hnn⟩ := hc.operator_neg.toNumber_exact assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hnv
  obtain ⟨j, hj⟩ := hj
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have ha0 : 0 ≤ assets.toRat := by rw [hj]; positivity
  have hcash := Vault.cash_update_eq v assetsNum s aa' hasset hv.1 ⟨hnn, -(j : ℤ), by rw [hnv, hj]; push_cast; ring⟩
    (by rw [hnv]; linarith) (by rw [hnv]; linarith [v.exact.assetsAvailable_nonneg]) hs haa
  rw [hrw]
  show aa'.toRat + v.assetsDeployed.toRat = _
  rw [hcash, hnv]
  ring

/-- The loan a successful loan transaction reads at `i`. -/
private lemma LendingLedger.loanRead_eq {l : LendingLedger} {i : Nat} {e : LoanEntry} {b : LoanBroker} {loan : Loan}
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan) :
    l.loanRead i = some loan := by
  simp only [LendingLedger.loanRead, he, hb, hw]

/-- A payment adds exactly its interest to AssetsTotal on a reachable ledger whose vault is not coarsened
before or after it. The vault gains the principal and the interest and gives up the principal from AssetsDeployed. -/
private lemma LendingLedger.pay_total_eq (l l' : LendingLedger) (i : Nat) (pt : LoanPaymentType) (amount : Number)
    (hr : l.Reachable) (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) (hnc : l.NotCoarsened)
    (hnc' : l'.NotCoarsened) :
    l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat =
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.paidInterest i pt amount := by
  have hbe' := LendingLedger.apply_baseExponent h
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, broker, loan, r, he, hb, hw, -, hpay, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
  change r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ r.pool'.baseExponent
    at hnc'
  change r.pool'.baseExponent = l.vault.baseExponent at hbe'
  rw [hbe'] at hnc'
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, -, -⟩ := LendingLedger.base_grid_proof l hr hmax
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb, hw⟩
  obtain ⟨hblo, hbhi, hbint⟩ := l.vault.baseExponent_bounds
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid l.vault
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hT : 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ≤ 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    mul_le_mul_of_nonneg_right (by norm_num) hp.le
  unfold LendingLedger.NotCoarsened at hnc

  obtain ⟨p, hp', hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hpay
  have hip : l.paidInterest i pt amount = p.amounts.interestPaid.toRat := by
    simp only [LendingLedger.paidInterest, LendingLedger.loanRead_eq he hb hw, hp']
  rw [hip]
  obtain ⟨-, hu', hst, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hp'
  obtain ⟨hpAA, hpAD, hpnt, hpbe⟩ := Loan.unimpairIfImpaired_balances loan l.vault p.pool loan.unimpaired
    (hr.storesAvailable hmax) hu'
  obtain ⟨toPool, yd, toBroker, cover', debt', raw, broker', hsums, hadj, hlaw, -, -, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  obtain ⟨hPg, hIg⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now p (by rw [hls]; omega) hp'
  rw [hls] at hPg hIg
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hparts
  obtain ⟨⟨hP0s, hI0s⟩, -⟩ := hparts
  have hP0 := Number.toRat_nonneg_of_not_signum_neg _ hPg.1 hP0s
  have hI0 := Number.toRat_nonneg_of_not_signum_neg _ hIg.1 hI0s
  obtain ⟨tot, credit, htot, hcred, hto⟩ := hsums.toPool
  rw [hpb, hnt, hpbe] at hcred
  obtain ⟨hsa, -⟩ := Vault.adjustBalances_ok_inv p.pool _ raw hadj
  obtain ⟨aa, haa, hround⟩ := hsa.cash
  have hdep := hsa.deployed
  rw [Vault.total_of_raw hlaw]
  have hraw := (RawVault.to_lawful_ok hlaw).1
  have hrAD0 : 0 ≤ raw.assetsDeployed.toRat := by
    have := r.pool'.exact.assetsDeployed_nonneg
    rwa [show r.pool'.toExact.assetsDeployed = r.pool'.toRawVault.assetsDeployed.toRat from rfl, hraw] at this
  have hrAA0 : 0 ≤ raw.assetsAvailable.toRat := by
    have := r.pool'.exact.assetsAvailable_nonneg
    rwa [show r.pool'.toExact.assetsAvailable = r.pool'.toRawVault.assetsAvailable.toRat from rfl, hraw] at this
  have hnc'' : raw.assetsAvailable.toRat + raw.assetsDeployed.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    rw [← Vault.total_of_raw hlaw]; exact hnc'
  have hpAAg : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable := by
    obtain ⟨k, hk⟩ := hAAg.2
    exact ⟨p.pool.wf.assetsAvailable_norm, k, by rw [hpAA, hk, hpbe]⟩
  have hpADg : Number.OnGrid p.pool.baseExponent p.pool.assetsDeployed := by
    obtain ⟨k, hk⟩ := hADg.2
    exact ⟨p.pool.wf.assetsDeployed_norm, k, by rw [hpAD, hk, hpbe]⟩
  rw [hpbe] at hpAAg hpADg
  -- the principal never exceeds AssetsDeployed, so taking it off is exact
  have hPAD : p.amounts.principalPaid.toRat ≤ l.vault.assetsDeployed.toRat := by
    by_contra hgt
    push Not at hgt
    obtain ⟨kD, hkD⟩ := hADg.2
    obtain ⟨kP, hkP⟩ := hPg.2
    have hlt : kD < kP := by
      have : (kD : ℚ) * 10 ^ l.vault.baseExponent < (kP : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [← hkD, ← hkP]; exact hgt
      exact_mod_cast lt_of_mul_lt_mul_right this hp.le
    obtain ⟨w, hw', hwv⟩ := Number.exists_normalized_int_mul_pow (-1) l.vault.baseExponent (by norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hR := operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsDeployed_norm
      (Number.operator_neg_isNormalized _ hPg.1) hdep
    have := Number.roundsToRepresentable_le _ _ hR w hw' (by
      rw [hwv, Number.toRat_neg, hpAD, hkD, hkP]
      have : ((kD - kP : ℤ) : ℚ) ≤ -1 := by exact_mod_cast (by omega : kD - kP ≤ -1)
      push_cast at this ⊢
      nlinarith)
    rw [hwv] at this
    push_cast at this
    linarith
  have hPdeploy : raw.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - p.amounts.principalPaid.toRat := by
    have := Number.add_exact_of_grid hpADg hPg.neg (by rw [Number.toRat_neg, hpAD]; nlinarith)
      (by rw [Number.toRat_neg, hpAD]; linarith) hsr hdep
    rw [this, Number.toRat_neg, hpAD]; ring
  rw [hPdeploy]
  have htotn := operator_add_isNormalized_to_nearest_sz _ _ _ hPg.1 hIg.1 htot
  have htot0 : 0 ≤ tot.toRat := operator_add_nonneg _ _ _ hPg.1 hIg.1 htot (by linarith)
  have hpasset : Vault.HoldsAsset p.pool := by unfold Vault.HoldsAsset; rw [hpnt]; exact hasset
  rw [hpnt] at hround
  obtain ⟨Wn, hWn, hWv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) l.vault.baseExponent
    (by constructor <;> norm_num) ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hWv' : Wn.toRat = 10 ^ 16 * 10 ^ l.vault.baseExponent := by rw [hWv]; push_cast; ring
  have hPI_of : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent →
      tot.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat := fun hlt =>
    Number.add_exact_of_grid hPg hIg (by nlinarith) (by linarith) hsr htot
  cases hint : l.vault.numericType.isIntegral
  · -- an IOU vault: the credit lands exactly unless it crosses `10^16` base units, and the vault is not coarsened
    -- after the payment
    have hfr := NumericType.eq_fractional_of_not_integral hint
    rw [hfr] at hcred hround
    by_cases hcross : 10 ^ 16 * 10 ^ l.vault.baseExponent ≤ p.pool.assetsAvailable.toRat + tot.toRat
    · exfalso
      have := vault_credit_cross p.pool.assetsAvailable tot l.vault.baseExponent credit toPool aa raw.assetsAvailable
        p.pool.wf.assetsAvailable_norm hpAAg.2 (by rw [hpAA]; exact hAA0) (by rw [hpAA]; linarith) htotn
        ⟨hblo, hbhi⟩ hcross hcred hto haa hround
      linarith
    push Not at hcross
    have hPI : tot.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat := by
      apply hPI_of
      by_contra hbig
      push Not at hbig
      have := Number.roundsToRepresentable_ge tot _ (operator_add_rounded_to_nearest _ _ _ hPg.1 hIg.1 htot) Wn hWn
        (by rw [hWv']; exact hbig)
      rw [hWv'] at this
      rw [hpAA] at hcross
      linarith
    obtain ⟨kA, hkA⟩ := hpAAg.2
    obtain ⟨kP, hkP⟩ := hPg.2
    obtain ⟨kI, hkI⟩ := hIg.2
    have hkA0 : 0 ≤ kA := by
      have : (0 : ℚ) ≤ (kA : ℚ) * 10 ^ l.vault.baseExponent := by rw [← hkA, hpAA]; exact hAA0
      exact_mod_cast nonneg_of_mul_nonneg_left this hp
    have htotk : tot.toRat = ((kP + kI : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [hPI, hkP, hkI]; push_cast; ring
    have hroom : p.pool.assetsAvailable.toRat + tot.toRat ≤
        (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
      have hsum : p.pool.assetsAvailable.toRat + tot.toRat = ((kA + kP + kI : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [htotk, hkA]; push_cast; ring
      have hk : kA + kP + kI < 10 ^ 16 := by
        have : ((kA + kP + kI : ℤ) : ℚ) * 10 ^ l.vault.baseExponent <
            ((10 ^ 16 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
          rw [← hsum]; push_cast; exact hcross
        exact_mod_cast lt_of_mul_lt_mul_right this hp.le
      rw [hsum, open_line_eq]
      have : ((kA + kP + kI : ℤ) : ℚ) ≤ 10 ^ 16 - 1 := by
        have : kA + kP + kI ≤ 10 ^ 16 - 1 := by omega
        exact_mod_cast this
      nlinarith
    have hcv := sumRoundAndSubtract_at_base _ _ _ credit kA.toNat p.pool.wf.assetsAvailable_norm
      (by rw [hkA]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hkA0).symm) htotn htot0 ⟨by omega, hbhi⟩ hroom hcred
    obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ credit p.pool.wf.assetsAvailable_norm
      (by rw [hpAA]; exact hAA0) htotn htot0 (Vault.baseExponent_range l.vault) hcred
    obtain ⟨htv, htnn⟩ := htn toPool hto
    have hfl : ⌊tot.toRat / 10 ^ l.vault.baseExponent⌋ = kP + kI := by
      rw [htotk, mul_div_assoc, div_self hp.ne', mul_one, Int.floor_intCast]
    have htoP : toPool.toRat = tot.toRat := by rw [htv, hcv, hfl, htotk]
    have htoPg : Number.OnGrid l.vault.baseExponent toPool := ⟨htnn, kP + kI, by rw [htoP, htotk]⟩
    have hAAp : raw.assetsAvailable.toRat = p.pool.assetsAvailable.toRat + toPool.toRat := by
      refine Vault.cash_update_eq p.pool toPool aa raw.assetsAvailable hpasset (by rw [hpbe]; exact hpAAg)
        (by rw [hpbe]; exact htoPg) (by rw [hpAA, htoP]; linarith) ?_ haa (by rw [hpnt, hfr]; exact hround)
      rw [hpbe, open_line_eq, hpAA, htoP]
      rw [hpAA] at hcross
      linarith
    rw [hAAp, hpAA, htoP, hPI]
    ring
  · -- an XRP or MPT vault: the credit is the sum floored to a whole unit, which it already is
    have hb0 : l.vault.baseExponent = 0 := hbint hint
    unfold sumRoundAndSubtract at hcred
    rw [if_pos hint] at hcred
    obtain ⟨x, hx, hcred⟩ := bind_ok_peel _ _ _ hcred
    obtain rfl : x = credit := Except.ok.inj hcred
    have htneg := Number.negative_false_of_nonneg tot htotn htot0
    obtain ⟨iv, hiv, hxv⟩ := STAmount.ofNumber_integral_toRat _ tot _ x hint htneg hx
    obtain ⟨hfl1, hfl2⟩ := Number.to_rep_downward_floor tot iv htotn htneg hiv
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ x hint hx
    have hsmall : x.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, hsnv, -⟩ := STAmount.toNumber_integral_small_exact x .to_nearest hic hsmall
    rw [hsn, Except.ok.injEq] at hto
    subst hto
    have hcrn : sn.isNormalized := STAmount.toNumber_isNormalized x _ sn hsn
    rw [hb0, zpow_zero, mul_one] at hnc hnc'' hWv'
    obtain ⟨kP, hkP⟩ := hPg.2
    obtain ⟨kI, hkI⟩ := hIg.2
    obtain ⟨kA, hkA⟩ := hpAAg.2
    rw [hb0, zpow_zero, mul_one] at hkP hkI hkA
    have hkA0 : 0 ≤ kA := by
      have : (0 : ℚ) ≤ (kA : ℚ) := by rw [← hkA, hpAA]; exact hAA0
      exact_mod_cast this
    have hround_ge : ∀ (y : Number) (k : ℤ), y.isNormalized → (k : ℚ) ≤ y.toRat → 0 ≤ k →
        STAmount.roundToNumericType l.vault.numericType y .to_nearest = .ok raw.assetsAvailable →
        (k : ℚ) ≤ raw.assetsAvailable.toRat := by
      intro y k hyn hky hk0 hr'
      unfold STAmount.roundToNumericType at hr'
      cases hof : STAmount.ofNumber l.vault.numericType y .to_nearest with
      | error e => rw [hof] at hr'; cases hr'
      | ok rr =>
      rw [hof] at hr'
      simp only at hr'
      obtain ⟨hic', hty'⟩ := STAmount.ofNumber_integral_canonical _ _ _ rr hint hof
      have hsmall' : rr.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have h1 := hic'.in_range
        rw [hty'] at h1
        have := hmax hint
        have : maxRep.toNat = 2 ^ 63 - 1 := by decide
        omega
      obtain ⟨sn', hsn', hsnv', -⟩ := STAmount.toNumber_integral_small_exact rr .to_nearest hic' hsmall'
      rw [hsn', Except.ok.injEq] at hr'
      have hy0 : 0 ≤ y.toRat := le_trans (by exact_mod_cast hk0) hky
      have hN := STAmount.ofNumber_to_nearest_neighbour _ y rr hyn hy0 hof (Or.inl hint)
      unfold RoundsToRepresentableAt at hN
      change rr.toRat = _ ∨ rr.toRat = _ at hN
      rw [show rr.exponent = rr.mOffset from rfl, hic'.offset_zero, zpow_zero, div_one, mul_one, mul_one] at hN
      rw [← hr', hsnv']
      rcases hN with hfl | hce
      · rw [hfl]; exact_mod_cast Int.le_floor.mpr hky
      · rw [hce]; exact hky.trans (Int.le_ceil _)
    -- the principal plus interest is below `10^16`, else AssetsAvailable' would reach it
    have hPIlt : kP + kI < 10 ^ 16 := by
      by_contra hbig
      push Not at hbig
      have htotW : (10 ^ 16 : ℚ) ≤ tot.toRat := by
        have := Number.roundsToRepresentable_ge tot _ (operator_add_rounded_to_nearest _ _ _ hPg.1 hIg.1 htot) Wn hWn
          (by rw [hWv', hkP, hkI]; exact_mod_cast hbig)
        rwa [hWv'] at this
      have hivW : (10 ^ 16 : ℤ) ≤ iv.toInt := by
        have : ((10 ^ 16 : ℤ) : ℚ) < iv.toInt + 1 := by push_cast; linarith
        have : (10 ^ 16 : ℤ) < iv.toInt + 1 := by exact_mod_cast this
        omega
      have haaW : (10 ^ 16 : ℚ) ≤ aa.toRat := by
        have := Number.roundsToRepresentable_ge aa _
          (operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa) Wn hWn (by
            rw [hWv', hsnv, hxv, hpAA]
            have : ((10 ^ 16 : ℤ) : ℚ) ≤ iv.toInt := by exact_mod_cast hivW
            push_cast at this
            linarith)
        rwa [hWv'] at this
      have := hround_ge aa (10 ^ 16) (operator_add_isNormalized_to_nearest_sz _ _ _ p.pool.wf.assetsAvailable_norm
        hcrn haa) (by push_cast; exact haaW) (by norm_num) hround
      push_cast at this
      linarith
    have hPI : tot.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
      hPI_of (by rw [hb0, zpow_zero, mul_one, hkP, hkI]; exact_mod_cast hPIlt)
    have hcr : sn.toRat = tot.toRat := by
      rw [hsnv, hxv]
      have htk : tot.toRat = ((kP + kI : ℤ) : ℚ) := by rw [hPI, hkP, hkI]; push_cast; ring
      rw [htk] at hfl1 hfl2 ⊢
      have h1 : iv.toInt ≤ kP + kI := by exact_mod_cast hfl1
      have h2 : kP + kI < iv.toInt + 1 := by exact_mod_cast hfl2
      have : iv.toInt = kP + kI := by omega
      rw [this]
    have hkP0 : 0 ≤ kP := by
      have : (0 : ℚ) ≤ (kP : ℚ) := by rw [← hkP]; exact hP0
      exact_mod_cast this
    have hkI0 : 0 ≤ kI := by
      have : (0 : ℚ) ≤ (kI : ℚ) := by rw [← hkI]; exact hI0
      exact_mod_cast this
    have hKA : kA + (kP + kI) < 2 ^ 63 := by
      have h1 : (kA : ℚ) < 10 ^ 16 := by rw [← hkA, hpAA]; linarith
      have : kA < 10 ^ 16 := by exact_mod_cast h1
      omega
    obtain ⟨w, hw', hwv⟩ := Number.exists_normalized_of_int (kA + (kP + kI)) (by omega)
    have haav := Number.operator_add_exact_of_fits p.pool.wf.assetsAvailable_norm hcrn haa
      ⟨w, hw', by rw [hwv, hcr, hPI, hkA, hkP, hkI]; push_cast; ring⟩
    have haan := operator_add_isNormalized_to_nearest_sz _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa
    have haa0 : 0 ≤ aa.toRat := by rw [haav, hcr]; linarith
    have hden : aa.toRat.den = 1 := by
      rw [haav, hcr, hPI, hkA, hkP, hkI]
      rw [show (kA : ℚ) + ((kP : ℚ) + (kI : ℚ)) = ((kA + (kP + kI) : ℤ) : ℚ) by push_cast; ring]
      exact Rat.den_intCast _
    have hrep := STAmount.isRounded_eq_false_of_integral_round _ aa _ hint haan haa0 hden hround
    rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep hround, haav, hcr, hPI, hpAA]
    ring

/-- A clawback that passed its preflight claws a canonical amount, or zero, which claws all the holder's shares. -/
private lemma LendingTx.preflight_vaultClawback_canonical' (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault)
    (h : Nat) (assets : STAmount) (hpre : ((LendingTx.vaultClawback h assets).preflight l).isTesSuccess = true) :
    assets.CanonicalOrZero := by
  have hc : (isCanonicalAmount assets l.vault.numericType && !assets.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp only [LendingTx.preflight, hne, Bool.not_false, ↓reduceIte] at hpre
    exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)
  rw [Bool.and_eq_true] at hc
  by_cases hz : assets.mValue = 0
  · exact Or.inr (by simp [STAmount.isZero, hz])
  · exact Or.inl (isCanonicalAmount_canonical assets _ hasset.maxValue_le hc.1 hz).1

/-- A default of the stored loan writes off exactly PrincipalOutstanding − defaultCovered while the vault is not
coarsened. -/
private lemma LendingLedger.default_total_eq (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (r : LoanWithAmounts Vault) (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hnc : l.NotCoarsened) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat -
        (loan.principalOutstanding.toRat - r.amountToPool.toRat) := by
  obtain ⟨p, hp, hpv, hpad, -⟩ := hr.loanAt_principal hat
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hpo : loan.principalOutstanding.toRat ≤ 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hp10.le
  obtain ⟨-, -, hbint⟩ := Vault.baseExponent_bounds l.vault
  have haa' := Loan.manageDefault_cash_exact loan l.vault r hok (hr.loanAt_scale hat).2 hr.availableStored
    (hr.assetsAvailable_units hr.holdsAsset) hpo (fun hint => Or.inl (by
      unfold LendingLedger.NotCoarsened at hnc
      rw [hbint hint, zpow_zero, mul_one] at hnc
      have hAD0 := l.vault.exact.assetsDeployed_nonneg
      linarith))
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan l.vault r hok
  have hd := Number.operator_sub_exact_of_fits l.vault.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm
    hs.deployed (hr.deployed_fits hat)
  rw [haa', hd]
  ring

/-- A transaction moves AssetsTotal by exactly its flow on a reachable ledger that is not coarsened before it. A
payment also needs the ledger after it not coarsened. -/
lemma LendingLedger.flow_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hnc : l.NotCoarsened)
    (hnc' : (∃ i pt amount, tx = .loanPay i pt amount) → l'.NotCoarsened) :
    l'.vault.toRawVault.toExact.assetsTotal = l.vault.toRawVault.toExact.assetsTotal + (l.flowOf tx).net := by
  show l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat =
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + _
  by_cases hpay : ∃ i pt amount, tx = .loanPay i pt amount
  · obtain ⟨i, pt, amount, rfl⟩ := hpay
    rw [LendingLedger.pay_total_eq l l' i pt amount hr h hnc (hnc' ⟨i, pt, amount, rfl⟩)]
    show _ = _ + ((0 : ℚ) - 0 - 0 + l.paidInterest i pt amount - 0)
    ring
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, hYg, -⟩ := LendingLedger.base_grid_proof l hr hmax
  have hv : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hS : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent) := by
    rw [open_line_eq]; exact hnc
  have hst := hr.availableStored
  obtain ⟨kA, hkA⟩ := hr.assetsAvailable_units hasset
  have hinv := hr.scaleInv
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hvt : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    cases tx with
    | vaultDeposit hd amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l hd amount isDonation hasset hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hdep : (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok _) := ‹_›
        rw [Vault.deposit_total_eq _ _ _ _ _ hc hty hasset hv hS hYg _ hdep]
        show _ = _ + (l.depositedAssets amount isDonation - 0 - 0 + 0 - 0)
        simp only [LendingLedger.depositedAssets, dif_pos hpos, hdep]
        ring
      · cases hu
    | vaultWithdraw hd amount =>
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hwh : (l.vault.withdraw amount (l.isSoleShareholder hd) l.now hpos (some (l.sharesOf hd))).run =
          .ok (.ok _) := ‹_›
        have hw := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ hwh).1
        obtain ⟨hc, hj, hle, raw, hadj, hraw⟩ := Vault.withdraw_payout_units' _ _ _ _ _ hst ⟨kA, hkA⟩ hmax _ hw
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw,
          show (_ : VaultWithAmounts).vault'.assetsDeployed = _ from congrArg RawVault.assetsDeployed hraw,
          Vault.debit_total_eq _ _ _ raw hasset hv hS hc hj hle hadj]
        show _ = _ + ((0 : ℚ) - l.withdrawalPayout hd amount - 0 + 0 - 0)
        simp only [LendingLedger.withdrawalPayout, dif_pos hpos, hwh]
        ring
      · cases hu
    | vaultClawback hd assets =>
      have hca := LendingTx.preflight_vaultClawback_canonical' l hasset hd assets hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hnn
        unfold_ter at hu
        walk_ok
        have hof : STAmount.ofNumber .int64 (l.sharesOf hd) .to_nearest = .ok _ := ‹_›
        have hcw : (l.vault.clawback assets _ (l.isSoleShareholder hd) hnn).run = .ok (.ok _) := ‹_›
        obtain ⟨hsn, hs0⟩ := hr.sharesNonneg.sharesOf hd
        have hhs := (STAmount.ofNumber_canonicalOrZero .int64 _ _ _ (fun _ => by decide) hof).1
        have hhs0 := STAmount.ofNumber_nonneg _ _ _ _ hsn (Number.negative_false_of_nonneg _ hsn hs0) hof
        obtain ⟨hc, hj, hle, raw, hadj, hraw⟩ :=
          Vault.clawback_payout_units' _ _ _ _ hnn hca ⟨hhs, hhs0⟩ hmax _ hcw
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw,
          show (_ : VaultWithAmounts).vault'.assetsDeployed = _ from congrArg RawVault.assetsDeployed hraw,
          Vault.debit_total_eq _ _ _ raw hasset hv hS hc hj hle hadj]
        show _ = _ + ((0 : ℚ) - 0 - l.clawedAssets hd assets + 0 - 0)
        simp only [LendingLedger.clawedAssets, dif_pos hnn, hof, hcw]
        ring
      · cases hu
    | vaultBurnShares hd amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      show _ = _ + AssetFlows.net 0
      rw [AssetFlows.net_zero]; ring
    | vaultSet m b ub =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      show _ = _ + AssetFlows.net 0
      rw [AssetFlows.net_zero]; ring
    | _ => simp only [LendingTx.isVault] at hvt; cases hvt
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    have h0 : (l.flowOf tx).net = 0 := by
      cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;> exact AssetFlows.net_zero
    show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat = _ + _
    rw [h0, add_zero]
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat = _
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb', hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      have hst' := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _
      rw [Loan.create_total_eq _ _ _ _ _ _ _ _ r hasset hv hS hpn hpos hst' (hinv.brokers i broker hb') hcr]
      show _ = _ + AssetFlows.net 0
      rw [AssetFlows.net_zero]; ring
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _
      rw [Loan.accept_total_eq _ _ _ hasset hv hS hr']
      show _ = _ + AssetFlows.net 0
      rw [AssetFlows.net_zero]; ring
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
      obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb', hw⟩
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _
      rw [Loan.delete_total_eq _ _ _ hasset hv hS hls hnt hr']
      show _ = _ + AssetFlows.net 0
      rw [AssetFlows.net_zero]; ring
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _
      cases action with
      | impair =>
        simp only [Loan.manage, Loan.manageImpair] at hr'
        unfold_ter at hr'
        walk_ok
        rw [Loan.changeImpairment_total_eq loan _ true _ hasset hv hS ‹_›]
        show _ = _ + AssetFlows.net 0
        rw [AssetFlows.net_zero]; ring
      | unimpair =>
        rw [Loan.changeImpairment_total_eq loan _ false r hasset hv hS hr']
        show _ = _ + AssetFlows.net 0
        rw [AssetFlows.net_zero]; ring
      | default =>
        have hdef : ∃ r₀ : LoanWithAmounts Vault, (loan.manageDefault l.vault).run = .ok (.ok r₀) ∧
            r = r₀.toLoanWithPool := by
          simp only [Loan.manage] at hr'
          unfold_ter at hr'
          walk_ok
          exact ⟨_, ‹_›, rfl⟩
        obtain ⟨r₀, hok₀, rfl⟩ := hdef
        rw [show r₀.toLoanWithPool.pool' = r₀.pool' from rfl,
          LendingLedger.default_total_eq l hr i loan ⟨e, broker, he, hb', hw⟩ r₀ hok₀ hnc]
        show _ = _ + ((0 : ℚ) - 0 - 0 + 0 - l.defaultLoss i)
        obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
        simp only [LendingLedger.defaultLoss, LendingLedger.loanRead_eq he hb' hw, hdc]
        ring
    | loanPay i paymentType amount => exact absurd ⟨i, paymentType, amount, rfl⟩ hpay
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    show _ = _ + AssetFlows.net 0
    rw [AssetFlows.net_zero]; ring
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    show _ = _ + AssetFlows.net 0
    rw [AssetFlows.net_zero]; ring

/-- Over a run on which the vault never coarsens -> AssetsTotal' = AssetsTotal + Σ deposits − Σ withdrawals −
Σ clawbacks + Σ interestPaid − Σ defaultLosses. -/
lemma LendingLedger.assetsTotal_eq_proof (start l : LendingLedger) (txs : List LendingTx) (x : ℚ)
    (hr : start.Reachable) (hrun : start.ReachableFromIn txs l x)
    (hnc : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre <+: txs →
      start.ReachableFromIn pre l₁ x₁ → l₁.NotCoarsened) :
    l.vault.toRawVault.toExact.assetsTotal = start.vault.toRawVault.toExact.assetsTotal +
      (start.flows txs).deposits - (start.flows txs).withdrawals - (start.flows txs).clawbacks +
      (start.flows txs).interestPaid - (start.flows txs).defaultLosses := by
  suffices h : l.vault.toRawVault.toExact.assetsTotal =
      start.vault.toRawVault.toExact.assetsTotal + (start.flows txs).net by
    rw [h]; unfold AssetFlows.net; ring
  induction hrun with
  | refl => rw [show start.flows [] = 0 from rfl, AssetFlows.net_zero, add_zero]
  | @step txs₀ l₀ l₁ x₀ tx hprev hok ih =>
    have ih' := ih (fun pre l₂ x₂ hpre hr' => hnc pre l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr')
    have hstep := LendingLedger.flow_step l₀ l₁ tx (hprev.reachable_of hr) hok
      (hnc txs₀ l₀ x₀ (List.prefix_append _ _) hprev)
      (fun _ => hnc (txs₀ ++ [tx]) l₁ _ (List.prefix_refl _) (.step tx hprev hok))
    rw [hstep, ih', LendingLedger.flows_snoc hprev.reaches hok, AssetFlows.net_add]
    ring

end XRPL.Model.Lending
