import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout
import XRPL.Properties.Vault.Proofs.Support.WithdrawExchange
import XRPL.Properties.Vault.Proofs.Support.Errors
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve

/-! # `Vault.withdraw` exits

Proof bodies behind `VaultWithdrawReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Nothing deployed means no unrealized loss, as the model's Booleans read it. -/
private lemma Vault.loss_ne_zero_false (v : Vault) (h : v.assetsDeployed.operator_ne Number.zero = false) :
    v.lossUnrealized.operator_ne Number.zero = false := by
  have hAD : v.assetsDeployed = Number.zero := by
    by_contra hne; rw [(Number.operator_ne_iff_ne _ _).mpr hne] at h; exact absurd h (by decide)
  rw [Vault.lossUnrealized_eq_zero_of_deployed v hAD]; decide

lemma Vault.sharesToAssetsWithdraw_zero_nav_proof (v : Vault) (shares : STAmount) (w : Bool)
    (netAssetValue : Number) (hnav : v.assetsTotalForWithdrawal w = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares w = .ok (STAmount.zero v.numericType) := by
  simp [Vault.sharesToAssetsWithdraw, hnav, hz, bind, Except.bind, pure, Except.pure]

lemma Vault.withdraw_too_soon_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hsoon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecTOO_SOON) := by
  simp only [Vault.withdraw]
  unfold_ter
  simp [hsoon]

lemma Vault.withdraw_compute_rejected_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) (ter : TER)
    (hsoon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hcomp : (computeWithdraw v amount waive).run = .ok (.error ter)) :
    (v.withdraw amount waive t hpos).run = .ok (.error ter) := by
  simp only [Vault.withdraw]
  unfold_ter
  simp only [ExceptT.run] at hcomp
  simp [hsoon, hcomp]

lemma Vault.withdraw_has_obligations_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts) (sharesTotalAmount : STAmount)
    (hsoon : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hcomp : (computeWithdraw v amount waive).run = .ok (.ok amounts))
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : amounts.shares.operator_eq sharesTotalAmount = true)
    (hdeployed : v.assetsDeployed.operator_ne Number.zero = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  simp only [Vault.withdraw]
  unfold_ter
  simp only [ExceptT.run] at hcomp
  simp [hsoon, hcomp, hst, hfinal, hdeployed]

lemma Vault.withdraw_zero_payout_proof (v : Vault) (shares : STAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber netAssetValue : Number)
    (hopen : v.WithdrawPriced (.vaultShares shares) waive t amounts sharesTotalAmount)
    (hfin : amounts.shares.operator_eq sharesTotalAmount = false)
    (haN : amounts.assets.toNumber .to_nearest = .ok assetsNumber)
    (hnav : v.assetsTotalForWithdrawal waive = .ok netAssetValue)
    (hz : amounts.assets.isZero = true) (hne : netAssetValue.operator_ne Number.zero = true) :
    (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  have hcomp := hopen.priced
  simp only [ExceptT.run] at hcomp
  simp only [Vault.withdraw]
  unfold_ter
  simp [hopen.soon, hcomp, hopen.sharesTotal, hfin, haN, hnav, hz, hne]

lemma Vault.withdraw_payout_too_small_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber netAssetValue : Number) (ter : TER)
    (hopen : v.WithdrawPriced amount waive t amounts sharesTotalAmount)
    (hfin : amounts.shares.operator_eq sharesTotalAmount = false)
    (haN : amounts.assets.toNumber .to_nearest = .ok assetsNumber)
    (hnav : v.assetsTotalForWithdrawal waive = .ok netAssetValue)
    (hzp : (amount.isByShares && amounts.assets.isZero && netAssetValue.operator_ne Number.zero) = false)
    (hdust : v.checkDebitNotDust assetsNumber = .ok ter) (hter : (ter != .tesSUCCESS) = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error ter) := by
  obtain ⟨hsoon, hcomp, hst, -⟩ := hopen
  simp only [ExceptT.run] at hcomp
  simp only [Vault.withdraw]
  unfold_ter
  cases amount <;> simp only [WithdrawAmount.isByShares, Bool.true_and, Bool.false_and] at hzp <;>
    simp [hsoon, hcomp, hst, hfin, haN, hnav, hzp, hdust, hter]

lemma Vault.withdraw_insufficient_funds_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber : Number)
    (hopen : v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber)
    (hfee : v.earlyExitFeeRateAt t = 0) (hlt : v.assetsAvailable.operator_lt assetsNumber = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS) := by
  obtain ⟨⟨hsoon, hcomp, hst, -⟩, hfin, haN, ⟨nav, hnav⟩, hdust, hnz⟩ := hopen
  simp only [ExceptT.run] at hcomp
  simp only [Vault.withdraw]
  unfold_ter
  simp [hsoon, hcomp, hst, hfin, haN, hnav, hdust, hnz, hfee, hlt,
    show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]

lemma Vault.withdraw_clamp_precision_loss_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber fee payoutNumber : Number) (payout : STAmount)
    (hopen : v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber)
    (hgross : (v.earlyExitFeeRateAt t == 0 && v.assetsAvailable.operator_lt assetsNumber) = false)
    (hpart : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false)
    (hfee : tenthBipsOfValue assetsNumber (v.earlyExitFeeRateAt t) .upward = .ok fee)
    (hsub : assetsNumber.operator_sub fee .downward = .ok payoutNumber)
    (hp : STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout)
    (hgone : payout.isZero = true ∨ ∃ clamped : STAmount,
      clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped ∧
        clamped.isFractionalNonPositive = .ok true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  obtain ⟨⟨hsoon, hcomp, hst, -⟩, hfin, haN, ⟨nav, hnav⟩, hdust, hnz⟩ := hopen
  simp only [ExceptT.run] at hcomp
  have hg : ¬ (v.earlyExitFeeRateAt t = 0 ∧ v.assetsAvailable.operator_lt assetsNumber = true) := by
    simpa using hgross
  simp only [Vault.withdraw]
  unfold_ter
  rcases hgone with hz | ⟨clamped, hcl, hnp⟩
  · simp [hsoon, hcomp, hst, hfin, haN, hnav, hdust, hnz, hg, hpart, hfee, hsub, hp, hz,
      show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]
  · by_cases hz : payout.isZero = true
    · simp [hsoon, hcomp, hst, hfin, haN, hnav, hdust, hnz, hg, hpart, hfee, hsub, hp, hz,
        show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]
    · simp [hsoon, hcomp, hst, hfin, haN, hnav, hdust, hnz, hg, hpart, hfee, hsub, hp, hz, hcl, hnp,
        show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]

lemma Vault.withdraw_payout_insufficient_funds_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber fee payoutNumber clampedNumber : Number)
    (payout clamped : STAmount)
    (hopen : v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber)
    (hgross : (v.earlyExitFeeRateAt t == 0 && v.assetsAvailable.operator_lt assetsNumber) = false)
    (hpart : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false)
    (hfee : tenthBipsOfValue assetsNumber (v.earlyExitFeeRateAt t) .upward = .ok fee)
    (hsub : assetsNumber.operator_sub fee .downward = .ok payoutNumber)
    (hp : STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout)
    (hpz : payout.isZero = false)
    (hcl : clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped)
    (hnp : clamped.isFractionalNonPositive = .ok false)
    (hcn : clamped.toNumber .to_nearest = .ok clampedNumber)
    (hlt : v.assetsAvailable.operator_lt clampedNumber = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS) := by
  obtain ⟨⟨hsoon, hcomp, hst, -⟩, hfin, haN, ⟨nav, hnav⟩, hdust, hnz⟩ := hopen
  simp only [ExceptT.run] at hcomp
  have hg : ¬ (v.earlyExitFeeRateAt t = 0 ∧ v.assetsAvailable.operator_lt assetsNumber = true) := by
    simpa using hgross
  simp only [Vault.withdraw]
  unfold_ter
  simp [hsoon, hcomp, hst, hfin, haN, hnav, hdust, hnz, hg, hpart, hfee, hsub, hp, hpz, hcl, hnp, hcn,
    hlt, show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]

lemma Vault.withdraw_final_insufficient_funds_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts)
    (sharesTotalAmount : STAmount) (assetsNumber : Number)
    (hopen : v.WithdrawPriced amount waive t amounts sharesTotalAmount)
    (hfinal : amounts.shares.operator_eq sharesTotalAmount = true)
    (haN : amounts.assets.toNumber .to_nearest = .ok assetsNumber)
    (hlt : v.assetsAvailable.operator_lt assetsNumber = true) :
    (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS) := by
  obtain ⟨hsoon, hcomp, hst, hobl⟩ := hopen
  simp only [ExceptT.run] at hcomp
  rw [hfinal, Bool.true_and] at hobl
  simp only [Vault.withdraw]
  unfold_ter
  simp [hsoon, hcomp, hst, hfinal, hobl, haN, hlt]

lemma Vault.withdraw_never_internal_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat) :
    (v.withdraw amount waive t hpos).run ≠ .ok (.error .tefINTERNAL) := by
  have hloss := Vault.loss_ne_zero_false v
  intro hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (simp_all; done)
  all_goals try
    have hd : TER.tefINTERNAL = .tesSUCCESS ∨ TER.tefINTERNAL = .tecPRECISION_LOSS ∨
        TER.tefINTERNAL = .tecPATH_DRY := Vault.checkDebitNotDust_codes _ _ _ ‹_›
    simp at hd
  all_goals try
    have hc : TER.tefINTERNAL = .tecPRECISION_LOSS ∨ TER.tefINTERNAL = .tecPATH_DRY :=
      computeWithdraw_codes v amount waive _ ‹_›
    simp at hc
  all_goals
    have h : TER.tefINTERNAL = .tefBAD_LEDGER := Vault.adjustAssetsAndShares_rejected_bad_ledger v _ _ _ ‹_›
    simp at h

set_option maxHeartbeats 400000 in
-- the walk splits every path of the withdrawal, about twice the default budget
/-- A final withdrawal pays the cash, converted into the asset. -/
lemma Vault.withdraw_final_pays_cash (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok r.assets := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok _) := ‹_›
    obtain ⟨hsic, hs64, hspos⟩ := computeWithdraw_shares_form v amount waive _ hc hty hpos hcomp
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hfin := (Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).mpr hfinal
  -- a non-final path compared the burned shares unequal to the share total
  all_goals try
    exfalso
    have hnf : STAmount.operator_eq _ _ = false := ‹_›
    rw [hnf] at hfin
    exact absurd hfin (by decide)
  have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
  exact hp

/-- A final withdrawal of a cash stored exactly empties the vault: it pays out all the cash and
leaves no cash and no shares. The headline over reachable vaults derives the exactness. -/
lemma Vault.withdraw_final_empties (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero := by
  have hp := Vault.withdraw_final_pays_cash v amount waive t hpos hc hty r hok hfinal
  obtain ⟨hsic, hs64, -⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  obtain ⟨raw, hadj, hraw⟩ := Vault.withdraw_ok_reduces v amount waive t hpos r hok
  have hfe := Vault.final_payout_exact v _ hexact hmax hp
  obtain ⟨hAA, hST⟩ := Vault.adjustAssetsAndShares_burn_all v _ _ _
    (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1 hfe hsic hs64 hfinal hadj
  exact ⟨hfe, (congrArg RawVault.assetsAvailable hraw).trans hAA, (congrArg RawVault.sharesTotal hraw).trans hST⟩

set_option maxHeartbeats 400000 in
-- the walk splits every path of the withdrawal, about twice the default budget
/-- A withdrawal never ends in `notLawful` when it burns at most the share total and a final
withdrawal finds the cash stored exactly. The headline over reachable vaults derives the exactness. -/
lemma Vault.withdraw_lawful (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hle : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ v.toExact.sharesTotal)
    (hexact : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toRat = v.toExact.sharesTotal → STAmount.isRounded v.numericType v.assetsAvailable = false) :
    (v.withdraw amount waive t hpos).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.withdraw] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a helper never returns `notLawful`
  all_goals try first
    | exact computeWithdraw_ne_notLawful _ _ _ ‹_›
    | exact Vault.adjustAssetsAndShares_ne_notLawful _ _ _ ‹_›
    | (simp only [STAmount.ofNumber_ne_notLawful, STAmount.toNumber_ne_notLawful,
        Vault.assetsTotalForWithdrawal_ne_notLawful, Vault.checkDebitNotDust_ne_notLawful,
        tenthBipsOfValue_ne_notLawful, Number.operator_sub_ne_notLawful, clampToSumExponent_ne_notLawful,
        STAmount.isFractionalNonPositive_ne_notLawful] at *)
  -- the cash update writes a lawful record: the burned shares and the payout it records
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok _) := ‹_›
    obtain ⟨hsic, hs64, hspos⟩ := computeWithdraw_shares_form v amount waive _ hc hty hpos hcomp
    have hsle := hle _ hcomp
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.ok _) := ‹_›
    apply RawVault.to_lawful_ne_notLawful _ ‹_›
  -- a non-final withdrawal burns fewer than all the shares
  all_goals try have hnf : STAmount.operator_eq _ _ = false := ‹_›
  · -- a 100% fee pays nothing
    have hz := (STAmount.zero_canonicalOrZero v.numericType).1
    exact Vault.withdraw_update_lawful v _ _ _ hmax
      ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]; simp⟩ hz
      (Vault.payout_keeps_cash v _ _ hz ‹_› ‹_›)
      hsic hs64 hspos.le hsle
      (fun heq => absurd ((Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).mpr heq) (by rw [hnf]; decide)) hadj
  · -- the fee path pays the clamped payout
    have hp : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    have hcf := (clampToSumExponent_canonicalOrZero _ _ _ _
      (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1.operator_neg
      v.baseExponent_range.1 v.baseExponent_range.2 hcl).1
    exact Vault.withdraw_update_lawful v _ _ _ hmax
      (Vault.clamp_grid v _ _ _ (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1.operator_neg hcl) hcf
      (Vault.payout_keeps_cash v _ _ hcf ‹_› ‹_›)
      hsic hs64 hspos.le hsle
      (fun heq => absurd ((Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).mpr heq) (by rw [hnf]; decide)) hadj
  · -- a zero priced payout skips the fee
    have haf := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax
      (computeWithdraw_ok_priced v amount waive _ hcomp)).1
    have hzs : ¬ (STAmount.operator_eq _ _ = false ∧ STAmount.isZero _ = false) := ‹_›
    have hz0 := Bool.of_not_eq_false (fun h => hzs ⟨hnf, h⟩)
    exact Vault.withdraw_update_lawful v _ _ _ hmax
      ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz0)]; simp⟩ haf
      (Vault.payout_keeps_cash v _ _ haf ‹_› ‹_›)
      hsic hs64 hspos.le hsle
      (fun heq => absurd ((Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).mpr heq) (by rw [hnf]; decide)) hadj
  · -- the final withdrawal pays all the cash, which is stored exactly, and nothing is deployed
    have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
    have hpf := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1
    have hfin : ¬ STAmount.operator_eq _ _ = false := ‹_›
    have hfe := Vault.final_payout_exact v _
      (hexact _ hcomp ((Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).mp (Bool.of_not_eq_false hfin)))
      hmax hp
    have hzero := (fun (p : STAmount) (hp : p.toRat = v.assetsAvailable.toRat) =>
      show v.assetsAvailable.toRat + p.operator_neg.toRat = 0 by rw [STAmount.operator_neg_toRat, hp]; ring) _ hfe
    have hobl : ¬ (STAmount.operator_eq _ _ = true ∧ v.assetsDeployed.operator_ne Number.zero = true) := ‹_›
    have hAD : v.assetsDeployed = Number.zero := by
      by_contra hne
      exact hobl ⟨Bool.of_not_eq_false hfin, (Number.operator_ne_iff_ne _ _).mpr hne⟩
    obtain ⟨k, hk⟩ := v.exact.assetsAvailable_onGrid
    exact Vault.withdraw_update_lawful v _ _ _ hmax ⟨k, by rw [hfe]; exact hk⟩ hpf (le_of_eq hzero.symm) hsic hs64
      hspos.le hsle
      (fun _ => ⟨hzero, hAD⟩) hadj

lemma Vault.withdraw_success_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hlt : ∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      amounts.shares.toRat < v.toExact.sharesTotal) :
    (v.withdraw amount waive t hpos).run ≠ .error .notLawful :=
  Vault.withdraw_lawful v amount waive t hpos hc hty hmax (fun a h => le_of_lt (hlt a h))
    (fun a h heq => absurd heq (ne_of_lt (hlt a h)))

lemma Vault.withdraw_final_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero :=
  Vault.withdraw_final_empties v amount waive t hpos hc hty hmax
    (Vault.Reachable.openZone_proof v t0 hr hmax).cashExact r hok hfinal

lemma Vault.withdraw_error_codes_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (ter : TER) (hok : (v.withdraw amount waive t hpos).run = .ok (.error ter)) :
    ter = .tecTOO_SOON ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY ∨ ter = .tecHAS_OBLIGATIONS ∨
      ter = .tecINSUFFICIENT_FUNDS ∨
      (ter = .tefBAD_LEDGER ∧ STAmount.isRounded v.numericType v.assetsAvailable = true) := by
  -- a final withdrawal has nothing deployed, so no loss: the `tefINTERNAL` branch never runs
  have hloss := Vault.loss_ne_zero_false v
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try simp only [true_or, or_true]
  -- the walk keeps both polarities of a Bool it branched on twice, so clear contradictory paths
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- Each step below finds its hypothesis by shape only. A full search on a path without it unfolds the
  -- `Number` operators of every other step.
  -- the dust check
  all_goals try
    have hd : ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY :=
      Vault.checkDebitNotDust_codes _ _ ter (by with_reducible assumption)
    have hne : (ter != .tesSUCCESS) = true := by with_reducible assumption
    rcases hd with h | h | h
    · subst h; exact absurd hne (by decide)
    all_goals simp [h]
  -- the share and asset computation
  all_goals try
    have hc : ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY := computeWithdraw_codes v amount waive ter
      (by with_reducible assumption : computeWithdraw v amount waive = .ok (.error ter))
    rcases hc with h | h <;> simp [h]
  -- the cash update: only `tefBAD_LEDGER`, and only when a final payout differs from the cash
  all_goals
    have h : ter = .tefBAD_LEDGER := Vault.adjustAssetsAndShares_rejected_bad_ledger v _ _ ter
      (by with_reducible assumption : v.adjustAssetsAndShares _ _ = .ok (.error ter))
    subst h
    have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.error .tefBAD_LEDGER) :=
      (by with_reducible assumption : v.adjustAssetsAndShares _ _ = .ok (.error .tefBAD_LEDGER))
  all_goals first
    -- a 100% fee pays nothing
    | exfalso
      have hz := (STAmount.zero_canonicalOrZero v.numericType).1
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hz.operator_neg
        (Vault.payout_keeps_cash v _ _ hz (by with_reducible assumption) (by with_reducible assumption)) hadj
    -- the fee path pays the clamped payout, which the cash covers
    | exfalso
      have hp := (by with_reducible assumption : STAmount.ofNumber v.numericType _ .downward = .ok _)
      have hcl := (by with_reducible assumption : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _)
      have hcf := (clampToSumExponent_canonicalOrZero _ _ _ _
        (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1.operator_neg
        v.baseExponent_range.1 v.baseExponent_range.2 hcl).1
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hcf.operator_neg
        (Vault.payout_keeps_cash v _ _ hcf (by with_reducible assumption) (by with_reducible assumption)) hadj
    -- no fee: the priced payout, which the cash covers
    | exfalso
      have hcomp := (by with_reducible assumption : computeWithdraw v amount waive = .ok (.ok _))
      have haf := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax
        (computeWithdraw_ok_priced v amount waive _ hcomp)).1
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ haf.operator_neg
        (Vault.payout_keeps_cash v _ _ haf (by with_reducible assumption) (by with_reducible assumption)) hadj
    -- the final payout is the cash rounded to the asset, which is the cash when stored exactly
    | have hp := (by with_reducible assumption :
        STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _)
      have hpf := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))))
      by_contra hr
      have hr' : STAmount.isRounded v.numericType v.assetsAvailable = false := by simpa using hr
      have hfe := Vault.final_payout_exact v _ hr' hmax hp
      exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hpf.operator_neg
        (by rw [STAmount.operator_neg_toRat, hfe]; simp) hadj

end XRPL.Model.SingleAssetVault
