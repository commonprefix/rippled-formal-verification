import XRPL.Properties.Vault.Proofs.Support.ComputeClawback
import XRPL.Properties.Vault.Proofs.Support.Errors

/-! # `Vault.clawback` exits

Proof bodies behind `VaultClawbackReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.clawback_no_permission_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType = NumericType.native) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error .tecNO_PERMISSION) := by
  simp only [Vault.clawback]
  unfold_ter
  simp [hxrp]

/-- A successful clawback ran on a vault whose asset is not XRP. -/
lemma Vault.clawback_ok_not_native (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    v.numericType ≠ NumericType.native := by
  intro h
  rw [Vault.clawback_no_permission_proof v assets holderShares waive hnn h] at hok
  exact absurd hok (by simp)

lemma Vault.clawback_compute_rejected_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native) (ter : TER)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.error ter)) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error ter) := by
  simp only [ExceptT.run] at hcomp
  simp only [Vault.clawback]
  unfold_ter
  simp [hxrp, hcomp]

lemma Vault.clawback_capped_internal_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native)
    (shares recovered capped shares' recovered' : STAmount) (n n' : Number)
    (hs : assetsToSharesClawback v assets holderShares waive = .ok shares)
    (ha : v.sharesToAssetsWithdraw shares waive = .ok recovered)
    (hn : recovered.toNumber .to_nearest = .ok n) (hgt : n.operator_gt v.assetsAvailable = true)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok capped)
    (hs' : assetsToSharesWithdraw v capped true waive = .ok shares')
    (ha' : v.sharesToAssetsWithdraw shares' waive = .ok recovered')
    (hn' : recovered'.toNumber .to_nearest = .ok n') (hgt' : n'.operator_gt v.assetsAvailable = true) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error .tecINTERNAL) := by
  refine Vault.clawback_compute_rejected_proof v assets holderShares waive hnn hxrp _ ?_
  simp only [computeClawback]
  unfold_ter
  simp [hs, ha, hn, hgt, hcash, hs', ha', hn', hgt']

private lemma computeClawback_has_obligations (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (shares recovered sharesTotalAmount : STAmount)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : shares.operator_eq sharesTotalAmount = true)
    (hdeployed : v.assetsDeployed.operator_ne Number.zero = true) :
    (computeClawback v assets holderShares waive).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  simp only [computeClawback]
  unfold_ter
  cases hpr with
  | direct _ _ n ha2s hs2a hn hgt => simp [ha2s, hs2a, hn, hgt, hst, hfinal, hdeployed]
  | capped _ _ _ _ _ _ _ ha2s0 hs2a0 hn0 hgt0 hcash ha2s hs2a hn hgt =>
    simp [ha2s0, hs2a0, hn0, hgt0, hcash, ha2s, hs2a, hn, hgt, hst, hfinal, hdeployed]

lemma Vault.clawback_has_obligations_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native)
    (shares recovered sharesTotalAmount : STAmount)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : shares.operator_eq sharesTotalAmount = true)
    (hdeployed : v.assetsDeployed.operator_ne Number.zero = true) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error .tecHAS_OBLIGATIONS) :=
  Vault.clawback_compute_rejected_proof v assets holderShares waive hnn hxrp _
    (computeClawback_has_obligations v assets holderShares waive shares recovered sharesTotalAmount hpr hst
      hfinal hdeployed)

private lemma computeClawback_clamp_precision_loss (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (shares recovered sharesTotalAmount clamped : STAmount)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hobl : (shares.operator_eq sharesTotalAmount && v.assetsDeployed.operator_ne Number.zero) = false)
    (hnz : recovered.isZero = false)
    (hcl : clampToSumExponent v.assetsAvailable recovered.operator_neg v.baseExponent = .ok clamped)
    (hnp : clamped.isFractionalNonPositive = .ok true) :
    (computeClawback v assets holderShares waive).run = .ok (.error .tecPRECISION_LOSS) := by
  have hob : ¬ (shares.operator_eq sharesTotalAmount = true ∧ v.assetsDeployed.operator_ne Number.zero = true) := by
    simpa using hobl
  simp only [computeClawback]
  unfold_ter
  cases hpr with
  | direct _ _ n ha2s hs2a hn hgt => simp [ha2s, hs2a, hn, hgt, hst, hob, hnz, hcl, hnp]
  | capped _ _ _ _ _ _ _ ha2s0 hs2a0 hn0 hgt0 hcash ha2s hs2a hn hgt =>
    simp [ha2s0, hs2a0, hn0, hgt0, hcash, ha2s, hs2a, hn, hgt, hst, hob, hnz, hcl, hnp]

lemma Vault.clawback_clamp_precision_loss_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native)
    (shares recovered sharesTotalAmount clamped : STAmount)
    (hpr : v.ClawbackPriced assets holderShares waive shares recovered)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hobl : (shares.operator_eq sharesTotalAmount && v.assetsDeployed.operator_ne Number.zero) = false)
    (hnz : recovered.isZero = false)
    (hcl : clampToSumExponent v.assetsAvailable recovered.operator_neg v.baseExponent = .ok clamped)
    (hnp : clamped.isFractionalNonPositive = .ok true) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPRECISION_LOSS) :=
  Vault.clawback_compute_rejected_proof v assets holderShares waive hnn hxrp _
    (computeClawback_clamp_precision_loss v assets holderShares waive shares recovered sharesTotalAmount
      clamped hpr hst hobl hnz hcl hnp)

lemma Vault.clawback_zero_shares_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native) (amounts : VaultAmounts)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts))
    (hz : amounts.shares.isZero = true) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPRECISION_LOSS) := by
  simp only [ExceptT.run] at hcomp
  simp only [Vault.clawback]
  unfold_ter
  simp [hxrp, hcomp, hz]

lemma Vault.clawback_recovery_too_small_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hxrp : v.numericType ≠ NumericType.native) (amounts : VaultAmounts)
    (assetsNumber : Number) (ter : TER)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts))
    (hz : amounts.shares.isZero = false)
    (haN : amounts.assets.toNumber .to_nearest = .ok assetsNumber)
    (hdust : v.checkDebitNotDust assetsNumber = .ok ter) (hter : (ter != .tesSUCCESS) = true) :
    (v.clawback assets holderShares waive hnn).run = .ok (.error ter) := by
  simp only [ExceptT.run] at hcomp
  simp only [Vault.clawback]
  unfold_ter
  simp [hxrp, hcomp, hz, haN, hdust, hter]

/-- A clawback recovers a whole number of base units: nothing, or a recovery clamped onto the base grid. -/
private lemma computeClawback_assets_grid (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (amounts : VaultAmounts) (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts)) :
    ∃ k : ℤ, amounts.assets.toRat = k * 10 ^ v.baseExponent := by
  obtain ⟨recovered, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  have hrc : recovered.CanonicalOrZero := by
    cases hpr with
    | direct _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
    | capped _ _ _ _ _ _ _ _ _ _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
  rcases hrec with ⟨hz, heq⟩ | ⟨-, hcl, -⟩
  · rw [heq]; exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]; simp⟩
  · exact Vault.clamp_grid v _ _ _ hrc.operator_neg hcl

/-- A clawback never ends in `notLawful` when it destroys at most the share total and a final
clawback recovers all the cash. -/
lemma Vault.clawback_lawful (v : Vault) (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat)
    (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hle : ∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ v.toExact.sharesTotal)
    (hall : ∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.toRat = v.toExact.sharesTotal →
      v.assetsAvailable.toRat + amounts.assets.operator_neg.toRat = 0) :
    (v.clawback assets holderShares waive hnn).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.clawback] at h
  unfold_ter at h
  walk_ok
  all_goals try (simp only [Bool.not_eq_true] at *)
  -- a helper never returns `notLawful`
  all_goals try first
    | exact computeClawback_ne_notLawful _ _ _ _ ‹_›
    | exact Vault.adjustAssetsAndShares_ne_notLawful _ _ _ ‹_›
    | exact STAmount.operator_lt_ne_notLawful _ _ ‹_›
    | (simp only [STAmount.toNumber_ne_notLawful, Vault.checkDebitNotDust_ne_notLawful] at *)
  -- the cash update writes a lawful record
  have hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok _) := ‹_›
  obtain ⟨hic, h64, h0, hac, hcash⟩ := computeClawback_amounts_form v _ _ waive _ hc hnn hhs hmax hcomp
  obtain ⟨_, _, -, hst, hobl, -⟩ := computeClawback_success_reduces v _ _ waive _ hcomp
  have hnz : STAmount.isZero _ = false := ‹_›
  have hpos : 0 < STAmount.toRat _ := lt_of_le_of_ne h0
    (Ne.symm (fun h' => absurd ((STAmount.toRat_eq_zero_iff _).mp h') (ne_of_beq_false hnz)))
  have hempty := fun heq => (⟨hall _ hcomp heq, by
    by_contra hne
    have hfin := (Vault.isFinalWithdrawal_iff v _ _ hic h64 hpos hst).mpr heq
    rw [hfin, (Number.operator_ne_iff_ne _ _).mpr hne] at hobl
    exact absurd hobl (by decide)⟩ : _ ∧ v.assetsDeployed = Number.zero)
  have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.ok _) := ‹_›
  exact RawVault.to_lawful_ne_notLawful
    (Vault.withdraw_update_lawful v _ _ _ hmax (computeClawback_assets_grid v _ _ waive _ hmax hcomp) hac hcash hic
      h64 h0 (hle _ hcomp) hempty hadj) ‹_›

lemma Vault.clawback_success_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hlt : ∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
      amounts.shares.toRat < v.toExact.sharesTotal) :
    (v.clawback assets holderShares waive hnn).run ≠ .error .notLawful :=
  Vault.clawback_lawful v assets holderShares waive hnn hc hhs hmax (fun a h => le_of_lt (hlt a h))
    (fun a h heq => absurd heq (ne_of_lt (hlt a h)))

lemma Vault.clawback_error_codes_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (ter : TER) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.error ter)) :
    ter = .tecNO_PERMISSION ∨ ter = .tecINTERNAL ∨ ter = .tecHAS_OBLIGATIONS ∨ ter = .tecPRECISION_LOSS ∨
      ter = .tecPATH_DRY ∨ ter = .tecINSUFFICIENT_FUNDS := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  all_goals try simp only [true_or, or_true]
  -- the pricing
  all_goals try
    exact (computeClawback_codes v _ _ waive ter ‹_›).elim (fun h => by simp [h])
      (fun h => h.elim (fun h => by simp [h]) (fun h => h.elim (fun h => by simp [h]) (fun h => by simp [h])))
  -- the dust check
  all_goals try
    have hd : ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY :=
      Vault.checkDebitNotDust_codes _ _ ter ‹_›
    have hne : (ter != .tesSUCCESS) = true := ‹_›
    rcases hd with h | h | h
    · subst h; exact absurd hne (by decide)
    all_goals simp [h]
  -- the cash update never goes negative: the cash covers the recovery
  have hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok _) := ‹_›
  obtain ⟨-, -, -, hac, hcash⟩ := computeClawback_amounts_form v _ _ waive _ hc hnn hhs hmax hcomp
  have h := Vault.adjustAssetsAndShares_rejected_bad_ledger v _ _ ter ‹_›
  subst h
  exact absurd ‹_› (Vault.adjustAssetsAndShares_not_bad_ledger_of_le v _ _ hac.operator_neg hcash)

end XRPL.Model.SingleAssetVault
