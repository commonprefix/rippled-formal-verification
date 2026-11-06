import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Protocol.STAmount.Compare.Compare
import XRPL.Properties.Vault.Proofs.Support.CashGrid

/-! # Withdrawal and clawback payouts

The codes the withdraw-side checks reject with, and the facts that keep a payout's cash update
nonnegative. -/

namespace XRPL.Model.Protocol

/-- Negating a canonical-or-zero amount keeps it canonical-or-zero: only the sign changes. -/
lemma STAmount.CanonicalOrZero.operator_neg {s : STAmount} (h : s.CanonicalOrZero) :
    s.operator_neg.CanonicalOrZero := by
  obtain ⟨hnt, hoff, hval⟩ := STAmount.operator_neg_fields s
  have hint : s.operator_neg.integral = s.integral := by unfold STAmount.integral; rw [hnt]
  rcases h with hc | hz
  · refine Or.inl ⟨fun hi => ?_, fun hfr => ?_⟩
    · obtain ⟨hic, hmax⟩ := hc.1 (hint ▸ hi)
      exact ⟨⟨by rw [hnt]; exact hic.is_integral, by rw [hoff]; exact hic.offset_zero,
        by rw [hval, hnt]; exact hic.in_range⟩, by rw [hnt]; exact hmax⟩
    · obtain hio := hc.2 (hint ▸ hfr)
      exact ⟨by rw [hnt]; exact hio.is_fractional, by rw [hval]; exact hio.mant_lo,
        by rw [hval]; exact hio.mant_hi, by rw [hoff]; exact hio.exp_lo, by rw [hoff]; exact hio.exp_hi⟩
  · exact Or.inr (by unfold STAmount.isZero at hz ⊢; rw [hval]; exact hz)

/-- The zero amount of a type is canonical-or-zero, of that type. -/
lemma STAmount.zero_canonicalOrZero (nt : NumericType) :
    (STAmount.zero nt).CanonicalOrZero ∧ (STAmount.zero nt).mNumericType = nt := by
  refine ⟨Or.inr (by simp [STAmount.isZero, STAmount.zero_mValue]), ?_⟩
  unfold STAmount.zero
  split
  · rename_i s hs
    exact STAmount.canonicalize_mNumericType _ s _ hs
  · rfl

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The dust check returns `tesSUCCESS`, `tecPRECISION_LOSS`, or `tecPATH_DRY` for an overflow. -/
lemma Vault.checkDebitNotDust_codes (v : Vault) (amount : Number) (ter : TER)
    (h : v.checkDebitNotDust amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY := by
  simp only [Vault.checkDebitNotDust, bind, Except.bind, pure, Except.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  walk_ok
  all_goals simp

/-- A withdrawal's share and asset computation rejects with `tecPRECISION_LOSS`, or `tecPATH_DRY`
for an overflow. -/
lemma computeWithdraw_codes (v : Vault) (amount : WithdrawAmount) (w : Bool) (ter : TER)
    (h : (computeWithdraw v amount w).run = .ok (.error ter)) :
    ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY := by
  simp only [computeWithdraw] at h
  unfold_ter at h
  walk_ok
  all_goals simp

/-- On a lawful vault with nothing deployed there is no unrealized loss. -/
lemma Vault.lossUnrealized_eq_zero_of_deployed (v : Vault) (h : v.assetsDeployed = Number.zero) :
    v.lossUnrealized = Number.zero := by
  have hle : v.lossUnrealized.toRat ≤ v.assetsDeployed.toRat := v.exact.lossUnrealized_le
  have hnn : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  rw [h, Number.toRat_zero] at hle
  exact (Number.toRat_eq_zero_iff_eq_zero v.wf.lossUnrealized_norm).mp (le_antisymm hle hnn)

/-- The assets a share count is worth at withdrawal are canonical-or-zero, in the vault's asset. -/
lemma Vault.sharesToAssetsWithdraw_form (v : Vault) (shares assets : STAmount) (w : Bool)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : v.sharesToAssetsWithdraw shares w = .ok assets) :
    assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact STAmount.zero_canonicalOrZero _
    | exact STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ‹_›

/-- A payout the cash covers keeps the cash nonnegative. -/
lemma Vault.payout_keeps_cash (v : Vault) (assets : STAmount) (n : Number) (hc : assets.CanonicalOrZero)
    (hn : assets.toNumber .to_nearest = .ok n) (hcover : v.assetsAvailable.operator_lt n = false) :
    0 ≤ v.assetsAvailable.toRat + assets.operator_neg.toRat := by
  obtain ⟨hv, hnorm⟩ := hc.toNumber_exact n hn
  have hle : n.toRat ≤ v.assetsAvailable.toRat := by
    have h := (operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm).not.mp (by simp [hcover])
    linarith [not_lt.mp h]
  rw [STAmount.operator_neg_toRat]
  linarith

/-- The final payout of a cash stored exactly is the cash itself. -/
lemma Vault.final_payout_exact (v : Vault) (payout : STAmount)
    (hr : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok payout) :
    payout.toRat = v.assetsAvailable.toRat := by
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hr
  rw [hok] at hr
  simp only [bind, Except.bind, pure, Except.pure] at hr
  cases hn : payout.toNumber .to_nearest with
  | error e => rw [hn] at hr; exact absurd hr (by simp)
  | ok n =>
    rw [hn] at hr
    have heq : n.operator_eq v.assetsAvailable = true := by simpa using hr
    obtain ⟨hv, hnorm⟩ := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hok).1.toNumber_exact n hn
    rw [← hv]
    exact (operator_eq_iff _ _ hnorm v.wf.assetsAvailable_norm).mp heq

/-- A withdrawal's cash update writes a lawful record when it pays out a whole number of base units, no more than the
cash, burns a whole number of shares up to the share total, and burning them all empties the vault. -/
lemma Vault.withdraw_update_lawful (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hk : ∃ k : ℤ, assets.toRat = k * 10 ^ v.baseExponent)
    (hc : assets.CanonicalOrZero) (hcash : 0 ≤ v.assetsAvailable.toRat + assets.operator_neg.toRat)
    (hsh : shares.IntegralCanonical) (hsh64 : shares.mNumericType = .int64) (hsh0 : 0 ≤ shares.toRat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal)
    (hempty : shares.toRat = v.toExact.sharesTotal →
      v.assetsAvailable.toRat + assets.operator_neg.toRat = 0 ∧ v.assetsDeployed = Number.zero)
    (hadj : (v.adjustAssetsAndShares assets.operator_neg shares.operator_neg).run = .ok (.ok raw)) :
    raw.WF ∧ raw.Valid := by
  have hk' : ∃ k : ℤ, assets.operator_neg.toRat = k * 10 ^ v.baseExponent := by
    obtain ⟨k, hk⟩ := hk
    exact ⟨-k, by rw [STAmount.operator_neg_toRat, hk]; push_cast; ring⟩
  obtain ⟨assetsNum, sharesNum, s, aa', st', hnum, hsnum, hst, hs, haa, rfl⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ := hc.operator_neg.toNumber_exact assetsNum hnum
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hsum : 0 ≤ s.toRat := operator_add_nonneg _ _ _ v.wf.assetsAvailable_norm hnorm hs (by rw [hv]; exact hcash)
  have haa0 := STAmount.roundToNumericType_nonneg _ _ _ hsn hsum haa
  have haan := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  -- the payout is a whole number of base units, so the new cash is stored exactly and on the base grid
  obtain ⟨haar, haak⟩ := Vault.adjustAssetsAndShares_cash_valid v assets.operator_neg shares.operator_neg _ hmax
    hc.operator_neg hk' hadj haa0
  -- the burned shares, exact as a whole number
  have hshc : shares.Canonical := hsh.canonical (by rw [hsh64]; decide)
  obtain ⟨hsv, hsnorm⟩ := (STAmount.CanonicalOrZero.operator_neg (Or.inl hshc)).toNumber_exact sharesNum hsnum
  rw [STAmount.operator_neg_toRat] at hsv
  have hsden : sharesNum.toRat.den = 1 := by
    rw [hsv, Rat.neg_den]; exact hsh.den_eq_one
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hcap := v.sharesTotal_le_maxRep
  rw [← hcast] at hcap
  have hbound := Rat.num_natAbs_add_lt_of_den_one _ _ v.wf.sharesTotal_int hsden
    (by rw [hsv, ← hcast]; linarith) (by rw [hsv, ← hcast]; linarith)
  obtain ⟨hstv, hstd⟩ := operator_add_exact_int _ _ _ v.wf.sharesTotal_norm hsnorm v.wf.sharesTotal_int
    hsden hbound hst
  have hstn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm hsnorm hst
  have hst0 : 0 ≤ st'.toRat := by rw [hstv, hsv, ← hcast]; linarith
  refine Vault.cash_shares_update_lawful v aa' st' haan haa0 haar (Vault.onGrid_clause v aa' haan haa0 haak) hstn
    hst0 hstd (by rw [hstv, hsv, ← hcast]; linarith) ?_
  -- burning every share pays out all the cash, so the vault ends empty
  intro hz
  have h0 : st'.toRat = 0 := by rw [hz, Number.toRat_zero]
  rw [hstv, hsv, ← hcast] at h0
  obtain ⟨hcash0, hAD⟩ := hempty (by linarith)
  have hs0 : s = Number.zero := by
    have hr := Number.RoundsToRepresentable.eq_of_representable _ _
      (operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hnorm hs) Number.zero
      Number.zero_isNormalized (by rw [Number.toRat_zero, hv]; linarith)
    have hsq : s.toRat = 0 := by rw [hr, hv]; linarith
    exact (Number.toRat_eq_zero_iff_eq_zero hsn).mp hsq
  rw [hs0, STAmount.roundToNumericType_zero_to_nearest] at haa
  exact ⟨(Except.ok.inj haa).symm, hAD⟩

/-- A withdrawal is final exactly when it burns the whole share total: the model compares the
burned amount with the stored share total. -/
lemma Vault.isFinalWithdrawal_iff (v : Vault) (shares sharesTotalAmount : STAmount)
    (hsh : shares.IntegralCanonical) (hsh64 : shares.mNumericType = .int64) (hpos : 0 < shares.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    shares.operator_eq sharesTotalAmount = true ↔ shares.toRat = v.toExact.sharesTotal := by
  obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) hst
  have hval : sharesTotalAmount.toRat = v.sharesTotal.toRat :=
    STAmount.ofNumber_integral_exact .int64 _ _ _ (by decide) v.wf.sharesTotal_norm v.wf.sharesTotal_int hst
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hne' : shares.mValue ≠ 0 := fun h0 => by
    have := (STAmount.toRat_eq_zero_iff _).mpr h0; linarith
  -- a zero share total is a zero amount, which carries no sign
  have h0r : sharesTotalAmount.mValue = 0 → sharesTotalAmount.mIsNegative = false := by
    intro h0
    have hz := (STAmount.toRat_eq_zero_iff _).mpr h0
    rw [hval] at hz
    have hst0 := (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp hz
    rw [hst0] at hst
    obtain rfl := Except.ok.inj (hst.symm.trans rfl)
    rfl
  rw [STAmount.operator_eq_eq _ _ (STAmount.CmpFaithful.ofIntegral _ _ hsh hic
    (by simp [STAmount.areComparable, hsh64, hty]) (fun h => absurd h hne') h0r)]
  simp [hval, ← hcast]

/-- Burning every share for all the cash empties the vault: no cash and no shares remain. -/
lemma Vault.adjustAssetsAndShares_burn_all (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hc : assets.CanonicalOrZero) (hpay : assets.toRat = v.assetsAvailable.toRat)
    (hsh : shares.IntegralCanonical) (hsh64 : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal)
    (hadj : (v.adjustAssetsAndShares assets.operator_neg shares.operator_neg).run = .ok (.ok raw)) :
    raw.assetsAvailable = Number.zero ∧ raw.sharesTotal = Number.zero := by
  obtain ⟨assetsNum, sharesNum, s, aa', st', hnum, hsnum, hst, hs, haa, rfl⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ := hc.operator_neg.toNumber_exact assetsNum hnum
  have hshc : shares.Canonical := hsh.canonical (by rw [hsh64]; decide)
  obtain ⟨hsv, hsnorm⟩ := (STAmount.CanonicalOrZero.operator_neg (Or.inl hshc)).toNumber_exact sharesNum hsnum
  rw [STAmount.operator_neg_toRat] at hv hsv
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  -- each sum is an exact zero, which rounds to zero
  have hzero : ∀ x y z : Number, x.isNormalized → y.isNormalized → x.toRat + y.toRat = 0 →
      x.operator_add y .to_nearest = .ok z → z = Number.zero := by
    intro x y z hx hy h0 hok
    have hr := Number.RoundsToRepresentable.eq_of_representable _ _
      (operator_add_rounded_to_nearest _ _ _ hx hy hok) Number.zero Number.zero_isNormalized
      (by rw [Number.toRat_zero, h0])
    exact (Number.toRat_eq_zero_iff_eq_zero (operator_add_isNormalized_to_nearest_sz _ _ _ hx hy hok)).mp
      (by rw [hr, h0])
  have hs0 := hzero _ _ _ v.wf.assetsAvailable_norm hnorm (by rw [hv, hpay]; ring) hs
  have hst0 := hzero _ _ _ v.wf.sharesTotal_norm hsnorm (by rw [hsv, hall, hcast]; ring) hst
  rw [hs0, STAmount.roundToNumericType_zero_to_nearest] at haa
  exact ⟨(Except.ok.inj haa).symm, hst0⟩

end XRPL.Model.SingleAssetVault
