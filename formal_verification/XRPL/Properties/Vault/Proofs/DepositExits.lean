import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Vault.Proofs.Support.CashGrid

/-! # `Vault.deposit` exits

Proof bodies behind `VaultDepositReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.roundedDepositAmount_rejected_code_proof (v : Vault) (amountDeposit : STAmount)
    (ter : TER) (hok : (v.roundedDepositAmount amountDeposit).run = .ok (.error ter)) :
    ter = .tecPRECISION_LOSS := by
  simp only [Vault.roundedDepositAmount] at hok
  unfold_ter at hok
  walk_ok
  all_goals rfl

lemma Vault.deposit_expired_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hphase : (v.phase t == .investment || v.phase t == .redemption) = true) :
    (v.deposit amountDeposit false t hpos).run = .ok (.error .tecEXPIRED) := by
  simp only [Vault.deposit]
  unfold_ter
  simp [hphase]

lemma Vault.deposit_donation_no_shares_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hsh : v.sharesTotal.mantissa_ = 0) :
    (v.deposit amountDeposit true t hpos).run = .ok (.error .tecNO_PERMISSION) := by
  simp only [Vault.deposit]
  unfold_ter
  simp [hsh]

/-- A successful donation comes into a vault that has shares, since a donation with none is rejected. -/
lemma Vault.deposit_donation_sharesTotal_pos (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    0 < v.toExact.sharesTotal := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hm : v.sharesTotal.mantissa_ = 0 := by
    by_contra hm
    apply Number.mantissa_ne_zero_iff.mp hm
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    exact_mod_cast h0
  rw [Vault.deposit_donation_no_shares_proof v amountDeposit t hpos hm] at hok
  cases hok

lemma Vault.deposit_insolvent_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hphase : (v.phase t == .investment || v.phase t == .redemption) = false)
    (hins : v.isInsolvent = true) :
    (v.deposit amountDeposit false t hpos).run = .ok (.error .tecLOCKED) := by
  simp only [Vault.deposit]
  unfold_ter
  simp [hphase, hins]

lemma Vault.deposit_blocked_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hphase : (!isDonation && (v.phase t == .investment || v.phase t == .redemption)) = false)
    (hdon : (isDonation && v.sharesTotal.mantissa_ == 0) = false)
    (hins : (v.isInsolvent && !isDonation) = false) (hblk : v.depositBlocked = true) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLOCKED) := by
  simp only [Vault.deposit]
  unfold_ter
  simp [hphase, hdon, hins, hblk]

lemma Vault.deposit_rounded_zero_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (assetsTotal : Number) (ra : STAmount)
    (hopen : v.DepositOpen isDonation t) (hat : v.assetsTotal = .ok assetsTotal)
    (hcl : clampToSumExponent assetsTotal amountDeposit v.baseExponent = .ok ra) (hz : ra.isZero = true) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  have hr : (v.roundedDepositAmount amountDeposit).run = .ok (.error .tecPRECISION_LOSS) := by
    rw [roundedDepositAmount_ok v amountDeposit ra assetsTotal hat hcl, if_pos hz]
  simp only [Vault.deposit]
  unfold_ter
  simp only [ExceptT.run] at hr
  simp [hopen.phase, hopen.donation, hopen.insolvent, hopen.blocked, hr]

lemma Vault.deposit_compute_rejected_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra : STAmount) (ter : TER)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.error ter)) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.error ter) := by
  simp only [Vault.deposit]
  unfold_ter
  simp only [ExceptT.run] at hcomp hrounded
  simp [hopen.phase, hopen.donation, hopen.insolvent, hopen.blocked, hrounded, hcomp]

lemma Vault.deposit_zero_shares_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra shares : STAmount) (hopen : v.DepositOpen false t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hs : assetsToSharesDeposit v ra = .ok shares) (hz : shares.isZero = true) :
    (v.deposit amountDeposit false t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  refine Vault.deposit_compute_rejected_proof v amountDeposit false t hpos ra _ hopen hrounded ?_
  simp only [computeDeposit]
  unfold_ter
  simp [hs, hz]

lemma Vault.deposit_overpriced_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra shares assets : STAmount) (hopen : v.DepositOpen false t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hs : assetsToSharesDeposit v ra = .ok shares) (hz : shares.isZero = false)
    (ha : sharesToAssetsDeposit v shares = .ok assets) (hgt : assets.operator_gt ra = .ok true) :
    (v.deposit amountDeposit false t hpos).run = .ok (.error .tecINTERNAL) := by
  refine Vault.deposit_compute_rejected_proof v amountDeposit false t hpos ra _ hopen hrounded ?_
  simp only [computeDeposit]
  unfold_ter
  simp [hs, hz, ha, hgt]

lemma Vault.deposit_zero_charge_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra shares assets charge : STAmount) (assetsTotal : Number)
    (hopen : v.DepositOpen false t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hs : assetsToSharesDeposit v ra = .ok shares) (hz : shares.isZero = false)
    (ha : sharesToAssetsDeposit v shares = .ok assets) (hgt : assets.operator_gt ra = .ok false)
    (hat : v.assetsTotal = .ok assetsTotal)
    (hcl : clampToSumExponent assetsTotal assets v.baseExponent = .ok charge)
    (hnp : charge.isFractionalNonPositive = .ok true) :
    (v.deposit amountDeposit false t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  refine Vault.deposit_compute_rejected_proof v amountDeposit false t hpos ra _ hopen hrounded ?_
  simp only [computeDeposit]
  unfold_ter
  simp [hs, hz, ha, hgt, hat, hcl, hnp]

lemma Vault.deposit_zero_donation_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra charge : STAmount) (assetsTotal : Number)
    (hopen : v.DepositOpen true t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hat : v.assetsTotal = .ok assetsTotal)
    (hcl : clampToSumExponent assetsTotal ra v.baseExponent = .ok charge)
    (hnp : charge.isFractionalNonPositive = .ok true) :
    (v.deposit amountDeposit true t hpos).run = .ok (.error .tecPRECISION_LOSS) := by
  refine Vault.deposit_compute_rejected_proof v amountDeposit true t hpos ra _ hopen hrounded ?_
  simp only [computeDeposit]
  unfold_ter
  simp [hat, hcl, hnp]

lemma Vault.deposit_inflow_rejected_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (ra : STAmount) (amounts : VaultAmounts) (ter : TER)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts))
    (hin : v.checkOpenLimit amounts.assets = .ok ter) (hter : (ter != .tesSUCCESS) = true) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.error ter) := by
  simp only [Vault.deposit]
  unfold_ter
  simp only [ExceptT.run] at hcomp hrounded
  simp [hopen.phase, hopen.donation, hopen.insolvent, hopen.blocked, hrounded, hcomp, hin, hter]

lemma Vault.deposit_maximum_exceeded_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (ra : STAmount) (amounts : VaultAmounts)
    (raw : RawVault) (assetsTotal' : Number)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts))
    (hin : v.checkOpenLimit amounts.assets = .ok .tesSUCCESS)
    (hadj : (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw))
    (hat' : raw.assetsTotal = .ok assetsTotal')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  simp only [Vault.deposit]
  unfold_ter
  simp only [ExceptT.run] at hcomp hadj hrounded
  rw [Bool.and_eq_true] at hmax
  simp [hopen.phase, hopen.donation, hopen.insolvent, hopen.blocked, hrounded, hcomp, hin, hadj, hat',
    hmax.1, hmax.2, (by decide : (TER.tesSUCCESS != TER.tesSUCCESS) = false)]

private lemma Vault.deposit_success_of_lawful (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (ra : STAmount) (amounts : VaultAmounts)
    (raw : RawVault) (assetsTotal' : Number) (v' : Vault)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts))
    (hin : v.checkOpenLimit amounts.assets = .ok .tesSUCCESS)
    (hadj : (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw))
    (hat' : raw.assetsTotal = .ok assetsTotal')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hl : raw.to_lawful = .ok v')
    (hSsz : (v.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) :
    (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok { amounts with vault' := v' }) := by
  have hcap : ¬ ((maxRep.toNat : ℚ) < v.sharesTotal.toRat + amounts.shares.toRat) := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, show maxRep.toNat = 2 ^ 63 - 1 from rfl]
    push_cast; linarith
  simp only [Vault.deposit]
  unfold_ter
  simp only [ExceptT.run] at hcomp hadj hrounded
  have hmax' : ¬ ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero = true ∧
      assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero) = true) := by
    rw [← Bool.and_eq_true, hmax]; decide
  simp [hopen.phase, hopen.donation, hopen.insolvent, hopen.blocked, hrounded, hcomp, hin, hadj, hat', hl,
    hmax', hcap, (by decide : (TER.tesSUCCESS != TER.tesSUCCESS) = false)]

/-- A deposit that passes every check produces a lawful vault. The new cash is the old cash plus a
nonnegative charge, and the new share total gains the minted shares exactly, within the MPT maximum and never zero. -/
lemma Vault.deposit_success_lawful (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (ra : STAmount) (amounts : VaultAmounts) (raw : RawVault)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts))
    (hadj : (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw))
    (hSsz : (v.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) :
    raw.WF ∧ raw.Valid := by
  have hmax := Vault.maxValue_fits_of_canonical v amountDeposit hc hty
  obtain ⟨hra1, hra2, hra3⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hrounded
  obtain ⟨ha1, -, ha3⟩ := computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcomp
  have hcharge : ∃ k : ℤ, amounts.assets.toRat = k * 10 ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ (sharesToAssetsDeposit_form v amounts.shares assets hmax hsta).1 hcl
    · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ hra1 hcl
  obtain ⟨assetsNum, sharesNum, s, aa', st', hnum, hsnum, hst, hs, haa, rfl⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ := ha1.toNumber_exact assetsNum hnum
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hAA : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hsum : 0 ≤ s.toRat := operator_add_nonneg _ _ _ v.wf.assetsAvailable_norm hnorm hs
    (by rw [hv]; linarith)
  have haa0 := STAmount.roundToNumericType_nonneg _ _ _ hsn hsum haa
  have haan := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  -- the charge is a whole number of base units, so the new cash is stored exactly and on the base grid
  obtain ⟨haar, haak⟩ := Vault.adjustAssetsAndShares_cash_valid v amounts.assets amounts.shares _ hmax ha1 hcharge
    hadj haa0
  -- the minted shares: a canonical `int64` amount, positive for a deposit and zero for a donation
  have hmint : amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧
      (isDonation = false → 0 < amounts.shares.toRat) ∧
      (isDonation = true → amounts.shares.toRat = 0) := by
    cases isDonation
    · obtain ⟨_, _, ha2s, hz, _⟩ := computeDeposit_success_reduces v ra amounts hcomp
      obtain ⟨hic, hint⟩ := assetsToSharesDeposit_int64_canonical v ra amounts.shares ha2s
      obtain ⟨_, _, _, hraz⟩ := roundedDepositAmount_rounded v amountDeposit ra hrounded
      have hrac : ra.Canonical := hra1.resolve_right (by simp [hraz])
      have hrapos : 0 < ra.toRat :=
        lt_of_le_of_ne hra3 (Ne.symm (STAmount.toRat_ne_zero ra (ne_of_beq_false hraz)))
      exact ⟨hic, hint, fun _ => assetsToSharesDeposit_pos v ra amounts.shares hrac hrapos ha2s hz,
        fun h => absurd h (by decide)⟩
    · obtain ⟨_, hsh, _⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      rw [hsh]
      exact ⟨zero_int64_IntegralCanonical, STAmount.zero_mNumericType _,
        fun h => absurd h (by decide), fun _ => STAmount.zero_toRat _⟩
  obtain ⟨hic, hint64, hpos', hzero⟩ := hmint
  have hshc : amounts.shares.Canonical := hic.canonical (by rw [hint64]; decide)
  obtain ⟨hsv, hsnorm⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hshc) sharesNum hsnum
  have hsden : sharesNum.toRat.den = 1 := by rw [hsv]; exact hic.den_eq_one
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hsum' : v.sharesTotal.toRat + sharesNum.toRat ≤ 2 ^ 63 - 1 := by
    rw [hsv, ← hcast]; exact hSsz
  have hsharesnn : 0 ≤ amounts.shares.toRat := by
    cases isDonation
    · exact le_of_lt (hpos' rfl)
    · rw [hzero rfl]
  -- the exact sum of two whole numbers below `2^63`
  have hbound : (v.sharesTotal.toRat + sharesNum.toRat).num.natAbs < 2 ^ 63 := by
    have hA := Rat.coe_int_num_of_den_eq_one v.wf.sharesTotal_int
    have hB := Rat.coe_int_num_of_den_eq_one hsden
    have hsumeq : v.sharesTotal.toRat + sharesNum.toRat =
        ((v.sharesTotal.toRat.num + sharesNum.toRat.num : ℤ) : ℚ) := by
      rw [Int.cast_add, hA, hB]
    rw [hsumeq, Rat.num_intCast]
    have hlo : (0 : ℚ) ≤ ((v.sharesTotal.toRat.num + sharesNum.toRat.num : ℤ) : ℚ) := by
      rw [← hsumeq, hsv]; linarith [v.wf.sharesTotal_nonneg]
    have hhi : ((v.sharesTotal.toRat.num + sharesNum.toRat.num : ℤ) : ℚ) ≤ 9223372036854775807 := by
      rw [← hsumeq]; linarith
    have hlo' : 0 ≤ v.sharesTotal.toRat.num + sharesNum.toRat.num := by exact_mod_cast hlo
    have hhi' : v.sharesTotal.toRat.num + sharesNum.toRat.num ≤ 9223372036854775807 := by exact_mod_cast hhi
    omega
  obtain ⟨hstv, hstd⟩ := operator_add_exact_int _ _ _ v.wf.sharesTotal_norm hsnorm v.wf.sharesTotal_int
    hsden hbound hst
  have hstn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm hsnorm hst
  have hst0 : 0 ≤ st'.toRat := by rw [hstv, hsv]; linarith [v.wf.sharesTotal_nonneg]
  refine Vault.cash_shares_update_lawful v aa' st' haan haa0 haar (Vault.onGrid_clause v aa' haan haa0 haak) hstn hst0
    hstd (by rw [hstv]; exact hsum') ?_
  -- the new share total is never zero
  intro hz
  exfalso
  have h0 : st'.toRat = 0 := by rw [hz, Number.toRat_zero]
  rw [hstv, hsv] at h0
  cases isDonation
  · linarith [hpos' rfl, v.wf.sharesTotal_nonneg]
  · rw [hzero rfl, add_zero] at h0
    have hm : ¬ v.sharesTotal.mantissa_ = 0 := by simpa using hopen.donation
    exact hm (Number.toRat_eq_zero_iff.mp h0)

/-- Proof of the success line of `Vault.deposit_exits`: the raw vault is lawful, so it converts, and the deposit
returns it. -/
lemma Vault.deposit_success_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hc : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType) (ra : STAmount) (amounts : VaultAmounts)
    (raw : RawVault) (assetsTotal' : Number)
    (hopen : v.DepositOpen isDonation t)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra))
    (hcomp : (computeDeposit v ra isDonation).run = .ok (.ok amounts))
    (hin : v.checkOpenLimit amounts.assets = .ok .tesSUCCESS)
    (hadj : (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw))
    (hat' : raw.assetsTotal = .ok assetsTotal')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault, (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok { amounts with vault' := v' }) ∧
      v'.toRawVault = raw := by
  obtain ⟨hwf, hval⟩ :=
    Vault.deposit_success_lawful v amountDeposit isDonation t hc hty ra amounts raw hopen hrounded hcomp hadj hSsz
  obtain ⟨v', hl, hv'⟩ := RawVault.to_lawful_ok_of hwf hval
  exact ⟨v', Vault.deposit_success_of_lawful v amountDeposit isDonation t hpos ra amounts raw assetsTotal' v' hopen
    hrounded hcomp hin hadj hat' hmax hl hSsz, hv'⟩

/-- Proof of `deposit_error_codes`: every exit is walked, and the cash update never reports a bad ledger. -/
lemma Vault.deposit_error_codes_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hc : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType) (ter : TER)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error ter)) :
    ter = .tecEXPIRED ∨ ter = .tecNO_PERMISSION ∨ ter = .tecLOCKED ∨ ter = .tecPRECISION_LOSS ∨
      ter = .tecINTERNAL ∨ ter = .tecPATH_DRY ∨ ter = .tecLIMIT_EXCEEDED := by
  have hmax := Vault.maxValue_fits_of_canonical v amountDeposit hc hty
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals try simp only [true_or, or_true]
  -- the rounded amount's rejection
  all_goals try
    have hr : (v.roundedDepositAmount amountDeposit).run = .ok (.error ter) := ‹_›
    simp [Vault.roundedDepositAmount_rejected_code_proof v amountDeposit ter hr]
  -- the share and charge computation
  all_goals try
    have hcd : (computeDeposit v _ isDonation).run = .ok (.error ter) := ‹_›
    rcases computeDeposit_codes v _ _ ter hcd with h | h | h <;> simp [h]
  -- the inflow check
  all_goals try
    have hin : Vault.checkOpenLimit _ _ = .ok ter := ‹_›
    have hne : (ter != .tesSUCCESS) = true := ‹_›
    rcases Vault.checkOpenLimit_codes _ _ _ hin with h | h
    · subst h; exact absurd hne (by decide)
    · simp [h]
  -- the cash update: a deposit's charge never makes the new cash negative
  all_goals
    have hrd : (v.roundedDepositAmount amountDeposit).run = .ok (.ok _) := ‹_›
    have hcd : (computeDeposit v _ isDonation).run = .ok (.ok _) := ‹_›
    have hadj : (v.adjustAssetsAndShares _ _).run = .ok (.error ter) := ‹_›
    obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amountDeposit _ hc hty hrd
    obtain ⟨ha1, -, ha3⟩ := computeDeposit_assets_form v _ isDonation _ hra1 hra2 hmax hcd
    rcases Vault.adjustAssetsAndShares_codes v _ _ ter hadj with h | h
    · subst h
      exact absurd hadj (Vault.adjustAssetsAndShares_not_bad_ledger v _ _ ha1 ha3)
    · simp [h]

end XRPL.Model.SingleAssetVault
