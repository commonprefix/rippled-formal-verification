import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Clamp
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Final

/-! # `Vault.withdraw` accuracy

Proof bodies behind the `Vault.withdraw` headlines in `VaultWithdraw.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.withdraw_sharesBurned_exact_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < shares.toRat)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares := by
  simp only [Vault.withdraw, computeWithdrawByShares, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals simp_all [WithdrawResult.rejected]

lemma Vault.withdraw_final_iff_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hposA : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hposA = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  obtain ⟨cw, an, sta, -, -, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hposA hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rw [hsb] at hpos hc hSnt ⊢
  constructor
  · intro heq
    rcases hcase with ⟨-, -, -, h⟩ | ⟨hf, -⟩
    · exact h
    · rw [heq] at hf; exact absurd hf (by decide)
  · intro hv
    rcases hcase with ⟨h, -⟩ | ⟨hf, an', sbn, at', atr, atr', av', st', -, -, -, hsbn, -, -, -, -,
      -, hsub, hrv⟩
    · exact h
    · exact absurd (congrArg RawVault.sharesTotal (hrv.symm.trans hv))
        (WdAcc.nonfinal_st_ne_zero v sta _ sbn st' hpos hc hSnt hst hf hsbn hsub)

lemma Vault.withdraw_vault_updates_integral_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assets'.toRat := by
  obtain ⟨cw, an, sta, hcomp, hcerr, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hpos hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rcases hcase with ⟨hf, -⟩ | ⟨-, an', sbn, at', atr, atr', av', st', hcl, -, han', -, hat, -, -,
    -, hav, -, hrv⟩
  · rw [hsb, hf] at hfin; exact absurd hfin (by decide)
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp hcerr
  obtain ⟨hpnt, hpoff, hpmv⟩ := WdAcc.price_integral_shape v _ _ _ hint hp
  have hcint : cw.assets'.integral = true := by
    show cw.assets'.mNumericType.isIntegral = true; rw [hpnt]; exact hint
  obtain ⟨hbnt, hboff, hbmv, -⟩ := WdAcc.clamp_integral _ _ _ hcint hcl
  obtain ⟨sn, hsn, hsnv, hsnn, hsnd⟩ := STAmount.toNumber_integral_exact' r.assets' .to_nearest
    (by rw [hbnt, hpnt]; exact hint) (by rw [hboff, hpoff]) (by rw [hbmv]; exact hpmv)
  obtain rfl : sn = an' := Except.ok.inj (hsn.symm.trans han')
  have hvx := v.exact
  have hAAeq : r.vault'.assetsAvailable = av' := congrArg RawVault.assetsAvailable hrv
  have hATeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  have hav0 : 0 ≤ av'.toRat := hAAeq ▸ r.vault'.exact.assetsAvailable_nonneg
  have hkAA : sn.toRat ≤ v.assetsAvailable.toRat :=
    WdAcc.le_of_sub_nonneg _ _ _ v.wf.assetsAvailable_norm hvx.assetsAvailable_nonneg hsnn
      (by rw [hsnv]; exact hsnd) hav hav0
  have hAAle : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := hvx.assetsAvailable_le
  have hsz' : v.assetsTotal.toRat ≤ 2 ^ 63 - 1 := hsz
  rw [hATeq, hAAeq, ← hsnv]
  exact ⟨operator_sub_exact_int_le _ _ _ _ v.wf.assetsTotal_norm hsz' hsnn rfl
      (by rw [hsnv]; exact hsnd) (hsnv ▸ hnn) (le_trans hkAA hAAle) hat,
    operator_sub_exact_int_le _ _ _ _ v.wf.assetsAvailable_norm (le_trans hAAle hsz') hsnn
      rfl (by rw [hsnv]; exact hsnd) (hsnv ▸ hnn) hkAA hav⟩

lemma Vault.withdraw_payout_integral_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
      1 + v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε := by
  obtain ⟨cw, an, sta, hcomp, hcerr, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hpos hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rcases hcase with ⟨hf, -⟩ | ⟨-, an', sbn, at', atr, atr', av', st', hcl, -, -, -, -, -, -,
    -, -, -, -⟩
  · rw [hsb, hf] at hfin; exact absurd hfin (by decide)
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp hcerr
  rw [← hsb] at hp
  obtain ⟨hpnt, hpoff, -⟩ := WdAcc.price_integral_shape v _ _ _ hint hp
  have hcint : cw.assets'.integral = true := by
    show cw.assets'.mNumericType.isIntegral = true; rw [hpnt]; exact hint
  obtain ⟨-, hboff, hbmv, hbneg⟩ := WdAcc.clamp_integral _ _ _ hcint hcl
  obtain ⟨hge, hr0⟩ := WdAcc.clamp_integral_ge _ _ hpoff hboff hbmv hbneg
  have hε : (0 : ℚ) ≤ depositε := by rw [WdAcc.depositε_val]; norm_num
  have hI0 := WdAcc.ideal_nonneg v waiveUnrealizedLoss _ hnn
  by_cases hI : 1 < v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat
  · obtain ⟨an, hof, hann, hanneg, -, hlo⟩ := WdAcc.price_an_lower v _ _ _ hc hnav hp
      (le_of_lt (lt_trans (by norm_num) hI))
    have h1 := STAmount.ofNumber_integral_within_one _ _ _ _ hint hann hanneg hof
    have := (abs_lt.mp h1).1
    nlinarith
  · push_neg at hI
    nlinarith

lemma Vault.withdraw_final_payout_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hposA : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hposA = .ok r) (herr : r.error = none)
    (hfinal : r.vault'.sharesTotal = Number.zero)
    (hAAc : ∀ aa : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok aa →
        aa.toRat = v.assetsAvailable.toRat) :
    r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    (0 < v.toExact.assetsAvailable →
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat) := by
  obtain ⟨cw, an, sta, hcomp, hcerr, han, hlt, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hposA hok herr
  rw [hsb] at hpos hc hSnt ⊢
  rcases hcase with ⟨hf, hloss, haa, -⟩ | ⟨hf, an', sbn, at', atr, atr', av', st', -, -, -, hsbn, -,
    -, -, -, -, hsub, hrv⟩
  swap
  · exact absurd ((congrArg RawVault.sharesTotal hrv).symm.trans hfinal)
      (WdAcc.nonfinal_st_ne_zero v sta _ sbn st' hpos hc hSnt hsta hf hsbn hsub)
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp hcerr
  have hS := v.wf
  have hSb := (WdAcc.burn_eq_iff v.sharesTotal _ sta hS.sharesTotal_norm hS.sharesTotal_nonneg
    hS.sharesTotal_int hsta hpos hc hSnt).mp hf
  have hloss0 : v.lossUnrealized.toRat = 0 := by
    by_contra hne
    have := (operator_ne_iff v.lossUnrealized Number.zero hS.lossUnrealized_norm (Or.inl rfl)).mpr
      (by rw [Number.toRat_zero]; exact hne)
    rw [this] at hloss; exact absurd hloss (by decide)
  have hpaid := hAAc _ haa
  have hvx := v.exact
  refine ⟨?_, fun hAApos => ?_⟩
  · have hST : (v.toExact.sharesTotal : ℚ) = v.sharesTotal.toRat :=
      RawVault.WF.toExact_sharesTotal v.toRawVault hS
    have hideal : v.idealAssetsWithdraw waiveUnrealizedLoss cw.sharesRedeemed.toRat =
        v.toExact.assetsTotal := by
      unfold RawVault.idealAssetsWithdraw
      rw [hST, hSb, mul_div_assoc, div_self (by rw [← hSb]; exact hpos.ne'), mul_one]
      cases waiveUnrealizedLoss
      · show v.toExact.assetsTotal - v.toExact.lossUnrealized = _
        rw [show v.toExact.lossUnrealized = 0 from hloss0, sub_zero]
      · rfl
    rw [hideal, hpaid]
    exact hvx.assetsAvailable_le
  · rw [hpaid]
    exact WdAcc.final_payout_lower v _ _ _ _ an hc hnav hp han hlt haa hpaid hAApos

lemma Vault.withdraw_payout_decreases_assets_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hc : r.sharesBurned.Canonical)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat < v.toExact.assetsTotal ∧
    r.vault'.assetsAvailable.toRat ≤ v.toExact.assetsAvailable := by
  obtain ⟨cw, an, sta, hcomp, hcerr, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount waiveUnrealizedLoss r hpos hok herr
  obtain rfl : sta = sharesTotalAmount := Except.ok.inj (hsta.symm.trans hst)
  rcases hcase with ⟨hf, -⟩ | ⟨-, an', sbn, at', atr, atr', av', st', hcl, -, han', -, hat, hatr,
    hatr', hguard, hav, -, hrv⟩
  · rw [hsb, hf] at hfin; exact absurd hfin (by decide)
  have hp := computeWithdraw_ok_priced v amount waiveUnrealizedLoss cw hcomp hcerr
  rw [hsb] at hc
  obtain ⟨hann, hanv⟩ := WdAcc.payout_toNumber v _ _ _ _ _ hc hp hcl han'
  have hanpos : 0 < an'.toRat := hanv ▸ hpay
  have hanm : an'.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hanpos.ne'
  have hATn := v.wf.assetsTotal_norm
  have hAAn := v.wf.assetsAvailable_norm
  have hATeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  have hAAeq : r.vault'.assetsAvailable = av' := congrArg RawVault.assetsAvailable hrv
  have hATle : at'.toRat ≤ v.assetsTotal.toRat :=
    operator_sub_le_of_le_normalized _ _ _ _ hATn hann hat hATn (by linarith)
  have hAAle : av'.toRat ≤ v.assetsAvailable.toRat :=
    operator_sub_le_of_le_normalized _ _ _ _ hAAn hann hav hAAn (by linarith)
  have hne : at'.toRat ≠ v.assetsTotal.toRat := by
    intro heq
    have hatn := operator_sub_isNormalized_to_nearest' _ _ _ hATn hann hat
    have hateq : at' = v.assetsTotal := hatn.toRat_inj hATn heq
    rw [hateq, hatr] at hatr'
    obtain rfl := Except.ok.inj hatr'
    have hA : (an'.mantissa_ != 0) = true := bne_iff_ne.mpr hanm
    have hB : atr.operator_eq atr = true := by
      simp only [STAmount.operator_eq, STAmount.areComparable, beq_self_eq_true, Bool.and_self]
    rw [hA, hB] at hguard
    exact absurd hguard (by decide)
  rw [hATeq, hAAeq]
  exact ⟨lt_of_le_of_ne hATle hne, hAAle⟩

end XRPL.Model.SingleAssetVault
