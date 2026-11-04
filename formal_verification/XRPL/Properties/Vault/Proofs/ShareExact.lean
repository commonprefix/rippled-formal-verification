import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.NumberBridge

/-! # Exact share pricing

When the share total times the amount and the ideal share count both fit a 19-digit `Number`, the two
`.to_nearest` stages of `assetsToSharesWithdraw` lose nothing, so the truncation gives the floor of the ideal. -/

namespace XRPL.Model.SingleAssetVault.WdTight

open XRPL.Model.Protocol

/-- A truncating withdrawal-side share price is the floor of the ideal at the computed net asset value when the
product and the quotient are both exact `Number`s. -/
lemma shares_exact (v : Vault) (a s : STAmount) (w : Bool) (nav : Number)
    (hnavN : v.assetsTotalForWithdrawal w = .ok nav) (hpos : 0 < a.toRat) (hc : a.Canonical)
    (hok : assetsToSharesWithdraw v a true w = .ok s) (hnz : s.isZero = false)
    (hprod : ∃ p : Number, p.isNormalized ∧ p.toRat = v.sharesTotal.toRat * a.toRat)
    (hquot : ∃ q : Number, q.isNormalized ∧ q.toRat = v.sharesTotal.toRat * a.toRat / nav.toRat) :
    s.toRat = (⌊v.idealSharesWithdrawAt nav.toRat a.toRat⌋ : ℚ) := by
  have hmv : s.mValue ≠ 0 := ne_of_beq_false (show (s.mValue == 0) = false from hnz)
  obtain ⟨nav', hsub, hcase⟩ := shares_reduces v a s w hok
  rw [hnavN, Except.ok.injEq] at hsub
  subst hsub
  obtain ⟨hnavn, hnav0⟩ := Vault.assetsTotalForWithdrawal_nonneg v w nav hnavN
  rcases hcase with ⟨-, rfl⟩ | ⟨hnm, an, SA, SN, t, han, hmul, hdiv, htr, hof⟩
  · exact absurd rfl hmv
  obtain ⟨an0, han0, hanv, hann⟩ := STAmount.toNumber_exact_canonical a .to_nearest
    (STAmount.Canonical.exactCanonical a hc)
  obtain rfl : an = an0 := Except.ok.inj (han.symm.trans han0)
  have htm : t.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 t .to_nearest s (by decide) hof hmv
  have hSNm : SN.mantissa_ ≠ 0 := Number.truncate_source_ne_zero SN t htr htm
  have hSAm : SA.mantissa_ ≠ 0 := operator_div_numerator_ne_zero_sz SA nav SN .to_nearest
    (Number.not_operator_eq_zero_of_mantissa_ne hnm) hdiv hSNm
  obtain ⟨hSm, hanm⟩ := operator_mul_operands_ne_zero v.wf.sharesTotal_norm hann hmul hSAm
  have hSAn := operator_mul_result_isNormalized _ _ _ _ v.wf.sharesTotal_norm hann hSm hanm hmul hSAm
  have hSNn := operator_div_result_isNormalized _ _ _ _ hSAn hnavn hSAm hnm hdiv hSNm
  -- the product is exact, then the quotient
  obtain ⟨p, hpn, hpv⟩ := hprod
  have hSAv : SA.toRat = v.sharesTotal.toRat * a.toRat := by
    have h := operator_mul_rounded_to_nearest _ _ _ v.wf.sharesTotal_norm hann hmul
    rw [hanv] at h
    exact Number.RoundsToRepresentable.eq_of_representable SA _ h p hpn hpv
  obtain ⟨q, hqn, hqv⟩ := hquot
  have hSNv : SN.toRat = v.sharesTotal.toRat * a.toRat / nav.toRat := by
    have h := operator_div_rounded_to_nearest _ _ _ hSAn hnavn hdiv
    rw [hSAv] at h
    exact Number.RoundsToRepresentable.eq_of_representable SN _ h q hqn hqv
  have hNpos : 0 < nav.toRat := lt_of_le_of_ne hnav0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hnm))
  have hSNpos : 0 < SN.toRat := by
    rw [hSNv]
    have hST0 : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
      (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSm))
    positivity
  obtain ⟨hfl, htn⟩ := Number.truncate_floor SN t hSNn (Number.negative_false_of_pos SN hSNpos) htr
  have htnn : 0 ≤ t.toRat := by rw [hfl]; exact_mod_cast Int.floor_nonneg.mpr hSNpos.le
  obtain ⟨z, hz, -, hzh, -⟩ := WdMono.int_pack .int64 (by decide) t s (htn htm) htnn hof
  have hzt : (z : ℚ) = t.toRat := by
    rw [hfl] at hzh ⊢
    have h1 : |((z - ⌊SN.toRat⌋ : ℤ) : ℚ)| ≤ 1 / 2 := by push_cast; exact hzh
    have h2 : z - ⌊SN.toRat⌋ = 0 := by
      by_contra hne
      have : (1 : ℚ) ≤ |((z - ⌊SN.toRat⌋ : ℤ) : ℚ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
      linarith
    have : z = ⌊SN.toRat⌋ := by omega
    rw [this]
  have hideal : v.idealSharesWithdrawAt nav.toRat a.toRat = v.sharesTotal.toRat * a.toRat / nav.toRat := by
    unfold RawVault.idealSharesWithdrawAt
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rw [hz, hzt, hfl, hSNv, hideal]

end XRPL.Model.SingleAssetVault.WdTight
