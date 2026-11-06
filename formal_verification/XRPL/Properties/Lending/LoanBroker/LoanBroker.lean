import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverWitness

/-! # `minimumBrokerCover`

The minimum cover is `debtTotal` times `coverRateMinimum`, rounded up at the vault scale.
More debt, a higher rate or a coarser scale never lowers it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- When minCover ≠ 0 before and after -> a coarser vault scale, a higher DebtTotal or a higher CoverRateMinimum
never lowers it. -/
theorem minimumBrokerCover_monotone (nt : NumericType) :
    -- `e'` is the coarser vault scale, both scales are in the IOU exponent range
    (∀ (debtTotal : Number) (coverRateMinimum : TenthBips32) (e e' : Int) (m m' : Number), e ≤ e' → -96 ≤ e →
      e' ≤ 80 → minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m →
      minimumBrokerCover nt debtTotal coverRateMinimum e' = .ok m' → m ≠ Number.zero → m' ≠ Number.zero →
      m.toRat ≤ m'.toRat) ∧
    -- the vault scale is in the IOU exponent range
    (∀ (debtTotal debtTotal' : Number) (coverRateMinimum : TenthBips32) (e : Int) (m m' : Number),
      debtTotal.isNormalized → debtTotal'.isNormalized → 0 ≤ debtTotal.toRat → debtTotal.toRat ≤ debtTotal'.toRat →
      -96 ≤ e → e ≤ 80 → minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m →
      minimumBrokerCover nt debtTotal' coverRateMinimum e = .ok m' → m' ≠ Number.zero → m.toRat ≤ m'.toRat) ∧
    -- the vault scale is in the IOU exponent range
    (∀ (debtTotal : Number) (rate rate' : TenthBips32) (e : Int) (m m' : Number), debtTotal.isNormalized →
      0 ≤ debtTotal.toRat → rate.toNat ≤ rate'.toNat → -96 ≤ e → e ≤ 80 →
      minimumBrokerCover nt debtTotal rate e = .ok m → minimumBrokerCover nt debtTotal rate' e = .ok m' →
      m' ≠ Number.zero → m.toRat ≤ m'.toRat) :=
  ⟨minimumBrokerCover_scale_monotone_proof nt, minimumBrokerCover_debt_monotone_proof nt,
    minimumBrokerCover_rate_monotone_proof nt⟩

/-- Witness: a coarser vault scale can strictly raise minCover. A debt of `12.34567890123` at `10%` needs
`1.234567890123` at scale `10^-13` but `2` at `10^0`. -/
theorem minimumBrokerCover_monotone_scale_attained :
    ∃ (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (e e' : Int) (m m' : Number),
      e < e' ∧ -96 ≤ e ∧ e' ≤ 80 ∧ minimumBrokerCover nt debtTotal rate e = .ok m ∧
      minimumBrokerCover nt debtTotal rate e' = .ok m' ∧ m ≠ Number.zero ∧ m' ≠ Number.zero ∧ m.toRat < m'.toRat :=
  minimumBrokerCover_scale_witness

end XRPL.Model.Lending
