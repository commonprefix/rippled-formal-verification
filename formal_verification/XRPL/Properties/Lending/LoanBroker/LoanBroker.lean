import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverWitness

/-! # `LoanBroker.HasMinimumCover`

The minimum cover is `debtTotal` times `coverRateMinimum`, rounded up at the vault scale.
More debt, a higher rate or a coarser scale never lowers it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A coarser vault scale never lowers the minCover when it is ≠ 0. -/
theorem minimumBrokerCover_scale_monotone (nt : NumericType) (debtTotal : Number)
    (coverRateMinimum : TenthBips32) (e e' : Int) (m m' : Number)
    (hle : e ≤ e') -- `e'` is the coarser vault scale
    (he : -96 ≤ e) (he' : e' ≤ 80) -- both scales are in the IOU exponent range
    (hm : minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m)
    (hm' : minimumBrokerCover nt debtTotal coverRateMinimum e' = .ok m')
    (hnz : m ≠ Number.zero) (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat :=
  minimumBrokerCover_scale_monotone_proof nt debtTotal coverRateMinimum e e' m m' hle he he' hm hm'
    hnz hnz'

/-- Witness: a coarser vault scale can cause CoverAvailable < minCover. A debt of `12.34567890123`
at `10%` needs `1.234567890123` at scale `10^-13` but `2` at `10^0`, so a cover of `1.3` meets
only the first. -/
theorem minimumBrokerCover_scale_monotone_attained :
    ∃ (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (e e' : Int) (m m' : Number),
      e < e' ∧ -96 ≤ e ∧ e' ≤ 80 ∧ minimumBrokerCover nt debtTotal rate e = .ok m ∧
      minimumBrokerCover nt debtTotal rate e' = .ok m' ∧ m.toRat < m'.toRat :=
  minimumBrokerCover_scale_witness

/-- A higher DebtTotal never lowers the minCover when it is ≠ 0. -/
theorem minimumBrokerCover_debt_monotone (nt : NumericType) (debtTotal debtTotal' : Number)
    (coverRateMinimum : TenthBips32) (e : Int) (m m' : Number)
    (hd : debtTotal.isNormalized) (hd' : debtTotal'.isNormalized) (h0 : 0 ≤ debtTotal.toRat)
    (hle : debtTotal.toRat ≤ debtTotal'.toRat)
    (he : -96 ≤ e) (he' : e ≤ 80) -- the vault scale is in the IOU exponent range
    (hm : minimumBrokerCover nt debtTotal coverRateMinimum e = .ok m)
    (hm' : minimumBrokerCover nt debtTotal' coverRateMinimum e = .ok m')
    (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat :=
  minimumBrokerCover_debt_monotone_proof nt debtTotal debtTotal' coverRateMinimum e m m' hd hd' h0
    hle he he' hm hm' hnz'

/-- A higher CoverRateMinimum never lowers the minCover when it is ≠ 0. -/
theorem minimumBrokerCover_rate_monotone (nt : NumericType) (debtTotal : Number)
    (rate rate' : TenthBips32) (e : Int) (m m' : Number)
    (hd : debtTotal.isNormalized) (h0 : 0 ≤ debtTotal.toRat)
    (hle : rate.toNat ≤ rate'.toNat)
    (he : -96 ≤ e) (he' : e ≤ 80) -- the vault scale is in the IOU exponent range
    (hm : minimumBrokerCover nt debtTotal rate e = .ok m)
    (hm' : minimumBrokerCover nt debtTotal rate' e = .ok m')
    (hnz' : m' ≠ Number.zero) :
    m.toRat ≤ m'.toRat :=
  minimumBrokerCover_rate_monotone_proof nt debtTotal rate rate' e m m' hd h0 hle he he' hm hm' hnz'

end XRPL.Model.Lending
