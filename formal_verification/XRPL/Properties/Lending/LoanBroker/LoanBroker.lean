import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverWitness

/-! # `LoanBroker.HasMinimumCover`

The cover floor compares `coverAvailable` with the minimum cover: `debtTotal`
times `coverRateMinimum`, rounded up at the vault scale. More debt, a higher rate
or a coarser vault scale never lowers the minimum cover, so a broker can meet the floor at one
vault scale and miss it at a coarser one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A coarser vault scale never lowers the minimum cover. The minimum cover is
rounded up to the vault scale, and every point of a coarser grid is also a point
of a finer one. -/
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

/-- Witness: `minimumBrokerCover_scale_monotone` can be strict, so the vault scale alone can
flip the cover floor. A debt of `12.34567890123` at `10%` needs `1.234567890123` at scale
`10^-13` but `2` at `10^0`, and a cover of `1.3` meets only the first. -/
theorem minimumBrokerCover_scale_monotone_attained :
    ∃ (lb : LoanBroker) (e e' : Int), e < e' ∧ lb.HasMinimumCover e ∧
      lb.hasMinimumCover e' = .ok false :=
  LoanBroker.hasMinimumCover_scale_witness

/-- More debt never lowers the minimum cover. The debt times the rate is rounded up
at every step, and rounding up keeps the order. -/
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

/-- A higher `coverRateMinimum` never lowers the minimum cover. The debt times the
rate is rounded up at every step, and rounding up keeps the order. -/
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
