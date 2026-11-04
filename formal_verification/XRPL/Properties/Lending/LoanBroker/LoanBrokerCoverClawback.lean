import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverClawback` and `LoanBroker.coverClawback`

A clawback takes the request, or all cover above minCover when there is none, capped at that excess. In the Open
zone it claws that amount floored to whole base units, and CoverAvailable drops by exactly that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- When the amount is unset or 0 and CoverAvailable is whole base units within the Open limit -> the clawed amount =
CoverAvailable − minCover, and the clawback leaves exactly minCover. -/
theorem LoanBroker.roundedCoverClawback_all (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number)
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker
    (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat = lb.toExact.coverAvailable - minimumCover.toRat ∧
      res.loanBroker'.toExact.coverAvailable = minimumCover.toRat :=
  ⟨LoanBroker.roundedCoverClawback_all_proof lb v amount res minimumCover hz hnt hmax hreq hall hmin hok,
    LoanBroker.coverClawback_all_leaves_minimum_proof lb v amount res minimumCover hz hnt hmax hreq hall hmin hok⟩

/-- Witness: off the Open zone the checks pass and the clawed amount ≠ CoverAvailable − minCover. On a cover of
`1000000000000001.6` with minCover `1`, a full clawback rounds the clawed amount up to `1000000000000001`. -/
theorem LoanBroker.roundedCoverClawback_all_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.amount'.toRat ≠ lb.toExact.coverAvailable - minimumCover.toRat :=
  LoanBroker.roundedCoverClawback_all_witness

/-- Witness: off the Open zone, a run where the checks pass and a full clawback leaves CoverAvailable' ≠
minCover. On the broker of `roundedCoverClawback_all_attained` it leaves `0.6` with minCover `1`. -/
theorem LoanBroker.roundedCoverClawback_all_leaves_minimum_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable ≠ minimumCover.toRat :=
  LoanBroker.coverClawback_all_leaves_minimum_witness

/-- When the amount ≠ 0 and CoverAvailable is whole base units within the Open limit -> the clawed amount ≤
min(amount, CoverAvailable − minCover), and less than 1 base unit below it. -/
theorem LoanBroker.roundedCoverClawback_capped (v : Vault) (a : STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number)
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker
    (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.amount'.toRat ≤ min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) ∧
      min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) - res.amount'.toRat < 10 ^ v.baseExponent :=
  have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a hreq.1 hnz hreq.2.1
  ⟨LoanBroker.roundedCoverClawback_capped_upper_bound_proof lb v a res minimumCover hz hnt hmax hreq hnz hmin hok,
    LoanBroker.roundedCoverClawback_capped_lower_bound_proof lb v a res minimumCover hz hnt hmax hreq hnz hmin hok⟩

/-- Witness: a run that claws exactly min(amount, CoverAvailable − minCover). One base unit is clawed
whole. -/
theorem LoanBroker.roundedCoverClawback_capped_upper_bound_attained :
    ∃ (lb : LoanBroker) (v : Vault) (a : STAmount) (res : LoanBrokerCoverResult) (minimumCover : Number),
      lb.OpenZone v.baseExponent ∧ v.numericType = lb.numericType ∧
      (a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧ a.isZero = false ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      (lb.coverClawback v (some a)).run = .ok (.ok res) ∧
      res.amount'.toRat = min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) :=
  LoanBroker.roundedCoverClawback_capped_upper_bound_witness

/-- Witness: a run where min(amount, CoverAvailable − minCover) − the clawed amount is just under 1 base unit,
1 − 10⁻¹⁵ base units. A clawback of `1.999999999999999` base units takes one. -/
theorem LoanBroker.roundedCoverClawback_capped_lower_bound_attained :
    ∃ (lb : LoanBroker) (v : Vault) (a : STAmount) (res : LoanBrokerCoverResult) (minimumCover : Number),
      lb.OpenZone v.baseExponent ∧ v.numericType = lb.numericType ∧
      (a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧ a.isZero = false ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      (lb.coverClawback v (some a)).run = .ok (.ok res) ∧
      min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) - res.amount'.toRat =
        (1 - 1 / 10 ^ 15) * 10 ^ v.baseExponent :=
  LoanBroker.roundedCoverClawback_capped_lower_bound_witness

/-- For MPT, on a reachable broker -> an amount ≠ 0 is clawed exactly, capped at CoverAvailable. -/
theorem LoanBroker.roundedCoverClawback_integral (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    -- an MPT: an integral asset that is not XRP, as C++ rejects any clawback of XRP
    (hmpt : lb.numericType.isIntegral = true ∧ lb.numericType ≠ .native) (a : STAmount)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.amount'.toRat = min a.toRat lb.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a hreq.1 hnz hreq.2.1
  LoanBroker.roundedCoverClawback_integral_proof lb base hr hmax v hvb hnt hmpt.1 a hreq hnz res hok

/-- A clawback on a reachable broker -> CoverAvailable drops by exactly the clawed amount, at most the amount when it
is ≠ 0. On any MPT broker with a whole CoverAvailable below 2^63 it also drops by exactly the clawed amount. -/
theorem LoanBroker.coverClawback_debit :
    (∀ (base : Int) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → (lb.coverClawback v amount).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (a : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType →
      a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat → a.isZero = false →
      (lb.coverClawback v (some a)).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ a.toRat) ∧
    (∀ (base : Int) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → (lb.coverClawback v amount).run = .ok (.ok res) →
      ∃ (deltaCover : Number) (deltaAmount : STAmount),
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat) ∧
    -- an MPT: an integral asset that is not XRP, as C++ rejects any clawback of XRP. The asset's maximum fits an
    -- int64 amount, as C++ caps every MPT maximum. An MPT balance is a whole number below 2^63, as every MPT
    -- maximum is
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      (lb.coverClawback pool amount).run = .ok (.ok res) →
      lb.numericType.isIntegral = true ∧ lb.numericType ≠ .native →
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      lb.toExact.coverAvailable.den = 1 → lb.toExact.coverAvailable < 2 ^ 63 →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat) :=
  ⟨fun base v amount res hr hvb hok =>
      have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
      LoanBroker.coverClawback_debit_proof lb base hr hmax v hvb amount res hok,
    fun base v a res hr hvb hnt hreq hnz hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a hreq.1 hnz hreq.2.1
      LoanBroker.coverClawback_debit_le_amount_proof lb base hr hmax v hvb hnt a hreq hnz res hok,
    fun base v amount res hr hvb hnt hok =>
      have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
      LoanBroker.coverClawback_applied_delta_proof lb base hr hmax v hvb hnt amount res hok,
    fun pool amount res hok hmpt hmax hcint hbound =>
      LoanBroker.coverClawback_debit_integral_proof lb pool amount res hok hmpt.1 hmax hcint hbound⟩

/-- Cover clawback only lowers CoverAvailable (monotone down). -/
theorem LoanBroker.coverClawback_decreases_cover (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback pool amount).run = .ok (.ok res))
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    -- the vault's base exponent is in the IOU exponent range
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_decreases_cover_proof lb pool amount res hok hmax hb

/-- On a reachable broker -> a bigger clawback amount never takes less. -/
theorem LoanBroker.coverClawback_monotone (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (ha : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hb : b.CanonicalOrZero ∧ b.mNumericType = lb.numericType ∧ 0 ≤ b.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false) (hab : a.toRat ≤ b.toRat)
    (ra rb : LoanBrokerCoverResult)
    (hoka : (lb.coverClawback v (some a)).run = .ok (.ok ra))
    (hokb : (lb.coverClawback v (some b)).run = .ok (.ok rb)) :
    ra.amount'.toRat ≤ rb.amount'.toRat :=
  have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a ha.1 hza ha.2.1
  LoanBroker.coverClawback_monotone_proof lb base hr hmax v hvb hnt a b ha hb hza hzb hab ra rb hoka hokb

/-- CoverAvailable' ≥ minCover, when CoverAvailable is whole base units within the Open limit. -/
theorem LoanBroker.coverClawback_keeps_minimum (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number)
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker
    (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    minimumCover.toRat ≤ res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_keeps_minimum_proof lb v amount res minimumCover hz hnt hmax hreq hmin hok

/-- Witness: off the Open zone the checks pass and CoverAvailable' < minCover. On a cover of
`1000000000000001.6` with minCover `1`, a full clawback takes `1000000000000001` and leaves `0.6`. -/
theorem LoanBroker.coverClawback_keeps_minimum_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat :=
  LoanBroker.coverClawback_keeps_minimum_witness

/-- On a reachable broker that does not hold XRP, with CoverAvailable > 0 -> there is an amount that lowers
CoverAvailable. -/
theorem LoanBroker.coverClawback_decrease_possible (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native) -- C++ rejects any clawback of XRP, which has no issuer
    (hpos : 0 < lb.toExact.coverAvailable) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
        lb.canCoverClawback v (some amount) = .ok .tesSUCCESS ∧
        (lb.coverClawback v (some amount)).run = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable < lb.toExact.coverAvailable :=
  have hmax := LoanBroker.Reachable.maxValue_fits lb base hr hpos
  LoanBroker.coverClawback_decrease_possible_proof lb base hr hmax v hvb hnt hxrp hpos

/-- When the checks pass -> the clawback never throws an error other than notLawful, and is never notLawful when
CoverAvailable is whole base units within the Open limit. -/
theorem LoanBroker.coverClawback_total (amount : Option STAmount) :
    -- CoverAvailable is an asset balance, and every IOU amount is below 10^96
    (∀ {α : Type} [AssetPool α] (pool : α), lb.canCoverClawback pool amount = .ok .tesSUCCESS →
      lb.toExact.coverAvailable < 10 ^ 96 →
      (∃ res, (lb.coverClawback pool amount).run = .ok (.ok res)) ∨
        (lb.coverClawback pool amount).run = .error .notLawful) ∧
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker, and the asset's
    -- maximum fits an int64 amount, as C++ caps every MPT maximum
    (∀ v : Vault, lb.OpenZone v.baseExponent → v.numericType = lb.numericType →
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) →
      lb.canCoverClawback v amount = .ok .tesSUCCESS →
      ∃ res, (lb.coverClawback v amount).run = .ok (.ok res)) :=
  ⟨fun pool hcan hcap => LoanBroker.coverClawback_total_proof lb pool amount hcan hcap,
    fun v hz hnt hmax hreq hcan => LoanBroker.coverClawback_lawful_total_proof lb v amount hz hnt hmax hreq hcan⟩

/-- Witness: off the Open zone a run passes the checks but is notLawful. With no debt and a cover of
`1000000000000000.6`, a full clawback takes `1000000000000001`, so the new cover is negative. -/
theorem LoanBroker.coverClawback_total_lawful_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .error .notLawful :=
  LoanBroker.coverClawback_lawful_total_witness

/-- On a reachable broker that does not hold XRP -> the whole cover (≠ 0) can be clawed back. -/
theorem LoanBroker.coverClawback_all (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native) -- C++ rejects any clawback of XRP, which has no issuer
    (s : STAmount)
    -- `s` is CoverAvailable in the vault asset
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s) (hnz : s.mValue ≠ 0) :
    lb.canCoverClawback v none = .ok .tesSUCCESS ∧
      ∃ res, (lb.coverClawback v none).run = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0 :=
  have hmax := LoanBroker.Reachable.cover_amount_maxValue_fits lb base hr s hs hnz
  LoanBroker.coverClawback_all_proof lb base hr hmax v hvb hnt hxrp s hs hnz

end XRPL.Model.Lending
