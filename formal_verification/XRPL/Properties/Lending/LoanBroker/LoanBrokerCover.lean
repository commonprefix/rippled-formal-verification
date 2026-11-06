import XRPL.Properties.Lending.LoanBroker.Common.CoverSequenceProofs
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits
import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness

/-! # Cover operations in sequence

Cover operations in sequence on a reachable broker: undoing one, splitting one in two, and swapping two.
Each one moves CoverAvailable by whole base units, so nothing else rounds along the way. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- On a reachable broker, a deposit's credit can be withdrawn right after the deposit, and that withdrawal restores
CoverAvailable. -/
theorem LoanBroker.coverDeposit_coverWithdraw_restores (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.canCoverWithdraw v res.amount' = .ok .tesSUCCESS ∧
    -- the credited amount is then withdrawn
    (∀ res' : LoanBrokerCoverResult, (res.loanBroker'.coverWithdraw v res.amount').run = .ok (.ok res') →
      res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable) :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
  ⟨LoanBroker.coverDeposit_withdrawable_proof lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok,
    fun res' hwd => LoanBroker.coverDeposit_coverWithdraw_restores_proof lb base hr hmax v hvb hnt amount hc hat hpos
      hcap hcan res res' hok hwd⟩

/-- On a reachable broker that does not hold XRP, a deposit's credit can be clawed back whole right after the
deposit, and that clawback restores CoverAvailable. -/
theorem LoanBroker.coverDeposit_coverClawback_restores (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native) -- C++ rejects any clawback of XRP, which has no issuer
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    (∃ claw : STAmount, (res.loanBroker'.roundedCoverClawback v (some res.amount')).run = .ok (.ok claw) ∧
      claw.toRat = res.amount'.toRat ∧ res.loanBroker'.canCoverClawback v (some res.amount') = .ok .tesSUCCESS) ∧
    -- the credited amount is then clawed back
    (∀ res' : LoanBrokerCoverResult, (res.loanBroker'.coverClawback v (some res.amount')).run = .ok (.ok res') →
      res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable) :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
  ⟨LoanBroker.coverDeposit_clawable_proof lb base hr hmax v hvb hnt hxrp amount hc hat hpos hcap hcan res hok,
    fun res' hclaw => LoanBroker.coverDeposit_coverClawback_restores_proof lb base hr hmax v hvb hnt hxrp amount hc
      hat hpos hcap hcan res res' hok hclaw⟩

/-- On a reachable broker, redepositing a withdrawal's payout restores CoverAvailable. -/
theorem LoanBroker.coverWithdraw_coverDeposit_restores (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res))
    -- the paid-out amount is then deposited back
    (hdep : (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
  LoanBroker.coverWithdraw_coverDeposit_restores_proof lb base hr hmax v hvb hnt amount hc hat hpos hcan
    res res' hok hdep

/-- On a reachable broker, redepositing a clawed-back amount restores CoverAvailable. -/
theorem LoanBroker.coverClawback_coverDeposit_restores (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : Option STAmount)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverClawback v amount).run = .ok (.ok res))
    -- the clawed amount is then deposited back
    (hdep : (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
  LoanBroker.coverClawback_coverDeposit_restores_proof lb base hr hmax v hvb hnt amount hreq hcan
    res res' hok hdep

/-- On a reachable broker, two withdrawals of whole base units give the same CoverAvailable as one
withdrawal of their sum. -/
theorem LoanBroker.coverWithdraw_split (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b c : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    -- both parts are whole base units of the vault
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    -- `a` then `b`
    (hcan1 : lb.canCoverWithdraw v a = .ok .tesSUCCESS) (h1 : (lb.coverWithdraw v a).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2))
    -- `c` at once
    (hcan3 : lb.canCoverWithdraw v c = .ok .tesSUCCESS) (h3 : (lb.coverWithdraw v c).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverWithdraw_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb hsum
    hga hgb r1 r2 s hcan1 h1 hcan2 h2 hcan3 h3

/-- Witness: with parts that are not whole base units, all checks pass and CoverAvailable differs. Two
withdrawals of `1.5` base units pay out one each, while one withdrawal of `3` pays out three. -/
theorem LoanBroker.coverWithdraw_split_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverWithdraw v a = .ok .tesSUCCESS ∧ (lb.coverWithdraw v a).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2) ∧
      lb.canCoverWithdraw v c = .ok .tesSUCCESS ∧ (lb.coverWithdraw v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_split_witness

/-- On a reachable broker, two deposits of whole base units give the same CoverAvailable as one
deposit of their sum. -/
theorem LoanBroker.coverDeposit_split (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b c : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    -- both parts are whole base units of the vault
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    -- `a` then `b`, an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap1 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan1 : lb.canCoverDeposit v a = .ok .tesSUCCESS) (h1 : (lb.coverDeposit v a).run = .ok (.ok r1))
    (hcap2 : lb.numericType.isIntegral = true →
      r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan2 : r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2))
    -- `c` at once
    (hcap3 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan3 : lb.canCoverDeposit v c = .ok .tesSUCCESS) (h3 : (lb.coverDeposit v c).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverDeposit_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb hsum
    hga hgb r1 r2 s hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3

/-- Witness: with parts that are not whole base units, all checks pass and CoverAvailable differs. Two
deposits of `1.5` base units are credited one each, while one deposit of `3` is credited whole. -/
theorem LoanBroker.coverDeposit_split_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v a = .ok .tesSUCCESS ∧ (lb.coverDeposit v a).run = .ok (.ok r1) ∧
      (lb.numericType.isIntegral = true →
        r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) ∧
      r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2) ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v c = .ok .tesSUCCESS ∧ (lb.coverDeposit v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_split_witness

/-- On a reachable broker, two clawbacks of whole base units give the same CoverAvailable as one
clawback of their sum. -/
theorem LoanBroker.coverClawback_split (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (a b c : STAmount) (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    -- both parts are whole base units of the vault
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    -- `a` then `b`
    (hcan1 : lb.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h1 : (lb.coverClawback v (some a)).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2))
    -- `c` at once
    (hcan3 : lb.canCoverClawback v (some c) = .ok .tesSUCCESS)
    (h3 : (lb.coverClawback v (some c)).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverClawback_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb
    hsum hga hgb r1 r2 s hcan1 h1 hcan2 h2 hcan3 h3

/-- Witness: with parts that are not whole base units, all checks pass and CoverAvailable differs. Two
clawbacks of `1.5` base units take one each, while one clawback of `3` takes three. -/
theorem LoanBroker.coverClawback_split_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some a)).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) ∧
      lb.canCoverClawback v (some c) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some c)).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_split_witness

/-- On a reachable broker, two withdrawals give the same CoverAvailable in either order. -/
theorem LoanBroker.coverWithdraw_comm (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    -- `a` then `b`
    (hcan1 : lb.canCoverWithdraw v a = .ok .tesSUCCESS) (h1 : (lb.coverWithdraw v a).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2))
    -- `b` then `a`
    (hcan3 : lb.canCoverWithdraw v b = .ok .tesSUCCESS) (h3 : (lb.coverWithdraw v b).run = .ok (.ok s1))
    (hcan4 : s1.loanBroker'.canCoverWithdraw v a = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverWithdraw v a).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverWithdraw_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
    hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4

/-- On a reachable broker, two clawbacks give the same CoverAvailable in either order. -/
theorem LoanBroker.coverClawback_comm (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (a b : STAmount) (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    -- `a` then `b`
    (hcan1 : lb.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h1 : (lb.coverClawback v (some a)).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2))
    -- `b` then `a`
    (hcan3 : lb.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h3 : (lb.coverClawback v (some b)).run = .ok (.ok s1))
    (hcan4 : s1.loanBroker'.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverClawback v (some a)).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverClawback_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
    hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4

/-- On a reachable broker, two deposits give the same CoverAvailable in either order. -/
theorem LoanBroker.coverDeposit_comm (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    -- `a` then `b`, an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap1 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan1 : lb.canCoverDeposit v a = .ok .tesSUCCESS) (h1 : (lb.coverDeposit v a).run = .ok (.ok r1))
    (hcap2 : lb.numericType.isIntegral = true →
      r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan2 : r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2))
    -- `b` then `a`
    (hcap3 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan3 : lb.canCoverDeposit v b = .ok .tesSUCCESS) (h3 : (lb.coverDeposit v b).run = .ok (.ok s1))
    (hcap4 : lb.numericType.isIntegral = true →
      s1.loanBroker'.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan4 : s1.loanBroker'.canCoverDeposit v a = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverDeposit v a).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
  LoanBroker.coverDeposit_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
    hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3 hcap4 hcan4 h4

end XRPL.Model.Lending
