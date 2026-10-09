import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.Common.ReachableWitness
import XRPL.Properties.Lending.LoanBroker.Common.CoverSequenceProofs

/-! # Cover operations in sequence

Cover operations run one after another: the total over `n` operations, undoing an
operation, splitting one in two, and changing the order. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- Over n cover operations without rounding -> CoverAvailable = start + Σdeposits - Σwithdrawals -
Σclawbacks. -/
theorem LoanBroker.ReachableFromIn.cover_eq (start lb : LoanBroker) (unit : ℚ) (n : ℕ)
    (applied requested : ℚ)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    lb.toExact.coverAvailable = start.toExact.coverAvailable + applied :=
  LoanBroker.ReachableFromIn.cover_eq_proof start unit lb n applied requested hr

/-- Over n cover operations -> 0 ≤ start + Σdeposits - Σwithdrawals - Σclawbacks - CoverAvailable ≤
n × unit, where `unit` is at least one ULP of the cover scale at every deposit. Today only deposits
round, so the error is n deposits × 1 ULP. Once C++ rounds withdrawals and clawbacks too, the bound
stays as stated. -/
theorem LoanBroker.ReachableFromIn.cover_within_bounds (start lb : LoanBroker) (unit : ℚ) (n : ℕ)
    (applied requested : ℚ)
    (hu0 : 0 ≤ unit)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    0 ≤ start.toExact.coverAvailable + requested - lb.toExact.coverAvailable ∧
      start.toExact.coverAvailable + requested - lb.toExact.coverAvailable ≤ n * unit :=
  LoanBroker.ReachableFromIn.cover_within_bounds_proof start unit lb n applied requested hu0 hr

/-- Witness: only deposits round, so for every n < 9·10^15 a run of n deposits, each rounded down by
1 − 10⁻¹⁵ ULP, brings the error to just under the bound. The deposits are `1.999999999999999` on
a cover starting at `10^15`, where one unit is `1`. -/
theorem LoanBroker.ReachableFromIn.cover_within_bounds_attained (n : ℕ)
    -- the cover `10^15 + n` stays below `10^16`, so one unit stays `1`
    (hn : n < 9 * 10 ^ 15) :
    ∃ (start lb : LoanBroker) (unit applied requested : ℚ),
      0 ≤ unit ∧ LoanBroker.ReachableFromIn start unit lb n applied requested ∧
      (1 - 1 / 10 ^ 15) * (n * unit) ≤
        start.toExact.coverAvailable + requested - lb.toExact.coverAvailable :=
  LoanBroker.ReachableFromIn.cover_within_bounds_witness n hn

/-- Withdrawing a deposit's roundedAmount restores CoverAvailable (if the sum fits a Number). -/
theorem LoanBroker.coverDeposit_coverWithdraw_restores (lb : LoanBroker) (amount : STAmount)
    (res res' : LoanBrokerCoverResult)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    -- the credited amount is then withdrawn
    (hwd : res.loanBroker'.coverWithdraw res.amount' = .ok (.ok res'))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  LoanBroker.coverDeposit_coverWithdraw_restores_proof lb amount res res' hdep hwd hc hexact

/-- Witness: a run where the withdrawal passes its checks and CoverAvailable' > CoverAvailable. A
deposit of `9999999999999999 * 10^15` on a cover of `6.6 * 10^12` is credited as if the cover
held `10^13`, and withdrawing the credited amount leaves `10^13`. -/
theorem LoanBroker.coverDeposit_coverWithdraw_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res res' : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧
      res.loanBroker'.canCoverWithdraw pool res.amount' = .ok .tesSUCCESS ∧
      res.loanBroker'.coverWithdraw res.amount' = .ok (.ok res') ∧ amount.ExactCanonical ∧
      lb.toExact.coverAvailable < res'.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_coverWithdraw_restores_witness

/-- A deposit's roundedAmount can be immediately withdrawn, when it passes the scale check at the
new CoverAvailable and CoverAvailable ≥ minCover. -/
theorem LoanBroker.coverDeposit_withdrawable (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    -- the sum is below `10^96`, above every IOU amount
    (hcap : lb.toExact.coverAvailable + res.amount'.toRat < 10 ^ 96)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : lb.HasMinimumCover e)
    -- the credited amount is nonzero at the scale of the new `coverAvailable`
    (hcheck : canApplyToBrokerCover res.loanBroker'.numericType res.loanBroker'.coverAvailable
      res.amount' = .ok .tesSUCCESS) :
    res.loanBroker'.canCoverWithdraw pool res.amount' = .ok .tesSUCCESS :=
  LoanBroker.coverDeposit_withdrawable_proof lb pool amount res e hdep hc hnn hcap hexact hexp
    hmin hcheck

/-- Witness: a deposit's roundedAmount can become un-withdrawable -> tecPRECISION_LOSS. The deposit
lifts `coverAvailable` across a power of ten, and the coarser cover scale rounds the credited
amount to zero. -/
theorem LoanBroker.coverDeposit_withdrawable_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverDeposit_withdrawable_witness

/-- A deposit's roundedAmount can be immediately clawed back whole, when it passes the scale check
at the new CoverAvailable and CoverAvailable ≥ minCover. -/
theorem LoanBroker.coverDeposit_clawable (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (claw : STAmount)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hat : amount.mNumericType = lb.numericType)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : lb.HasMinimumCover e)
    (hrr : res.loanBroker'.roundedCoverClawback pool (some res.amount') = .ok (.rounded claw))
    -- the credited amount is nonzero at the scale of the new `coverAvailable`
    (hcheck : canApplyToBrokerCover res.loanBroker'.numericType res.loanBroker'.coverAvailable
      res.amount' = .ok .tesSUCCESS) :
    claw = res.amount' ∧
      res.loanBroker'.canCoverClawback pool (some res.amount') = .ok .tesSUCCESS :=
  LoanBroker.coverDeposit_clawable_proof lb pool amount res e claw hdep hc hnn hat hexact hexp
    hmin hrr hcheck

/-- Witness: a deposit's roundedAmount can no longer be clawed back -> tecPRECISION_LOSS. The
deposit lifts `coverAvailable` across a power of ten, and the coarser cover scale rounds the
credited amount to zero. -/
theorem LoanBroker.coverDeposit_clawable_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverClawback pool (some amount) = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverDeposit_clawable_witness

/-- With no debt, clawing back a deposit's roundedAmount restores CoverAvailable (if the sum fits a
Number). -/
theorem LoanBroker.coverDeposit_coverClawback_restores (lb : LoanBroker) (pool : α)
    (amount : STAmount) (res res' : LoanBrokerCoverResult)
    (hdebt : lb.debtTotal = Number.zero)
    (hdep : lb.coverDeposit amount = .ok (.ok res))
    -- the credited amount is then clawed back
    (hclaw : res.loanBroker'.coverClawback pool (some res.amount') = .ok (.ok res'))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hat : amount.mNumericType = lb.numericType)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  LoanBroker.coverDeposit_coverClawback_restores_proof lb pool amount res res' hdebt hdep hclaw hc
    hnn hat hexact

/-- Witness: a run where the clawback passes its checks and CoverAvailable' > CoverAvailable. On the
run of `coverDeposit_coverWithdraw_restores_attained`, clawing back the credited amount also
leaves `10^13` instead of `6.6 * 10^12`. -/
theorem LoanBroker.coverDeposit_coverClawback_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res res' : LoanBrokerCoverResult),
      lb.debtTotal = Number.zero ∧ lb.coverDeposit amount = .ok (.ok res) ∧
      res.loanBroker'.canCoverClawback pool (some res.amount') = .ok .tesSUCCESS ∧
      res.loanBroker'.coverClawback pool (some res.amount') = .ok (.ok res') ∧
      amount.ExactCanonical ∧ 0 ≤ amount.toRat ∧ amount.mNumericType = lb.numericType ∧
      lb.toExact.coverAvailable < res'.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_coverClawback_restores_witness

/-- Two clawbacks give the same CoverAvailable as one clawback of their exact sum (if neither part is
capped and nothing rounds). -/
theorem LoanBroker.coverClawback_split (lb : LoanBroker) (pool : α) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    -- `a` then `b`
    (h1 : lb.coverClawback pool (some a) = .ok (.ok r1))
    (h2 : r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2))
    (h3 : lb.coverClawback pool (some c) = .ok (.ok s)) -- `c` at once
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hb0 : 0 ≤ b.toRat) (hc0 : 0 ≤ c.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false) (hzc : c.isZero = false)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : c.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hcan1 : lb.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hcan2 : r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan3 : lb.canCoverClawback pool (some c) = .ok .tesSUCCESS)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_split_proof lb pool a b c r1 r2 s e minimumCover h1 h2 h3 hca hcb hcc
    hat hbt hct ha0 hb0 hc0 hza hzb hzc hsum hexp hmin hfit hcan1 hcan2 hcan3 hx1 hx2

/-- Witness: a run where all checks pass and CoverAvailable is different. From a cover of `10^18`,
clawing `1000.5` twice ends at `999999999999998000`, while clawing `2001` at once ends at
`999999999999997999`. -/
theorem LoanBroker.coverClawback_split_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult)
      (e : Int) (minimumCover : Number),
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2) ∧
      lb.coverClawback pool (some c) = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧
      c.mNumericType = lb.numericType ∧
      0 ≤ a.toRat ∧ 0 ≤ b.toRat ∧ 0 ≤ c.toRat ∧
      a.isZero = false ∧ b.isZero = false ∧ c.isZero = false ∧
      c.toRat = a.toRat + b.toRat ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      c.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat ∧
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some c) = .ok .tesSUCCESS ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_split_witness

/-- Two withdrawals give the same CoverAvailable as one withdrawal of their exact sum (if nothing
rounds). -/
theorem LoanBroker.coverWithdraw_split (lb : LoanBroker) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult)
    -- `a` then `b`
    (h1 : lb.coverWithdraw a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverWithdraw b = .ok (.ok r2))
    (h3 : lb.coverWithdraw c = .ok (.ok s)) -- `c` at once
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_split_proof lb a b c r1 r2 s h1 h2 h3 hca hcb hcc hsum hx1 hx2

/-- Witness: a run where all checks pass and CoverAvailable is different. From a cover of `10^18`,
withdrawing `1000.5` twice ends at `999999999999998000`, while withdrawing `2001` at once ends
at `999999999999997999`. -/
theorem LoanBroker.coverWithdraw_split_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      r1.loanBroker'.coverWithdraw b = .ok (.ok r2) ∧
      lb.canCoverWithdraw pool c = .ok .tesSUCCESS ∧ lb.coverWithdraw c = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧ c.toRat = a.toRat + b.toRat ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_split_witness

/-- Two deposits give the same CoverAvailable as one deposit of their exact sum (if the cover scale
doesn't change and nothing rounds). -/
theorem LoanBroker.coverDeposit_split (lb : LoanBroker) (a b c : STAmount)
    (r1 r2 s : LoanBrokerCoverResult) (e : Int)
    -- `a` then `b`
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    (h3 : lb.coverDeposit c = .ok (.ok s)) -- `c` at once
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical) (hcc : c.ExactCanonical)
    (hsum : c.toRat = a.toRat + b.toRat)
    -- the cover scale, and the scale after the first part is the same
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    -- all three amounts sit on the cover scale, so no deposit rounds them
    (hga : e ≤ a.exponent) (hgb : e ≤ b.exponent) (hgc : e ≤ c.exponent)
    (hx1 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + a.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + c.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_split_proof lb a b c r1 r2 s e h1 h2 h3 hca hcb hcc hsum he hr hga hgb
    hgc hx1 hx2

/-- Witness: a run where all checks pass and CoverAvailable is different. On a cover of `5 * 10^15`,
depositing `6 * 10^15` lifts the cover to `1.1 * 10^16`, where one unit is `10`, so the second
part `1000000000000001` is rounded down to `10^15`. Depositing `7000000000000001` at once is
taken whole. -/
theorem LoanBroker.coverDeposit_split_attained :
    ∃ (lb : LoanBroker) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult) (e : Int),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit c = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧ c.toRat = a.toRat + b.toRat ∧
      numberExponent lb.coverAvailable lb.numericType = .ok e ∧
      e ≤ a.exponent ∧ e ≤ b.exponent ∧ e ≤ c.exponent ∧
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + a.toRat) ∧
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + c.toRat) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable ∧
      r1.amount'.toRat + r2.amount'.toRat ≠ s.amount'.toRat :=
  LoanBroker.coverDeposit_split_witness

/-- Redepositing a withdrawn amount restores CoverAvailable (if nothing rounds). -/
theorem LoanBroker.coverWithdraw_coverDeposit_restores (lb : LoanBroker) (amount : STAmount)
    (res res' : LoanBrokerCoverResult) (e : Int)
    (hwd : lb.coverWithdraw amount = .ok (.ok res))
    -- the withdrawn amount is then deposited back
    (hdep : res.loanBroker'.coverDeposit amount = .ok (.ok res'))
    -- the scale of the cover after the withdrawal, and the amount sits on it
    (hexp : numberExponent res.loanBroker'.coverAvailable res.loanBroker'.numericType = .ok e)
    (hgrid : e ≤ amount.exponent)
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_coverDeposit_restores_proof lb amount res res' e hwd hdep hexp hgrid
    hc hexact

/-- Witness: a run where the redeposit rounds. Withdrawing `7.6 * 10^-10` from `10^6` and depositing
it back credits only `7 * 10^-10`. -/
theorem LoanBroker.coverWithdraw_coverDeposit_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit amount = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_coverDeposit_witness

/-- Redepositing a clawed roundedAmount restores CoverAvailable (if nothing rounds). -/
theorem LoanBroker.coverClawback_coverDeposit_restores (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res res' : LoanBrokerCoverResult) (e : Int)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hclaw : lb.coverClawback pool amount = .ok (.ok res))
    -- the clawed amount is then deposited back
    (hdep : res.loanBroker'.coverDeposit res.amount' = .ok (.ok res'))
    -- the scale of the cover after the clawback, and the amount sits on it
    (hexp : numberExponent res.loanBroker'.coverAvailable res.loanBroker'.numericType = .ok e)
    (hgrid : e ≤ res.amount'.exponent)
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_coverDeposit_restores_proof lb pool amount res res' e hcan hclaw hdep
    hexp hgrid hreq hexact

/-- Witness: a run where the redeposit rounds. Clawing `7.6 * 10^-10` from `10^6` and depositing it
back credits only `7 * 10^-10`. -/
theorem LoanBroker.coverClawback_coverDeposit_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some amount) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some amount) = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit r1.amount' = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_coverDeposit_witness

/-- Withdrawals are commutative when nothing rounds: two withdrawals give the same CoverAvailable in
either order. -/
theorem LoanBroker.coverWithdraw_comm (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult)
    -- `a` then `b`
    (h1 : lb.coverWithdraw a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverWithdraw b = .ok (.ok r2))
    -- `b` then `a`
    (h3 : lb.coverWithdraw b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverWithdraw a = .ok (.ok s2))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hxa : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hxb : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - b.toRat)
    (hxab : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - a.toRat - b.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_comm_proof lb a b r1 r2 s1 s2 h1 h2 h3 h4 hca hcb hxa hxb hxab

/-- Witness: a run where all checks pass in both orders and CoverAvailable is different. From a
cover of `10^18`, withdrawing `1000.5` then `1001.25` ends at `999999999999997999`, and the
other order ends at `999999999999997998`. -/
theorem LoanBroker.coverWithdraw_comm_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      r1.loanBroker'.coverWithdraw b = .ok (.ok r2) ∧
      lb.canCoverWithdraw pool b = .ok .tesSUCCESS ∧ lb.coverWithdraw b = .ok (.ok s1) ∧
      s1.loanBroker'.canCoverWithdraw pool a = .ok .tesSUCCESS ∧
      s1.loanBroker'.coverWithdraw a = .ok (.ok s2) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_comm_witness

/-- Clawbacks are commutative when neither is capped and nothing rounds: two clawbacks give the same
CoverAvailable in either order. -/
theorem LoanBroker.coverClawback_comm (lb : LoanBroker) (pool : α) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int) (minimumCover : Number)
    -- `a` then `b`
    (h1 : lb.coverClawback pool (some a) = .ok (.ok r1))
    (h2 : r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2))
    -- `b` then `a`
    (h3 : lb.coverClawback pool (some b) = .ok (.ok s1))
    (h4 : s1.loanBroker'.coverClawback pool (some a) = .ok (.ok s2))
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (ha0 : 0 ≤ a.toRat) (hb0 : 0 ≤ b.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hfit : a.toRat + b.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat)
    (hcan1 : lb.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hcan2 : r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan3 : lb.canCoverClawback pool (some b) = .ok .tesSUCCESS)
    (hcan4 : s1.loanBroker'.canCoverClawback pool (some a) = .ok .tesSUCCESS)
    (hxa : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - a.toRat)
    (hxb : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - b.toRat)
    (hxab : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - a.toRat - b.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_comm_proof lb pool a b r1 r2 s1 s2 e minimumCover h1 h2 h3 h4 hca hcb
    hat hbt ha0 hb0 hza hzb hexp hmin hfit hcan1 hcan2 hcan3 hcan4 hxa hxb hxab

/-- Witness: a run where all checks pass in both orders and CoverAvailable is different. From a
cover of `10^18`, clawing `1000.5` then `1001.25` ends at `999999999999997999`, and the other
order ends at `999999999999997998`. -/
theorem LoanBroker.coverClawback_comm_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult)
      (e : Int) (minimumCover : Number),
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2) ∧
      lb.coverClawback pool (some b) = .ok (.ok s1) ∧
      s1.loanBroker'.coverClawback pool (some a) = .ok (.ok s2) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧
      0 ≤ a.toRat ∧ 0 ≤ b.toRat ∧ a.isZero = false ∧ b.isZero = false ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      a.toRat + b.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat ∧
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      s1.loanBroker'.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_comm_witness

/-- Deposits are commutative when neither changes the cover scale and nothing rounds: two deposits
give the same CoverAvailable in either order. -/
theorem LoanBroker.coverDeposit_comm (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int)
    -- `a` then `b`
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    -- `b` then `a`
    (h3 : lb.coverDeposit b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverDeposit a = .ok (.ok s2))
    -- the cover scale is the same before and after each first deposit
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hs : numberExponent s1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hca : a.ExactCanonical) (hcb : b.ExactCanonical)
    (hx1 : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + r1.amount'.toRat)
    (hx2 : ∃ w : Number, w.isNormalized ∧
      w.toRat = r1.loanBroker'.toExact.coverAvailable + r2.amount'.toRat)
    (hx3 : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + s1.amount'.toRat)
    (hx4 : ∃ w : Number, w.isNormalized ∧
      w.toRat = s1.loanBroker'.toExact.coverAvailable + s2.amount'.toRat) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_comm_proof lb a b r1 r2 s1 s2 e h1 h2 h3 h4 he hr hs hca hcb hx1 hx2 hx3 hx4

/-- Witness: a run where all checks pass in both orders and CoverAvailable is different. Depositing
`10^-14` and `1.3 * 10^-14` onto `9.99999999999999` ends at `10.00000000000001` in one order and at
`10.000000000000013` in the other. -/
theorem LoanBroker.coverDeposit_comm_attained :
    ∃ (lb : LoanBroker) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit b = .ok (.ok s1) ∧ s1.loanBroker'.coverDeposit a = .ok (.ok s2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_comm_witness

end XRPL.Model.Lending
