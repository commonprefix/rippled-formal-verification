import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.Common.CoverSequenceProofs

/-! # Cover operations in sequence

`LoanBroker.ReachableFromIn start unit lb n applied requested` follows `n` cover
operations from `start` to `lb`. The cover is the start plus the net amount
moved, and within `n` rounding units of the net amount requested. Undoing an
operation restores the cover only when nothing was rounded, and the order of two
operations can decide whether they pass their checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- Over `n` cover operations whose results fit a `Number`, `coverAvailable` is
the starting cover plus the net amount moved: deposits minus withdrawals minus
clawbacks. -/
theorem LoanBroker.ReachableFromIn.cover_eq (start lb : LoanBroker) (unit : ℚ) (n : ℕ)
    (applied requested : ℚ)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    lb.toExact.coverAvailable = start.toExact.coverAvailable + applied :=
  LoanBroker.ReachableFromIn.cover_eq_proof start unit lb n applied requested hr

/-- Over `n` cover operations, `coverAvailable` is within `n` rounding units of
the starting cover plus the net requested amount. -/
theorem LoanBroker.ReachableFromIn.cover_within (start lb : LoanBroker) (unit : ℚ) (n : ℕ)
    (applied requested : ℚ)
    (hu0 : 0 ≤ unit)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    |lb.toExact.coverAvailable - (start.toExact.coverAvailable + requested)| ≤ n * unit :=
  LoanBroker.ReachableFromIn.cover_within_proof start unit lb n applied requested hu0 hr

/-- Withdrawing the amount a deposit credited restores `coverAvailable`, when the
deposit's sum fits a `Number`. -/
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

/-- The amount a deposit credited can be withdrawn again, when it passes the scale
check at the new `coverAvailable` and `coverAvailable` was at least the minimum cover. -/
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

/-- Witness: the scale-check hypothesis of `coverDeposit_withdrawable` cannot be
dropped. The deposit lifts `coverAvailable` across a power of ten, and the coarser
cover scale rounds the credited amount to zero. -/
theorem LoanBroker.coverDeposit_withdrawable_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverDeposit_withdrawable_witness

/-- The amount a deposit credited is clawed back whole and passes the checks, when
it passes the scale check at the new `coverAvailable` and `coverAvailable` was at least
the minimum cover. -/
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

/-- Witness: the scale-check hypothesis of `coverDeposit_clawable` cannot be
dropped. The deposit lifts `coverAvailable` across a power of ten, and the coarser
cover scale rounds the credited amount to zero. -/
theorem LoanBroker.coverDeposit_clawable_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverClawback pool (some amount) = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverDeposit_clawable_witness

/-- With no debt, clawing back the amount a deposit credited restores
`coverAvailable`, when the deposit's sum fits a `Number`. -/
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

/-- Splitting a clawback into two parts ends at the same `coverAvailable` as one
clawback of their sum, when the sum fits under the cover above the minimum and
every difference fits a `Number`. -/
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

/-- Splitting a withdrawal into two parts ends at the same `coverAvailable` as
withdrawing their sum at once, when every difference fits a `Number`. -/
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

/-- Depositing back the amount a withdrawal paid out restores `coverAvailable`,
when the amount sits on the scale of the cover after the withdrawal and the
withdrawal's difference fits a `Number`. -/
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

/-- Witness: the scale hypothesis of `coverWithdraw_coverDeposit_restores` cannot
be dropped. Withdrawing `7.6 * 10^-10` from `10^6` and depositing it back credits
only `7 * 10^-10`. -/
theorem LoanBroker.coverWithdraw_coverDeposit_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit amount = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_coverDeposit_witness

/-- Depositing back the amount a clawback took restores `coverAvailable`, when
the amount sits on the scale of the cover after the clawback and the clawback's
difference fits a `Number`. -/
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

/-- Witness: the scale hypothesis of `coverClawback_coverDeposit_restores` cannot
be dropped. Clawing `7.6 * 10^-10` from `10^6` and depositing it back credits
only `7 * 10^-10`. -/
theorem LoanBroker.coverClawback_coverDeposit_restores_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some amount) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some amount) = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit r1.amount' = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable :=
  LoanBroker.coverClawback_coverDeposit_witness

/-- Two withdrawals end at the same `coverAvailable` in either order, when every
difference fits a `Number`. -/
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

/-- Witness: `coverWithdraw_comm` needs both orders to pass their checks. From `10^6`,
`5.1 * 10^-10` then `4.9 * 10^-10` both pass, while `4.9 * 10^-10` first rounds to zero
and is rejected. -/
theorem LoanBroker.coverWithdraw_comm_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool a = .ok .tesSUCCESS ∧ lb.coverWithdraw a = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw pool b = .ok .tesSUCCESS ∧
      lb.canCoverWithdraw pool b = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverWithdraw_order_witness

/-- Two clawbacks end at the same `coverAvailable` in either order, when both
requests together fit under the cover above the minimum and every difference
fits a `Number`. -/
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

/-- Witness: `coverClawback_comm` needs both orders to pass their checks. From `10^6`,
`5.1 * 10^-10` then `4.9 * 10^-10` both pass, while `4.9 * 10^-10` first rounds to zero
and is rejected. -/
theorem LoanBroker.coverClawback_comm_attained :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some b) = .ok .tecPRECISION_LOSS :=
  LoanBroker.coverClawback_order_witness

/-- Two deposits take the same amounts in either order when neither order moves
`coverAvailable` to a new scale. -/
theorem LoanBroker.coverDeposit_comm (lb : LoanBroker) (a b : STAmount)
    (r1 r2 s1 s2 : LoanBrokerCoverResult) (e : Int)
    -- `a` then `b`
    (h1 : lb.coverDeposit a = .ok (.ok r1)) (h2 : r1.loanBroker'.coverDeposit b = .ok (.ok r2))
    -- `b` then `a`
    (h3 : lb.coverDeposit b = .ok (.ok s1)) (h4 : s1.loanBroker'.coverDeposit a = .ok (.ok s2))
    -- the cover scale is the same before and after each first deposit
    (he : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hr : numberExponent r1.loanBroker'.coverAvailable lb.numericType = .ok e)
    (hs : numberExponent s1.loanBroker'.coverAvailable lb.numericType = .ok e) :
    r1.amount' = s2.amount' ∧ r2.amount' = s1.amount' :=
  LoanBroker.coverDeposit_comm_proof lb a b r1 r2 s1 s2 e h1 h2 h3 h4 he hr hs

/-- Two deposits end at the same `coverAvailable` in either order when neither
order moves the cover to a new scale and every sum fits a `Number`. -/
theorem LoanBroker.coverDeposit_comm_cover (lb : LoanBroker) (a b : STAmount)
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
  LoanBroker.coverDeposit_comm_cover_proof lb a b r1 r2 s1 s2 e h1 h2 h3 h4 he hr hs hca hcb hx1
    hx2 hx3 hx4

/-- Witness: the same-scale hypotheses of `coverDeposit_comm` cannot be dropped.
Depositing `10^-14` and `1.3 * 10^-14` onto `9.99999999999999` takes
`2 * 10^-14` in one order and `2.3 * 10^-14` in the other. -/
theorem LoanBroker.coverDeposit_comm_attained :
    ∃ (lb : LoanBroker) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit b = .ok (.ok s1) ∧ s1.loanBroker'.coverDeposit a = .ok (.ok s2) ∧
      r1.amount'.toRat + r2.amount'.toRat ≠ s1.amount'.toRat + s2.amount'.toRat :=
  LoanBroker.coverDeposit_comm_witness

end XRPL.Model.Lending
