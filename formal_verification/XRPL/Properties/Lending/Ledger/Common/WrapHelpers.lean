import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Defs
import XRPL.Properties.Lending.Loan.Common.Amortization
import XRPL.Properties.Lending.Loan.Common.SetDefs
import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Vault.Proofs.Support.Wrap

/-! # The lending helpers never wrap around

The interest, amortization and state helpers run the Protocol operations and a few checked fixed-width ones:
the overdue seconds behind a check that the payment is late, a payment count below `2^32`, and the count of
the instalments left after the next one. Only the last needs a hypothesis, a count other than zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

lemma RawLoan.to_lawful_ne_wrap (rl : RawLoan) : rl.to_lawful ≠ .error .wrap := by
  unfold RawLoan.to_lawful
  split <;> simp

lemma RawLoanBroker.to_lawful_ne_wrap (rb : RawLoanBroker) : rb.to_lawful ≠ .error .wrap := by
  unfold RawLoanBroker.to_lawful
  split <;> simp

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | exact XRPL.Model.Lending.RawLoan.WF.originationFee_norm (XRPL.Model.Lending.Loan.wf _)
    | exact XRPL.Model.Lending.RawLoan.WF.serviceFee_norm (XRPL.Model.Lending.Loan.wf _)
    | exact XRPL.Model.Lending.RawLoan.WF.latePaymentFee_norm (XRPL.Model.Lending.Loan.wf _)
    | exact XRPL.Model.Lending.RawLoan.WF.closePaymentFee_norm (XRPL.Model.Lending.Loan.wf _))

lemma secondsInYear_isNormalized : secondsInYear.isNormalized := Number.ofInt64_isNormalized _

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | exact XRPL.Model.Lending.secondsInYear_isNormalized
    | (refine XRPL.Model.Lending.Number.power_isNormalized _ ?_ _ _ (by wrap_hyp); wrap_side))

/-- The binomial series counts its terms in an `Int64`, which holds every count below `2^63`. -/
lemma powerMinusOneLoop_ne_wrap (rate : Number) (n i : Nat) (term sum : Number) (hn : n < 2 ^ 63)
    (hrate : rate.isNormalized) (hterm : term.isNormalized) (hsum : sum.isNormalized) :
    powerMinusOneLoop rate n i term sum ≠ .error .wrap := by
  fun_induction powerMinusOneLoop rate n i term sum with
  | case1 i term sum hi ih =>
    intro h
    simp only [bind, Except.bind, pure, Except.pure, Nat.toInt64Checked_of_lt (show n - i < 2 ^ 63 by omega),
      Nat.toInt64Checked_of_lt (show i + 1 < 2 ^ 63 by omega)] at h
    walk_ok
    all_goals first
      | wrap_leaf
      | (refine ih _ _ ?_ ?_ ‹_› <;> wrap_side)
  | case2 => simp [pure, Except.pure]

lemma powerMinusOneLoop_isNormalized {rate : Number} {n i : Nat} {term sum r : Number} (hrate : rate.isNormalized)
    (hterm : term.isNormalized) (hsum : sum.isNormalized) (h : powerMinusOneLoop rate n i term sum = .ok r) :
    r.isNormalized := by
  fun_induction powerMinusOneLoop rate n i term sum with
  | case1 i term sum hi ih =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    walk_ok
    all_goals first
      | wrap_side
      | (refine ih _ _ ?_ ?_ ‹_› <;> wrap_side)
  | case2 => simp only [pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hsum

lemma computePowerMinusOne_ne_wrap (rate n : Number) (pr : UInt32) (hrate : rate.isNormalized)
    (hn : n.isNormalized) : computePowerMinusOne rate n pr ≠ .error .wrap := by
  intro h
  unfold computePowerMinusOne at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | wrap_leaf
    | (refine powerMinusOneLoop_ne_wrap _ _ _ _ _ ?_ ?_ ?_ ?_ ‹_› <;> first | (have := pr.toNat_lt; omega) | wrap_side)

lemma computePowerMinusOneHybrid_ne_wrap (rate n : Number) (pr : UInt32) (hrate : rate.isNormalized)
    (hn : n.isNormalized) : computePowerMinusOneHybrid rate n pr ≠ .error .wrap := by
  intro h; wrap_leaf

lemma computePaymentFactor_ne_wrap (rate n : Number) (pr : UInt32) (hrate : rate.isNormalized)
    (hn : n.isNormalized) : computePaymentFactor rate n pr ≠ .error .wrap := by
  intro h; wrap_leaf

lemma loanPeriodicPayment_ne_wrap (principal rate : Number) (pr : UInt32) (hrate : rate.isNormalized) :
    loanPeriodicPayment principal rate pr ≠ .error .wrap := by
  intro h; wrap_leaf

lemma loanPrincipalFromPeriodicPayment_ne_wrap (pp rate : Number) (pr : UInt32) (hrate : rate.isNormalized) :
    loanPrincipalFromPeriodicPayment pp rate pr ≠ .error .wrap := by
  intro h; wrap_leaf

lemma loanPrincipalFromPeriodicPayment_isNormalized {pp rate r : Number} {pr : UInt32} (hpp : pp.isNormalized)
    (hrate : rate.isNormalized) (h : loanPrincipalFromPeriodicPayment pp rate pr = .ok r) : r.isNormalized := by
  wrap_side

lemma loanPeriodicRate_ne_wrap (rate : TenthBips32) (interval : UInt32) :
    loanPeriodicRate rate interval ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The overdue seconds are counted only when the payment is late. -/
lemma loanLatePaymentInterest_ne_wrap (po : Number) (rate : TenthBips32) (now due : UInt32) :
    loanLatePaymentInterest po rate now due ≠ .error .wrap := by
  intro h
  unfold loanLatePaymentInterest at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | wrap_leaf
    | exact UInt32.subChecked_ne_wrap (UInt32.le_of_lt (UInt32.not_le.mp ‹_›)) ‹_›

/-- The seconds since the last payment are counted only when time has passed. -/
lemma loanAccruedInterest_ne_wrap (po rate : Number) (now start prev interval : UInt32) :
    loanAccruedInterest po rate now start prev interval ≠ .error .wrap := by
  intro h
  unfold loanAccruedInterest at h
  generalize (if prev < start then start else prev) = last at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | wrap_leaf
    | exact UInt32.subChecked_ne_wrap (UInt32.le_of_lt (UInt32.not_le.mp ‹_›)) ‹_›

lemma computeFullPaymentInterest_ne_wrap (tpo rate : Number) (now interval prev start : UInt32)
    (closeRate : TenthBips32) (htpo : tpo.isNormalized) (hrate : rate.isNormalized) :
    computeFullPaymentInterest tpo rate now interval prev start closeRate ≠ .error .wrap := by
  intro h; wrap_leaf

lemma computeManagementFee_ne_wrap (nt : NumericType) (value : Number) (rate : TenthBips16) (e : Int) :
    computeManagementFee nt value rate e ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The instalments left after the next one are counted only when one is left. -/
lemma computeLoanPropertiesFromPeriodicRate_ne_wrap (principal rate : Number) (pr : UInt32) (mgmt : TenthBips16)
    (nt : NumericType) (minScale : Int) (hpr : pr ≠ 0) (hp : principal.isNormalized) (hrate : rate.isNormalized) :
    computeLoanPropertiesFromPeriodicRate principal rate pr mgmt nt minScale ≠ .error .wrap := by
  intro h
  unfold computeLoanPropertiesFromPeriodicRate at h
  simp only [bind, Except.bind, pure, Except.pure, UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hpr)] at h
  walk_ok
  all_goals wrap_leaf

lemma computeLoanProperties_ne_wrap (principal : Number) (ir : TenthBips32) (interval pr : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (hpr : pr ≠ 0) (hp : principal.isNormalized) :
    computeLoanProperties principal ir interval pr mgmt nt minScale ≠ .error .wrap := by
  intro h; wrap_leaf

/-- Every amount of a loan's derived values is normalized. -/
structure LoanProperties.Normalized (p : LoanProperties) : Prop where
  periodicPayment : p.periodicPayment.isNormalized
  totalValueOutstanding : p.totalValueOutstanding.isNormalized
  managementFeeOutstanding : p.managementFeeOutstanding.isNormalized
  principalOutstanding : p.principalOutstanding.isNormalized
  firstPaymentPrincipal : p.firstPaymentPrincipal.isNormalized

lemma computeLoanPropertiesFromPeriodicRate_normalized {principal rate : Number} {pr : UInt32}
    {mgmt : TenthBips16} {nt : NumericType} {minScale : Int} {p : LoanProperties} (hp : principal.isNormalized)
    (hrate : rate.isNormalized) (h : computeLoanPropertiesFromPeriodicRate principal rate pr mgmt nt minScale = .ok p) :
    p.Normalized := by
  unfold computeLoanPropertiesFromPeriodicRate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

lemma computeLoanProperties_normalized {principal : Number} {ir : TenthBips32} {interval pr : UInt32}
    {mgmt : TenthBips16} {nt : NumericType} {minScale : Int} {p : LoanProperties} (hp : principal.isNormalized)
    (h : computeLoanProperties principal ir interval pr mgmt nt minScale = .ok p) : p.Normalized := by
  wrap_side

lemma LoanState.build_ne_wrap (a b c : Number) (ha : a.isNormalized) (hb : b.isNormalized) (hc : c.isNormalized) :
    LoanState.build a b c ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanState.buildTheoretical_ne_wrap (pp rate : Number) (pr : UInt32) (mgmt : TenthBips16)
    (hpp : pp.isNormalized) (hrate : rate.isNormalized) :
    LoanState.buildTheoretical pp rate pr mgmt ≠ .error .wrap := by
  intro h; wrap_leaf

/-- Every amount of a loan state is normalized. -/
structure LoanState.Normalized (s : LoanState) : Prop where
  valueOutstanding : s.valueOutstanding.isNormalized
  principalOutstanding : s.principalOutstanding.isNormalized
  interestDue : s.interestDue.isNormalized
  managementFeeDue : s.managementFeeDue.isNormalized

/-- Every change between two loan states is normalized. -/
structure LoanStateDeltas.Normalized (d : LoanStateDeltas) : Prop where
  principal : d.principal.isNormalized
  interest : d.interest.isNormalized
  managementFee : d.managementFee.isNormalized

lemma LoanState.build_normalized {a b c : Number} {s : LoanState} (ha : a.isNormalized) (hb : b.isNormalized)
    (hc : c.isNormalized) (h : LoanState.build a b c = .ok s) : s.Normalized := by
  wrap_side

lemma LoanState.buildTheoretical_normalized {pp rate : Number} {pr : UInt32} {mgmt : TenthBips16} {s : LoanState}
    (hpp : pp.isNormalized) (hrate : rate.isNormalized) (h : LoanState.buildTheoretical pp rate pr mgmt = .ok s) :
    s.Normalized := by
  wrap_side

lemma LoanState.calculateDeltas_normalized {x y : LoanState} {d : LoanStateDeltas} (hx : x.Normalized)
    (hy : y.Normalized) (h : LoanState.calculateDeltas x y = .ok d) : d.Normalized := by
  wrap_side

lemma LoanStateDeltas.total_isNormalized {d : LoanStateDeltas} {n : Number} (hd : d.Normalized)
    (h : d.total = .ok n) : n.isNormalized := by
  wrap_side

lemma LoanState.addDeltas_normalized {x s : LoanState} {d : LoanStateDeltas} (hx : x.Normalized)
    (hd : d.Normalized) (h : x.addDeltas d = .ok s) : s.Normalized := by
  wrap_side

lemma LoanStateDeltas.reduceByExcess_normalized {d r : LoanStateDeltas} {e : Number} (hd : d.Normalized)
    (he : e.isNormalized) (h : d.reduceByExcess e = .ok r) : r.Normalized := by
  wrap_side

lemma LoanStateDeltas.nonNegative_normalized {d : LoanStateDeltas} (hd : d.Normalized) :
    d.nonNegative.Normalized := by
  unfold LoanStateDeltas.nonNegative
  wrap_side

lemma LoanState.grossInterestOutstanding_isNormalized {s : LoanState} {n : Number} (hs : s.Normalized)
    (h : s.grossInterestOutstanding = .ok n) : n.isNormalized := by
  wrap_side

lemma Loan.state_normalized {loan : Loan} {s : LoanState} (h : loan.state = .ok s) : s.Normalized := by
  wrap_side

lemma LoanState.calculateDeltas_ne_wrap (x y : LoanState) (hx : x.Normalized) (hy : y.Normalized) :
    LoanState.calculateDeltas x y ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanStateDeltas.total_ne_wrap (d : LoanStateDeltas) (hd : d.Normalized) : d.total ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanState.addDeltas_ne_wrap (x : LoanState) (d : LoanStateDeltas) (hx : x.Normalized) (hd : d.Normalized) :
    x.addDeltas d ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanStateDeltas.reduceByExcess_ne_wrap (d : LoanStateDeltas) (e : Number) (hd : d.Normalized)
    (he : e.isNormalized) : d.reduceByExcess e ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanState.grossInterestOutstanding_ne_wrap (s : LoanState) (hs : s.Normalized) :
    s.grossInterestOutstanding ≠ .error .wrap := by
  intro h; wrap_leaf

macro_rules
  | `(tactic| wrap_rule) => `(tactic| (refine XRPL.Model.Lending.LoanStateDeltas.nonNegative_normalized ?_; wrap_side))

lemma Loan.periodicRate_ne_wrap (loan : Loan) : loan.periodicRate ≠ .error .wrap :=
  loanPeriodicRate_ne_wrap _ _

lemma Loan.state_ne_wrap (loan : Loan) : loan.state ≠ .error .wrap := by
  intro h; wrap_leaf

lemma RawLoanBroker.hasMinimumCover_ne_wrap (rb : RawLoanBroker) (e : Int) :
    rb.hasMinimumCover e ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The schedule check counts the time left before the largest ledger time, and the time for the payments
only when the grace period fits in it. -/
lemma LoanSchedule.checkTimeAvailability_ne_wrap (s : LoanSchedule) :
    s.checkTimeAvailability ≠ .error .wrap := by
  rw [LoanSchedule.checkTimeAvailability_eq]
  split <;> exact nofun

end XRPL.Model.Lending
