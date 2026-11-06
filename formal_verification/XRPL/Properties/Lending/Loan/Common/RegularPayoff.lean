import XRPL.Properties.Lending.Loan.Common.InterestDue
import XRPL.Properties.Lending.Loan.Common.InterestMonotone
import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Loan.Common.ReamortizationInterest
import XRPL.Properties.Lending.Loan.Common.RegularInterest

/-! # What the regular payments of a loan pay

Each regular instalment takes whole LoanScale units off the loan and charges its value plus LoanServiceFee. While
the value plus every LoanServiceFee stays below `2^61` units, every running sum is exact. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_outstanding from XRPL.Properties.Lending.Loan.Common.RegularInterest
open private Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue

/-- What one regular instalment moves, read exactly: it charges the value it takes off the loan plus
LoanServiceFee, pays the principal and interest parts to the vault and the fee parts to the broker. -/
structure Loan.InstalmentMoves (l l' : Loan) (fee due : Number) (a : PaymentAmounts) : Prop where
  charge : due.toRat = (l.totalValueOutstanding.toRat - l'.totalValueOutstanding.toRat) + fee.toRat
  principal : a.principalPaid.toRat = l.principalOutstanding.toRat - l'.principalOutstanding.toRat
  interest : a.interestPaid.toRat = (l.totalValueOutstanding.toRat - l'.totalValueOutstanding.toRat) -
    (l.principalOutstanding.toRat - l'.principalOutstanding.toRat) -
    (l.managementFeeOutstanding.toRat - l'.managementFeeOutstanding.toRat)
  feePart : a.feePaid.toRat = (l.managementFeeOutstanding.toRat - l'.managementFeeOutstanding.toRat) + fee.toRat
  value_le : l'.totalValueOutstanding.toRat ≤ l.totalValueOutstanding.toRat
  principal_le : l'.principalOutstanding.toRat ≤ l.principalOutstanding.toRat
  fee_le : l'.managementFeeOutstanding.toRat ≤ l.managementFeeOutstanding.toRat
  fee_le_value : l.managementFeeOutstanding.toRat - l'.managementFeeOutstanding.toRat ≤
    l.totalValueOutstanding.toRat - l'.totalValueOutstanding.toRat
  charge_grid : Number.OnGrid l.loanScale due
  grid_principal : Number.OnGrid l.loanScale a.principalPaid
  grid_interest : Number.OnGrid l.loanScale a.interestPaid
  grid_fee : Number.OnGrid l.loanScale a.feePaid

/-- One regular instalment, read exactly. The fee is on the LoanScale grid and the loan's value plus the fee
stays below `2^62` units. -/
lemma Loan.regularInstalment_moves (l l' : Loan) (pc : PaymentComponents) (fee due : Number) (a : PaymentAmounts)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (gfee : Number.OnGrid l.loanScale fee) (hfee0 : 0 ≤ fee.toRat)
    (hb : l.totalValueOutstanding.toRat + fee.toRat < 2 ^ 62 * 10 ^ l.loanScale)
    (hpc : Loan.scheduledComponents l = .ok pc)
    (hdue : ({ pc with untrackedManagementFee := fee } : PaymentComponents).totalDue = .ok due)
    (hpa : ({ pc with untrackedManagementFee := fee } : PaymentComponents).paidAmounts = .ok a)
    (hdo : Loan.doPayment l { pc with untrackedManagementFee := fee } = .ok l') :
    Loan.InstalmentMoves l l' fee due a := by
  have hs := Loan.loanScale_bounds l
  have hp : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  have h62 : (2 : ℚ) ^ 62 * 10 ^ l.loanScale < 2 ^ 63 * 10 ^ l.loanScale := by nlinarith
  obtain ⟨gT, gP, gM, -, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hiD : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
    hi
  obtain ⟨hui, hfin⟩ := Loan.scheduledComponents_shape l pc hpc
  obtain ⟨vap, id, e1, e2, e3, e4, e5⟩ := PaymentComponents.paidAmounts_ok_inv _ a hpa
  simp only at e1 e2 e3 e4 e5
  rw [hui, Number.operator_add_zero_right, Except.ok.injEq] at e3
  subst e3
  unfold PaymentComponents.totalDue at hdue
  obtain ⟨v1, hv1, hdue⟩ := bind_ok_peel _ _ _ hdue
  simp only at hv1 hdue
  rw [hui, Number.operator_add_zero_right, Except.ok.injEq] at hv1
  subst hv1
  obtain ⟨hfz, hnf⟩ := Loan.doPayment_outstanding l l' _ hdo
  -- the value, principal and fee deltas: everything the loan owes, or the tracked deltas
  obtain ⟨gtv, gpd, gmd, tv0, tv1, pd0, pd1, md0, md1, mtv, vT, vP, vM⟩ :
      Number.OnGrid l.loanScale pc.totalValueDelta ∧ Number.OnGrid l.loanScale pc.principalDelta ∧
      Number.OnGrid l.loanScale pc.managementFeeDelta ∧ 0 ≤ pc.totalValueDelta.toRat ∧
      pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat ∧ 0 ≤ pc.principalDelta.toRat ∧
      pc.principalDelta.toRat ≤ l.principalOutstanding.toRat ∧ 0 ≤ pc.managementFeeDelta.toRat ∧
      pc.managementFeeDelta.toRat ≤ l.managementFeeOutstanding.toRat ∧
      pc.managementFeeDelta.toRat ≤ pc.totalValueDelta.toRat ∧
      l'.totalValueOutstanding.toRat = l.totalValueOutstanding.toRat - pc.totalValueDelta.toRat ∧
      l'.principalOutstanding.toRat = l.principalOutstanding.toRat - pc.principalDelta.toRat ∧
      l'.managementFeeOutstanding.toRat = l.managementFeeOutstanding.toRat - pc.managementFeeDelta.toRat := by
    rcases Loan.scheduledComponents_tracked l pc hlo hint hi hpc with hf | ⟨hf, ht⟩
    · obtain ⟨f1, f2, f3⟩ := hfin hf
      obtain ⟨z1, z2, z3⟩ := hfz hf
      rw [f1, f2, f3, z1, z2, z3, Number.toRat_zero]
      exact ⟨gT, gP, gM, hT0, le_refl _, hP0, le_refl _, hM0, le_refl _, by linarith, by ring, by ring, by ring⟩
    · obtain ⟨d1, d2, d3⟩ := hnf hf
      obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, -, hmv⟩ := ht
      have hTb : l.totalValueOutstanding.toRat < 2 ^ 63 * 10 ^ l.loanScale := by linarith
      exact ⟨gtv, gpd, gmd, tv0, tv1, pd0, pd1, md0, md1, hmv,
        Number.OnGrid.sub_exact gT gtv tv0 tv1 hTb hs d1,
        Number.OnGrid.sub_exact gP gpd pd0 pd1 (by linarith) hs d2,
        Number.OnGrid.sub_exact gM gmd md0 md1 (by linarith) hs d3⟩
  have vdue := Number.OnGrid.add_exact gtv gfee tv0 hfee0 (by linarith) hs hdue
  have vvap := Number.OnGrid.sub_toRat gtv gpd hs (by rw [abs_lt]; constructor <;> linarith) e1
  have gvap := Number.OnGrid.sub gtv gpd hs e1
  have vid := Number.OnGrid.sub_toRat gvap gmd hs (by rw [vvap, abs_lt]; constructor <;> linarith) e2
  have gid := Number.OnGrid.sub gvap gmd hs e2
  have vfp := Number.OnGrid.add_exact gmd gfee md0 hfee0 (by linarith) hs e4
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith, by linarith, by linarith, Number.OnGrid.add gtv gfee hs hdue,
    by rw [e5]; exact gpd, gid, Number.OnGrid.add gmd gfee hs e4⟩
  · rw [vdue, vT]; ring
  · rw [e5, vP]; ring
  · rw [vid, vvap, vT, vP, vM]; ring
  · rw [vfp, vM]; ring

/-- The sums of the instalments a payment paid so far, against the loan it started from, which owed `T0` of value,
`P0` of principal and `M0` of management fee. `B` bounds the value plus LoanServiceFee for every payment. -/
structure UnsettledPayment.Moves {α : Type} (p : UnsettledPayment α) (s : Int) (nt : NumericType) (fee : Number)
    (T0 P0 M0 B : ℚ) : Prop where
  loanScale : p.loan.loanScale = s
  numericType : p.loan.broker.numericType = nt
  serviceFee : p.loan.fees.serviceFee = fee
  interest_nonneg : 0 ≤ p.loan.toExact.interestDue
  charged : p.totalPaid.toRat = (T0 - p.loan.totalValueOutstanding.toRat) + fee.toRat * p.count
  principal : p.amounts.principalPaid.toRat = P0 - p.loan.principalOutstanding.toRat
  interest : p.amounts.interestPaid.toRat = (T0 - p.loan.totalValueOutstanding.toRat) -
    (P0 - p.loan.principalOutstanding.toRat) - (M0 - p.loan.managementFeeOutstanding.toRat)
  feePart : p.amounts.feePaid.toRat = (M0 - p.loan.managementFeeOutstanding.toRat) + fee.toRat * p.count
  value_le : p.loan.totalValueOutstanding.toRat ≤ T0
  principal_le : p.loan.principalOutstanding.toRat ≤ P0
  mgmt_le : p.loan.managementFeeOutstanding.toRat ≤ M0
  bound : T0 + fee.toRat * (p.count + p.loan.paymentRemaining.toNat) ≤ B
  charged_grid : Number.OnGrid s p.totalPaid
  principal_grid : Number.OnGrid s p.amounts.principalPaid
  interest_grid : Number.OnGrid s p.amounts.interestPaid
  fee_grid : Number.OnGrid s p.amounts.feePaid

/-- Summing two payment amounts sums each part. -/
private lemma PaymentAmounts.add_parts (a b c : PaymentAmounts) (h : a.add b = .ok c) :
    a.principalPaid.operator_add b.principalPaid .to_nearest = .ok c.principalPaid ∧
      a.interestPaid.operator_add b.interestPaid .to_nearest = .ok c.interestPaid ∧
      a.feePaid.operator_add b.feePaid .to_nearest = .ok c.feePaid := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ⟨‹_›, ‹_›, ‹_›⟩

/-- One more regular instalment keeps the sums exact. -/
private lemma UnsettledPayment.Moves.step {α : Type} {p : UnsettledPayment α} {s : Int} {nt : NumericType}
    {fee : Number} {T0 P0 M0 B : ℚ} (hm : p.Moves s nt fee T0 P0 M0 B) (hlo : -81 ≤ s)
    (hnt : nt.isIntegral = true → s ≤ 0)
    (gfee : Number.OnGrid s fee) (hfee0 : 0 ≤ fee.toRat) (hB : B < 2 ^ 61 * 10 ^ s) (hPT : P0 ≤ T0)
    (hMT : M0 ≤ T0) (hpr : p.loan.paymentRemaining ≠ 0)
    {pc : PaymentComponents} {due tp : Number} {inst amounts' : PaymentAmounts} {loan' : Loan}
    (hpc : Loan.scheduledComponents p.loan = .ok pc)
    (hdue : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).totalDue = .ok due)
    (hpa : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).paidAmounts = .ok inst)
    (hdo : Loan.doPayment p.loan { pc with untrackedManagementFee := p.loan.fees.serviceFee } = .ok loan')
    (hadd : p.amounts.add inst = .ok amounts') (htp : p.totalPaid.operator_add due .to_nearest = .ok tp) :
    ({ p with loan := loan', amounts := amounts', totalPaid := tp, count := p.count + 1 } :
      UnsettledPayment α).Moves s nt fee T0 P0 M0 B ∧
      (pc.isFinal = true → loan'.paymentRemaining = 0) ∧
      (pc.isFinal = false → loan'.paymentRemaining = p.loan.paymentRemaining - 1) := by
  have hls := hm.loanScale
  have hsb : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by rw [← hls]; exact Loan.loanScale_bounds p.loan
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hfee := hm.serviceFee
  rw [hfee] at hdue hpa hdo
  have hint : p.loan.broker.numericType.isIntegral = true → p.loan.loanScale ≤ 0 := fun h => by
    rw [hls]; exact hnt (by rw [← hm.numericType]; exact h)
  have hpos : 1 ≤ p.loan.paymentRemaining.toNat := by
    have := UInt32.toNat_inj.not.mpr hpr
    simp at this; omega
  -- the counts as rationals: `f c` is LoanServiceFee charged so far, `f rr` what the payments left would charge
  set c : ℚ := (p.count : ℚ) with hc
  set rr : ℚ := (p.loan.paymentRemaining.toNat : ℚ) with hrr
  set f : ℚ := fee.toRat with hf
  have hc0 : 0 ≤ c := by positivity
  have hr1 : 1 ≤ rr := by rw [hrr]; exact_mod_cast hpos
  have hfc0 : 0 ≤ f * c := mul_nonneg hfee0 hc0
  have hfr : f ≤ f * rr := by nlinarith
  have hbnd : T0 + f * c + f * rr ≤ B := by have := hm.bound; rw [← hc, ← hrr] at this; linarith [mul_add f c rr]
  have hT := hm.value_le
  have hP := hm.principal_le
  have hM := hm.mgmt_le
  have hTb : p.loan.totalValueOutstanding.toRat + fee.toRat < 2 ^ 62 * 10 ^ p.loan.loanScale := by
    rw [hls]
    have : (2 : ℚ) ^ 61 * 10 ^ s ≤ 2 ^ 62 * 10 ^ s := by nlinarith
    have hT0 : 0 ≤ T0 := le_trans p.loan.exact.totalValueOutstanding_nonneg hT
    linarith
  have hmv := Loan.regularInstalment_moves p.loan loan' pc fee due inst (by rw [hls]; exact hlo) hint
    hm.interest_nonneg (by rw [hls]; exact gfee) hfee0 hTb hpc hdue hpa hdo
  have gdue := hmv.charge_grid
  have gpp := hmv.grid_principal
  have gip := hmv.grid_interest
  have gfp := hmv.grid_fee
  rw [hls] at gdue gpp gip gfp
  have hkt := Loan.doPayment_keepsTerms _ _ _ hdo
  have hst := Loan.doPayment_sameTerms _ _ _ hdo
  obtain ⟨a1, a2, a3⟩ := PaymentAmounts.add_parts _ _ _ hadd
  obtain ⟨-, -, -, -, hP', hM', -⟩ := Loan.outstanding_grid loan'
  have hT' : 0 ≤ loan'.totalValueOutstanding.toRat := loan'.exact.totalValueOutstanding_nonneg
  have h63 : (2 : ℚ) ^ 61 * 10 ^ s * 4 ≤ 2 ^ 63 * 10 ^ s := by nlinarith
  have hB0 : B < 2 ^ 63 * 10 ^ s := by nlinarith
  have hT0 : 0 ≤ T0 := le_trans p.loan.exact.totalValueOutstanding_nonneg hT
  have hTv := hmv.value_le
  have hPv := hmv.principal_le
  have hMv := hmv.fee_le
  have vtp := Number.OnGrid.add_toRat hm.charged_grid gdue hsb (by
    rw [hm.charged, hmv.charge, abs_lt]; constructor <;> linarith) htp
  have vpp := Number.OnGrid.add_toRat hm.principal_grid gpp hsb (by
    rw [hm.principal, hmv.principal, abs_lt]; constructor <;> linarith) a1
  have vip := Number.OnGrid.add_toRat hm.interest_grid gip hsb (by
    rw [hm.interest, hmv.interest, abs_lt]; constructor <;> linarith) a2
  have vfp := Number.OnGrid.add_toRat hm.fee_grid gfp hsb (by
    rw [hm.feePart, hmv.feePart, abs_lt]; constructor <;> linarith) a3
  have hi' : 0 ≤ loan'.toExact.interestDue := by
    refine Loan.doPayment_interestDue _ _ _ hm.interest_nonneg ?_ hdo
    rcases Loan.scheduledComponents_tracked p.loan pc (by rw [hls]; exact hlo) hint hm.interest_nonneg hpc with
      hf | ⟨hf, ht⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hf, ht.totalValue_grid, ht.principal_grid, ht.managementFee_grid, ht.totalValue_range,
        ht.principal_range, ht.managementFee_range, ht.interest_le, ht.managementFee_le_value⟩
  have hfin : pc.isFinal = true → loan'.paymentRemaining = 0 := fun hf => Loan.doPayment_final _ _ _ hf hdo
  have hnf : pc.isFinal = false → loan'.paymentRemaining = p.loan.paymentRemaining - 1 :=
    fun hf => (Loan.doPayment_notFinal _ _ _ hf hdo).1
  have hcount : ((p.count + 1 : ℕ) : ℚ) + loan'.paymentRemaining.toNat ≤ c + rr := by
    have : p.count + 1 + loan'.paymentRemaining.toNat ≤ p.count + p.loan.paymentRemaining.toNat := by
      cases hf : pc.isFinal
      · rw [hnf hf, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hpos)]
        simp; omega
      · rw [hfin hf]; simp; omega
    rw [hc, hrr]
    exact_mod_cast this
  refine ⟨⟨by rw [hkt.loanScale, hls], by rw [hst.broker]; exact hm.numericType, by rw [hkt.fees, hfee], hi',
    ?_, ?_, ?_, ?_, by linarith [hmv.value_le], by linarith [hmv.principal_le, hm.principal_le],
    by linarith [hmv.fee_le, hm.mgmt_le], ?_, Number.OnGrid.add hm.charged_grid gdue hsb htp,
    Number.OnGrid.add hm.principal_grid gpp hsb a1,
    Number.OnGrid.add hm.interest_grid gip hsb a2,
    Number.OnGrid.add hm.fee_grid gfp hsb a3⟩, hfin, hnf⟩
  · show tp.toRat = _
    rw [vtp, hm.charged, hmv.charge]; push_cast; ring
  · show amounts'.principalPaid.toRat = _
    rw [vpp, hm.principal, hmv.principal]; ring
  · show amounts'.interestPaid.toRat = _
    rw [vip, hm.interest, hmv.interest]; ring
  · show amounts'.feePaid.toRat = _
    rw [vfp, hm.feePart, hmv.feePart]; push_cast; ring
  · show T0 + fee.toRat * (((p.count + 1 : ℕ) : ℚ) + loan'.paymentRemaining.toNat) ≤ B
    have := mul_le_mul_of_nonneg_left hcount hfee0
    linarith [mul_add f c rr]

/-- The regular instalments of a payment keep the sums exact. -/
lemma UnsettledPayment.payInstalments_moves {α : Type} (amount : Number) (s : Int) (nt : NumericType)
    (fee : Number) (T0 P0 M0 B : ℚ) (hlo : -81 ≤ s) (hnt : nt.isIntegral = true → s ≤ 0)
    (gfee : Number.OnGrid s fee) (hfee0 : 0 ≤ fee.toRat)
    (hB : B < 2 ^ 61 * 10 ^ s) (hPT : P0 ≤ T0) (hMT : M0 ≤ T0) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.Moves s nt fee T0 P0 M0 B → p.Moves s nt fee T0 P0 M0 B := by
  intro n
  induction n with
  | zero =>
    intro payment p h hm
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hm
  | succ k ih =>
    intro payment p h hm
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | exact hm
      | (have hpr : payment.loan.paymentRemaining ≠ 0 := by
           simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
         have hstep := hm.step hlo hnt gfee hfee0 hB hPT hMT hpr ‹Loan.scheduledComponents payment.loan = _›
           ‹PaymentComponents.totalDue _ = _› ‹PaymentComponents.paidAmounts _ = _› ‹Loan.doPayment _ _ = _›
           ‹PaymentAmounts.add _ _ = _› ‹payment.totalPaid.operator_add _ _ = _›
         first
           | exact hstep.1
           | exact ih _ _ ‹UnsettledPayment.payInstalments _ k amount = _› hstep.1)

end XRPL.Model.Lending
