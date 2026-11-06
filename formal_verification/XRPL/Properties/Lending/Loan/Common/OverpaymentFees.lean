import XRPL.Properties.Lending.Loan.Common.PaidAmounts
import XRPL.Properties.Lending.Loan.Common.PayLedger
import XRPL.Properties.Lending.Loan.Common.PayUnits
import XRPL.Properties.Lending.Loan.Common.OverpaymentDrop

/-! # What the extra part of an overpayment pays the broker

The extra part of an overpayment that isn't dropped charges ⌊OverpaymentFee × extra⌉ and the management fee on its
interest, and feePaid adds both to the fees of the scheduled payments before it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private UnsettledPayment.applyOverpayment Loan.overpaymentComponents Loan.tryOverpayment roundAndSplitInterest
  from XRPL.Model.Lending.Loan.LoanPay
open private tenthBipsOfValue_nonneg computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums

/-- A re-amortization that keeps the extra part pays its two fees. -/
private lemma Loan.tryOverpayment_feePaid (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    opc.managementFeeDelta.operator_add opc.untrackedManagementFee .to_nearest = .ok re.amounts.feePaid := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  assumption

/-- The extra part's fee is ⌊OverpaymentFee × extra⌉, and its management fee is the one on
⌊OverpaymentInterestRate × extra⌉. -/
private lemma Loan.overpaymentComponents_fees (l : Loan) (x : Number) (opc : PaymentComponents)
    (h : Loan.overpaymentComponents l x = .ok opc) :
    ∃ f i i', tenthBipsOfValue x l.rates.overpaymentFee .to_nearest = .ok f ∧
      STAmount.roundToNumericType l.broker.numericType f .to_nearest (some l.loanScale) =
        .ok opc.untrackedManagementFee ∧
      tenthBipsOfValue x l.rates.overpaymentInterestRate .to_nearest = .ok i ∧
      STAmount.roundToNumericType l.broker.numericType i .to_nearest (some l.loanScale) = .ok i' ∧
      computeManagementFee l.broker.numericType i' l.broker.managementFeeRate l.loanScale =
        .ok opc.managementFeeDelta := by
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok opc›)
  obtain ⟨i', h1, h2, -⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ ‹roundAndSplitInterest _ _ _ _ _ = _›
  exact ⟨_, _, i', ‹tenthBipsOfValue x l.rates.overpaymentFee .to_nearest = _›,
    ‹STAmount.roundToNumericType _ _ .to_nearest _ = _›,
    ‹tenthBipsOfValue x l.rates.overpaymentInterestRate .to_nearest = _›, h1, h2⟩

/-- Summing two payments adds their fee parts. -/
private lemma PaymentAmounts.add_fee (a b c : PaymentAmounts) (h : a.add b = .ok c) :
    a.feePaid.operator_add b.feePaid .to_nearest = .ok c.feePaid := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ‹a.feePaid.operator_add b.feePaid .to_nearest = _›

/-- The extra part of an overpayment that isn't dropped adds ⌊OverpaymentFee × extra⌉ and the management fee on its
interest to feePaid, while the fees stay below `2^63` LoanScale units. -/
private lemma UnsettledPayment.applyOverpayment_feePaid (p p' : UnsettledPayment Vault) (amount : Number)
    (hr : -81 ≤ p.loan.loanScale ∧ p.loan.loanScale ≤ 0) (gp : Number.OnGrid p.loan.loanScale p.amounts.feePaid)
    (h : UnsettledPayment.applyOverpayment p amount = .ok p') (hne : p' ≠ p)
    (amount' unspent extra f fee i i' managementFee : Number)
    (hamount : STAmount.roundToNumericType p.loan.broker.numericType amount .towards_zero (some p.loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub p.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType p.loan.broker.numericType
      (Number.min unspent p.loan.totalValueOutstanding) .downward (some p.loan.loanScale) = .ok extra)
    (hf : tenthBipsOfValue extra p.loan.rates.overpaymentFee .to_nearest = .ok f)
    (hfee : STAmount.roundToNumericType p.loan.broker.numericType f .to_nearest (some p.loan.loanScale) = .ok fee)
    (hi : tenthBipsOfValue extra p.loan.rates.overpaymentInterestRate .to_nearest = .ok i)
    (hi' : STAmount.roundToNumericType p.loan.broker.numericType i .to_nearest (some p.loan.loanScale) = .ok i')
    (hmf : computeManagementFee p.loan.broker.numericType i' p.loan.broker.managementFeeRate p.loan.loanScale =
      .ok managementFee)
    (hsum : |p.amounts.feePaid.toRat| + fee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ p.loan.loanScale) :
    p'.amounts.feePaid.toRat = p.amounts.feePaid.toRat + fee.toRat + managementFee.toRat := by
  have hsb := Loan.loanScale_bounds p.loan
  have hs : -81 ≤ p.loan.loanScale ∧ p.loan.loanScale ≤ 80 := ⟨hr.1, by omega⟩
  have hint : p.loan.broker.numericType.isIntegral = true → p.loan.loanScale ≤ 0 := fun _ => hr.2
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first | exact absurd rfl hne | skip
  rename_i _ a' ha' hcond _ un hun _ ov hov hovp _ opc hopc hpd _ _ re hre _ am ham _ l' hl'
  -- the extra amount the overpayment computes is `extra`
  rw [hamount] at ha'
  obtain rfl := Except.ok.inj ha'
  rw [hunspent] at hun
  obtain rfl := Except.ok.inj hun
  rw [hextra] at hov
  obtain rfl := Except.ok.inj hov
  -- its fee and management fee are `fee` and `managementFee`
  obtain ⟨f', i₁, i₁', hf', hfee', hi₁, hi₁', hmf'⟩ := Loan.overpaymentComponents_fees _ _ _ hopc
  rw [hf] at hf'
  obtain rfl := Except.ok.inj hf'
  rw [hfee] at hfee'
  have efee := (Except.ok.inj hfee').symm
  rw [hi] at hi₁
  obtain rfl := Except.ok.inj hi₁
  rw [hi'] at hi₁'
  obtain rfl := Except.ok.inj hi₁'
  rw [hmf] at hmf'
  have emf := (Except.ok.inj hmf').symm
  -- both are whole LoanScale units of at least zero
  have hxn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hextra
  have hx0 : 0 < extra.toRat := by
    have hgt : extra.operator_gt Number.zero = true := by
      revert hovp; cases extra.operator_gt Number.zero <;> simp
    have := (operator_gt_iff _ _ hxn Number.zero_isNormalized).mp hgt
    rwa [Number.toRat_zero] at this
  have hfn := tenthBipsOfValue_normalized hxn hf
  have hf0 := tenthBipsOfValue_nonneg hxn hx0.le hf
  have gfee := STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint hfee
  have hfee0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfn hf0 (Or.inl rfl) hs hfee
  have hin := tenthBipsOfValue_normalized hxn hi
  have hi0 := tenthBipsOfValue_nonneg hxn hx0.le hi
  have hi'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hi'
  have hi'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hin hi0 (Or.inl rfl) hs hi'
  have hrate : p.loan.broker.managementFeeRate.toNat ≤ 10000 := by
    have := p.loan.broker.exact.managementFeeRate_cap
    exact_mod_cast this
  obtain ⟨gmf, hmf0, -⟩ := computeManagementFee_le _ _ _ _ _ hi'n hi'0 hrate hs hint hmf
  -- the re-amortization adds them exactly, and so does the sum with the scheduled payments' fees
  have hre' := Loan.tryOverpayment_feePaid _ _ _ hre
  rw [emf, efee] at hre'
  have hpa := abs_nonneg p.amounts.feePaid.toRat
  have h2 : |managementFee.toRat + fee.toRat| = managementFee.toRat + fee.toRat := abs_of_nonneg (by linarith)
  have vre := Number.OnGrid.add_toRat gmf gfee hsb (by rw [h2]; linarith) hre'
  have gre := Number.OnGrid.add gmf gfee hsb hre'
  have vam := Number.OnGrid.add_toRat gp gre hsb
    (by rw [vre]; exact lt_of_le_of_lt (abs_add_le _ _) (by rw [h2]; linarith))
    (PaymentAmounts.add_fee _ _ _ ham)
  show am.feePaid.toRat = _
  rw [vam, vre]
  ring

/-- Proof body of `Lending.overpayment_fees`. -/
lemma LendingLedger.overpayment_fees_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (payment p : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hp : (loan.payInstalments l.vault .overpayment amount l.now).run = .ok (.ok p))
    (happlied : (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run)
    (amount' unspent extra f fee interest interest' managementFee : Number)
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hf : tenthBipsOfValue extra loan.rates.overpaymentFee .to_nearest = .ok f)
    (hfee : STAmount.roundToNumericType loan.broker.numericType f .to_nearest (some loan.loanScale) = .ok fee)
    (hi : tenthBipsOfValue extra loan.rates.overpaymentInterestRate .to_nearest = .ok interest)
    (hi' : STAmount.roundToNumericType loan.broker.numericType interest .to_nearest (some loan.loanScale) =
      .ok interest')
    (hmf : computeManagementFee loan.broker.numericType interest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee)
    (hsum : |payment.amounts.feePaid.toRat| + fee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale) :
    p.amounts.feePaid.toRat = payment.amounts.feePaid.toRat + fee.toRat + managementFee.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨gs, gl, -⟩ := Loan.Reachable.fees_onGrid hreach
  have hsr := hr.loanScale_range hat
  obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan l.vault amount l.now p hp
  rw [hpay] at h0
  obtain rfl : payment = p0 := Except.ok.inj (Except.ok.inj h0)
  -- an extra part that is dropped leaves the regular payment
  have hne : p ≠ payment := by
    rintro rfl
    refine happlied (h.trans (LendingLedger.apply_regular_of_overpayment h hat
      (Loan.overpayment_of_same_instalments loan l.vault amount l.now fun q hq => ?_)).symm)
    rw [hpay] at hq
    obtain rfl := Except.ok.inj (Except.ok.inj hq)
    exact hp
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now payment hpay
  have gp := Loan.payInstalments_fee_onGrid loan l.vault .regular amount l.now payment hsr gs gl hpay
  have els : payment.loan.loanScale = loan.loanScale := hst.loanScale
  have ebr : payment.loan.broker = loan.broker := hst.broker
  have era : payment.loan.rates = loan.rates := hst.rates
  rw [← els] at gp hsr hsum hamount hextra hfee hi' hmf
  rw [← ebr] at hamount hextra hfee hi' hmf
  rw [← era] at hf hi
  exact UnsettledPayment.applyOverpayment_feePaid payment p amount hsr gp h1 hne amount' unspent extra f fee interest
    interest' managementFee hamount hunspent hextra hf hfee hi hi' hmf hsum

end XRPL.Model.Lending
