import XRPL.Properties.Lending.LoanBroker.Common.DepositForward
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawForward
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackForward
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy

/-! # Proof bodies for cover operations in sequence

On a reachable broker a deposit or withdrawal moves CoverAvailable by its amount floored to whole base units, and a
clawback by its amount capped at the cover and floored. The broker stays reachable, so the steps chain. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- A deposit's credit is a canonical amount of the broker's asset. -/
private lemma LoanBroker.roundedCoverAmount_canonical (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) :
    r.Canonical ∧ r.mNumericType = lb.numericType := by
  obtain ⟨aN, -, hs, hpos⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hok
  have hnz : r.mValue ≠ 0 := by
    intro h0
    have : r.signum = 0 := by simp [STAmount.signum, h0]
    omega
  by_cases hint : lb.numericType.isIntegral = true
  · unfold sumRoundAndSubtract at hs
    rw [if_pos hint] at hs
    simp only [bind_pure] at hs
    obtain ⟨hic, hnt⟩ := STAmount.ofNumber_integral_canonical _ _ _ r hint hs
    exact ⟨hic.canonical (by rw [hnt]; exact hmax hint), hnt⟩
  · have hfr : lb.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    rw [hfr] at hs ⊢
    have hf := sumRoundAndSubtract_frac_fczr _ _ _ _ r hs
    exact ⟨(STAmount.FracCanonZero.canonicalOrZero hf).resolve_right (by simp [STAmount.isZero, hnz]), hf.1⟩

/-- A deposit on a reachable broker keeps it reachable with the same asset and credits a canonical
positive whole number of base units, the amount floored, added to CoverAvailable. -/
lemma LoanBroker.Reachable.coverDeposit_facts (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base ∧ res.loanBroker'.numericType = lb.numericType ∧
      res.amount'.Canonical ∧ res.amount'.mNumericType = lb.numericType ∧ 0 < res.amount'.toRat ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * 10 ^ base) ∧
      res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable + res.amount'.toRat := by
  have hr1 := LoanBroker.Reachable.coverDeposit_step lb base hr v amount res hvb hnt hc hat hpos hcap hcan hok
  subst hvb
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨hrc, hj, hpos', -, hcov⟩ := LoanBroker.coverDeposit_exact lb v amount res hz hnt hc hpos hcan hok
  obtain ⟨hcr, htr⟩ := LoanBroker.roundedCoverAmount_canonical lb v amount _ hmax hrc
  exact ⟨hr1, (LoanBroker.coverDeposit_fixed_fields lb v amount res hok).numericType, hcr, htr, hpos', hj,
    LoanBroker.coverDeposit_floor lb v amount res hz hnt hc hat hpos hcan hok, hcov⟩

/-- A withdrawal on a reachable broker keeps it reachable with the same asset and pays out a canonical
positive whole number of base units, the amount floored, taken from CoverAvailable. -/
lemma LoanBroker.Reachable.coverWithdraw_facts (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base ∧ res.loanBroker'.numericType = lb.numericType ∧
      res.amount'.Canonical ∧ res.amount'.mNumericType = lb.numericType ∧ 0 < res.amount'.toRat ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * 10 ^ base) ∧
      res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - res.amount'.toRat := by
  have hr1 := LoanBroker.Reachable.coverWithdraw_step lb base hr v amount res hvb hnt hc hat hpos hcan hok
  subst hvb
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨hcl, hj, hpos', -, -, hcov⟩ := LoanBroker.coverWithdraw_exact lb v amount res hz hc hpos hcan hok
  obtain ⟨hcz, hrt, -⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ _ _
    (STAmount.CanonicalOrZero.operator_neg (Or.inl hc)) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  refine ⟨hr1, (LoanBroker.coverWithdraw_fixed_fields lb v amount res hok).numericType,
    hcz.resolve_right (by simp [(STAmount.isZero_eq_false_iff_pos _ hpos'.le).2 hpos']), ?_, hpos', hj,
    LoanBroker.coverWithdraw_floor lb v amount res hz hnt hc hat hpos hcan hok, hcov⟩
  rw [hrt, STAmount.operator_neg_mNumericType, hat]

/-- A clawback on a reachable broker keeps it reachable with the same asset and takes a canonical
positive whole number of base units, the request capped at CoverAvailable and floored. -/
lemma LoanBroker.Reachable.coverClawback_facts (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : Option STAmount)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base ∧ res.loanBroker'.numericType = lb.numericType ∧
      res.amount'.Canonical ∧ res.amount'.mNumericType = lb.numericType ∧ 0 < res.amount'.toRat ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * 10 ^ base) ∧
      res.amount'.toRat = (⌊lb.clawTarget 0 amount / 10 ^ base⌋ : ℚ) * 10 ^ base ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - res.amount'.toRat := by
  have hr1 := LoanBroker.Reachable.coverClawback_step lb base hr v amount res hvb hnt hreq hcan hok
  subst hvb
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb _ hr hmax v rfl
  obtain ⟨hrc, hj, hpos', -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz.coverFits hmax hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, _⟩ := LoanBroker.roundedCoverClawback_ok lb v amount _ hrc
  have hcz := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1
  obtain ⟨hrz, hrt, -⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ _ _
    (STAmount.CanonicalOrZero.operator_neg hcz) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hfl := LoanBroker.coverClawback_floor lb v amount res _ hz.coverFits hnt hmax hreq hm hok
  rw [Number.toRat_zero] at hfl
  refine ⟨hr1, (LoanBroker.coverClawback_fixed_fields lb v amount res hok).numericType,
    hrz.resolve_right (by simp [(STAmount.isZero_eq_false_iff_pos _ hpos'.le).2 hpos']), ?_, hpos', hj, hfl, hcov⟩
  rw [hrt, STAmount.operator_neg_mNumericType, STAmount.ofNumber_mNumericType _ _ _ _ hof]

/-- Proof body of the withdrawable part of the deposit then withdrawal line of `LoanBroker.cover_restores`. -/
lemma LoanBroker.coverDeposit_withdrawable_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.canCoverWithdraw v res.amount' = .ok .tesSUCCESS := by
  obtain ⟨hr1, hnt1, hcr, htr, hpos', ⟨j, hj⟩, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  obtain ⟨hz1, hm1⟩ := LoanBroker.Reachable.zone_setup _ base hr1 (by rw [hnt1]; exact hmax) v hvb
  subst hvb
  refine LoanBroker.canCoverWithdraw_of_units _ v _ _ hz1 hcr ⟨j, units_pos hj hpos', hj⟩ hm1 ?_
  rw [Number.toRat_zero, zero_add, hcov]
  linarith [lb.exact.coverAvailable_nonneg]

/-- Proof body of the restore part of the deposit then withdrawal line of `LoanBroker.cover_restores`. -/
lemma LoanBroker.coverDeposit_coverWithdraw_restores_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res))
    (hwd : (res.loanBroker'.coverWithdraw v res.amount').run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  have hcan' := LoanBroker.coverDeposit_withdrawable_proof lb base hr hmax v hvb hnt amount hc hat hpos hcap
    hcan res hok
  obtain ⟨hr1, hnt1, hcr, htr, hpos', ⟨j, hj⟩, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  obtain ⟨-, -, -, -, -, -, hfl, hcov'⟩ := LoanBroker.Reachable.coverWithdraw_facts _ base hr1
    (by rw [hnt1]; exact hmax) v hvb (by rw [hnt1]; exact hnt) _ hcr (by rw [hnt1]; exact htr) hpos' hcan' res' hwd
  rw [floor_units_self _ _ (j : ℤ) (by rw [hj]; norm_cast)] at hfl
  rw [hcov', hfl, hcov]
  ring

/-- Proof body of the clawable part of the deposit then clawback line of `LoanBroker.cover_restores`. -/
lemma LoanBroker.coverDeposit_clawable_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    ∃ claw : STAmount, (res.loanBroker'.roundedCoverClawback v (some res.amount')).run = .ok (.ok claw) ∧
      claw.toRat = res.amount'.toRat ∧ res.loanBroker'.canCoverClawback v (some res.amount') = .ok .tesSUCCESS := by
  obtain ⟨hr1, hnt1, hcr, htr, hpos', ⟨j, hj⟩, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  have hmax1 : res.loanBroker'.numericType.isIntegral = true →
      res.loanBroker'.numericType.maxValue.toNat ≤ maxRep.toNat := by rw [hnt1]; exact hmax
  have hnt' : v.numericType = res.loanBroker'.numericType := by rw [hnt1]; exact hnt
  obtain ⟨hz1, hm1⟩ := LoanBroker.Reachable.zone_setup _ base hr1 hmax1 v hvb
  have hreq1 : ∀ a ∈ some res.amount',
      a.CanonicalOrZero ∧ a.mNumericType = res.loanBroker'.numericType ∧ 0 ≤ a.toRat := by
    intro a ha
    cases ha
    exact ⟨Or.inl hcr, by rw [hnt1]; exact htr, hpos'.le⟩
  have hle : res.amount'.toRat ≤ res.loanBroker'.toExact.coverAvailable := by
    rw [hcov]; linarith [lb.exact.coverAvailable_nonneg]
  subst hvb
  have hcan1 := LoanBroker.canCoverClawback_of_units _ v _ _ hz1 hnt' (by rw [hnt1]; exact hxrp) hmax1 hreq1
    (fun a ha => by cases ha; exact ⟨j, hj⟩) hm1 (by rw [Number.toRat_zero]; linarith)
  obtain ⟨-, res2, -, hok2, -⟩ :=
    LoanBroker.coverClawback_lawful_total_proof _ v _ hz1.coverFits hnt' hmax1 hreq1 hcan1
  obtain ⟨hrc, -⟩ := LoanBroker.coverClawback_exact _ v _ res2 hz1.coverFits hmax1 hok2
  have hfl := LoanBroker.coverClawback_floor _ v _ res2 _ hz1.coverFits hnt' hmax1 hreq1 hm1 hok2
  refine ⟨res2.amount', hrc, ?_, hcan1⟩
  rw [hfl]
  simp only [LoanBroker.clawTarget, (STAmount.isZero_eq_false_iff_pos _ hpos'.le).2 hpos', Bool.false_eq_true,
    if_false, Number.toRat_zero, sub_zero]
  rw [min_eq_left hle]
  exact floor_units_self _ _ (j : ℤ) (by rw [hj]; norm_cast)

/-- Proof body of the restore part of the deposit then clawback line of `LoanBroker.cover_restores`. -/
lemma LoanBroker.coverDeposit_coverClawback_restores_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hxrp : lb.numericType ≠ .native)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res))
    (hclaw : (res.loanBroker'.coverClawback v (some res.amount')).run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, -, -, -, -, -, hcov⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok
  have hmax1 : res.loanBroker'.numericType.isIntegral = true →
      res.loanBroker'.numericType.maxValue.toNat ≤ maxRep.toNat := by rw [hnt1]; exact hmax
  obtain ⟨hz1, -⟩ := LoanBroker.Reachable.zone_setup _ base hr1 hmax1 v hvb
  subst hvb
  obtain ⟨hrc, -, -, -, hcov'⟩ := LoanBroker.coverClawback_exact _ v _ res' hz1.coverFits hmax1 hclaw
  obtain ⟨claw, hrr, hamt, -⟩ :=
    LoanBroker.coverDeposit_clawable_proof lb _ hr hmax v rfl hnt hxrp amount hc hat hpos hcap hcan res hok
  rw [hrc, Except.ok.injEq, Except.ok.injEq] at hrr
  subst hrr
  rw [hcov', hamt, hcov]
  ring

/-- Redepositing a positive whole number of base units that a step took out of a reachable broker
passes the deposit checks, and CoverAvailable is back where it was. -/
private lemma LoanBroker.Reachable.redeposit (lb lb1 : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hr1 : lb1.Reachable base) (hnt1 : lb1.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (r : STAmount)
    (hcr : r.Canonical) (htr : r.mNumericType = lb.numericType) (hpos : 0 < r.toRat)
    (hj : ∃ j : ℕ, r.toRat = (j : ℚ) * 10 ^ base)
    (hcov : lb1.toExact.coverAvailable = lb.toExact.coverAvailable - r.toRat)
    (res' : LoanBrokerCoverResult) (hdep : (lb1.coverDeposit v r).run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  obtain ⟨j, hj⟩ := hj
  have hmax1 : lb1.numericType.isIntegral = true → lb1.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hnt1]; exact hmax
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  obtain ⟨hz1, -⟩ := LoanBroker.Reachable.zone_setup lb1 base hr1 hmax1 v hvb
  have hsum : lb1.toExact.coverAvailable + r.toRat = lb.toExact.coverAvailable := by rw [hcov]; ring
  have hcap1 : lb1.numericType.isIntegral = true →
      lb1.toExact.coverAvailable + r.toRat ≤ lb1.numericType.maxValue.toNat := by
    intro hi
    rw [hsum, hnt1]
    exact LoanBroker.OpenZone.cover_le_maxValue lb _ hz (by rw [← hnt1]; exact hi)
  have hnt' : v.numericType = lb1.numericType := by rw [hnt1]; exact hnt
  have htr' : r.mNumericType = lb1.numericType := by rw [hnt1]; exact htr
  have hcan1 : lb1.canCoverDeposit v r = .ok .tesSUCCESS := by
    subst hvb
    have hoff1 : lb1.numericType.isIntegral = true → (0 : Int) ≤ lb1.numericType.maxOffset := by
      intro hi
      rw [hnt1] at hi ⊢
      exact LoanBroker.OpenZone.maxOffset_nonneg lb _ hz hi
        (by rw [← hsum]; linarith [lb1.exact.coverAvailable_nonneg])
    exact LoanBroker.canCoverDeposit_of_units lb1 v r hz1 hnt' hcr htr' ⟨j, units_pos hj hpos, hj⟩ hcap1 hoff1
      (by rw [hsum]; exact hz.coverLimit)
  obtain ⟨-, -, -, -, -, -, hfl, hcov'⟩ := LoanBroker.Reachable.coverDeposit_facts lb1 base hr1 hmax1 v hvb hnt'
    r hcr htr' hpos hcap1 hcan1 res' hdep
  rw [floor_units_self _ _ (j : ℤ) (by rw [hj]; norm_cast)] at hfl
  rw [hcov', hfl, hsum]

/-- Proof body of the withdrawal then deposit line of `cover_restores`. -/
lemma LoanBroker.coverWithdraw_coverDeposit_restores_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res))
    (hdep : (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, hcr, htr, hpos', hj, -, hcov⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb base hr hmax v hvb hnt amount hc hat hpos hcan res hok
  exact LoanBroker.Reachable.redeposit lb _ base hr hr1 hnt1 hmax v hvb hnt _ hcr htr hpos' hj hcov res' hdep

/-- Proof body of the clawback then deposit line of `cover_restores`. -/
lemma LoanBroker.coverClawback_coverDeposit_restores_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : Option STAmount)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (res res' : LoanBrokerCoverResult) (hok : (lb.coverClawback v amount).run = .ok (.ok res))
    (hdep : (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res')) :
    res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, hcr, htr, hpos', hj, -, hcov⟩ :=
    LoanBroker.Reachable.coverClawback_facts lb base hr hmax v hvb hnt amount hreq hcan res hok
  exact LoanBroker.Reachable.redeposit lb _ base hr hr1 hnt1 hmax v hvb hnt _ hcr htr hpos' hj hcov res' hdep

/-- Proof body of the withdrawal line of `cover_split`. -/
lemma LoanBroker.coverWithdraw_split_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b c : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    (hcan1 : lb.canCoverWithdraw v a = .ok .tesSUCCESS) (h1 : (lb.coverWithdraw v a).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2))
    (hcan3 : lb.canCoverWithdraw v c = .ok .tesSUCCESS) (h3 : (lb.coverWithdraw v c).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  obtain ⟨ka, hka⟩ := hga
  obtain ⟨kb, hkb⟩ := hgb
  obtain ⟨hr1, hnt1, -, -, -, -, hf1, hcov1⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb base hr hmax v hvb hnt a hca hat hpa hcan1 r1 h1
  obtain ⟨-, -, -, -, -, -, hf2, hcov2⟩ := LoanBroker.Reachable.coverWithdraw_facts _ base hr1
    (by rw [hnt1]; exact hmax) v hvb (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb hcan2 r2 h2
  obtain ⟨-, -, -, -, -, -, hf3, hcov3⟩ := LoanBroker.Reachable.coverWithdraw_facts lb base hr hmax v hvb hnt c
    hcc hct (by rw [hsum]; linarith) hcan3 s h3
  rw [floor_units_self _ _ (ka : ℤ) (by rw [hka]; norm_cast)] at hf1
  rw [floor_units_self _ _ (kb : ℤ) (by rw [hkb]; norm_cast)] at hf2
  rw [floor_units_self _ _ ((ka + kb : ℕ) : ℤ) (by rw [hsum, hka, hkb]; push_cast; ring)] at hf3
  rw [hcov2, hcov1, hcov3, hf1, hf2, hf3, hsum]
  ring

/-- Proof body of the deposit line of `cover_split`. -/
lemma LoanBroker.coverDeposit_split_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b c : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    (hcap1 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan1 : lb.canCoverDeposit v a = .ok .tesSUCCESS) (h1 : (lb.coverDeposit v a).run = .ok (.ok r1))
    (hcap2 : lb.numericType.isIntegral = true →
      r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan2 : r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2))
    (hcap3 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan3 : lb.canCoverDeposit v c = .ok .tesSUCCESS) (h3 : (lb.coverDeposit v c).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  obtain ⟨ka, hka⟩ := hga
  obtain ⟨kb, hkb⟩ := hgb
  obtain ⟨hr1, hnt1, -, -, -, -, hf1, hcov1⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt a hca hat hpa hcap1 hcan1 r1 h1
  obtain ⟨-, -, -, -, -, -, hf2, hcov2⟩ := LoanBroker.Reachable.coverDeposit_facts _ base hr1
    (by rw [hnt1]; exact hmax) v hvb (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb
    (by rw [hnt1]; exact hcap2) hcan2 r2 h2
  obtain ⟨-, -, -, -, -, -, hf3, hcov3⟩ := LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt c
    hcc hct (by rw [hsum]; linarith) hcap3 hcan3 s h3
  rw [floor_units_self _ _ (ka : ℤ) (by rw [hka]; norm_cast)] at hf1
  rw [floor_units_self _ _ (kb : ℤ) (by rw [hkb]; norm_cast)] at hf2
  rw [floor_units_self _ _ ((ka + kb : ℕ) : ℤ) (by rw [hsum, hka, hkb]; push_cast; ring)] at hf3
  rw [hcov2, hcov1, hcov3, hf1, hf2, hf3, hsum]
  ring

/-- A clawback of a positive amount on a reachable broker takes the amount floored to whole base
units, capped at CoverAvailable. -/
private lemma LoanBroker.Reachable.clawback_some (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (a : STAmount) (hca : a.Canonical)
    (hat : a.mNumericType = lb.numericType) (hpa : 0 < a.toRat)
    (hcan : lb.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base ∧ res.loanBroker'.numericType = lb.numericType ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable -
        min ((⌊a.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) lb.toExact.coverAvailable := by
  have hreq : ∀ x ∈ some a, x.CanonicalOrZero ∧ x.mNumericType = lb.numericType ∧ 0 ≤ x.toRat := by
    intro x hx
    cases hx
    exact ⟨Or.inl hca, hat, hpa.le⟩
  obtain ⟨hr1, hnt1, -, -, -, -, hfl, hcov⟩ :=
    LoanBroker.Reachable.coverClawback_facts lb base hr hmax v hvb hnt (some a) hreq hcan res hok
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  obtain ⟨-, jc, hjc⟩ := hz.cover
  simp only [LoanBroker.clawTarget, (STAmount.isZero_eq_false_iff_pos _ hpa.le).2 hpa, Bool.false_eq_true, if_false,
    sub_zero] at hfl
  rw [hvb] at hjc
  rw [floor_min_grid a.toRat lb.toExact.coverAvailable base jc hjc] at hfl
  exact ⟨hr1, hnt1, by rw [hcov, hfl]⟩

/-- Proof body of the clawback line of `cover_split`. -/
lemma LoanBroker.coverClawback_split_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (a b c : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical) (hcc : c.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hct : c.mNumericType = lb.numericType) (hpa : 0 < a.toRat) (hpb : 0 < b.toRat)
    (hsum : c.toRat = a.toRat + b.toRat)
    (hga : ∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) (hgb : ∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base)
    (r1 r2 s : LoanBrokerCoverResult)
    (hcan1 : lb.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h1 : (lb.coverClawback v (some a)).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2))
    (hcan3 : lb.canCoverClawback v (some c) = .ok .tesSUCCESS)
    (h3 : (lb.coverClawback v (some c)).run = .ok (.ok s)) :
    r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable := by
  obtain ⟨ka, hka⟩ := hga
  obtain ⟨kb, hkb⟩ := hgb
  obtain ⟨hr1, hnt1, hcov1⟩ :=
    LoanBroker.Reachable.clawback_some lb base hr hmax v hvb hnt a hca hat hpa hcan1 r1 h1
  obtain ⟨-, -, hcov2⟩ := LoanBroker.Reachable.clawback_some _ base hr1 (by rw [hnt1]; exact hmax) v hvb
    (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb hcan2 r2 h2
  obtain ⟨-, -, hcov3⟩ := LoanBroker.Reachable.clawback_some lb base hr hmax v hvb hnt c hcc hct
    (by rw [hsum]; linarith) hcan3 s h3
  rw [floor_units_self _ _ (ka : ℤ) (by rw [hka]; norm_cast)] at hcov1
  rw [floor_units_self _ _ (kb : ℤ) (by rw [hkb]; norm_cast)] at hcov2
  rw [floor_units_self _ _ ((ka + kb : ℕ) : ℤ) (by rw [hsum, hka, hkb]; push_cast; ring)] at hcov3
  rw [hcov2, hcov1, hcov3, hsum, ← min_add_min_sub a.toRat b.toRat _ hpb.le]
  ring

/-- Proof body of the withdrawal line of `cover_comm`. -/
lemma LoanBroker.coverWithdraw_comm_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    (hcan1 : lb.canCoverWithdraw v a = .ok .tesSUCCESS) (h1 : (lb.coverWithdraw v a).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2))
    (hcan3 : lb.canCoverWithdraw v b = .ok .tesSUCCESS) (h3 : (lb.coverWithdraw v b).run = .ok (.ok s1))
    (hcan4 : s1.loanBroker'.canCoverWithdraw v a = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverWithdraw v a).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, -, -, -, -, hf1, hcov1⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb base hr hmax v hvb hnt a hca hat hpa hcan1 r1 h1
  obtain ⟨-, -, -, -, -, -, hf2, hcov2⟩ := LoanBroker.Reachable.coverWithdraw_facts _ base hr1
    (by rw [hnt1]; exact hmax) v hvb (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb hcan2 r2 h2
  obtain ⟨hs1, hnts, -, -, -, -, hf3, hcov3⟩ :=
    LoanBroker.Reachable.coverWithdraw_facts lb base hr hmax v hvb hnt b hcb hbt hpb hcan3 s1 h3
  obtain ⟨-, -, -, -, -, -, hf4, hcov4⟩ := LoanBroker.Reachable.coverWithdraw_facts _ base hs1
    (by rw [hnts]; exact hmax) v hvb (by rw [hnts]; exact hnt) a hca (by rw [hnts]; exact hat) hpa hcan4 s2 h4
  rw [hcov2, hcov1, hcov4, hcov3, hf1, hf2, hf3, hf4]
  ring

/-- Proof body of the deposit line of `cover_comm`. -/
lemma LoanBroker.coverDeposit_comm_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    (hcap1 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan1 : lb.canCoverDeposit v a = .ok .tesSUCCESS) (h1 : (lb.coverDeposit v a).run = .ok (.ok r1))
    (hcap2 : lb.numericType.isIntegral = true →
      r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan2 : r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2))
    (hcap3 : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan3 : lb.canCoverDeposit v b = .ok .tesSUCCESS) (h3 : (lb.coverDeposit v b).run = .ok (.ok s1))
    (hcap4 : lb.numericType.isIntegral = true →
      s1.loanBroker'.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan4 : s1.loanBroker'.canCoverDeposit v a = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverDeposit v a).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, -, -, -, -, hf1, hcov1⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt a hca hat hpa hcap1 hcan1 r1 h1
  obtain ⟨-, -, -, -, -, -, hf2, hcov2⟩ := LoanBroker.Reachable.coverDeposit_facts _ base hr1
    (by rw [hnt1]; exact hmax) v hvb (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb
    (by rw [hnt1]; exact hcap2) hcan2 r2 h2
  obtain ⟨hs1, hnts, -, -, -, -, hf3, hcov3⟩ :=
    LoanBroker.Reachable.coverDeposit_facts lb base hr hmax v hvb hnt b hcb hbt hpb hcap3 hcan3 s1 h3
  obtain ⟨-, -, -, -, -, -, hf4, hcov4⟩ := LoanBroker.Reachable.coverDeposit_facts _ base hs1
    (by rw [hnts]; exact hmax) v hvb (by rw [hnts]; exact hnt) a hca (by rw [hnts]; exact hat) hpa
    (by rw [hnts]; exact hcap4) hcan4 s2 h4
  rw [hcov2, hcov1, hcov4, hcov3, hf1, hf2, hf3, hf4]
  ring

/-- Proof body of the clawback line of `cover_comm`. -/
lemma LoanBroker.coverClawback_comm_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (a b : STAmount) (hca : a.Canonical) (hcb : b.Canonical)
    (hat : a.mNumericType = lb.numericType) (hbt : b.mNumericType = lb.numericType)
    (hpa : 0 < a.toRat) (hpb : 0 < b.toRat) (r1 r2 s1 s2 : LoanBrokerCoverResult)
    (hcan1 : lb.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h1 : (lb.coverClawback v (some a)).run = .ok (.ok r1))
    (hcan2 : r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h2 : (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2))
    (hcan3 : lb.canCoverClawback v (some b) = .ok .tesSUCCESS)
    (h3 : (lb.coverClawback v (some b)).run = .ok (.ok s1))
    (hcan4 : s1.loanBroker'.canCoverClawback v (some a) = .ok .tesSUCCESS)
    (h4 : (s1.loanBroker'.coverClawback v (some a)).run = .ok (.ok s2)) :
    r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable := by
  obtain ⟨hr1, hnt1, hcov1⟩ :=
    LoanBroker.Reachable.clawback_some lb base hr hmax v hvb hnt a hca hat hpa hcan1 r1 h1
  obtain ⟨-, -, hcov2⟩ := LoanBroker.Reachable.clawback_some _ base hr1 (by rw [hnt1]; exact hmax) v hvb
    (by rw [hnt1]; exact hnt) b hcb (by rw [hnt1]; exact hbt) hpb hcan2 r2 h2
  obtain ⟨hs1, hnts, hcov3⟩ :=
    LoanBroker.Reachable.clawback_some lb base hr hmax v hvb hnt b hcb hbt hpb hcan3 s1 h3
  obtain ⟨-, -, hcov4⟩ := LoanBroker.Reachable.clawback_some _ base hs1 (by rw [hnts]; exact hmax) v hvb
    (by rw [hnts]; exact hnt) a hca (by rw [hnts]; exact hat) hpa hcan4 s2 h4
  rw [hcov2, hcov1, hcov4, hcov3]
  have hfa := floor_units_nonneg a.toRat base hpa.le
  have hfb := floor_units_nonneg b.toRat base hpb.le
  have e1 := min_add_min_sub ((⌊a.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base)
    ((⌊b.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) lb.toExact.coverAvailable hfb
  have e2 := min_add_min_sub ((⌊b.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base)
    ((⌊a.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) lb.toExact.coverAvailable hfa
  rw [add_comm ((⌊b.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base)] at e2
  linarith

end XRPL.Model.Lending
