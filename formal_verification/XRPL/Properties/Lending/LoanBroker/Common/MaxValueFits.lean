import XRPL.Properties.Lending.LoanBroker.Common.OpenZone

/-! # The asset of a reachable broker with cover fits an `int64` amount

Every broker with cover took a deposit of a canonical amount in its asset, which bounds an integral asset's maximum
by `maxRep`. So every reachable broker with cover has that bound, and every reachable broker is in the Open zone. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- A canonical amount in the broker's asset bounds an integral asset type within `maxRep`. -/
lemma LoanBroker.maxValue_fits_of_canonical (lb : LoanBroker) (a : STAmount) (hc : a.Canonical)
    (hty : a.mNumericType = lb.numericType) :
    lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat := by
  intro hint
  have hai : a.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
  have := (hc.1 hai).2
  rwa [hty] at this

/-- A nonzero canonical-or-zero amount in the broker's asset bounds an integral asset type within
`maxRep`. -/
lemma LoanBroker.maxValue_fits_of_canonicalOrZero (lb : LoanBroker) (a : STAmount) (hcz : a.CanonicalOrZero)
    (hnz : a.isZero = false) (hty : a.mNumericType = lb.numericType) :
    lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat :=
  LoanBroker.maxValue_fits_of_canonical lb a (hcz.resolve_right (by rw [hnz]; exact Bool.false_ne_true)) hty

/-- A clawback from a broker with no debt only succeeds when there is cover: it claws the excess
above the minimum cover, which is zero. -/
lemma LoanBroker.coverClawback_cover_pos (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hdebt : lb.debtTotal = Number.zero)
    (hok : (lb.coverClawback pool amount).run = .ok (.ok res)) : 0 < lb.toExact.coverAvailable := by
  obtain ⟨c, hc, -⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨minimumCover, maxClaw, -, -, hmin, hsub, hpos, -⟩ :=
    LoanBroker.roundedCoverClawback_ok lb pool amount c hc
  rw [hdebt, minimumBrokerCover_zero_debt, Except.ok.injEq] at hmin
  subst hmin
  rw [Number.operator_sub_zero, Except.ok.injEq] at hsub
  subst hsub
  rw [signum_eq _ lb.wf.coverAvailable_norm] at hpos
  show 0 < lb.coverAvailable.toRat
  by_contra h
  rw [if_neg h] at hpos
  split_ifs at hpos <;> omega

/-- Along a broker-only history from an empty broker in the Open zone, the broker stays in the Open
zone, and its asset's integral maximum fits an `int64` amount once it holds any cover. -/
private lemma LoanBroker.ReachableFrom.openZone_maxValue_fits (base : Int) (start lb : LoanBroker)
    (hz : start.OpenZone base) (hcov : start.coverAvailable = Number.zero)
    (hdebt : start.debtTotal = Number.zero) (hr : LoanBroker.ReachableFrom base start lb) :
    lb.OpenZone base ∧
      ((lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∨
        lb.coverAvailable = Number.zero) := by
  induction hr with
  | refl => exact ⟨hz, Or.inr hcov⟩
  | update lb lb' v dm hrf hvb _ hcan hok ih =>
    obtain ⟨hz', hm⟩ := ih
    rw [← hvb] at hz' ⊢
    refine ⟨LoanBroker.update_openZone lb lb' v dm hz' hcan hok, ?_⟩
    rw [LoanBroker.update_eq] at hok
    have hraw := (RawLoanBroker.to_lawful_ok hok).1
    have hnt : lb'.numericType = lb.numericType := by
      show lb'.toRawLoanBroker.numericType = _; rw [hraw]
    have hcv : lb'.coverAvailable = lb.coverAvailable := by
      show lb'.toRawLoanBroker.coverAvailable = _; rw [hraw]
    rw [hnt, hcv]
    exact hm
  | coverDeposit lb v amount res hrf hvb hnt hc hat hpos hcap hcan hok ih =>
    obtain ⟨hz', -⟩ := ih
    rw [← hvb] at hz' ⊢
    refine ⟨LoanBroker.coverDeposit_openZone lb v amount res hz' hnt hc hat hpos hcap hcan hok, Or.inl ?_⟩
    rw [(LoanBroker.coverDeposit_fixed_fields lb v amount res hok).numericType]
    exact LoanBroker.maxValue_fits_of_canonical lb amount hc hat
  | coverWithdraw lb v amount res hrf hvb hnt hc hat hpos hcan hok ih =>
    obtain ⟨hz', -⟩ := ih
    rw [← hvb] at hz' ⊢
    refine ⟨LoanBroker.coverWithdraw_openZone lb v amount res hz' hnt hc hok, Or.inl ?_⟩
    rw [(LoanBroker.coverWithdraw_fixed_fields lb v amount res hok).numericType]
    exact LoanBroker.maxValue_fits_of_canonical lb amount hc hat
  | coverClawback lb v amount res hrf hvb hnt _ _ hok ih =>
    obtain ⟨hz', hm⟩ := ih
    -- the clawback found cover, so the bound already holds
    have hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat := by
      rcases hm with hm | hm
      · exact hm
      · exfalso
        have hd : lb.debtTotal = Number.zero := by
          rw [(LoanBroker.ReachableFrom.fixed_fields base start lb hrf).debtTotal]; exact hdebt
        have h := LoanBroker.coverClawback_cover_pos lb v amount res hd hok
        rw [show lb.toExact.coverAvailable = lb.coverAvailable.toRat from rfl, hm, Number.toRat_zero] at h
        exact lt_irrefl 0 h
    rw [← hvb] at hz' ⊢
    refine ⟨LoanBroker.coverClawback_openZone lb v amount res hz' hnt hmax hok, Or.inl ?_⟩
    rw [(LoanBroker.coverClawback_fixed_fields lb v amount res hok).numericType]
    exact hmax

/-- A reachable broker is in the Open zone of its vault, and its asset's integral maximum fits an
`int64` amount once it holds any cover. -/
private lemma LoanBroker.Reachable.openZone_maxValue_fits (lb : LoanBroker) (base : Int)
    (hr : lb.Reachable base) :
    lb.OpenZone base ∧
      ((lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∨
        lb.coverAvailable = Number.zero) := by
  obtain ⟨v, tx, start, hvb, hcan, hc, hrf⟩ := hr
  obtain ⟨hdebt, hcov, -⟩ := LoanBroker.create_no_exposure_proof tx _ start hc
  have hz := LoanBroker.create_openZone v tx start hcan hc
  rw [hvb] at hz
  exact LoanBroker.ReachableFrom.openZone_maxValue_fits base start lb hz hcov hdebt hrf

/-- Every reachable broker is in the Open zone of its vault. -/
lemma LoanBroker.Reachable.openZone (lb : LoanBroker) (base : Int) (hr : lb.Reachable base) :
    lb.OpenZone base :=
  (LoanBroker.Reachable.openZone_maxValue_fits lb base hr).1

/-- Every reachable broker has an asset whose integral maximum fits an `int64` amount, or no cover. -/
lemma LoanBroker.Reachable.maxValue_fits_or_no_cover (lb : LoanBroker) (base : Int) (hr : lb.Reachable base) :
    (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∨
      lb.coverAvailable = Number.zero :=
  (LoanBroker.Reachable.openZone_maxValue_fits lb base hr).2

/-- A reachable broker with cover has an asset whose integral maximum fits an `int64` amount. The
asset never changes along the history, and the cover came from a deposit of a canonical amount in it. -/
lemma LoanBroker.Reachable.maxValue_fits (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hpos : 0 < lb.toExact.coverAvailable) :
    lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat := by
  rcases LoanBroker.Reachable.maxValue_fits_or_no_cover lb base hr with h | h
  · exact h
  · rw [show lb.toExact.coverAvailable = lb.coverAvailable.toRat from rfl, h, Number.toRat_zero] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- A successful clawback from a reachable broker found cover, so the asset's integral maximum fits
an `int64` amount. -/
lemma LoanBroker.Reachable.coverClawback_maxValue_fits (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (pool : α) (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hok : (lb.coverClawback pool amount).run = .ok (.ok res)) :
    lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat :=
  LoanBroker.Reachable.maxValue_fits lb base hr (LoanBroker.coverClawback_cover_pos lb pool amount res
    (LoanBroker.Reachable.debtTotal_zero_proof lb base hr) hok)

/-- The whole cover of a reachable broker converted to a nonzero amount shows there is cover, so the
asset's integral maximum fits an `int64` amount. -/
lemma LoanBroker.Reachable.cover_amount_maxValue_fits (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (s : STAmount) (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) :
    lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat := by
  have hv := LoanBroker.roundedCoverAvailable_of_exact lb s (LoanBroker.Reachable.openZone lb base hr).coverExact hs
  refine LoanBroker.Reachable.maxValue_fits lb base hr ?_
  rw [← hv]
  exact lt_of_le_of_ne (hv ▸ lb.exact.coverAvailable_nonneg)
    (fun h => hnz ((STAmount.toRat_eq_zero_iff s).mp h.symm))

/-- Proof body of `Reachable.roundedCoverAvailable_exact`. -/
lemma LoanBroker.Reachable.roundedCoverAvailable_exact_proof (lb : LoanBroker) (base : Int)
    (hr : lb.Reachable base) (s : STAmount) (hok : lb.roundedCoverAvailable = .ok s) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.roundedCoverAvailable_of_exact lb s (LoanBroker.Reachable.openZone lb base hr).coverExact hok

end XRPL.Model.Lending
