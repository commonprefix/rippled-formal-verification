import XRPL.Properties.Lending.Loan.Common.ManageProofs

/-! # Proof bodies for the order of impairs and defaults

An impair followed by a default writes the same vault and broker as the default alone: the impair only
parks the principal in LossUnrealized, and the default releases it again. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (loan : Loan) (v : Vault) (now : UInt32)

/-- Proof body of `impair_default_same`. -/
lemma Loan.impair_default_same_proof (r₁ : LoanWithPool Vault) (r₂ r : LoanWithAmounts Vault)
    (himp : loan.isImpaired = false)
    (h₁ : (loan.manageImpair v now).run = .ok (.ok r₁))
    (h₂ : (r₁.loan'.manageDefault r₁.pool').run = .ok (.ok r₂))
    (h : (loan.manageDefault v).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = v.lossUnrealized.toRat + loan.principalOutstanding.toRat) :
    r₂.pool' = r.pool' ∧ r₂.loan'.broker = r.loan'.broker := by
  -- the impair flags the loan and parks the principal in LossUnrealized
  obtain ⟨-, -, -, -, hloan₁⟩ := Loan.manageImpair_ok_parts loan v now r₁ h₁
  obtain ⟨hrec₁, hl₁⟩ := Loan.manageImpair_record loan v now r₁ h₁ haa
  have hf : ∀ f : RawLoan → Prop, f { loan.toRawLoan with isImpaired := true } → f r₁.loan'.toRawLoan :=
    fun f hf => by rw [hloan₁]; exact hf
  have hb : r₁.loan'.broker = loan.broker := hf (·.broker = loan.broker) rfl
  have hpo : r₁.loan'.principalOutstanding = loan.principalOutstanding :=
    hf (·.principalOutstanding = loan.principalOutstanding) rfl
  have himp₁ : r₁.loan'.isImpaired = true := hf (·.isImpaired = true) rfl
  have hi : r₁.loan'.interestDue = loan.interestDue := hf (·.interestDue = loan.interestDue) rfl
  have hv : ∀ f : RawVault → Prop, f { v.toRawVault with lossUnrealized := r₁.pool'.lossUnrealized } →
      f r₁.pool'.toRawVault := fun f hf => by rw [hrec₁]; exact hf
  have haa₁ : r₁.pool'.assetsAvailable = v.assetsAvailable := hv (·.assetsAvailable = v.assetsAvailable) rfl
  have had₁ : r₁.pool'.assetsDeployed = v.assetsDeployed := hv (·.assetsDeployed = v.assetsDeployed) rfl
  have har₁ : r₁.pool'.assetsReserved = v.assetsReserved := hv (·.assetsReserved = v.assetsReserved) rfl
  have hyu₁ : r₁.pool'.yieldUnrealized = v.yieldUnrealized := hv (·.yieldUnrealized = v.yieldUnrealized) rfl
  have hnt₁ : r₁.pool'.numericType = v.numericType := hv (·.numericType = v.numericType) rfl
  have hbe₁ : r₁.pool'.baseExponent = v.baseExponent := by
    unfold Vault.baseExponent
    rw [hnt₁, hv (·.scale = v.scale) rfl]

  -- both defaults compute the same interest and the same cover
  obtain ⟨i₂, d₂, c₂, raw₂, b₂, hi₂, hdc₂, hadj₂, hpool₂, hd₂, hc₂, hb₂, hloan₂, -⟩ :=
    Loan.manageDefault_ok_parts r₁.loan' r₁.pool' r₂ h₂
  obtain ⟨i, d, c, raw, b, hi', hdc, hadj, hpool, hd, hc, hbr, hloan, -⟩ :=
    Loan.manageDefault_ok_parts loan v r h
  rw [hi, hi'] at hi₂
  cases hi₂
  have hcov : r₁.loan'.defaultCover r₁.pool' = loan.defaultCover v := by
    unfold Loan.defaultCover
    rw [hb, hpo, haa₁, hbe₁]
  rw [hcov, hdc] at hdc₂
  have hdceq : r₂.amountToPool = r.amountToPool := (Except.ok.inj hdc₂).symm

  have hbroker : r₂.loan'.broker = r.loan'.broker := by
    have e₂ : r₂.loan'.broker = b₂ := by
      rw [show r₂.loan'.broker = r₂.loan'.toRawLoan.broker from rfl, hloan₂]; rfl
    have e : r.loan'.broker = b := by
      rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]; rfl
    rw [e₂, e]
    apply broker_eq_of_raw
    rw [hb₂, hbr]
    rw [hb, hpo, hd] at hd₂
    rw [hb, hdceq, hc] at hc₂
    cases hd₂
    cases hc₂
    unfold Loan.defaultedBroker
    rw [hb]
  refine ⟨?_, hbroker⟩

  -- the vault takes the same balances, LossUnrealized comes back to where it was
  obtain ⟨j₂, hj₂, hs₂⟩ := Loan.manageDefault_sums r₁.loan' r₁.pool' r₂ h₂
  obtain ⟨j, hj, hs⟩ := Loan.manageDefault_sums loan v r h
  rw [hi, hi'] at hj₂
  rw [hi'] at hj
  cases hj₂
  cases hj
  have eAA : r₂.pool'.assetsAvailable = r.pool'.assetsAvailable := by
    obtain ⟨a₂, ha₂, hr₂⟩ := hs₂.cash
    obtain ⟨a, ha, hr⟩ := hs.cash
    simp only [Loan.defaultChange] at ha₂ ha
    rw [haa₁, hdceq, ha] at ha₂
    cases ha₂
    rw [hnt₁, hr] at hr₂
    exact (Except.ok.inj hr₂).symm
  have eAD : r₂.pool'.assetsDeployed = r.pool'.assetsDeployed := by
    have e₂ := hs₂.deployed
    have e := hs.deployed
    simp only [Loan.defaultChange] at e₂ e
    rw [had₁, hpo, e] at e₂
    exact (Except.ok.inj e₂).symm
  have eAR : r₂.pool'.assetsReserved = r.pool'.assetsReserved := by
    rw [Number.eq_of_add_zero hs₂.reserved, Number.eq_of_add_zero hs.reserved, har₁]
  have eYU : r₂.pool'.yieldUnrealized = r.pool'.yieldUnrealized := by
    have e₂ := hs₂.yield
    have e := hs.yield
    simp only [Loan.defaultChange] at e₂ e
    rw [hyu₁, e] at e₂
    exact (Except.ok.inj e₂).symm
  have eLU : r₂.pool'.lossUnrealized = r.pool'.lossUnrealized := by
    have e₂ := hs₂.loss
    have e := hs.loss
    simp only [Loan.defaultChange, himp₁, himp, Bool.false_eq_true, ↓reduceIte] at e₂ e
    rw [hpo] at e₂
    have hpn := loan.wf.principalOutstanding_norm
    have h1 := Number.operator_add_exact_of_fits v.wf.lossUnrealized_norm hpn hl₁ hexact
    have h2 := Number.operator_sub_exact_of_fits r₁.pool'.wf.lossUnrealized_norm hpn e₂
      ⟨v.lossUnrealized, v.wf.lossUnrealized_norm, by rw [h1]; ring⟩
    rw [Number.eq_of_add_zero e]
    exact Number.isNormalized.toRat_inj r₂.pool'.wf.lossUnrealized_norm v.wf.lossUnrealized_norm
      (by rw [h2, h1]; ring)
  apply vault_eq_of_raw
  rw [Loan.manageDefault_vault_record _ _ r₂ h₂, Loan.manageDefault_vault_record loan v r h, hrec₁, eAA, eAD, eAR, eLU,
    eYU]

end XRPL.Model.Lending
