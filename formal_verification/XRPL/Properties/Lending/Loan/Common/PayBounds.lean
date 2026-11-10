import XRPL.Properties.Lending.Loan.Common.PayMonotone
import XRPL.Properties.Lending.Loan.Common.ManageCoverBase

/-! # Proof bodies for the LoanPay overpayment and settlement bounds

The extra amount of an overpayment, and what the settlement credits the vault and the broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.payScheduledInstalments
  UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments Loan.overpaymentComponents Loan.tryOverpayment
  Loan.settlePayment Loan.unimpairIfImpaired Loan.doPayment roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)

/-- An overpayment pays the scheduled instalments of a regular payment, then its extra amount. -/
private lemma Loan.overPayInstalments_run :
    (loan.payInstalments v .overpayment amount now).run =
      (match (loan.payInstalments v .regular amount now).run with
       | .error e => .error e
       | .ok (.error t) => .ok (.error t)
       | .ok (.ok p) => (UnsettledPayment.applyOverpayment p amount).map Except.ok) := by
  simp only [Loan.payInstalments]
  unfold_ter
  rcases Loan.payScheduledInstalments loan v amount now with e | t | p <;> rfl

/-- An overpayment whose instalments are those of the regular payment is the regular payment. -/
lemma Loan.overpayment_of_same_instalments
    (hdrop : ∀ payment, (loan.payInstalments v .regular amount now).run = .ok (.ok payment) →
      (loan.payInstalments v .overpayment amount now).run = .ok (.ok payment)) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run := by
  have hsame : loan.payInstalments v .overpayment amount now = loan.payInstalments v .regular amount now := by
    show (loan.payInstalments v .overpayment amount now).run = (loan.payInstalments v .regular amount now).run
    rcases h : (loan.payInstalments v .regular amount now).run with e | t | p
    · rw [Loan.overPayInstalments_run, h]
    · rw [Loan.overPayInstalments_run, h]
    · exact hdrop p h
  have e₁ := Loan.pay_run loan v .overpayment amount now
  have e₂ := Loan.pay_run loan v .regular amount now
  simp only [Loan.pay] at e₁ e₂
  rw [e₁, e₂, hsame]

/-- A rounded value clamped into `[0, cap]` is at most `cap`. -/
private lemma roundAndClamp_le_cap (value cap : Number) (mode : rounding_mode) (nt : NumericType) (s : Int)
    (y : Number) (hcap : cap.isNormalized) (hcap0 : 0 ≤ cap.toRat) (h : roundAndClamp value cap mode nt s = .ok y) :
    y.toRat ≤ cap.toRat := by
  unfold roundAndClamp at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain rfl := (Except.ok.inj h).symm
    have hrn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hr
    unfold Number.clamp
    split_ifs with h1 h2
    · rw [Number.toRat_zero]; exact hcap0
    · exact le_refl _
    · exact (operator_lt_eq_false_iff _ _ hcap hrn).mp (by simpa using h2)

private lemma LoanState.build_eq (a b c : Number) (st : LoanState) (h : LoanState.build a b c = .ok st) :
    st.valueOutstanding = a ∧ st.principalOutstanding = b ∧ st.managementFeeDue = c ∧
      LoanState.build st.valueOutstanding st.principalOutstanding st.managementFeeDue = .ok st := by
  have h' := h
  unfold LoanState.build at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok st›)
  exact ⟨rfl, rfl, rfl, h'⟩

/-- A re-amortization that passes lowers PrincipalOutstanding and doesn't raise interestDue or
ManagementFeeOutstanding. Its new state is built from its three amounts. -/
private lemma Loan.tryOverpayment_lowers (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    ∃ state deltas, l.state = .ok state ∧ state.calculateDeltas re.state = .ok deltas ∧
      state.principalOutstanding.operator_le re.state.principalOutstanding = false ∧
      deltas.interest.operator_neg.operator_gt Number.zero = false ∧
      re.state.managementFeeDue.toRat ≤ state.managementFeeDue.toRat ∧
      LoanState.build re.state.valueOutstanding re.state.principalOutstanding re.state.managementFeeDue =
        .ok re.state := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  obtain ⟨-, b2, b3, b4⟩ := LoanState.build_eq _ _ _ _ ‹LoanState.build _ _ _ = Except.ok _›
  have hs := ‹l.state = Except.ok _›
  unfold Loan.state at hs
  obtain ⟨-, -, hm, -⟩ := LoanState.build_eq _ _ _ _ hs
  refine ⟨_, _, ‹l.state = _›, ‹_›, ?_, Bool.eq_false_iff.mpr ‹_›, ?_, b4⟩
  · simp only
    rw [b2]
    exact Bool.eq_false_iff.mpr ‹_›
  · simp only
    have h6 := ‹roundAndClamp _ _ rounding_mode.to_nearest _ _ = _›
    rw [hm] at h6
    rw [b3, hm]
    exact roundAndClamp_le_cap _ _ _ _ _ _ l.wf.managementFeeOutstanding_norm
      ((l.exact.managementFeeOutstanding_nonneg : 0 ≤ l.managementFeeOutstanding.toRat)) h6


private lemma LoanState.calculateDeltas_interest (x y : LoanState) (d : LoanStateDeltas)
    (h : x.calculateDeltas y = .ok d) : x.interestDue.operator_sub y.interestDue .to_nearest = .ok d.interest := by
  unfold LoanState.calculateDeltas at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok d›)
  exact ‹x.interestDue.operator_sub y.interestDue .to_nearest = _›

/-- The loan a re-amortized raw loan becomes reads back the state it was built from. -/
private lemma Loan.state_of_build (l : Loan) (st : LoanState)
    (h : LoanState.build l.totalValueOutstanding l.principalOutstanding l.managementFeeOutstanding = .ok st) :
    l.state = .ok st := h

/-- The extra amount of an overpayment that isn't dropped lowers PrincipalOutstanding and
TotalValueOutstanding. -/
private lemma UnsettledPayment.applyOverpayment_lowers (p p' : UnsettledPayment Vault) (amount : Number)
    (h : UnsettledPayment.applyOverpayment p amount = .ok p') (hne : p' ≠ p) :
    p'.loan.principalOutstanding.toRat < p.loan.principalOutstanding.toRat ∧
      p'.loan.totalValueOutstanding.toRat < p.loan.totalValueOutstanding.toRat := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first | exact absurd rfl hne | skip
  obtain ⟨state, deltas, hst, hd, hpo, hint, hmf, hb⟩ :=
    Loan.tryOverpayment_lowers _ _ _ ‹Loan.tryOverpayment _ _ = _›
  rename_i re _ _ _ _ _ l' hl'
  have h1 := (RawLoan.to_lawful_ok hl').1
  have e1 : l'.totalValueOutstanding = re.state.valueOutstanding := (congrArg RawLoan.totalValueOutstanding h1 :)
  have e2 : l'.principalOutstanding = re.state.principalOutstanding := (congrArg RawLoan.principalOutstanding h1 :)
  have e3 : l'.managementFeeOutstanding = re.state.managementFeeDue :=
    (congrArg RawLoan.managementFeeOutstanding h1 :)
  have e4 : l'.loanScale = p.loan.loanScale := (congrArg RawLoan.loanScale h1 :)
  have hst' : l'.state = .ok re.state := by
    apply Loan.state_of_build
    rw [e1, e2, e3]
    exact hb
  obtain ⟨t, pr, m, -, -, -, ht, hp, hm, hi, -, hsv, hsp, hsm⟩ := Loan.state_units p.loan state hst
  obtain ⟨t', pr', m', -, -, -, ht', hp', hm', hi', -, hsv', hsp', hsm'⟩ := Loan.state_units l' re.state hst'
  rw [e4] at ht' hp' hm' hi'
  have hs := Loan.loanScale_bounds p.loan
  have hpos : (0 : ℚ) < 10 ^ p.loan.loanScale := zpow_pos (by norm_num) _
  have hlt : pr' < pr := by
    have hn1 := hp.norm
    have hn2 := hp'.norm
    unfold Number.operator_le at hpo
    simp only [Bool.not_eq_false'] at hpo
    have := (operator_lt_iff _ _ hn2 hn1).mp hpo
    rw [hp.val, hp'.val] at this
    exact_mod_cast lt_of_mul_lt_mul_right this hpos.le
  have hle : m' ≤ m := by
    rw [hm.val, hm'.val] at hmf
    exact_mod_cast le_of_mul_le_mul_right hmf hpos
  have hid : (t' : ℤ) - pr' - m' ≤ (t : ℤ) - pr - m := by
    by_contra hcon
    have hR := operator_sub_rounded_to_nearest _ _ _ hi.norm hi'.norm (LoanState.calculateDeltas_interest _ _ _ hd)
    have hq : state.interestDue.toRat - re.state.interestDue.toRat ≤ -(10 : ℚ) ^ p.loan.loanScale := by
      rw [hi.val, hi'.val]
      have : (((t : ℤ) - pr - m : ℤ) : ℚ) - (((t' : ℤ) - pr' - m' : ℤ) : ℚ) ≤ -1 := by
        have : ((t : ℤ) - pr - m) - ((t' : ℤ) - pr' - m') ≤ -1 := by omega
        exact_mod_cast this
      nlinarith
    have hneg := Number.neg_of_rounds_le _ _ _ hs hR hq
    have hn := operator_sub_isNormalized_to_nearest_sz _ _ _ hi.norm hi'.norm
      (LoanState.calculateDeltas_interest _ _ _ hd)
    have : deltas.interest.operator_neg.operator_gt Number.zero = true := by
      rw [operator_gt_iff _ _ (Number.operator_neg_isNormalized _ hn) Number.zero_isNormalized, Number.toRat_neg,
        Number.toRat_zero]
      linarith
    rw [hint] at this
    exact absurd this (by decide)
  refine ⟨?_, ?_⟩
  · show l'.principalOutstanding.toRat < p.loan.principalOutstanding.toRat
    rw [e2, ← hsp, hp.val, hp'.val]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hlt) hpos
  · show l'.totalValueOutstanding.toRat < p.loan.totalValueOutstanding.toRat
    rw [e1, ← hsv, ht.val, ht'.val]
    refine mul_lt_mul_of_pos_right ?_ hpos
    have : (t' : ℤ) < t := by omega
    exact_mod_cast this

/-- A fractional rounding lands on an amount stored canonically, or on zero. -/
private lemma STAmount.roundToNumericType_frac_canon (x y : Number) (mode : rounding_mode) (s : Option Int)
    (h : STAmount.roundToNumericType .fractional x mode s = .ok y) :
    ∃ a : STAmount, a.FracCanonZero ∧ a.toRat = y.toRat := by
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber .fractional x mode with
  | error e => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    have hfc := STAmount.ofNumber_fractional_fczr x mode ret hof
    have hint : ret.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
    cases s with
    | none => exact ⟨ret, hfc, (STAmount.FracCanonZero.toNumber_val hfc mode y h).symm⟩
    | some s =>
      simp only [hint, Bool.false_eq_true, if_false] at h
      cases hre : STAmount.roundToExponent ret s mode with
      | error e => rw [hre] at h; exact absurd h (by simp)
      | ok rounded =>
        rw [hre] at h
        have hrc := STAmount.roundToExponent_fczr ret rounded s mode hfc hre
        exact ⟨rounded, hrc, (STAmount.FracCanonZero.toNumber_val hrc mode y h).symm⟩

/-- A to-nearest rounding to a fractional asset never lands above an amount the asset stores that bounds
the value. -/
private lemma STAmount.roundToNumericType_frac_le (x y : Number) (a : STAmount) (hx : x.isNormalized)
    (ha : a.FracCanonZero) (ha0 : 0 ≤ a.toRat) (hle : x.toRat ≤ a.toRat)
    (h : STAmount.roundToNumericType .fractional x .to_nearest = .ok y) : y.toRat ≤ a.toRat := by
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber .fractional x .to_nearest with
  | error e => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    have hfc := STAmount.ofNumber_fractional_fczr x _ ret hof
    rw [STAmount.FracCanonZero.toNumber_val hfc _ y h]
    by_cases hz : ret.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero ret hz]; exact ha0
    by_cases h0 : 0 ≤ x.toRat
    · rcases ha.2 with hac | haz
      · exact STAmount.ofNumber_to_nearest_le_of_canonical .fractional x ret a hx h0 (Or.inl hac) hac.is_fractional
          hle hof hz
      · rw [STAmount.toRat_eq_zero_of_mValue_zero a haz] at hle ⊢
        exact absurd (le_antisymm hle h0) (fun hx0 => by
          have := STAmount.ofNumber_nonneg .fractional x _ ret hx (Number.negative_false_of_nonneg x hx h0) hof
          have hxz : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp hx0
          subst hxz
          rw [STAmount.ofNumber_fractional_zero] at hof
          obtain rfl := Except.ok.inj hof
          exact hz rfl)
    · push Not at h0
      have hneg : x.negative_ = true := by
        by_contra hc
        exact absurd (Number.toRat_nonneg_of_nonnegative x (by simpa using hc)) (not_le.mpr h0)
      exact le_trans (STAmount.ofNumber_signtrue_nonpos .fractional x _ ret rfl hx hneg hof) ha0


/-- The fractional credit never lifts the balance past the amount added. Either the credit is not positive,
or an amount the asset stores sits between the balance plus the credit and the balance plus the amount. -/
private lemma sumRoundAndSubtract_frac_room (A c : Number) (e : Int) (st : STAmount)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (h : sumRoundAndSubtract A c e .fractional .downward = .ok st) :
    st.toRat ≤ 0 ∨ ∃ a : STAmount, a.FracCanonZero ∧ 0 ≤ a.toRat ∧ A.toRat + st.toRat ≤ a.toRat ∧
      a.toRat ≤ A.toRat + c.toRat := by
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
  have hErange : (-96 : ℤ) ≤ E ∧ E ≤ 80 := (postSumExponent_range _ _ _ _ _ he.1 he.2 hE).2

  obtain ⟨hs1, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  have hsn := Number.operator_add_isNormalized_any A c sum _ hA hc hsum
  obtain ⟨hs'0, hs'1, hs'n⟩ := STAmount.roundToNumericType_downward_le sum sum' E hsn hs0 hErange hsum'
  obtain ⟨a, ha, hav⟩ := STAmount.roundToNumericType_frac_canon sum sum' _ _ hsum'
  have hdn := Number.operator_sub_isNormalized_any sum' A d _ hs'n hA hd
  have hst := STAmount.ofNumber_downward_le_max .fractional d st hdn (by simp [NumericType.isIntegral]) h
  by_cases hd0 : d.toRat ≤ 0
  · exact Or.inl (le_trans hst (max_le hd0 le_rfl))
  · push Not at hd0
    have hdm : d.mantissa_ ≠ 0 := fun h0 => by
      rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hd0; exact lt_irrefl _ hd0
    obtain ⟨n, hn, hv⟩ := operator_sub_rounded_downward sum' A d hs'n hA hd hdm
    have hdle : d.toRat ≤ sum'.toRat - A.toRat := by rw [hv]; exact Number.lower_le _ n hn
    have hstd : st.toRat ≤ d.toRat := le_trans hst (max_le le_rfl hd0.le)
    refine Or.inr ⟨a, ha, by rw [hav]; exact hs'0, by rw [hav]; linarith, by rw [hav]; linarith⟩


/-- An amount a fractional asset stores exactly, as an amount of the asset. -/
private lemma STAmount.frac_canon_of_isRounded_false (A : Number) (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (h : STAmount.isRounded .fractional A = false) : ∃ a : STAmount, a.FracCanonZero ∧ a.toRat = A.toRat := by
  rcases (STAmount.isRounded_eq_false_iff _ A hA hA0).mp h with h0 | ⟨m, e, hlo, hhi, helo, hehi, hv⟩
  · exact ⟨⟨.fractional, 0, -100, false⟩, ⟨rfl, Or.inr rfl⟩, by
      rw [h0, STAmount.toRat_eq_zero_of_mValue_zero _ rfl]⟩
  · have hm : (m.toUInt64).toNat = m := by
      rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨.fractional, m.toUInt64, e, false⟩, ⟨rfl, Or.inl ⟨rfl, by rw [hm]; exact hlo, by rw [hm]; exact hhi,
      helo, hehi⟩⟩, ?_⟩
    rw [STAmount.toRat_of_nonneg _ rfl, hv, hm]

/-- An amount of a fractional asset is a normalized `Number` of the same value. -/
private lemma STAmount.FracCanonZero.number {a : STAmount} (ha : a.FracCanonZero) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = a.toRat := by
  rcases ha.2 with hc | hz
  · obtain ⟨sn, -, hv, hn⟩ := STAmount.toNumber_iou_exact a .to_nearest hc
    exact ⟨sn, hn, hv⟩
  · exact ⟨Number.zero, Number.zero_isNormalized, by
      rw [Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero a hz]⟩

/-- A fractional vault credit never lifts AssetsAvailable past the amount added, when AssetsAvailable is an
amount the asset stores. -/
private lemma vault_credit_frac_le (A c toPool aa A' : Number) (e : Int) (st : STAmount)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded .fractional A = false)
    (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (hst : sumRoundAndSubtract A c e .fractional .downward = .ok st) (hto : st.toNumber .to_nearest = .ok toPool)
    (haa : A.operator_add toPool .to_nearest = .ok aa)
    (hA' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok A') :
    A'.toRat ≤ A.toRat + c.toRat := by
  obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le A c e .fractional st hA hA0 hc hc0 he hst
  obtain ⟨htv, htnn⟩ := htn toPool hto
  have hR := operator_add_rounded_to_nearest A toPool aa hA htnn haa
  have haan := operator_add_isNormalized_to_nearest_sz A toPool aa hA htnn haa
  rcases sumRoundAndSubtract_frac_room A c e st hA hA0 hc hc0 he hst with hneg | ⟨a, ha, ha0, h1, h2⟩
  · -- a credit that isn't positive leaves AssetsAvailable at most where it was
    have haale : aa.toRat ≤ A.toRat := Number.roundsToRepresentable_le aa _ hR A hA (by rw [htv]; linarith)
    obtain ⟨b, hb, hbv⟩ := STAmount.frac_canon_of_isRounded_false A hA hA0 hArep
    have := STAmount.roundToNumericType_frac_le aa A' b haan hb (by rw [hbv]; exact hA0) (by rw [hbv]; exact haale)
      hA'
    rw [hbv] at this
    linarith
  · -- otherwise the credited sum stays at or below an amount the asset stores, itself at most A + c
    obtain ⟨w, hw, hwv⟩ := STAmount.FracCanonZero.number ha
    have haale : aa.toRat ≤ a.toRat := by
      rw [← hwv]; exact Number.roundsToRepresentable_le aa _ hR w hw (by rw [hwv, htv]; exact h1)
    exact le_trans (STAmount.roundToNumericType_frac_le aa A' a haan ha ha0 haale hA') h2


/-- An integral vault credit never lifts AssetsAvailable past the amount added, when AssetsAvailable is an
amount the asset stores. The credit is the amount floored to a whole unit. -/
private lemma vault_credit_int_le (nt : NumericType) (hint : nt.isIntegral = true) (A c toPool aa A' : Number)
    (e : Int) (st : STAmount) (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hArep : STAmount.isRounded nt A = false)
    (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (hst : sumRoundAndSubtract A c e nt .downward = .ok st) (hto : st.toNumber .to_nearest = .ok toPool)
    (haa : A.operator_add toPool .to_nearest = .ok aa)
    (hA' : STAmount.roundToNumericType nt aa .to_nearest = .ok A') :
    A'.toRat ≤ A.toRat + c.toRat := by
  obtain ⟨hstle, htn⟩ := sumRoundAndSubtract_downward_le A c e nt st hA hA0 hc hc0 he hst
  obtain ⟨htv, htnn⟩ := htn toPool hto
  have hst' : STAmount.ofNumber nt c .downward = .ok st := by
    unfold sumRoundAndSubtract at hst
    rw [if_pos hint] at hst
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ hst
    rw [hx, Except.ok.inj h]

  obtain ⟨iv, -, hiv⟩ := STAmount.ofNumber_integral_toRat nt c _ st hint
    (Number.negative_false_of_nonneg c hc hc0) hst'
  have hst0 := STAmount.ofNumber_nonneg nt c _ st hc (Number.negative_false_of_nonneg c hc hc0) hst'
  rw [hiv] at hst0
  obtain ⟨k, hk, hAk⟩ : ∃ k : ℕ, k ≤ 2 ^ 63 - 1 ∧ A.toRat = k := by
    rcases (STAmount.isRounded_eq_false_iff nt A hA hA0).mp hArep with h0 | h
    · exact ⟨0, by norm_num, by rw [h0]; simp⟩
    · cases hnt : nt with
      | fractional => rw [hnt] at hint; exact absurd hint (by decide)
      | integral mv mo ms msh =>
        rw [hnt] at h
        obtain ⟨-, k, -, hk, hv⟩ := h
        exact ⟨k, hk, hv⟩

  -- the new AssetsAvailable is the `to_rep` integer of the sum
  have haa0 : 0 ≤ aa.toRat := operator_add_nonneg A toPool aa hA htnn haa (by rw [htv, hiv]; linarith)
  have haan := operator_add_isNormalized_to_nearest_sz A toPool aa hA htnn haa
  unfold STAmount.roundToNumericType at hA'
  cases hof : STAmount.ofNumber nt aa .to_nearest with
  | error err => rw [hof] at hA'; exact absurd hA' (by simp)
  | ok ret =>
    rw [hof] at hA'
    have hA'v := (STAmount.ofNumber_toNumber_exact nt aa _ _ ret A' haan (fun _ => haa0) hof hA').1
    obtain ⟨iv', -, hiv'⟩ := STAmount.ofNumber_integral_toRat nt aa _ ret hint
      (Number.negative_false_of_nonneg aa haan haa0) hof
    rw [hA'v]
    have hjv : (iv.toInt : ℚ) = ((iv.toInt.toNat : ℕ) : ℚ) := by
      have : (0 : ℤ) ≤ iv.toInt := by exact_mod_cast hst0
      rw [show ((iv.toInt.toNat : ℕ) : ℚ) = ((iv.toInt.toNat : ℤ) : ℚ) by norm_cast, Int.toNat_of_nonneg this]
    by_cases hsmall : k + iv.toInt.toNat ≤ 2 ^ 63 - 1
    · -- the sum is exact, and the asset holds a whole number exactly
      have hs0 : minExponent + 18 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
      have hu := UnitsAt.add (x := A) (y := toPool) (s := 0) (a := k) (b := iv.toInt.toNat) ⟨hA, by rw [hAk]; simp⟩
        ⟨htnn, by rw [htv, hiv, hjv]; simp⟩ (by constructor <;> omega) hs0 haa
      have hden : aa.toRat.den = 1 := by rw [hu.val]; push_cast; simp
      rw [STAmount.ofNumber_integral_exact nt aa _ ret hint haan hden hof, hu.val, hAk]
      push_cast
      rw [← hjv, ← hiv]
      linarith
    · -- the asset holds at most `2^63 - 1` units, less than the sum
      have h1 : (iv'.toInt : ℚ) < 2 ^ 63 := by exact_mod_cast Int64.toInt_lt iv'
      have h2 : (2 : ℚ) ^ 63 ≤ (k : ℚ) + (iv.toInt.toNat : ℚ) := by
        have : 2 ^ 63 ≤ k + iv.toInt.toNat := by omega
        exact_mod_cast this
      rw [hiv']
      rw [← hjv, ← hiv] at h2
      linarith


/-- The three amounts a payment moves are normalized numbers. -/
def PaymentAmounts.Norm (a : PaymentAmounts) : Prop :=
  a.principalPaid.isNormalized ∧ a.interestPaid.isNormalized ∧ a.feePaid.isNormalized

/-- The parts of an instalment are normalized numbers. -/
private def PaymentComponents.Norm (pc : PaymentComponents) : Prop :=
  pc.totalValueDelta.isNormalized ∧ pc.principalDelta.isNormalized ∧ pc.managementFeeDelta.isNormalized ∧
    pc.untrackedInterest.isNormalized ∧ pc.untrackedManagementFee.isNormalized

private lemma PaymentAmounts.zero_norm : PaymentAmounts.zero.Norm :=
  ⟨Number.zero_isNormalized, Number.zero_isNormalized, Number.zero_isNormalized⟩

private lemma PaymentAmounts.add_norm {a b c : PaymentAmounts} (ha : a.Norm) (hb : b.Norm) (h : a.add b = .ok c) :
    c.Norm := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ⟨operator_add_isNormalized_to_nearest_sz _ _ _ ha.1 hb.1 ‹_›,
    operator_add_isNormalized_to_nearest_sz _ _ _ ha.2.1 hb.2.1 ‹_›,
    operator_add_isNormalized_to_nearest_sz _ _ _ ha.2.2 hb.2.2 ‹_›⟩

private lemma PaymentComponents.paidAmounts_norm {pc : PaymentComponents} {a : PaymentAmounts} (h : pc.Norm)
    (hp : pc.paidAmounts = .ok a) : a.Norm := by
  obtain ⟨vap, id, h1, h2, h3, h4, h5⟩ := PaymentComponents.paidAmounts_ok_inv pc a hp
  have hv := operator_sub_isNormalized_to_nearest_sz _ _ _ h.1 h.2.1 h1
  have hi := operator_sub_isNormalized_to_nearest_sz _ _ _ hv h.2.2.1 h2
  exact ⟨by rw [h5]; exact h.2.1, operator_add_isNormalized_to_nearest_sz _ _ _ hi h.2.2.2.1 h3,
    operator_add_isNormalized_to_nearest_sz _ _ _ h.2.2.1 h.2.2.2.2 h4⟩

/-- The next scheduled instalment takes normalized amounts off the loan. -/
private lemma Loan.scheduledComponents_norm (l : Loan) (pc : PaymentComponents)
    (h : Loan.scheduledComponents l = .ok pc) :
    pc.totalValueDelta.isNormalized ∧ pc.principalDelta.isNormalized ∧ pc.managementFeeDelta.isNormalized ∧
      pc.untrackedInterest = Number.zero := by
  have hT := l.wf.totalValueOutstanding_norm
  have hP := l.wf.principalOutstanding_norm
  have hM := l.wf.managementFeeOutstanding_norm
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
  all_goals first
    | exact ⟨hT, hP, hM, rfl⟩
    | (obtain ⟨h1, h2, h3, h4⟩ := Loan.state_fields l _ ‹l.state = _›
       rw [← h1] at hT
       rw [← h2] at hP
       rw [← h3] at hM
       pay_norm_forward
       refine ⟨?_, ?_, ?_, rfl⟩ <;> pay_prove_norm)

/-- The instalment loop sums normalized amounts. -/
private lemma UnsettledPayment.payInstalments_norm {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number) (p' : UnsettledPayment α) (hok : payment.amounts.Norm)
    (h : UnsettledPayment.payInstalments payment n amount = .ok p') : p'.amounts.Norm := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact hok
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact hok
    · exact hok
    all_goals
      obtain ⟨h1, h2, h3, h4⟩ := Loan.scheduledComponents_norm payment.loan _
        ‹Loan.scheduledComponents payment.loan = _›
      have hpaid := ‹PaymentComponents.paidAmounts _ = _›
      have hi := PaymentComponents.paidAmounts_norm
        (by exact ⟨h1, h2, h3, by rw [h4]; exact Number.zero_isNormalized, payment.loan.wf.serviceFee_norm⟩) hpaid
      have ha := PaymentAmounts.add_norm hok hi ‹PaymentAmounts.add _ _ = _›
    · exact ha
    · exact ih _ ha ‹_›

/-- The interest split is two normalized numbers. -/
private lemma roundAndSplitInterest_norm (interest : Number) (rate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (sc : Int) (net fee : Number)
    (h : roundAndSplitInterest interest rate mode nt sc = .ok (net, fee)) : net.isNormalized ∧ fee.isNormalized := by
  obtain ⟨i', h1, h2, h3⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ h
  have hi := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h1
  have hf := computeManagementFee_isNormalized _ _ _ _ _ h2
  exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hi hf h3, hf⟩

/-- The late instalment is made of normalized numbers. -/
private lemma Loan.lateComponents_norm (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.lateComponents l now = .ok pc) : pc.Norm := by
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok pc›)
  obtain ⟨h1, h2, h3, -⟩ := Loan.scheduledComponents_norm l _ ‹Loan.scheduledComponents l = _›
  obtain ⟨hn, hf⟩ := roundAndSplitInterest_norm _ _ _ _ _ _ _ ‹roundAndSplitInterest _ _ _ _ _ = _›
  have hsl := operator_add_isNormalized_to_nearest_sz _ _ _ l.wf.serviceFee_norm l.wf.latePaymentFee_norm
    ‹l.fees.serviceFee.operator_add _ _ = _›
  exact ⟨h1, h2, h3, hn, operator_add_isNormalized_to_nearest_sz _ _ _ hsl hf ‹_›⟩

/-- The full payoff is made of normalized numbers. -/
private lemma Loan.fullComponents_norm (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.fullComponents l now = .ok pc) : pc.Norm := by
  obtain ⟨_, _, _, net, split, state, cf, ppi, tracked, cfm, uf, ui, -, -, -, hsplit, hstate, hcf, hppi, htracked,
    hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv l now pc h
  obtain ⟨h1, h2, h3, h4⟩ := Loan.state_fields l state hstate
  have hP : state.principalOutstanding.isNormalized := by rw [h2]; exact l.wf.principalOutstanding_norm
  have hM : state.managementFeeDue.isNormalized := by rw [h3]; exact l.wf.managementFeeOutstanding_norm
  obtain ⟨hn, hf⟩ := roundAndSplitInterest_norm _ _ _ _ _ _ _ hsplit
  have hcfn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf
  have hppin := operator_add_isNormalized_to_nearest_sz _ _ _ hP h4 hppi
  have hcfmn := operator_add_isNormalized_to_nearest_sz _ _ _ hcfn hf hcfm
  exact ⟨operator_add_isNormalized_to_nearest_sz _ _ _ hppin hM htracked, hP, hM,
    operator_sub_isNormalized_to_nearest_sz _ _ _ hn h4 hui, operator_sub_isNormalized_to_nearest_sz _ _ _ hcfmn hM huf⟩

/-- The split of an overpayment is made of normalized numbers. -/
private lemma Loan.overpaymentComponents_norm (l : Loan) (x : Number) (opc : PaymentComponents)
    (h : Loan.overpaymentComponents l x = .ok opc) :
    opc.managementFeeDelta.isNormalized ∧ opc.untrackedInterest.isNormalized ∧
      opc.untrackedManagementFee.isNormalized := by
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok opc›)
  obtain ⟨hn, hf⟩ := roundAndSplitInterest_norm _ _ _ _ _ _ _ ‹roundAndSplitInterest _ _ _ _ _ = _›
  exact ⟨hf, hn, STAmount.roundToNumericType_isNormalized _ _ _ _ _ ‹STAmount.roundToNumericType _ _ _ _ = _›⟩

private lemma roundAndClamp_norm (value cap : Number) (mode : rounding_mode) (nt : NumericType) (sc : Int)
    (y : Number) (hcap : cap.isNormalized) (h : roundAndClamp value cap mode nt sc = .ok y) : y.isNormalized := by
  unfold roundAndClamp at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain rfl := (Except.ok.inj h).symm
    have hrn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hr
    unfold Number.clamp
    split_ifs
    · exact Number.zero_isNormalized
    · exact hcap
    · exact hrn

private lemma LoanState.calculateDeltas_principal_norm (x y : LoanState) (d : LoanStateDeltas)
    (hx : x.principalOutstanding.isNormalized) (hy : y.principalOutstanding.isNormalized)
    (h : x.calculateDeltas y = .ok d) : d.principal.isNormalized := by
  unfold LoanState.calculateDeltas at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok d›)
  exact operator_sub_isNormalized_to_nearest_sz _ _ _ hx hy ‹_›

/-- A re-amortization pays normalized amounts. -/
private lemma Loan.tryOverpayment_norm (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hopc : opc.managementFeeDelta.isNormalized ∧ opc.untrackedInterest.isNormalized ∧
      opc.untrackedManagementFee.isNormalized)
    (h : Loan.tryOverpayment l opc = .ok (some re)) : re.amounts.Norm := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  -- Find the steps by their shape only. A full search unfolds the `Number` operators of the other steps.
  rename_i hfee hres
  obtain rfl := Option.some.inj (Except.ok.inj hres)
  obtain ⟨-, b2, -, -⟩ := LoanState.build_eq _ _ _ _
    (by with_reducible assumption : LoanState.build _ _ _ = Except.ok _)
  obtain ⟨-, hs2, -, -⟩ := Loan.state_fields l _ (by with_reducible assumption : l.state = _)
  have hcl := (by with_reducible assumption :
    roundAndClamp _ (LoanState.principalOutstanding _) rounding_mode.upward _ _ = _)
  have hd := (by with_reducible assumption : LoanState.calculateDeltas _ _ = Except.ok _)
  refine ⟨LoanState.calculateDeltas_principal_norm _ _ _ (by rw [hs2]; exact l.wf.principalOutstanding_norm)
    (by rw [b2]; exact roundAndClamp_norm _ _ _ _ _ _ (by rw [hs2]; exact l.wf.principalOutstanding_norm) hcl) hd,
    hopc.2.1, operator_add_isNormalized_to_nearest_sz _ _ _ hopc.1 hopc.2.2 hfee⟩

/-- The extra amount of an overpayment adds normalized amounts. -/
private lemma UnsettledPayment.applyOverpayment_norm (p p' : UnsettledPayment Vault) (amount : Number)
    (hok : p.amounts.Norm) (h : UnsettledPayment.applyOverpayment p amount = .ok p') : p'.amounts.Norm := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hok
    | skip
  have hopc := Loan.overpaymentComponents_norm _ _ _ ‹Loan.overpaymentComponents _ _ = _›
  have hre := Loan.tryOverpayment_norm _ _ _ hopc ‹Loan.tryOverpayment _ _ = _›
  exact PaymentAmounts.add_norm hok hre ‹PaymentAmounts.add _ _ = _›

/-- Every payment moves normalized amounts. -/
lemma Loan.payInstalments_norm (pt : LoanPaymentType) (p : UnsettledPayment Vault)
    (h : (loan.payInstalments v pt amount now).run = .ok (.ok p)) : p.amounts.Norm := by
  have hreg : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      p0.amounts.Norm := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    exact UnsettledPayment.payInstalments_norm _ _ _ _ PaymentAmounts.zero_norm hloop
  cases pt
  · exact hreg p h
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.latePayInstalments_ok loan v amount now p h
    exact PaymentComponents.paidAmounts_norm (Loan.lateComponents_norm _ _ _ hpc) hamt
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.fullPayInstalments_ok loan v amount now p h
    exact PaymentComponents.paidAmounts_norm (Loan.fullComponents_norm _ _ _ hpc) hamt
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p h
    exact UnsettledPayment.applyOverpayment_norm p0 p amount (hreg p0 h0) h1

/-- The unimpair keeps AssetsAvailable, an amount the asset stores, and AssetsDeployed, and the vault's asset and
scale. -/
private lemma Loan.unimpair_pool (loan : Loan) (v v1 : Vault)
    (hu : (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := v1 }))
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    v1.assetsAvailable.toRat = v.assetsAvailable.toRat ∧
      STAmount.isRounded v1.numericType v1.assetsAvailable = false ∧ v1.numericType = v.numericType ∧
      v1.baseExponent = v.baseExponent ∧ v1.assetsDeployed = v.assetsDeployed := by
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v v1 _ hu
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
    obtain rfl : v = v1 := by injection hu with hu; injection hu with hu; injection hu
    exact ⟨rfl, hAA, rfl, rfl, rfl⟩
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
    split at hu
    · cases hu
    · cases hu
    · rename_i v2 hadj
      obtain rfl : v2 = v1 := by injection hu with hu; injection hu with hu; injection hu
      obtain ⟨hs, hnt, -⟩ := Vault.poolAdjust_sums v v2 _ hadj
      obtain ⟨aa, h1, h2⟩ := hs.cash
      rw [show ({ loss := loan.principalOutstanding.operator_neg } : PoolBalanceChange).cash = Number.zero from rfl,
        Number.operator_add_zero_right, Except.ok.injEq] at h1
      subst h1
      have hd := hs.deployed
      rw [show ({ loss := loan.principalOutstanding.operator_neg } : PoolBalanceChange).deployed = Number.zero from rfl,
        Number.operator_add_zero_right, Except.ok.injEq] at hd
      have hA0 := v.exact.assetsAvailable_nonneg
      refine ⟨STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm hAA h2,
        by rw [hnt]; exact STAmount.isRounded_roundToNumericType _ _ _ v.wf.assetsAvailable_norm hA0 h2, hnt, hbe,
        hd.symm⟩


/-- The vault side of a settlement: the credit, the new AssetsAvailable and the new AssetsDeployed. -/
private lemma Loan.pay_vault_sums (pt : LoanPaymentType) (r : LoanWithAmounts Vault)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    ∃ p tp credit toPool aa, (loan.payInstalments v pt amount now).run = .ok (.ok p) ∧
      (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := p.pool }) ∧
      p.amounts.principalPaid.operator_add p.amounts.interestPaid .to_nearest = .ok tp ∧
      sumRoundAndSubtract p.pool.assetsAvailable tp p.pool.baseExponent p.loan.broker.numericType .downward =
        .ok credit ∧
      credit.toNumber .to_nearest = .ok toPool ∧ r.amountToPool = toPool ∧
      p.pool.assetsAvailable.operator_add toPool .to_nearest = .ok aa ∧
      STAmount.roundToNumericType p.pool.numericType aa .to_nearest = .ok r.pool'.assetsAvailable ∧
      p.pool.assetsDeployed.operator_add p.amounts.principalPaid.operator_neg .to_nearest =
        .ok r.pool'.assetsDeployed ∧
      p.loan.broker = loan.broker := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨toPool, yieldDelta, _, _, _, raw, _, hsums, hadj, hv', -, -, hto, -⟩ := UnsettledPayment.settle_ok p r hs
  obtain ⟨tp, credit, htp, hcredit, htoPool⟩ := hsums.toPool
  obtain ⟨hsum, -⟩ := Vault.adjustBalances_ok_inv p.pool _ raw hadj
  obtain ⟨aa, h1, h2⟩ := hsum.cash
  have hraw := (RawVault.to_lawful_ok hv').1
  have e1 : r.pool'.assetsAvailable = raw.assetsAvailable := by
    rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl, hraw]
  have e2 : r.pool'.assetsDeployed = raw.assetsDeployed := by
    rw [show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw]
  refine ⟨p, tp, credit, toPool, aa, hp, hu, htp, hcredit, htoPool, hto, h1, by rw [e1]; exact h2,
    by rw [e2]; exact hsum.deployed, ?_⟩
  exact hst.broker

/-- The vault never receives more than principalPaid + interestPaid, when AssetsAvailable is an amount the
asset stores and principalPaid + interestPaid is a `Number` at least zero. -/
private lemma Loan.pay_vault_le (pt : LoanPaymentType) (r : LoanWithAmounts Vault) (payment : UnsettledPayment Vault)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v pt amount now).run = .ok (.ok payment))
    (hok : (loan.pay v pt amount now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) :
    r.pool'.assetsAvailable.toRat ≤
      v.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) := by
  obtain ⟨p, tp, credit, toPool, aa, hp, hu, htp, hcredit, hto, -, haa, hA', -, hb⟩ :=
    Loan.pay_vault_sums loan v amount now pt r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨w, hw, hw0, hwv⟩ := hsum
  obtain ⟨hpp, hip, -⟩ := Loan.payInstalments_norm loan v amount now pt payment hpay
  have htpv := Number.operator_add_exact_of_fits hpp hip htp ⟨w, hw, hwv⟩
  have htpn := operator_add_isNormalized_to_nearest_sz _ _ _ hpp hip htp
  obtain ⟨hAv, hArep, hnt1, hbe, -⟩ := Loan.unimpair_pool loan v payment.pool hu hAA
  have hA := payment.pool.wf.assetsAvailable_norm
  have hA0 := payment.pool.exact.assetsAvailable_nonneg
  have htp0 : 0 ≤ tp.toRat := by rw [htpv, ← hwv]; exact hw0
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds payment.pool
  have he : (-96 : ℤ) ≤ payment.pool.baseExponent ∧ payment.pool.baseExponent ≤ 80 := by omega
  rw [hb, hnt, ← hnt1] at hcredit
  rw [← hAv, ← htpv]
  cases hint : payment.pool.numericType.isIntegral
  · have hfr : payment.pool.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    rw [hfr] at hcredit hA' hArep
    exact vault_credit_frac_le _ _ _ _ _ _ _ hA hA0 hArep htpn htp0 he hcredit hto haa hA'
  · exact vault_credit_int_le _ hint _ _ _ _ _ _ _ hA hA0 hArep htpn htp0 he hcredit hto haa hA'


variable (paymentType : LoanPaymentType) (r : LoanWithAmounts Vault)

/-- `payment_vault_upper_bound` when the asset stores AssetsAvailable and principalPaid + interestPaid fits a
`Number`. -/
lemma Loan.payment_vault_upper_bound_of_fits (payment : UnsettledPayment Vault)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) :
    (r.pool'.assetsAvailable.toRat - v.assetsAvailable.toRat) -
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤ 0 := by
  have := Loan.pay_vault_le loan v amount now paymentType r payment hnt hAA hpay hok hsum
  linarith

/-- The new AssetsDeployed is AssetsDeployed − principalPaid, when that fits a `Number`. -/
private lemma Loan.pay_deployed (payment : UnsettledPayment Vault)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = v.assetsDeployed.toRat - payment.amounts.principalPaid.toRat) :
    r.pool'.assetsDeployed.toRat = v.assetsDeployed.toRat - payment.amounts.principalPaid.toRat := by
  obtain ⟨p, -, -, -, -, hp, hu, -, -, -, -, -, -, hd, -⟩ := Loan.pay_vault_sums loan v amount now paymentType r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨-, -, -, -, hAD⟩ := Loan.unimpair_pool loan v payment.pool hu hAA
  obtain ⟨hpp, -, -⟩ := Loan.payInstalments_norm loan v amount now paymentType payment hpay
  rw [hAD] at hd
  obtain ⟨w, hw, hwv⟩ := hdeployed
  have := Number.operator_add_exact_of_fits v.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpp) hd
    ⟨w, hw, by rw [hwv, Number.toRat_neg]; ring⟩
  rw [this, Number.toRat_neg]
  ring

/-- The broker side of a settlement below minCover: the fee floored onto the cover's grid joins the cover. -/
private lemma Loan.pay_cover_sums (hcover : loan.broker.hasMinimumCover v.baseExponent = .ok false)
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    ∃ p feeToCover toBroker, (loan.payInstalments v paymentType amount now).run = .ok (.ok p) ∧
      sumRoundAndSubtract loan.broker.coverAvailable p.amounts.feePaid v.baseExponent loan.broker.numericType
        .downward = .ok feeToCover ∧
      feeToCover.toNumber .to_nearest = .ok toBroker ∧ r.amountToBroker = toBroker ∧
      loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok r.loan'.broker.coverAvailable := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v paymentType amount now r hok
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v paymentType amount now p hp
  obtain ⟨_, _, toBroker, cover', _, _, broker', hsums, -, -, hbroker, hloan, -, hto⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v p.pool _ hu
  have hb : p.loan.broker = loan.broker := hst.broker
  rcases hsums.fee with ⟨hc, -, -⟩ | ⟨-, fc, hfc, hfb, hcov⟩
  · rw [hb, hbe, hcover] at hc; cases hc
  · have h1 := (RawLoan.to_lawful_ok hloan).1
    have h2 := (RawLoanBroker.to_lawful_ok hbroker).1
    have hc' : r.loan'.broker.coverAvailable = cover' := by
      rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, h1]
      simp only
      rw [show broker'.coverAvailable = broker'.toRawLoanBroker.coverAvailable from rfl, h2]
    rw [hb, hbe] at hfc
    rw [hb] at hcov
    exact ⟨p, fc, toBroker, hp, hfc, hfb, hto, by rw [hc']; exact hcov⟩

/-- The upper line of `Lending.payment_fees` when an XRP or MPT CoverAvailable + feePaid fits a `Number`. -/
lemma Loan.payment_fees_upper_bound_of_fits (payment : UnsettledPayment Vault)
    (hcover : loan.broker.hasMinimumCover v.baseExponent = .ok false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hfee : 0 ≤ payment.amounts.feePaid.toRat)
    (hfits : loan.broker.numericType.isIntegral = true → ∃ w : Number, w.isNormalized ∧
      w.toRat = loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat) :
    (r.loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat ≤ 0 := by
  obtain ⟨p, fc, toBroker, hp, hfc, hto, -, hcov⟩ := Loan.pay_cover_sums loan v amount now paymentType r hcover hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨-, -, hfn⟩ := Loan.payInstalments_norm loan v amount now paymentType payment hpay
  have hC := loan.broker.wf.coverAvailable_norm
  have hC0 := loan.broker.exact.coverAvailable_nonneg
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds v
  have he : (-96 : ℤ) ≤ v.baseExponent ∧ v.baseExponent ≤ 80 := by omega
  obtain ⟨hfcle, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ fc hC hC0 hfn hfee he hfc
  obtain ⟨htv, htnn⟩ := htn toBroker hto
  have hR := operator_add_rounded_to_nearest _ _ _ hC htnn hcov
  cases hint : loan.broker.numericType.isIntegral
  · have hfr : loan.broker.numericType = .fractional :=
      NumericType.eq_fractional_of_not_integral (by simpa using hint)
    rw [hfr] at hfc
    rcases sumRoundAndSubtract_frac_room _ _ _ fc hC hC0 hfn hfee he hfc with hneg | ⟨a, ha, -, h1, h2⟩
    · have := Number.roundsToRepresentable_le _ _ hR _ hC (by rw [htv]; linarith)
      linarith
    · obtain ⟨w, hw, hwv⟩ := STAmount.FracCanonZero.number ha
      have := Number.roundsToRepresentable_le _ _ hR w hw (by rw [hwv, htv]; exact h1)
      linarith
  · obtain ⟨w, hw, hwv⟩ := hfits hint
    have := Number.roundsToRepresentable_le _ _ hR w hw (by rw [hwv, htv]; linarith)
    linarith


/-- The credit on the base grid is the amount floored to whole base units. -/
private lemma credit_at_base (nt : NumericType) (A c : Number) (b : Int) (st : STAmount) (a : ℕ)
    (hint : nt.isIntegral = true → b = 0) (hbr : (-10 : ℤ) ≤ b ∧ b ≤ 0)
    (hA : A.isNormalized) (hAv : A.toRat = (a : ℚ) * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hroom : A.toRat + c.toRat ≤ (10 : ℚ) ^ (16 + b) - 10 ^ b)
    (hst : sumRoundAndSubtract A c b nt .downward = .ok st) :
    st.toRat = (⌊c.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b := by
  cases hnt : nt.isIntegral
  · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hnt)
    subst hfr
    exact sumRoundAndSubtract_at_base A c b st a hA hAv hc hc0 ⟨by omega, hbr.2⟩ hroom hst
  · have hb0 := hint hnt
    subst hb0
    unfold sumRoundAndSubtract at hst
    rw [if_pos hnt] at hst
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ hst
    obtain rfl := Except.ok.inj h
    have hneg := Number.negative_false_of_nonneg c hc hc0
    obtain ⟨iv, hiv, hv⟩ := STAmount.ofNumber_integral_toRat nt c _ x hnt hneg hx
    obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor c iv hc hneg hiv
    rw [hv]
    simp only [zpow_zero, div_one, mul_one]
    have : ⌊c.toRat⌋ = iv.toInt := by
      rw [Int.floor_eq_iff]; exact ⟨h1, h2⟩
    rw [this]

/-- On the base grid the vault holds AssetsAvailable plus the amount floored to whole base units. -/
private lemma vault_credit_at_base (nt : NumericType) (A c toPool aa A' : Number) (b : Int) (st : STAmount)
    (a : ℕ) (hint : nt.isIntegral = true → b = 0) (hbr : (-10 : ℤ) ≤ b ∧ b ≤ 0)
    (hA : A.isNormalized) (hAv : A.toRat = (a : ℚ) * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hroom : A.toRat + c.toRat ≤ (10 : ℚ) ^ (16 + b) - 10 ^ b)
    (hst : sumRoundAndSubtract A c b nt .downward = .ok st) (hto : st.toNumber .to_nearest = .ok toPool)
    (haa : A.operator_add toPool .to_nearest = .ok aa)
    (hA' : STAmount.roundToNumericType nt aa .to_nearest = .ok A') :
    toPool.toRat = (⌊c.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b ∧ A'.toRat = A.toRat + toPool.toRat := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ A.toRat := by rw [hAv]; positivity
  obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le A c b nt st hA hA0 hc hc0 ⟨by omega, by omega⟩ hst
  obtain ⟨htv, htnn⟩ := htn toPool hto
  have hstv := credit_at_base nt A c b st a hint hbr hA hAv hc hc0 hroom hst

  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = ⌊c.toRat / 10 ^ b⌋ :=
    ⟨_, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg hc0 hp.le))⟩
  have hk1 : (kn : ℚ) * 10 ^ b ≤ c.toRat := by
    have := Int.floor_le (c.toRat / 10 ^ b)
    rw [← hkn, le_div_iff₀ hp] at this
    exact_mod_cast this
  have htv' : toPool.toRat = (kn : ℚ) * 10 ^ b := by rw [htv, hstv, ← hkn]; norm_cast
  have hK : a + kn < 10 ^ 16 := by
    have hpow16 : (10 : ℚ) ^ (16 + b) = (10 : ℚ) ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num
    have h1 : ((a + kn : ℕ) : ℚ) * 10 ^ b < (10 : ℚ) ^ 16 * 10 ^ b := by
      push_cast; rw [hAv] at hroom; nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp.le
  refine ⟨by rw [htv', ← hkn]; norm_cast, ?_⟩

  -- the sum is exact, and the asset holds it
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hu := UnitsAt.add (a := a) (b := kn) ⟨hA, by rw [hAv]; norm_cast⟩ ⟨htnn, by rw [htv']; norm_cast⟩
    (by constructor <;> omega) hs haa
  have haan := hu.norm
  have haa0 : 0 ≤ aa.toRat := by rw [hu.val]; positivity
  have hrep : STAmount.isRounded nt aa = false := by
    cases hnt : nt.isIntegral
    · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hnt)
      rw [STAmount.isRounded_eq_false_iff _ _ haan haa0, hfr, hu.val]
      have := STAmount.representable_fractional_of_units (a + kn) b hK (by omega) (by omega)
      push_cast at this ⊢
      exact this
    · refine STAmount.isRounded_eq_false_of_integral_round _ _ _ hnt haan haa0 ?_ hA'
      rw [hu.val, hint hnt]
      simp only [zpow_zero, mul_one]
      norm_cast
  rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep hA', hu.val, hAv, htv']
  push_cast
  ring


/-- On the base grid a payment credits principalPaid + interestPaid floored to whole base units, which is amountToPool.
The sum stays a unit below `10^(16 + b)`, so the scale of AssetsAvailable' is the base scale. -/
lemma Loan.payment_vault_at_base (payment : UnsettledPayment Vault) (a : ℕ)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤
      (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat +
      (⌊(payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) / 10 ^ v.baseExponent⌋ : ℚ) *
        10 ^ v.baseExponent ∧
      (∀ e, numberExponent r.pool'.assetsAvailable v.baseExponent v.numericType = .ok e → e = v.baseExponent) ∧
      r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountToPool.toRat := by
  obtain ⟨p, tp, credit, toPool, aa, hp, hu, htp, hcredit, hto, hamt, haa', hA', -, hb⟩ :=
    Loan.pay_vault_sums loan v amount now paymentType r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨w, hw, hw0, hwv⟩ := hsum
  obtain ⟨hpp, hip, -⟩ := Loan.payInstalments_norm loan v amount now paymentType payment hpay
  have htpv := Number.operator_add_exact_of_fits hpp hip htp ⟨w, hw, hwv⟩
  have htpn := operator_add_isNormalized_to_nearest_sz _ _ _ hpp hip htp
  obtain ⟨hAv, -, hnt1, hbe, -⟩ := Loan.unimpair_pool loan v payment.pool hu hAA
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  rw [hb, hnt, ← hnt1, hbe] at hcredit
  have hAv' : payment.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent := by rw [hAv, haa]
  have hroom' : payment.pool.assetsAvailable.toRat + tp.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) -
      10 ^ v.baseExponent := by rw [hAv, htpv]; exact hroom
  have htp0 : 0 ≤ tp.toRat := by rw [htpv, ← hwv]; exact hw0
  obtain ⟨htov, hA'v⟩ := vault_credit_at_base _ _ _ _ _ _ _ _ a (by rw [hnt1]; exact hbint)
    ⟨hblo, hbhi⟩ payment.pool.wf.assetsAvailable_norm hAv' htpn htp0 hroom' hcredit hto haa' hA'
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  refine ⟨by rw [hA'v, htov, hAv, htpv], fun e he => ?_, by rw [hA'v, hamt, hAv]⟩
  refine numberExponent_at_base _ _ _ e r.pool'.wf.assetsAvailable_norm r.pool'.exact.assetsAvailable_nonneg
    (by omega) hbint ?_ he
  change r.pool'.assetsAvailable.toRat < _
  rw [hA'v, htov, hAv, htpv]
  have := Int.floor_le ((payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) /
    10 ^ v.baseExponent)
  rw [le_div_iff₀ hp] at this
  linarith

/-- On the base grid a payment credits the vault less than one base unit short of principalPaid + interestPaid,
and AssetsAvailable' stays at the base scale. -/
lemma Loan.payment_vault_lower_bound_at_base (payment : UnsettledPayment Vault) (a : ℕ)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤
      (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
        (r.pool'.assetsAvailable.toRat - v.assetsAvailable.toRat) < 10 ^ v.baseExponent ∧
      ∀ e, numberExponent r.pool'.assetsAvailable v.baseExponent v.numericType = .ok e → e = v.baseExponent := by
  obtain ⟨h1, h2, -⟩ := Loan.payment_vault_at_base loan v amount now paymentType r payment a hnt hAA hpay hok hsum haa
    hroom
  refine ⟨?_, h2⟩
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have := Int.lt_floor_add_one
    ((payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) / 10 ^ v.baseExponent)
  rw [div_lt_iff₀ hp] at this
  rw [h1]
  linarith

/-- On the base grid a payment raises AssetsTotal less than one base unit short of interestPaid, and
AssetsAvailable' stays at the base scale. -/
lemma Loan.payment_assetsTotal_lower_bound_at_base (payment : UnsettledPayment Vault) (a : ℕ)
    (hnt : loan.broker.numericType = v.numericType)
    (hAA : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat)
    (hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = v.assetsDeployed.toRat - payment.amounts.principalPaid.toRat)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤
      (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    v.toExact.assetsTotal + payment.amounts.interestPaid.toRat - r.pool'.toExact.assetsTotal < 10 ^ v.baseExponent ∧
      ∀ e, numberExponent r.pool'.assetsAvailable v.baseExponent v.numericType = .ok e → e = v.baseExponent := by
  obtain ⟨h1, h2⟩ := Loan.payment_vault_lower_bound_at_base loan v amount now paymentType r payment a hnt hAA hpay
    hok hsum haa hroom
  have h3 := Loan.pay_deployed loan v amount now paymentType r payment hAA hpay hok hdeployed
  refine ⟨?_, h2⟩
  show v.assetsAvailable.toRat + v.assetsDeployed.toRat + payment.amounts.interestPaid.toRat -
    (r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat) < _
  rw [h3]
  linarith


/-- Proof body of the base-grid `payment_fees_lower_bound`. The cover gains feePaid floored to whole base
units, which is amountToBroker, and the scale of CoverAvailable' is the base scale. -/
lemma Loan.payment_fees_lower_bound_at_base (payment : UnsettledPayment Vault) (c : ℕ)
    (hnt : loan.broker.numericType = v.numericType)
    (hcover : loan.broker.hasMinimumCover v.baseExponent = .ok false)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r))
    (hfee : 0 ≤ payment.amounts.feePaid.toRat)
    (hcv : loan.broker.coverAvailable.toRat = (c : ℚ) * 10 ^ v.baseExponent)
    (hroom : loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat ≤
      (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat - r.loan'.broker.coverAvailable.toRat <
        10 ^ v.baseExponent ∧
      (∀ e, numberExponent r.loan'.broker.coverAvailable v.baseExponent loan.broker.numericType = .ok e →
        e = v.baseExponent) ∧
      r.loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat + r.amountToBroker.toRat := by
  obtain ⟨p, fc, toBroker, hp, hfc, hto, htob, hcov⟩ := Loan.pay_cover_sums loan v amount now paymentType r hcover hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨-, -, hfn⟩ := Loan.payInstalments_norm loan v amount now paymentType payment hpay
  have hC := loan.broker.wf.coverAvailable_norm
  have hC0 := loan.broker.exact.coverAvailable_nonneg
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  have hint : loan.broker.numericType.isIntegral = true → v.baseExponent = 0 := by rw [hnt]; exact hbint
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ fc hC hC0 hfn hfee ⟨by omega, by omega⟩ hfc
  obtain ⟨htv, htnn⟩ := htn toBroker hto
  have hfcv := credit_at_base _ _ _ _ fc c hint ⟨hblo, hbhi⟩ hC hcv hfn hfee hroom hfc

  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = ⌊payment.amounts.feePaid.toRat / 10 ^ v.baseExponent⌋ :=
    ⟨_, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg hfee hp.le))⟩
  have hk1 : (kn : ℚ) * 10 ^ v.baseExponent ≤ payment.amounts.feePaid.toRat := by
    have := Int.floor_le (payment.amounts.feePaid.toRat / 10 ^ v.baseExponent)
    rw [← hkn, le_div_iff₀ hp] at this
    exact_mod_cast this
  have hk2 : payment.amounts.feePaid.toRat < ((kn : ℚ) + 1) * 10 ^ v.baseExponent := by
    have := Int.lt_floor_add_one (payment.amounts.feePaid.toRat / 10 ^ v.baseExponent)
    rw [← hkn, div_lt_iff₀ hp] at this
    exact_mod_cast this
  have htv' : toBroker.toRat = (kn : ℚ) * 10 ^ v.baseExponent := by rw [htv, hfcv, ← hkn]; norm_cast
  have hK : c + kn < 10 ^ 16 := by
    have hpow16 : (10 : ℚ) ^ (16 + v.baseExponent) = (10 : ℚ) ^ 16 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have h1 : ((c + kn : ℕ) : ℚ) * 10 ^ v.baseExponent < (10 : ℚ) ^ 16 * 10 ^ v.baseExponent := by
      push_cast; rw [hcv] at hroom; nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp.le

  have hs : minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hu := UnitsAt.add (a := c) (b := kn) ⟨hC, by rw [hcv]; norm_cast⟩ ⟨htnn, by rw [htv']; norm_cast⟩
    (by constructor <;> omega) hs hcov
  have hcv' : r.loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat + toBroker.toRat := by
    rw [hu.val, hcv, htv']; push_cast; ring
  refine ⟨by rw [hcv', htv']; linarith, fun e he => ?_, by rw [hcv', htob]⟩
  refine numberExponent_at_base _ _ _ e r.loan'.broker.wf.coverAvailable_norm r.loan'.broker.exact.coverAvailable_nonneg
    (by omega) hint ?_ he
  rw [hcv', htv']
  linarith


end XRPL.Model.Lending
