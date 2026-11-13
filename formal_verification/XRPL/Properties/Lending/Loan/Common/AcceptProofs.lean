import XRPL.Properties.Lending.Loan.Common.AcceptExits
import XRPL.Properties.Lending.Loan.Common.SetUpdates
import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # Proof bodies for the `Loan.accept` properties

What an accept moves in the vault, and that a pending create then an accept gives the same result as an active
create. The private lemmas show that the new loan's PrincipalOutstanding is PrincipalRequested. -/

namespace XRPL.Model.Protocol

open private STAmount.repack_exact from XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid

/-- A value the asset stores exactly and that the LoanSet precision check finds exact at scale `s`
rounds to itself at that scale. The check compares the downward and upward roundings. -/
private lemma STAmount.roundToNumericType_scale_exact (nt : NumericType) (x y : Number) (s : ℤ)
    (hx : x.isNormalized) (hx0 : 0 ≤ x.toRat) (hst : STAmount.isRounded nt x = false)
    (hs : -81 ≤ s) (hs_hi : s ≤ 80) (hchk : XRPL.Model.Protocol.isRounded x s nt = .ok true)
    (hy : STAmount.roundToNumericType nt x .to_nearest (some s) = .ok y) : y.toRat = x.toRat := by
  cases nt with
  | integral mv mo ms msh =>
    -- an integral amount ignores the scale
    have h : STAmount.roundToNumericType (.integral mv mo ms msh) x .to_nearest (some s) =
        STAmount.roundToNumericType (.integral mv mo ms msh) x .to_nearest none := by
      unfold STAmount.roundToNumericType
      cases hof : STAmount.ofNumber (.integral mv mo ms msh) x .to_nearest with
      | error e => rfl
      | ok ret =>
        have hty := STAmount.ofNumber_mNumericType _ _ _ ret hof
        have hint : ret.integral = true := by unfold STAmount.integral; rw [hty]; rfl
        simp only [hint, if_true]
    rw [h] at hy
    exact STAmount.roundToNumericType_of_isRounded_false _ _ _ hx hst hy
  | fractional =>
    by_cases hz : x.toRat = 0
    · have hx' : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp hz
      subst hx'
      have h : STAmount.roundToNumericType .fractional Number.zero .to_nearest (some s) = .ok Number.zero := by
        have hint : (⟨.fractional, 0, -100, false⟩ : STAmount).integral = false := rfl
        unfold STAmount.roundToNumericType
        rw [STAmount.ofNumber_fractional_zero]
        dsimp only
        rw [if_neg (by rw [hint]; decide), STAmount.roundToExponent_eq_self _ s _ (Or.inr (Or.inl rfl))]
        exact STAmount.toNumber_zero_fractional _ .to_nearest hint rfl
      rw [h, Except.ok.injEq] at hy
      rw [← hy]
    have hneg := Number.negative_false_of_nonneg x hx hx0
    have hm0 : x.mantissa_ ≠ 0 := fun h => hz (Number.toRat_eq_zero_of_mantissa_zero x h)
    -- the stored amount has 16 digits, so the 19-digit mantissa ends in three zeros
    obtain ⟨m, e, hmlo, hmhi, helo, hehi, hval⟩ :=
      ((STAmount.isRounded_eq_false_iff _ x hx hx0).mp hst).resolve_left hz
    have hm64 : (m * 1000).toUInt64.toNat = m * 1000 :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have hwnorm : (⟨false, (m * 1000).toUInt64, e - 3⟩ : Number).isNormalized := by
      refine Or.inr ⟨?_, ?_, Or.inr ?_, ?_, ?_⟩
      · show largeRange.min ≤ (m * 1000).toUInt64
        rw [UInt64.le_iff_toNat_le, hm64]; simp [largeRange]; omega
      · show (m * 1000).toUInt64 ≤ largeRange.max
        rw [UInt64.le_iff_toNat_le, hm64]; simp [largeRange]; omega
      · show (m * 1000).toUInt64.toNat % 10 = 0
        rw [hm64]; omega
      · show minExponent ≤ e - 3
        unfold minExponent; omega
      · show e - 3 ≤ maxExponent
        unfold maxExponent; omega
    have hwval : (⟨false, (m * 1000).toUInt64, e - 3⟩ : Number).toRat = x.toRat := by
      rw [Number.toRat_of_nonneg _ rfl, hval]
      show ((m * 1000).toUInt64.toNat : ℚ) * (10 : ℚ) ^ (e - 3) = (m : ℚ) * (10 : ℚ) ^ e
      rw [hm64, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
      push_cast
      field_simp
    have hvw : x = ⟨false, (m * 1000).toUInt64, e - 3⟩ := Number.isNormalized.toRat_inj hx hwnorm hwval.symm
    have hmod : x.mantissa_.toNat % 1000 = 0 := by
      rw [hvw]; show (m * 1000).toUInt64.toNat % 1000 = 0; rw [hm64]; omega
    have hexp : x.exponent_ = e - 3 := by rw [hvw]
    have hof : ∀ mode, STAmount.ofNumber .fractional x mode =
        .ok ⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ := fun mode =>
      STAmount.ofNumber_fractional_of_trailing_zeros x mode hx hm0 hneg hmod (by omega) (by omega)
    obtain ⟨-, -, hst_c, hst_val⟩ :=
      STAmount.repack_exact x .to_nearest hx hneg hm0 hmod (by omega) (by omega)
    set st : STAmount := ⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ with hst_def
    have hround : ∀ mode r, STAmount.roundToNumericType .fractional x mode (some s) = .ok r →
        ∃ rs, st.roundToExponent s mode = .ok rs ∧ rs.toNumber mode = .ok r := by
      intro mode r h
      unfold STAmount.roundToNumericType at h
      rw [hof mode] at h
      simp only [] at h
      rw [if_neg (by show ¬ (NumericType.fractional).isIntegral = true; decide)] at h
      cases hr : st.roundToExponent s mode with
      | error e => rw [hr] at h; cases h
      | ok rs => rw [hr] at h; exact ⟨rs, rfl, h⟩
    have hread : ∀ (rs : STAmount) (mode : rounding_mode) (n : Number), rs.mNumericType = .fractional →
        (rs.mValue = 0 ∨ rs.IOUCanonical) → rs.toNumber mode = .ok n → n.toRat = rs.toRat := by
      intro rs mode n hty hcz hn
      rcases hcz with h0 | hcan
      · rw [STAmount.toNumber_zero_fractional rs mode (by unfold STAmount.integral; rw [hty]; rfl) h0,
          Except.ok.injEq] at hn
        rw [← hn, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero _ h0]
      · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact rs mode hcan
        rw [hsn, Except.ok.injEq] at hn
        rw [← hn, hv]
    obtain ⟨rn, hrn, hy'⟩ := hround _ _ hy
    by_cases hge : s ≤ x.exponent_ + 3
    · -- the amount is already on the grid
      rw [STAmount.roundToExponent_eq_self st s _ (Or.inr (Or.inr hge)), Except.ok.injEq] at hrn
      subst hrn
      rw [hread st _ y rfl (Or.inr hst_c) hy', hst_val]
    push Not at hge
    have hev : st.mOffset < s := hge
    have hxpos : 0 < x.toRat := lt_of_le_of_ne hx0 (Ne.symm hz)
    have hps : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
    -- the precision check found the downward and the upward roundings equal
    unfold XRPL.Model.Protocol.isRounded at hchk
    obtain ⟨dn, hdn, hchk⟩ := bind_ok_peel _ _ _ hchk
    obtain ⟨un, hun, hchk⟩ := bind_ok_peel _ _ _ hchk
    have heq : dn.operator_eq un = true := Except.ok.inj hchk
    obtain ⟨rd, hrd, hdn'⟩ := hround _ _ hdn
    obtain ⟨ru, hru, hun'⟩ := hround _ _ hun
    obtain ⟨kd, hkd_val, hkd_ty, hkd_cz, -, hkd, -⟩ :=
      STAmount.roundToExponent_nonneg_units st rd s .downward hst_c rfl hev hs hs_hi hrd
    obtain ⟨ku, hku_val, hku_ty, hku_cz, -, -, hku⟩ :=
      STAmount.roundToExponent_nonneg_units st ru s .upward hst_c rfl hev hs hs_hi hru
    have hdv := hread rd _ dn hkd_ty hkd_cz hdn'
    have huv := hread ru _ un hku_ty hku_cz hun'
    rw [(Number.operator_eq_iff_eq _ _).mp heq, huv, hku_val] at hdv
    rw [hkd_val] at hdv
    have hk : (kd : ℚ) = ku := (mul_right_cancel₀ hps.ne' hdv).symm
    -- so the value is a whole number of grid units
    set q := st.toRat / 10 ^ s with hq
    have hfl := hkd rfl
    have hce := hku rfl
    have hfc : (⌊q⌋ : ℚ) = ⌈q⌉ := by rw [← hfl, ← hce]; exact_mod_cast hk
    have hqf : q = ⌊q⌋ := le_antisymm (by rw [hfc]; exact Int.le_ceil q) (Int.floor_le q)
    have hq0 : 0 < q := by rw [hq, hst_val]; positivity
    have hku1 : 1 ≤ ku := by
      have h1 : (0 : ℤ) < ⌈q⌉ := Int.ceil_pos.mpr hq0
      omega
    have hgrid : st.toRat = (ku : ℚ) * 10 ^ s := by
      have h1 : st.toRat = q * 10 ^ s := by rw [hq]; field_simp
      rw [h1, hqf, hfc, ← hce]; push_cast; ring
    rw [STAmount.roundToExponent_grid_self st s ku hst_c rfl hku1 hgrid hs hs_hi, Except.ok.injEq] at hrn
    subst hrn
    rw [hread st _ y rfl (Or.inr hst_c) hy', hst_val]

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Number.signum_nonneg_of_le Number.toRat_nonneg_of_le from XRPL.Properties.Lending.Loan.Common.AcceptExits

variable (loan : Loan) (v : Vault)

/-- Proof body of `accept_releases`. -/
lemma Loan.accept_releases_proof (interestDue : Number) (r : LoanWithDisbursement Vault)
    (hi : loan.interestDue = .ok interestDue) (hok : (loan.accept v).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (har : STAmount.Representable v.numericType (v.assetsReserved.toRat - loan.principalOutstanding.toRat))
    (hyu : STAmount.Representable v.numericType (v.yieldUnrealized.toRat + interestDue.toRat)) :
    r.pool'.assetsReserved.toRat = v.assetsReserved.toRat - loan.principalOutstanding.toRat ∧
      r.pool'.yieldUnrealized.toRat = v.yieldUnrealized.toRat + interestDue.toRat ∧
      { r.pool'.toRawVault with assetsReserved := v.assetsReserved, yieldUnrealized := v.yieldUnrealized } =
        v.toRawVault ∧
      r.loan'.broker = loan.broker := by
  obtain ⟨raw, hadj, hv', hl, -⟩ := Loan.accept_ok_inv loan v interestDue r hi hok
  have hraw := (RawVault.to_lawful_ok hv').1
  have hloan := (RawLoan.to_lawful_ok hl).1
  obtain ⟨aa', ad', lu', ar', yu', hs, -, -, hrawEq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  obtain ⟨aa, h1, h2⟩ := hs.cash
  have hd := hs.deployed
  have hlu := hs.loss
  have hr := hs.reserved
  have hy := hs.yield
  simp only [Loan.acceptChange, Number.operator_add_zero_right, Except.ok.injEq] at h1 hd hlu hr hy
  subst h1 hd hlu

  -- the vault stores AssetsAvailable exactly, so rounding it again keeps it
  have haa' : aa' = v.assetsAvailable :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2) v.wf.assetsAvailable_norm
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm haa h2)
  subst haa'

  have hpn := loan.wf.principalOutstanding_norm
  have har' : ar'.toRat = v.assetsReserved.toRat - loan.principalOutstanding.toRat := by
    have h := Number.operator_add_exact_of_fits v.wf.assetsReserved_norm (Number.operator_neg_isNormalized _ hpn) hr
      (by rw [Number.toRat_neg, ← sub_eq_add_neg]; exact STAmount.Representable.number har)
    rw [h, Number.toRat_neg, ← sub_eq_add_neg]
  have hyu' : yu'.toRat = v.yieldUnrealized.toRat + interestDue.toRat :=
    Number.operator_add_exact_of_fits v.wf.yieldUnrealized_norm (RawLoan.interestDue_isNormalized loan _ hi) hy
      (STAmount.Representable.number hyu)

  rw [hraw, hrawEq]
  exact ⟨har', hyu', rfl, (congrArg RawLoan.broker hloan :)⟩

/-- The loan properties hold PrincipalRequested rounded at LoanScale, and LoanScale is never finer
than the minimum scale. -/
private lemma computeLoanProperties_principal (principal : Number) (ir : TenthBips32) (interval n : UInt32)
    (mgmt : TenthBips16) (nt : NumericType) (minScale : Int) (props : LoanProperties)
    (h : computeLoanProperties principal ir interval n mgmt nt minScale = .ok props) :
    minScale ≤ props.loanScale ∧
      STAmount.roundToNumericType nt principal .to_nearest (some props.loanScale) = .ok props.principalOutstanding := by
  unfold computeLoanProperties at h
  obtain ⟨rate, -, h⟩ := bind_ok_peel _ _ _ h
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  obtain ⟨amount, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨amountSt, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tvo, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨rp, hrp, h⟩ := bind_ok_peel _ _ _ h
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨le_max_left _ _, hrp⟩

/-- A vault's base scale is at least `-10`, the finest IOU scale. -/
private lemma Vault.baseExponent_ge (v : Vault) : -10 ≤ v.baseExponent := by
  have h := v.wf.scale_le
  unfold XRPL.Model.SingleAssetVault.Vault.baseExponent NumericType.baseExponent
  split
  · omega
  · have : v.scale.toNat ≤ 10 := by
      have := UInt8.le_iff_toNat_le.mp h
      simpa [XRPL.Model.SingleAssetVault.vaultMaximumIOUScale] using this
    omega

/-- A new loan's PrincipalOutstanding is PrincipalRequested when the asset stores it exactly, as
LoanSet preclaim checks. The precision check at LoanScale then makes the rounding at LoanScale exact. -/
private lemma Loan.create_principalOutstanding (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault) (hpn : principal.isNormalized) (hp0 : 0 ≤ principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.loan'.principalOutstanding = principal := by
  obtain ⟨props, _, _, _, broker', hchecks, _, _, _, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  have hl := (RawLoan.to_lawful_ok hloan).1
  have hpo : r.loan'.principalOutstanding = props.principalOutstanding := (congrArg RawLoan.principalOutstanding hl :)
  have hsc : r.loan'.loanScale = props.loanScale := (congrArg RawLoan.loanScale hl :)
  obtain ⟨hmin, hround⟩ := computeLoanProperties_principal _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hchk := hchecks.exact principal List.mem_cons_self
  have hrange := r.loan'.wf.loanScale_range
  rw [hsc] at hrange
  have hbase := Vault.baseExponent_ge v
  have hv := STAmount.roundToNumericType_scale_exact _ _ _ _ hpn hp0 hst (by omega)
    (by have := hrange.2; unfold cMaxOffset at this; omega) hchk hround
  rw [hpo]
  exact Number.isNormalized.toRat_inj (hpo ▸ r.loan'.wf.principalOutstanding_norm) hpn hv

/-- The interest a pending loan computes at accept is the interest its create computed, once its
PrincipalOutstanding is PrincipalRequested. -/
private lemma Loan.create_interestDue (principal : Number) (rates : LoanRates) (fees : LoanFees)
    (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (props : LoanProperties)
    (loanState : LoanState) (broker' : LoanBroker)
    (hstate : LoanState.build props.totalValueOutstanding principal props.managementFeeOutstanding = .ok loanState)
    (hloan : (RawLoan.build principal props rates fees schedule broker' allowsOverpayment pending
      (schedule.startDate + schedule.paymentInterval)).to_lawful = .ok r.loan')
    (hpo : r.loan'.principalOutstanding = principal) :
    r.loan'.interestDue = .ok loanState.interestDue := by
  have hl := (RawLoan.to_lawful_ok hloan).1
  have htvo : r.loan'.totalValueOutstanding = props.totalValueOutstanding :=
    (congrArg RawLoan.totalValueOutstanding hl :)
  have hmfo : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding :=
    (congrArg RawLoan.managementFeeOutstanding hl :)
  unfold LoanState.build at hstate
  obtain ⟨t, ht, hstate⟩ := bind_ok_peel _ _ _ hstate
  obtain ⟨i, hi, hstate⟩ := bind_ok_peel _ _ _ hstate
  simp only [pure, Except.pure, Except.ok.injEq] at hstate
  subst hstate
  unfold RawLoan.interestDue
  rw [htvo, hpo, ht, ok_bind, hmfo]
  exact hi

/-- What a create sends the borrower: an active loan PrincipalRequested less the origination fee, exactly, a pending
one nothing. -/
lemma Loan.create_amountToBorrower_proof (broker : LoanBroker) (v : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r : LoanWithDisbursement Vault) (hpn : principal.isNormalized) (hp0 : 0 ≤ principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    (pending = false → r.amountToBorrower.toRat + fees.originationFee.toRat = principal.toRat) ∧
      (pending = true → r.amountToBorrower = Number.zero) := by
  have hamt := Loan.create_ok_amount broker v principal rates fees schedule allowsOverpayment pending r hok
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · subst hp
    -- the new loan holds PrincipalRequested and the fee, and the accept amount of a loan is exact
    have hPO := Loan.create_principalOutstanding broker v principal rates fees schedule allowsOverpayment false r
      hpn hp0 hst hok
    obtain ⟨_, _, _, _, _, -, -, -, -, hloan⟩ :=
      Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment false r hok
    have hfees : r.loan'.fees = fees := (congrArg RawLoan.fees (RawLoan.to_lawful_ok hloan).1 :)
    obtain ⟨a, ha, hav⟩ := Loan.acceptAmount_ok r.loan'
    rw [hPO, hfees] at ha hav
    simp only [Loan.createAmountToBorrower, Bool.false_eq_true, ↓reduceIte, ha, Except.ok.injEq] at hamt
    rw [← hamt, hav]; ring
  · subst hp
    simpa [Loan.createAmountToBorrower] using hamt.symm

/-- What an accept sends the borrower: PrincipalOutstanding less the origination fee, exactly. -/
lemma Loan.accept_amountToBorrower_proof (r : LoanWithDisbursement Vault) (hok : (loan.accept v).run = .ok (.ok r)) :
    r.amountToBorrower.toRat + loan.fees.originationFee.toRat = loan.principalOutstanding.toRat := by
  cases hi : loan.interestDue with
  | error e =>
    simp only [Loan.accept] at hok
    unfold_ter at hok
    simp [hi] at hok
  | ok interestDue =>
    obtain ⟨-, -, -, -, ha⟩ := Loan.accept_ok_inv loan v interestDue r hi hok
    obtain ⟨a, ha', hav⟩ := Loan.acceptAmount_ok loan
    rw [ha'] at ha
    rw [← Except.ok.inj ha, hav]; ring

variable (broker : LoanBroker) (principal : Number) (rates : LoanRates) (fees : LoanFees)
  (schedule : LoanSchedule) (allowsOverpayment : Bool)

/-- Proof body of `createPending_accept`. -/
lemma Loan.createPending_accept_proof (r rA : LoanWithDisbursement Vault)
    (hpn : principal.isNormalized) (hp0 : 0 ≤ principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (har : STAmount.Representable v.numericType (v.assetsReserved.toRat + principal.toRat))
    (hcreate : (Loan.create broker v principal rates fees schedule allowsOverpayment true).run = .ok (.ok r))
    (haccept : (r.loan'.accept r.pool').run = .ok (.ok rA)) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment false).run = .ok (.ok rA) := by
  obtain ⟨props, loanState, debtTotal', principal', broker', hchecks, hround, hpool, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment true r hcreate
  have hPO := Loan.create_principalOutstanding broker v principal rates fees schedule allowsOverpayment true r
    hpn hp0 hst hcreate
  -- the asset stores PrincipalRequested exactly, so its rounding keeps it
  have hp' : principal' = principal :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround) hpn
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ hpn hst hround)
  subst hp'
  have hi := Loan.create_interestDue principal' rates fees schedule allowsOverpayment true r props loanState broker'
    hchecks.state hloan hPO
  obtain ⟨rawA, hadjA, hvA, hlA, haA⟩ := Loan.accept_ok_inv r.loan' r.pool' loanState.interestDue rA hi haccept
  obtain ⟨rawP, hadjP, hvP⟩ := Vault.poolAdjust_ok_inv v _ r.pool' hpool
  have hrawP := (RawVault.to_lawful_ok hvP).1
  obtain ⟨aaP, adP, luP, arP, yuP, hsP, ⟨hgaP, hgdP, hglP, -, -⟩, hleP, hrawPeq⟩ :=
    Vault.adjustBalances_ok_parts v _ rawP hadjP
  obtain ⟨aaA, adA, luA, arA, yuA, hsA, ⟨-, -, -, hgyA, -⟩, -, hrawAeq⟩ :=
    Vault.adjustBalances_ok_parts r.pool' _ rawA hadjA
  have hpf := hrawP.trans hrawPeq
  obtain ⟨aa, h1P, h2P⟩ := hsP.cash
  have hdP := hsP.deployed
  have hlP := hsP.loss
  have hrP := hsP.reserved
  have hyP := hsP.yield
  obtain ⟨aa', h1A, h2A⟩ := hsA.cash
  have hdA := hsA.deployed
  have hlA' := hsA.loss
  have hrA := hsA.reserved
  have hyA := hsA.yield
  simp only [Loan.createChange, Loan.acceptChange, if_true, Number.operator_add_zero_right, Except.ok.injEq,
    hPO] at h1P hdP hlP hrP hyP h1A hdA hlA' hrA hyA
  rw [show r.pool'.assetsAvailable = aaP from (congrArg RawVault.assetsAvailable hpf :)] at h1A
  rw [show r.pool'.assetsDeployed = adP from (congrArg RawVault.assetsDeployed hpf :)] at hdA
  rw [show r.pool'.lossUnrealized = luP from (congrArg RawVault.lossUnrealized hpf :)] at hlA'
  rw [show r.pool'.assetsReserved = arP from (congrArg RawVault.assetsReserved hpf :)] at hrA
  rw [show r.pool'.yieldUnrealized = yuP from (congrArg RawVault.yieldUnrealized hpf :)] at hyA
  rw [show r.pool'.numericType = v.numericType from (congrArg RawVault.numericType hpf :)] at h2A
  subst hlP hyP h1A hdA hlA'
  have hneg := Number.operator_neg_isNormalized _ hpn

  -- the accept rounds the available assets again, and a stored amount rounds to itself
  have haan : aa.isNormalized := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hneg h1P
  have haa0 : 0 ≤ aa.toRat := by
    have hle := (operator_lt_eq_false_iff _ _ v.wf.assetsAvailable_norm hpn).mp hchecks.funds
    have h := Number.roundsToRepresentable_ge _ _ (operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm
      hneg h1P) Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero, Number.toRat_neg]; linarith)
    rwa [Number.toRat_zero] at h
  have haaPn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2P
  have haaA : aaA = aaP :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2A) haaPn
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ haaPn
        (STAmount.isRounded_roundToNumericType _ _ _ haan haa0 h2P) h2A)
  subst haaA

  -- the reserve takes the principal and gives it back exactly
  have harPn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsReserved_norm hpn hrP
  have harPv := Number.operator_add_exact_of_fits v.wf.assetsReserved_norm hpn hrP
    (STAmount.Representable.number har)
  have harA : arA = v.assetsReserved := by
    have h := Number.operator_add_exact_of_fits harPn hneg hrA
      ⟨v.assetsReserved, v.wf.assetsReserved_norm, by rw [harPv, Number.toRat_neg]; ring⟩
    refine Number.isNormalized.toRat_inj (operator_add_isNormalized_to_nearest_sz _ _ _ harPn hneg hrA)
      v.wf.assetsReserved_norm ?_
    rw [h, harPv, Number.toRat_neg]; ring
  subst harA

  have hsI : Vault.AdjustSums v (Loan.createChange principal' principal' loanState.interestDue false) aaA adP
      v.lossUnrealized v.assetsReserved yuA :=
    ⟨⟨aa, h1P, h2P⟩, hdP, Number.operator_add_zero_right _ _, Number.operator_add_zero_right _ _, hyA⟩
  have hadjI := Vault.adjustBalances_ok v _ aaA adP v.lossUnrealized v.assetsReserved yuA hsI
    ⟨hgaP, hgdP, hglP, hgyA, Number.signum_nonneg_of_le _ v.wf.assetsReserved_norm v.valid.assetsReserved_nonneg⟩ hleP
  have hrawI : rawA = { v.toRawVault with
      assetsAvailable := aaA
      assetsDeployed := adP
      assetsReserved := v.assetsReserved
      lossUnrealized := v.lossUnrealized
      yieldUnrealized := yuA } := by
    rw [hrawAeq, hpf]
  rw [hrawI] at hvA
  have hl := (RawLoan.to_lawful_ok hloan).1
  have hbuild : RawLoan.build principal' props rates fees schedule broker' allowsOverpayment false
    (schedule.startDate + schedule.paymentInterval) =
      { r.loan'.toRawLoan with isPending := false } := by
    rw [hl]; rfl
  rw [Loan.create_run_of_checks broker v principal' rates fees schedule allowsOverpayment false props loanState
    debtTotal' principal' _ rA.pool' broker' hchecks hround hadjI hvA hbroker
    (Loan.create_ok_fits _ _ _ _ _ _ _ _ _ hcreate).1 (Loan.create_ok_fits _ _ _ _ _ _ _ _ _ hcreate).2, hbuild, hlA]
  -- the accept sends PrincipalOutstanding less the fee, which is what an active create sends
  have hfees : r.loan'.fees = fees := (congrArg RawLoan.fees hl :)
  rw [hPO, hfees] at haA
  simp only [Loan.createAmountToBorrower, Bool.false_eq_true, ↓reduceIte, haA]
  exact congrArg (fun x => Except.ok (Except.ok x)) (Loan.accept_eta _ _ rA haccept).symm

/-- A create sends the broker owner the amount its loan reports: the origination fee once active. -/
lemma Loan.create_eta (r : LoanWithDisbursement Vault) (pending : Bool)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r = { loan' := r.loan', pool' := r.pool', amountToBorrower := r.amountToBorrower } := by
  obtain ⟨properties, loanState, debtTotal', principal', broker', hchecks, hround, hpool, hbroker, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨hcount, hdue⟩ := Loan.create_ok_fits broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ r.pool' hpool
  rw [Loan.create_run_of_checks broker v principal rates fees schedule allowsOverpayment pending properties
    loanState debtTotal' principal' raw r.pool' broker' hchecks hround hadj hv' hbroker hcount hdue, hloan] at hok
  revert hok
  cases Loan.createAmountToBorrower principal fees pending with
  | error e => intro hok; cases hok
  | ok a => intro hok; injection hok with hok; injection hok with hok; rw [← hok]

/-- An active create sends PrincipalRequested out exactly: to the borrower, and the origination fee to the broker
owner. -/
theorem Loan.create_conserves (r : LoanWithDisbursement Vault) (hpn : principal.isNormalized)
    (hp0 : 0 ≤ principal.toRat) (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment false).run = .ok (.ok r)) :
    r.amountToBorrower.toRat + r.amountToBroker.toRat = principal.toRat := by
  obtain ⟨_, _, _, _, _, -, -, -, -, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule allowsOverpayment false r hok
  have hl := (RawLoan.to_lawful_ok hloan).1
  have hfees : r.loan'.fees = fees := (congrArg RawLoan.fees hl :)
  have hpend : r.loan'.isPending = false := (congrArg RawLoan.isPending hl :)
  rw [Loan.create_eta (r := r) (pending := false) (hok := hok)]
  simp only [hpend, hfees, Bool.false_eq_true, ↓reduceIte]
  exact (Loan.create_amountToBorrower_proof broker v principal rates fees schedule allowsOverpayment false r hpn hp0
    hst hok).1 rfl

/-- An accept sends PrincipalOutstanding out exactly: to the borrower, and the origination fee to the broker
owner. -/
theorem Loan.accept_conserves (loan : Loan) (r : LoanWithDisbursement Vault)
    (hok : (loan.accept v).run = .ok (.ok r)) :
    r.amountToBorrower.toRat + r.amountToBroker.toRat = loan.principalOutstanding.toRat := by
  have hl : ({ loan.toRawLoan with isPending := false } : RawLoan) = r.loan'.toRawLoan := by
    simp only [Loan.accept] at hok
    unfold_ter at hok
    walk_ok
    all_goals exact (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1.symm
  have hfees : r.loan'.fees = loan.fees := (congrArg RawLoan.fees hl :).symm
  have hpend : r.loan'.isPending = false := (congrArg RawLoan.isPending hl :).symm
  rw [Loan.accept_eta loan v r hok]
  simp only [hpend, hfees, Bool.false_eq_true, ↓reduceIte]
  exact Loan.accept_amountToBorrower_proof loan v r hok

end XRPL.Model.Lending
