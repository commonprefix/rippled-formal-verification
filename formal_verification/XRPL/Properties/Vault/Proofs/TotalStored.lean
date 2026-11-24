import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Proofs.Support.TotalStores
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Every vault operation leaves a total the asset stores

C++ `syncAssetsTotal` stores AssetsAvailable + AssetsDeployed as an amount of the asset, so after a successful
deposit, withdrawal or clawback the vault's total is such an amount. A burn and an update leave both balances. -/

namespace XRPL.Model.Protocol

/-- Rounding a negative value to an asset gives at most zero. -/
lemma STAmount.roundToNumericType_nonpos_of_neg (nt : NumericType) (x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (hx : x.isNormalized) (hx0 : x.toRat < 0)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.toRat ≤ 0 := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, -⟩ := STAmount.ofNumber_canonicalOrZero nt x _ st hmax hof
    rw [(hcz.toNumber_exact y hok).1]
    have hneg : x.negative_ = true := by
      by_contra h
      have := Number.toRat_nonneg_of_nonnegative x (by simpa using h)
      linarith
    cases hint : nt.isIntegral
    · exact STAmount.ofNumber_signtrue_nonpos nt x _ st hint hx hneg hof
    · exact STAmount.ofNumber_integral_negative_nonpos nt x _ st hint hneg hof

/-- Rounding a value to an asset never lands above an amount the asset stores exactly and that bounds the
value. -/
lemma STAmount.roundToNumericType_le_of_stored (nt : NumericType) (w x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (hw : w.isNormalized) (hw0 : 0 ≤ w.toRat)
    (hst : STAmount.isRounded nt w = false) (hx : x.isNormalized) (hxw : x.toRat ≤ w.toRat)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) : y.toRat ≤ w.toRat := by
  by_cases hx0 : x.toRat < 0
  · exact (STAmount.roundToNumericType_nonpos_of_neg nt x y hmax hx hx0 hok).trans hw0
  push Not at hx0
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero nt x _ st hmax hof
    rw [(hcz.toNumber_exact y hok).1]
    by_cases hz : st.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hz]; exact hw0
    unfold STAmount.isRounded STAmount.equalAfterNumberConvert at hst
    cases ha : STAmount.ofNumber nt w .to_nearest with
    | error e => rw [ha] at hst; exact absurd hst (by simp [bind, Except.bind])
    | ok a =>
      rw [ha] at hst
      simp only [bind, Except.bind, pure, Except.pure] at hst
      cases hn : a.toNumber .to_nearest with
      | error e => rw [hn] at hst; exact absurd hst (by simp)
      | ok n =>
        rw [hn] at hst
        have heq : n.operator_eq w = true := by simpa using hst
        obtain ⟨hnv, hnn⟩ := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ha).1.toNumber_exact n hn
        have hav : a.toRat = w.toRat := by rw [← hnv]; exact (Number.operator_eq_iff _ _ hnn hw).mp heq
        by_cases ha0 : a.mValue = 0
        · -- a zero bound leaves only a zero value, which converts to zero
          have hw0' : w.toRat = 0 := by rw [← hav, STAmount.toRat_eq_zero_of_mValue_zero _ ha0]
          have hxz : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp (by linarith)
          subst hxz
          exact absurd (STAmount.ofNumber_source_ne_zero nt _ _ st hof hz) (by decide)
        have hac := STAmount.ofNumber_exactCanonical nt w .to_nearest a hw hw0 ha ha0
        have hat := STAmount.ofNumber_mNumericType nt w .to_nearest a ha
        rw [← hav]
        exact STAmount.ofNumber_to_nearest_le_of_canonical nt x st a hx hx0 hac hat (by rw [hav]; exact hxw) hof hz

/-- Rounding a value at least zero to an XRP or MPT amount raises it by at most half a unit. -/
lemma STAmount.roundToNumericType_integral_le_half (nt : NumericType) (hint : nt.isIntegral = true)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (x y : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) :
    y.toRat ≤ x.toRat + 1 / 2 := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, -⟩ := STAmount.ofNumber_canonicalOrZero nt x _ st hmax hof
    rw [(hcz.toNumber_exact y hok).1]
    have := STAmount.ofNumber_integral_within_half nt x st hint hx (Number.negative_false_of_nonneg x hx h0) hof
    linarith [(abs_le.mp this).2]

/-- A whole number less than one unit above another whole number is at most it. -/
lemma Rat.le_of_lt_add_one {x y : ℚ} (hx : x.den = 1) (hy : y.den = 1) (h : x < y + 1) : x ≤ y := by
  have hxe : (x.num : ℚ) = x := Rat.coe_int_num_of_den_eq_one hx
  have hye : (y.num : ℚ) = y := Rat.coe_int_num_of_den_eq_one hy
  have h1 : (x.num : ℚ) < (y.num : ℚ) + 1 := by rw [hxe, hye]; exact h
  have h2 : x.num < y.num + 1 := by exact_mod_cast h1
  have h3 : x.num ≤ y.num := by omega
  calc x = (x.num : ℚ) := hxe.symm
    _ ≤ (y.num : ℚ) := by exact_mod_cast h3
    _ = y := hye

/-- A whole number at most half a unit above another whole number is at most it. -/
lemma Rat.le_of_le_add_half {x y : ℚ} (hx : x.den = 1) (hy : y.den = 1) (h : x ≤ y + 1 / 2) : x ≤ y :=
  Rat.le_of_lt_add_one hx hy (by linarith)

/-- A value an XRP or MPT amount stores exactly is a whole number below `2^63`. -/
lemma STAmount.whole_of_stored (nt : NumericType) (hi : nt.isIntegral = true) (x : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hst : STAmount.isRounded nt x = false) : x.toRat.den = 1 ∧ x.toRat < 2 ^ 63 := by
  rcases (STAmount.isRounded_eq_false_iff nt x hx h0).mp hst with h | h
  · rw [h]; exact ⟨rfl, by norm_num⟩
  · cases nt with
    | fractional => cases hi
    | integral mv mo ms msh =>
      obtain ⟨-, k, -, hk63, hk⟩ := h
      rw [hk]
      have hlt : k < 9223372036854775808 := by omega
      exact ⟨Rat.den_natCast k, by exact_mod_cast hlt⟩

/-- A `to_nearest` sum of two whole numbers that is below `2^63` in size is exact. -/
lemma Number.add_whole_exact {x y r : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_add y .to_nearest = .ok r) (hxd : x.toRat.den = 1) (hyd : y.toRat.den = 1)
    (hlo : -2 ^ 63 < x.toRat + y.toRat) (hhi : x.toRat + y.toRat < 2 ^ 63) : r.toRat = x.toRat + y.toRat := by
  obtain ⟨w, hw, hwv⟩ := Number.exists_of_int (x.toRat + y.toRat) (Rat.den_one_add _ _ hxd hyd) hlo hhi
  exact Number.operator_add_exact_of_fits hx hy hok ⟨w, hw, hwv⟩

/-- Rounding a whole number from zero to an XRP or MPT amount does not raise it. -/
lemma STAmount.round_whole_le (nt : NumericType) (hi : nt.isIntegral = true)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat) (x y : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hxd : x.toRat.den = 1) (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) :
    y.toRat ≤ x.toRat := by
  have hhalf := STAmount.roundToNumericType_integral_le_half nt hi hmax x y hx h0 hok
  have hyN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hok
  have hy0 := STAmount.roundToNumericType_nonneg _ _ _ hx h0 hok
  have hyd := (STAmount.whole_of_stored nt hi y hyN hy0 (STAmount.isRounded_roundToNumericType _ _ _ hx h0 hok)).1
  exact Rat.le_of_le_add_half hyd hxd hhalf

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful balance update left a total that is an amount of the asset. -/
lemma Vault.adjustBalances_totalStores (v : Vault) (c : Lending.PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    TotalStores v.numericType raw.assetsAvailable raw.assetsDeployed := by
  simp only [Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  exact ⟨_, _, ‹_›, ‹_›⟩

/-- A successful update of the cash and the shares left a total that is an amount of the asset. -/
lemma Vault.adjustAssetsAndShares_totalStores (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    TotalStores v.numericType raw.assetsAvailable raw.assetsDeployed := by
  simp only [Vault.adjustAssetsAndShares] at h
  unfold_ter at h
  walk_ok
  have hts := Vault.adjustBalances_totalStores v _ _ ‹v.adjustBalances _ = _›
  exact hts

/-- A record that differs from a vault only in the cash and the shares has the vault's asset. -/
private lemma totalStored_of_frame {v v' : Vault} {raw : RawVault} {aa' st' : Number}
    (hraw : raw = { v.toRawVault with assetsAvailable := aa', sharesTotal := st' }) (hv' : v'.toRawVault = raw)
    (hts : TotalStores v.numericType raw.assetsAvailable raw.assetsDeployed) : v'.TotalStored := by
  unfold Vault.TotalStored
  rw [show v'.numericType = v.numericType from by
    show v'.toRawVault.numericType = _; rw [hv', hraw]]
  show TotalStores v.numericType v'.toRawVault.assetsAvailable v'.toRawVault.assetsDeployed
  rw [hv']
  exact hts

/-- After a successful deposit the vault's total is an amount of the asset. -/
lemma Vault.deposit_totalStored (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) : r.vault'.TotalStored := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨aa', st', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    have hts := Vault.adjustAssetsAndShares_totalStores _ _ _ _ ‹_›
    exact totalStored_of_frame hrv (RawVault.to_lawful_ok ‹_›).1 hts

/-- After a successful withdrawal the vault's total is an amount of the asset. -/
lemma Vault.withdraw_totalStored (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) : r.vault'.TotalStored := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨aa', st', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    have hts := Vault.adjustAssetsAndShares_totalStores _ _ _ _ ‹_›
    exact totalStored_of_frame hrv (RawVault.to_lawful_ok ‹_›).1 hts

/-- After a successful clawback the vault's total is an amount of the asset. -/
lemma Vault.clawback_totalStored (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) : r.vault'.TotalStored := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    obtain ⟨aa', st', hrv⟩ := Vault.adjustAssetsAndShares_frame _ _ _ _ ‹_›
    have hts := Vault.adjustAssetsAndShares_totalStores _ _ _ _ ‹_›
    exact totalStored_of_frame hrv (RawVault.to_lawful_ok ‹_›).1 hts

/-- A burn of shares keeps the vault's total an amount of the asset. -/
lemma Vault.burnShares_totalStored (v : Vault) (sharesDestroyed : STAmount) (v' : Vault)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v')) (hts : v.TotalStored) : v'.TotalStored := by
  obtain ⟨st', hf⟩ := Vault.burnShares_frame v sharesDestroyed v' hok
  unfold Vault.TotalStored at hts ⊢
  rwa [show v'.numericType = v.numericType from (congrArg RawVault.numericType hf :),
    show v'.assetsAvailable = v.assetsAvailable from (congrArg RawVault.assetsAvailable hf :),
    show v'.assetsDeployed = v.assetsDeployed from (congrArg RawVault.assetsDeployed hf :)]

/-- An update keeps the vault's total an amount of the asset. -/
lemma Vault.update_totalStored (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    (v' : Vault) (hok : v.update assetsMaximum blockDeposit = .ok v') (hts : v.TotalStored) : v'.TotalStored := by
  obtain ⟨m', b', hf⟩ := Vault.update_frame v assetsMaximum blockDeposit v' hok
  unfold Vault.TotalStored at hts ⊢
  rwa [show v'.numericType = v.numericType from (congrArg RawVault.numericType hf :),
    show v'.assetsAvailable = v.assetsAvailable from (congrArg RawVault.assetsAvailable hf :),
    show v'.assetsDeployed = v.assetsDeployed from (congrArg RawVault.assetsDeployed hf :)]

/-- Every smaller cash balance the asset stores keeps the vault's total an amount of the asset. A debit of the cash
then passes C++ `syncAssetsTotal`. -/
def Vault.DebitStores (v : Vault) : Prop :=
  ∀ y : Number, y.isNormalized → 0 ≤ y.toRat → y.toRat ≤ v.assetsAvailable.toRat →
    STAmount.isRounded v.numericType y = false → TotalStores v.numericType y v.assetsDeployed

/-- A vault that has lent nothing stores every cash balance as its total. -/
lemma Vault.DebitStores.of_noLending (v : Vault) (hAD : v.assetsDeployed = Number.zero) : v.DebitStores := by
  intro y hy h0 _ hrep
  rw [hAD]
  exact TotalStores.of_zero_deployed _ y hy h0 hrep

/-- A vault of an IOU, XRP or an MPT whose total is an amount of the asset keeps it so under a debit. -/
lemma Vault.TotalStored.debitStores {v : Vault} (h : v.TotalStored)
    (hasset : v.numericType = .fractional ∨ v.numericType = NumericType.native ∨ v.numericType = NumericType.int64) :
    v.DebitStores := by
  intro y hy h0 hle _
  exact TotalStores.mono h hasset v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm v.exact.assetsAvailable_nonneg
    v.exact.assetsDeployed_nonneg y v.assetsDeployed hy v.wf.assetsDeployed_norm h0 v.exact.assetsDeployed_nonneg
    (by linarith)

/-- An IOU value the asset stores exactly is at most the largest IOU amount, `10^96 - 10^80`. -/
private lemma representable_frac_le {x : ℚ} (h : STAmount.Representable .fractional x) : x ≤ 10 ^ 96 - 10 ^ 80 := by
  rcases h with rfl | ⟨m, e, -, hm, -, he, rfl⟩
  · norm_num
  have hm' : (m : ℚ) ≤ 10 ^ 16 - 1 := by
    have : m + 1 ≤ 10 ^ 16 := hm
    have h2 : ((m + 1 : ℕ) : ℚ) ≤ ((10 ^ 16 : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  calc (m : ℚ) * 10 ^ e ≤ (10 ^ 16 - 1) * 10 ^ e := mul_le_mul_of_nonneg_right hm' hp.le
    _ ≤ (10 ^ 16 - 1) * 10 ^ (80 : ℤ) := mul_le_mul_of_nonneg_left he' (by norm_num)
    _ = 10 ^ 96 - 10 ^ 80 := by norm_num

/-- The total after a cash update stores, as C++ `syncAssetsTotal` needs: on XRP or an MPT when the new cash before
rounding plus the new deployed balance is a unit below the maximum, on an IOU when the deployed one is below `10^80`. -/
lemma TotalStores.of_rounded_cash (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (x aa' d : Number)
    (hx : x.isNormalized) (hx0 : 0 ≤ x.toRat) (hround : STAmount.roundToNumericType nt x .to_nearest = .ok aa')
    (hd : d.isNormalized) (hd0 : 0 ≤ d.toRat)
    (hint : nt.isIntegral = true → x.toRat + d.toRat + 1 ≤ nt.maxValue.toNat)
    (hfrac : nt.isIntegral = false → d.toRat < 10 ^ 80) : TotalStores nt aa' d := by
  have haaN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have haa0 := STAmount.roundToNumericType_nonneg _ _ _ hx hx0 hround
  by_cases hi : nt.isIntegral = true
  · have hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat := by
      intro _
      rcases hasset with rfl | rfl | rfl
      · exact absurd hi (by decide)
      all_goals decide
    have hhalf := STAmount.roundToNumericType_integral_le_half nt hi hmax x aa' hx hx0 hround
    exact TotalStores.of_le nt hasset aa' d haaN hd haa0 hd0 (fun _ => by linarith [hint hi])
      (fun h => absurd hi (by simp [h]))
  · have hfr : nt = .fractional := by
      rcases hasset with rfl | rfl | rfl
      · rfl
      all_goals exact absurd rfl hi
    subst hfr
    have hrep := (STAmount.isRounded_eq_false_iff _ aa' haaN haa0).mp
      (STAmount.isRounded_roundToNumericType _ _ _ hx hx0 hround)
    have hle := representable_frac_le hrep
    have hd80 := hfrac rfl
    exact TotalStores.of_le _ hasset aa' d haaN hd haa0 hd0 (fun h => absurd h (by decide)) (fun _ => by linarith)

/-- A cash balance the asset stores and a deployed balance store their total: on XRP or an MPT when they sum to at
most a pair whose total stores, on an IOU when the deployed one is below `10^80`. -/
lemma TotalStores.of_stored_cash {nt : NumericType} {a d : Number} (h : TotalStores nt a d)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat) (a' d' : Number)
    (ha' : a'.isNormalized) (hd' : d'.isNormalized) (ha'0 : 0 ≤ a'.toRat) (hd'0 : 0 ≤ d'.toRat)
    (hst : STAmount.isRounded nt a' = false)
    (hint : nt.isIntegral = true → a'.toRat + d'.toRat ≤ a.toRat + d.toRat)
    (hfrac : nt.isIntegral = false → d'.toRat < 10 ^ 80) : TotalStores nt a' d' := by
  by_cases hi : nt.isIntegral = true
  · exact TotalStores.mono h hasset ha hd ha0 hd0 a' d' ha' hd' ha'0 hd'0 (hint hi)
  · have hfr : nt = .fractional := by
      rcases hasset with rfl | rfl | rfl
      · rfl
      all_goals exact absurd rfl hi
    subst hfr
    have hle := representable_frac_le ((STAmount.isRounded_eq_false_iff _ a' ha' ha'0).mp hst)
    have hd80 := hfrac rfl
    exact TotalStores.of_le _ hasset a' d' ha' hd' ha'0 hd'0 (fun h => absurd h (by decide)) (fun _ => by linarith)

/-- A cash balance the asset stores and a deployed balance store their total: on XRP or an MPT when they sum to at
most the asset's maximum, on an IOU when the deployed one is below `10^80`. -/
lemma TotalStores.of_stored_cash_le (nt : NumericType)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (a' d' : Number)
    (ha' : a'.isNormalized) (hd' : d'.isNormalized) (ha'0 : 0 ≤ a'.toRat) (hd'0 : 0 ≤ d'.toRat)
    (hst : STAmount.isRounded nt a' = false)
    (hint : nt.isIntegral = true → a'.toRat + d'.toRat ≤ nt.maxValue.toNat)
    (hfrac : nt.isIntegral = false → d'.toRat < 10 ^ 80) : TotalStores nt a' d' := by
  refine TotalStores.of_le nt hasset a' d' ha' hd' ha'0 hd'0 hint (fun hi => ?_)
  have hfr : nt = .fractional := by
    rcases hasset with rfl | rfl | rfl
    · rfl
    all_goals exact absurd hi (by decide)
  subst hfr
  have hle := representable_frac_le ((STAmount.isRounded_eq_false_iff _ a' ha' ha'0).mp hst)
  linarith [hfrac rfl]

/-- Whole balances that sum to less than `2^63` and whose total stores sum to at most the maximum of XRP or the
MPT: their sum is exact, so the stored total is the sum itself. -/
lemma TotalStores.whole_le {nt : NumericType} {a d : Number} (h : TotalStores nt a d)
    (hasset : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hi : nt.isIntegral = true)
    (ha : a.isNormalized) (hd : d.isNormalized) (ha0 : 0 ≤ a.toRat) (hd0 : 0 ≤ d.toRat)
    (had : a.toRat.den = 1) (hdd : d.toRat.den = 1) (hlt : a.toRat + d.toRat < 2 ^ 63) :
    a.toRat + d.toRat ≤ nt.maxValue.toNat := by
  obtain ⟨total, hsum, -, -, -, hmax, -⟩ := h.total_lt hasset ha hd ha0 hd0
  have hsd : (a.toRat + d.toRat).den = 1 := Rat.den_one_add _ _ had hdd
  obtain ⟨w, hw, hwv⟩ := Number.exists_of_int (a.toRat + d.toRat) hsd (by linarith) hlt
  have hfloor := Number.add_downward_floor a d total w ha hd ha0 hd0 hsum hw (le_of_eq hwv)
  rw [hwv] at hfloor
  have hlt' : a.toRat + d.toRat < (nt.maxValue.toNat : ℚ) + 1 := lt_of_le_of_lt hfloor (hmax hi)
  exact Rat.le_of_lt_add_one hsd (Rat.den_natCast _) hlt'

end XRPL.Model.SingleAssetVault
