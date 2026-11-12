import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits
import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness

/-! # Cover deposit, withdrawal and clawback

What the three cover transactions share: the direction CoverAvailable moves, the minimum cover, success once the
checks pass, and taking all of the cover. Then cover transactions in sequence on a reachable broker: undoing one,
splitting one in two, and swapping two. Each one moves CoverAvailable by whole base units, so nothing else rounds
along the way. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Cover transaction on any lawful broker -> deposit gives CoverAvailable' ≥ CoverAvailable, withdrawal and clawback
give CoverAvailable' ≤ CoverAvailable. -/
theorem LoanBroker.cover_direction (lb : LoanBroker) :
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      (lb.coverDeposit pool amount).run = .ok (.ok res) →
      amount.Canonical → -- a transaction amount is a canonical amount
      0 ≤ amount.toRat →
      -- the vault's base exponent is in the IOU exponent range
      (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      (lb.coverWithdraw pool amount).run = .ok (.ok res) →
      amount.Canonical → -- a transaction amount is a canonical amount
      -- the vault's base exponent is in the IOU exponent range
      (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable) ∧
    ∀ {α : Type} [AssetPool α] (pool : α) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      (lb.coverClawback pool amount).run = .ok (.ok res) →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      -- the vault's base exponent is in the IOU exponent range
      (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  ⟨fun pool amount res hok hc hnn hb => LoanBroker.coverDeposit_increases_cover_proof lb pool amount res hok hc hnn hb,
    fun pool amount res hok hc hb => LoanBroker.coverWithdraw_decreases_cover_proof lb pool amount res hok hc hb,
    fun pool amount res hok hmax hb => LoanBroker.coverClawback_decreases_cover_proof lb pool amount res hok hmax hb⟩

/-- Cover transaction on any lawful broker -> CoverAvailable' ≥ minCover after a deposit from CoverAvailable ≥ minCover,
after a withdrawal, and after a clawback. -/
theorem LoanBroker.cover_keeps_minimum (lb : LoanBroker) :
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      (lb.coverDeposit pool amount).run = .ok (.ok res) →
      amount.Canonical → -- a transaction amount is a canonical amount
      0 ≤ amount.toRat →
      -- the vault's base exponent is in the IOU exponent range
      (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      ∀ e : Int, lb.HasMinimumCover e → res.loanBroker'.HasMinimumCover e) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS → (lb.coverWithdraw pool amount).run = .ok (.ok res) →
      res.loanBroker'.HasMinimumCover (AssetPool.baseExponent pool)) ∧
    ∀ (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult) (minimumCover : Number),
      -- CoverAvailable is whole base units, as on every reachable broker, and is not coarsened
      lb.CoverFits v.baseExponent →
      v.numericType = lb.numericType →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) →
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover →
      (lb.coverClawback v amount).run = .ok (.ok res) →
      minimumCover.toRat ≤ res.loanBroker'.toExact.coverAvailable :=
  ⟨fun pool amount res hok hc hnn hb e hmin =>
      LoanBroker.coverDeposit_keeps_minimum_proof lb pool amount res e hok hc hnn hb hmin,
    fun pool amount res hcan hok => LoanBroker.coverWithdraw_keeps_minimum_proof lb pool amount res hcan hok,
    fun v amount res minimumCover hf hnt hmax hreq hmin hok =>
      LoanBroker.coverClawback_keeps_minimum_proof lb v amount res minimumCover hf hnt hmax hreq hmin hok⟩

/-- Witness: a run on a coarsened cover where a clawback leaves CoverAvailable' < minCover. A LoanPay fee takes the
cover to `2000001` at the scale `10^-10`, and a full clawback leaves `500.1`, below minCover `500.1000000001`. -/
theorem LoanBroker.cover_keeps_minimum_clawback_attained :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (lb.coverClawback l.vault amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat :=
  LoanBroker.coverClawback_keeps_minimum_witness

/-- Cover transaction on any lawful broker that passes its checks -> it succeeds, deposit and withdrawal with
roundedAmount, clawback with clawAmount. -/
theorem LoanBroker.cover_total (lb : LoanBroker) :
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount),
      amount.Canonical → -- a transaction amount is a canonical amount
      0 ≤ amount.toRat →
      -- the vault's base exponent is in the IOU exponent range
      (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      lb.canCoverDeposit pool amount = .ok .tesSUCCESS →
      ∃ r res, (lb.roundedCoverAmount pool amount).run = .ok (.ok r) ∧
        (lb.coverDeposit pool amount).run = .ok (.ok res) ∧ res.amount' = r) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS →
      ∃ a res, clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a ∧
        (lb.coverWithdraw pool amount).run = .ok (.ok res) ∧ res.amount' = a) ∧
    -- CoverAvailable is whole base units, as on every reachable broker, and is not coarsened, and the asset's
    -- maximum fits an int64 amount, as C++ caps every MPT maximum
    ∀ (v : Vault) (amount : Option STAmount), lb.CoverFits v.baseExponent → v.numericType = lb.numericType →
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) →
      lb.canCoverClawback v amount = .ok .tesSUCCESS →
      ∃ c res, (lb.roundedCoverClawback v amount).run = .ok (.ok c) ∧
        (lb.coverClawback v amount).run = .ok (.ok res) ∧ res.amount' = c :=
  ⟨fun pool amount hc hnn hb hcan => LoanBroker.coverDeposit_total_proof lb pool amount hc hnn hb hcan,
    fun pool amount hcan => LoanBroker.coverWithdraw_total_proof lb pool amount hcan,
    fun v amount hf hnt hmax hreq hcan => LoanBroker.coverClawback_lawful_total_proof lb v amount hf hnt hmax hreq hcan⟩

/-- Witness: a run on a coarsened cover where a clawback that passes its checks fails. A default leaves no debt and
a cover of `1999999.9999999999`, and a full clawback rounds the claw up to `2000000`, above the cover. -/
theorem LoanBroker.cover_total_clawback_attained :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      lb.canCoverClawback l.vault amount = .ok .tesSUCCESS ∧
      (lb.coverClawback l.vault amount).run = .error .notLawful :=
  LoanBroker.coverClawback_lawful_total_witness

/-- Every reachable broker -> when CoverAvailable + 1 base unit ≤ the Open limit a deposit can give CoverAvailable' >
CoverAvailable, and when CoverAvailable ≠ 0 a withdrawal, or a clawback of an IOU or MPT, can take all of it. -/
theorem LoanBroker.cover_possible (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) :
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum. CoverAvailable + 1 base unit is within
    -- the Open limit, and for MPT within MaximumAmount, so a holder can still have a unit to deposit. The asset
    -- accepts whole amounts (offset 0), as XRP, MPT and IOU do
    ((lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) →
      lb.toExact.coverAvailable + 10 ^ base ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ base →
      (lb.numericType ≠ .native → lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + 1 ≤ lb.numericType.maxValue.toNat) →
      (0 : Int) ≤ lb.numericType.maxOffset →
      ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
        amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
          lb.canCoverDeposit v amount = .ok .tesSUCCESS ∧ (lb.coverDeposit v amount).run = .ok (.ok res) ∧
          lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable) ∧
    (lb.toExact.coverAvailable ≠ 0 →
      ∃ (s : STAmount) (res : LoanBrokerCoverResult),
        s.Canonical ∧ s.mNumericType = lb.numericType ∧ s.toRat = lb.toExact.coverAvailable ∧
          lb.canCoverWithdraw v s = .ok .tesSUCCESS ∧ (lb.coverWithdraw v s).run = .ok (.ok res) ∧
          res.loanBroker'.toExact.coverAvailable = 0) ∧
    (lb.toExact.coverAvailable ≠ 0 →
      lb.numericType ≠ .native → -- C++ rejects any clawback of XRP, which has no issuer
      (lb.canCoverClawback v none = .ok .tesSUCCESS ∧
        ∃ res, (lb.coverClawback v none).run = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0) ∧
      ∃ (s : STAmount) (res : LoanBrokerCoverResult),
        s.Canonical ∧ s.mNumericType = lb.numericType ∧ s.toRat = lb.toExact.coverAvailable ∧
          lb.canCoverClawback v (some s) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some s)).run = .ok (.ok res) ∧
          res.loanBroker'.toExact.coverAvailable = 0) :=
  ⟨fun hmax hroom hmpt hmaxoff =>
      -- for XRP the Open limit, `9·10^15` drops, is below the `10^17` drops that exist
      have hone : lb.numericType.isIntegral = true →
          lb.toExact.coverAvailable + 1 ≤ lb.numericType.maxValue.toNat := by
        intro hi
        by_cases hx : lb.numericType = .native
        · have h1 : (10 : ℚ) ^ base ≤ 1 :=
            zpow_le_one_of_nonpos₀ (by norm_num) (by rw [← hvb]; exact v.baseExponent_bounds.2.1)
          have h0 : (0 : ℚ) < 10 ^ base := zpow_pos (by norm_num) _
          have hxrp : NumericType.native.maxValue.toNat = 100000000000000000 := rfl
          rw [hx, hxrp]
          push_cast
          linarith
        · exact hmpt hx hi
      LoanBroker.coverDeposit_increase_possible_proof lb base hr hmax v hvb hnt hroom hone hmaxoff,
    fun hnz =>
      have hpos : 0 < lb.toExact.coverAvailable := lt_of_le_of_ne lb.exact.coverAvailable_nonneg (Ne.symm hnz)
      LoanBroker.coverWithdraw_all_proof lb base hr (LoanBroker.Reachable.maxValue_fits lb base hr hpos) v hvb hnt
        hpos,
    fun hnz hxrp =>
      have hpos : 0 < lb.toExact.coverAvailable := lt_of_le_of_ne lb.exact.coverAvailable_nonneg (Ne.symm hnz)
      LoanBroker.coverClawback_all_proof lb base hr (LoanBroker.Reachable.maxValue_fits lb base hr hpos) v hvb hnt
        hxrp hpos⟩

/-- Cover transaction then the opposite one for its amount -> CoverAvailable is restored, and after a deposit the
withdrawal, or the clawback of an IOU or MPT with clawAmount = roundedAmount, passes its checks. -/
theorem LoanBroker.cover_restores (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) :
    (∀ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      -- an XRP or MPT holding never exceeds the asset's maximum amount
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.loanBroker'.canCoverWithdraw v res.amount' = .ok .tesSUCCESS ∧
      -- the credited amount is then withdrawn
      (∀ res' : LoanBrokerCoverResult, (res.loanBroker'.coverWithdraw v res.amount').run = .ok (.ok res') →
        res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable)) ∧
    (∀ (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.numericType ≠ .native → -- C++ rejects any clawback of XRP, which has no issuer
      amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      -- an XRP or MPT holding never exceeds the asset's maximum amount
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      (∃ claw : STAmount, (res.loanBroker'.roundedCoverClawback v (some res.amount')).run = .ok (.ok claw) ∧
        claw.toRat = res.amount'.toRat ∧ res.loanBroker'.canCoverClawback v (some res.amount') = .ok .tesSUCCESS) ∧
      -- the credited amount is then clawed back
      (∀ res' : LoanBrokerCoverResult, (res.loanBroker'.coverClawback v (some res.amount')).run = .ok (.ok res') →
        res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable)) ∧
    (∀ (amount : STAmount) (res res' : LoanBrokerCoverResult),
      amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS → (lb.coverWithdraw v amount).run = .ok (.ok res) →
      -- the paid-out amount is then deposited back
      (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res') →
      res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable) ∧
    ∀ (amount : Option STAmount) (res res' : LoanBrokerCoverResult),
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) →
      lb.canCoverClawback v amount = .ok .tesSUCCESS → (lb.coverClawback v amount).run = .ok (.ok res) →
      -- the clawed amount is then deposited back
      (res.loanBroker'.coverDeposit v res.amount').run = .ok (.ok res') →
      res'.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable :=
  ⟨fun amount res hc hat hpos hcap hcan hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
      ⟨LoanBroker.coverDeposit_withdrawable_proof lb base hr hmax v hvb hnt amount hc hat hpos hcap hcan res hok,
        fun res' hwd => LoanBroker.coverDeposit_coverWithdraw_restores_proof lb base hr hmax v hvb hnt amount hc hat
          hpos hcap hcan res res' hok hwd⟩,
    fun amount res hxrp hc hat hpos hcap hcan hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
      ⟨LoanBroker.coverDeposit_clawable_proof lb base hr hmax v hvb hnt hxrp amount hc hat hpos hcap hcan res hok,
        fun res' hclaw => LoanBroker.coverDeposit_coverClawback_restores_proof lb base hr hmax v hvb hnt hxrp amount
          hc hat hpos hcap hcan res res' hok hclaw⟩,
    fun amount res res' hc hat hpos hcan hok hdep =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
      LoanBroker.coverWithdraw_coverDeposit_restores_proof lb base hr hmax v hvb hnt amount hc hat hpos hcan
        res res' hok hdep,
    fun amount res res' hreq hcan hok hdep =>
      have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
      LoanBroker.coverClawback_coverDeposit_restores_proof lb base hr hmax v hvb hnt amount hreq hcan
        res res' hok hdep⟩

/-- Two cover deposits, two withdrawals or two clawbacks, of whole base units -> the same CoverAvailable' as one of
their sum. -/
theorem LoanBroker.cover_split (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) :
    (∀ (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → c.Canonical →
      a.mNumericType = lb.numericType → b.mNumericType = lb.numericType → c.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat → c.toRat = a.toRat + b.toRat →
      -- both parts are whole base units of the vault
      (∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) → (∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base) →
      -- `a` then `b`, an XRP or MPT holding never exceeds the asset's maximum amount
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v a = .ok .tesSUCCESS → (lb.coverDeposit v a).run = .ok (.ok r1) →
      (lb.numericType.isIntegral = true →
        r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) →
      r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS →
      (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2) →
      -- `c` at once
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v c = .ok .tesSUCCESS → (lb.coverDeposit v c).run = .ok (.ok s) →
      r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable) ∧
    (∀ (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → c.Canonical →
      a.mNumericType = lb.numericType → b.mNumericType = lb.numericType → c.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat → c.toRat = a.toRat + b.toRat →
      -- both parts are whole base units of the vault
      (∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) → (∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base) →
      -- `a` then `b`
      lb.canCoverWithdraw v a = .ok .tesSUCCESS → (lb.coverWithdraw v a).run = .ok (.ok r1) →
      r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS →
      (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2) →
      -- `c` at once
      lb.canCoverWithdraw v c = .ok .tesSUCCESS → (lb.coverWithdraw v c).run = .ok (.ok s) →
      r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable) ∧
    ∀ (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → c.Canonical →
      a.mNumericType = lb.numericType → b.mNumericType = lb.numericType → c.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat → c.toRat = a.toRat + b.toRat →
      -- both parts are whole base units of the vault
      (∃ k : ℕ, a.toRat = (k : ℚ) * 10 ^ base) → (∃ k : ℕ, b.toRat = (k : ℚ) * 10 ^ base) →
      -- `a` then `b`
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS →
      (lb.coverClawback v (some a)).run = .ok (.ok r1) →
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS →
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) →
      -- `c` at once
      lb.canCoverClawback v (some c) = .ok .tesSUCCESS →
      (lb.coverClawback v (some c)).run = .ok (.ok s) →
      r2.loanBroker'.toExact.coverAvailable = s.loanBroker'.toExact.coverAvailable :=
  ⟨fun a b c r1 r2 s hca hcb hcc hat hbt hct hpa hpb hsum hga hgb hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverDeposit_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb hsum
        hga hgb r1 r2 s hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3,
    fun a b c r1 r2 s hca hcb hcc hat hbt hct hpa hpb hsum hga hgb hcan1 h1 hcan2 h2 hcan3 h3 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverWithdraw_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb hsum
        hga hgb r1 r2 s hcan1 h1 hcan2 h2 hcan3 h3,
    fun a b c r1 r2 s hca hcb hcc hat hbt hct hpa hpb hsum hga hgb hcan1 h1 hcan2 h2 hcan3 h3 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverClawback_split_proof lb base hr hmax v hvb hnt a b c hca hcb hcc hat hbt hct hpa hpb
        hsum hga hgb r1 r2 s hcan1 h1 hcan2 h2 hcan3 h3⟩

/-- Witness: a run where two deposits of `1.5` base units give a different CoverAvailable' than one of `3`. Each of
the two is credited one base unit, the single deposit all three. -/
theorem LoanBroker.cover_split_deposit_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v a = .ok .tesSUCCESS ∧ (lb.coverDeposit v a).run = .ok (.ok r1) ∧
      (lb.numericType.isIntegral = true →
        r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) ∧
      r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2) ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v c = .ok .tesSUCCESS ∧ (lb.coverDeposit v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_split_witness

/-- Witness: a run where two withdrawals of `1.5` base units give a different CoverAvailable' than one of `3`. Each
of the two pays out one base unit, the single withdrawal all three. -/
theorem LoanBroker.cover_split_withdraw_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverWithdraw v a = .ok .tesSUCCESS ∧ (lb.coverWithdraw v a).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2) ∧
      lb.canCoverWithdraw v c = .ok .tesSUCCESS ∧ (lb.coverWithdraw v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_split_witness

/-- Witness: a run where two clawbacks of `1.5` base units give a different CoverAvailable' than one of `3`. Each
of the two takes one base unit, the single clawback all three. -/
theorem LoanBroker.cover_split_clawback_attained :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧ v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some a)).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) ∧
      lb.canCoverClawback v (some c) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some c)).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverClawback_split_witness

/-- Two cover deposits, two withdrawals or two clawbacks -> the same CoverAvailable' in either order. -/
theorem LoanBroker.cover_comm (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) :
    (∀ (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → a.mNumericType = lb.numericType → b.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat →
      -- `a` then `b`, an XRP or MPT holding never exceeds the asset's maximum amount
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v a = .ok .tesSUCCESS → (lb.coverDeposit v a).run = .ok (.ok r1) →
      (lb.numericType.isIntegral = true →
        r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) →
      r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS →
      (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2) →
      -- `b` then `a`
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v b = .ok .tesSUCCESS → (lb.coverDeposit v b).run = .ok (.ok s1) →
      (lb.numericType.isIntegral = true →
        s1.loanBroker'.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) →
      s1.loanBroker'.canCoverDeposit v a = .ok .tesSUCCESS →
      (s1.loanBroker'.coverDeposit v a).run = .ok (.ok s2) →
      r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable) ∧
    (∀ (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → a.mNumericType = lb.numericType → b.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat →
      -- `a` then `b`
      lb.canCoverWithdraw v a = .ok .tesSUCCESS → (lb.coverWithdraw v a).run = .ok (.ok r1) →
      r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS →
      (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2) →
      -- `b` then `a`
      lb.canCoverWithdraw v b = .ok .tesSUCCESS → (lb.coverWithdraw v b).run = .ok (.ok s1) →
      s1.loanBroker'.canCoverWithdraw v a = .ok .tesSUCCESS →
      (s1.loanBroker'.coverWithdraw v a).run = .ok (.ok s2) →
      r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable) ∧
    ∀ (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      a.Canonical → b.Canonical → a.mNumericType = lb.numericType → b.mNumericType = lb.numericType →
      0 < a.toRat → 0 < b.toRat →
      -- `a` then `b`
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS →
      (lb.coverClawback v (some a)).run = .ok (.ok r1) →
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS →
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) →
      -- `b` then `a`
      lb.canCoverClawback v (some b) = .ok .tesSUCCESS →
      (lb.coverClawback v (some b)).run = .ok (.ok s1) →
      s1.loanBroker'.canCoverClawback v (some a) = .ok .tesSUCCESS →
      (s1.loanBroker'.coverClawback v (some a)).run = .ok (.ok s2) →
      r2.loanBroker'.toExact.coverAvailable = s2.loanBroker'.toExact.coverAvailable :=
  ⟨fun a b r1 r2 s1 s2 hca hcb hat hbt hpa hpb hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3 hcap4 hcan4 h4 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverDeposit_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
        hcap1 hcan1 h1 hcap2 hcan2 h2 hcap3 hcan3 h3 hcap4 hcan4 h4,
    fun a b r1 r2 s1 s2 hca hcb hat hbt hpa hpb hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverWithdraw_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
        hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4,
    fun a b r1 r2 s1 s2 hca hcb hat hbt hpa hpb hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4 =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb a hca hat
      LoanBroker.coverClawback_comm_proof lb base hr hmax v hvb hnt a b hca hcb hat hbt hpa hpb r1 r2 s1 s2
        hcan1 h1 hcan2 h2 hcan3 h3 hcan4 h4⟩

end XRPL.Model.Lending
