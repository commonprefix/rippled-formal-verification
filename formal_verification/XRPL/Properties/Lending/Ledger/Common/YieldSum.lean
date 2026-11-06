import XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps
import XRPL.Properties.Lending.Loan.Common.VaultOwed

/-! # YieldUnrealized is the interest of the active loans

AssetsDeployed + YieldUnrealized stays at most the Open limit: LoanSet and LoanAccept pass the Open-limit check, and
no other transaction raises what the loans owe the vault. So every update of YieldUnrealized is exact. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Vault.assetsTotal_eq_of_grid Vault.assetsTotal_bounds
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private Loan.canAccept_open from XRPL.Properties.Lending.Loan.Common.YieldValue
open private LendingLedger.Genesis.empty from XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps

/-- interestDue of a slot's loan when `p` selects it, else zero. -/
def LoanEntry.interestIf (p : Loan → Bool) : Option LoanEntry → ℚ
  | some e => if p e.loan then e.loan.toExact.interestDue else 0
  | none => 0

/-- Σ interestDue of the stored loans that `p` selects. -/
def LendingLedger.interestSum (l : LendingLedger) (p : Loan → Bool) : ℚ :=
  (l.loans.map (LoanEntry.interestIf p)).sum

/-- A loan effect changes the sum by its slot. -/
lemma LendingLedger.interestSum_commitLoan (l : LendingLedger) (u : LoanEffect) (p : Loan → Bool) :
    (l.commitLoan u).interestSum p + LoanEntry.interestIf p (l.loan? u.loanIndex) =
      l.interestSum p + LoanEntry.interestIf p u.loan :=
  List.sum_map_storeSlot (LoanEntry.interestIf p) rfl l.loans u.loanIndex u.loan

/-- A ledger with the same loans has the same sums. -/
lemma LendingLedger.interestSum_of_loans {l l' : LendingLedger} (h : l'.loans = l.loans) (p : Loan → Bool) :
    l'.interestSum p = l.interestSum p := by
  unfold LendingLedger.interestSum; rw [h]

/-- No stored loan selected -> the sum is zero. -/
lemma LendingLedger.interestSum_eq_zero (l : LendingLedger) (p : Loan → Bool)
    (h : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → p e.loan = false) : l.interestSum p = 0 := by
  unfold LendingLedger.interestSum
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  cases o with
  | none => rfl
  | some e =>
    obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem ho
    have he : l.loan? j = some e := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_getElem hj, hjo]; rfl
    simp [LoanEntry.interestIf, h j e he]

/-- On a reachable ledger every slot adds at least zero, because a reachable loan's interestDue is never
negative. -/
private lemma LendingLedger.Reachable.interestIf_nonneg {l : LendingLedger} (hr : l.Reachable) (p : Loan → Bool)
    (o : Option LoanEntry) (ho : o ∈ l.loans) : 0 ≤ LoanEntry.interestIf p o := by
  cases o with
  | none => exact le_refl _
  | some e =>
    obtain ⟨s, hs⟩ := hr.loansInv
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ho
    have he : l.loan? j = some e := by unfold LendingLedger.loan?; rw [hj]; rfl
    obtain ⟨t, -, hrl⟩ := hs.reachable j e he
    simp only [LoanEntry.interestIf]
    split
    · exact Loan.Reachable.interestDue_nonneg hrl
    · exact le_refl _

/-- One slot of a reachable ledger adds at least zero and at most the whole sum. -/
lemma LendingLedger.Reachable.interestIf_le_sum {l : LendingLedger} (hr : l.Reachable) (p : Loan → Bool) (i : Nat) :
    0 ≤ LoanEntry.interestIf p (l.loan? i) ∧ LoanEntry.interestIf p (l.loan? i) ≤ l.interestSum p := by
  have hnn : ∀ x ∈ l.loans.map (LoanEntry.interestIf p), 0 ≤ x := fun _ hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact hr.interestIf_nonneg p o ho
  unfold LendingLedger.loan? LendingLedger.interestSum
  cases h : l.loans[i]? with
  | none => exact ⟨le_refl _, List.sum_nonneg hnn⟩
  | some o =>
    exact ⟨hr.interestIf_nonneg p o (List.mem_of_getElem? h),
      List.single_le_sum hnn _ (List.mem_map_of_mem (List.mem_of_getElem? h))⟩

/-- When the Open-limit check passes for a nonnegative amount `x` on the base grid, AssetsAvailable + AssetsDeployed +
YieldUnrealized + `x` is at most the Open limit. A passing check already rules out a coarsened vault. -/
lemma Vault.exceedsOpenLimit_false_sum (v : Vault) (x : Number) (hv : Vault.OnBaseGrid v)
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized) (hx : Number.OnGrid v.baseExponent x)
    (hx0 : 0 ≤ x.toRat) (h : v.exceedsOpenLimit x = .ok false) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat + x.toRat ≤
      9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  have hbase := Vault.baseExponent_scale_range v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  obtain ⟨atot, hat⟩ := Vault.assetsTotal_of_exceedsOpenLimit v _ _ h
  have hopen := (Vault.exceedsOpenLimit_false_bound v x hx.1 h).2.2 atot hat
  -- a sum of `10^16` base units or more would give a computed total above what the check let through
  have hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent) := by
    have h2 : (10 : ℚ) ^ (v.baseExponent - 1) = 10 ^ v.baseExponent / 10 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 16 + 5) (v.baseExponent - 1)
      (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
    have hle := Vault.assetsTotal_ge_of_le v atot hat w hw (by
      rw [hwv, h2, open_line_eq] at *
      push_cast
      nlinarith)
    rw [hwv, h2] at hle
    rw [h2] at hopen
    push_cast at hle hopen
    linarith
  have hatv := Vault.assetsTotal_eq_of_grid v atot hv hS hat
  obtain ⟨hatn, -, -⟩ := Vault.assetsTotal_bounds v atot hat
  obtain ⟨⟨-, a, ha⟩, ⟨-, d, hd⟩⟩ := hv
  have hb := Vault.exceedsOpenLimit_false_total v x atot hx.1 hx0 hat hatn
    (by rw [hatv]; linarith)
    ⟨a + d, by rw [hatv, ha, hd]; push_cast; ring⟩ hYg.2 hx.2 h
  rw [hatv] at hb
  exact hb

/-- A new loan stays inside the Open zone. AssetsDeployed gains the principal, which AssetsAvailable covers,
and YieldUnrealized at most the interest the Open-limit check read. -/
private lemma Loan.create_open_bound (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithPool Vault)
    (hv : Vault.OnBaseGrid v) (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    v.assetsDeployed.toRat + principal.toRat + r.pool'.yieldUnrealized.toRat ≤
      9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  have hbase := Vault.baseExponent_scale_range v
  have hsr : minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule ao pending r hp hpos hst hnt h
  obtain ⟨-, -, hPO, -, -⟩ := Loan.create_reserved broker v principal rates fees schedule ao pending r hp hpos hst
    hnt har h
  obtain ⟨-, hfunds⟩ := Loan.create_inside_open_zone broker v principal rates fees schedule ao pending r hp hpos hst h
  obtain ⟨props, loanState, _, principal', broker', aa', ad', lu', ar', yu', hchecks, -, hsums, hpool, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule ao pending r h
  obtain ⟨hiN, hi0⟩ := Loan.create_checkedInterest_nonneg broker v principal rates fees schedule ao pending r props
    loanState _ broker' hp hpos hst h hchecks hl hb
  have hsb := Loan.loanScale_bounds r.loan'
  rw [hls] at hsb
  obtain ⟨ht, hpg, hm⟩ := Loan.outstanding_onGrid r.loan'
  rw [hls] at ht hpg hm
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
    show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
  rw [hTV] at ht
  rw [hMF] at hm
  have hpr : Number.OnGrid v.baseExponent principal := by
    obtain ⟨-, k, hk⟩ := hpg
    exact ⟨hp, k, by rw [← hPO]; exact hk⟩
  have hig : Number.OnGrid v.baseExponent loanState.interestDue := by
    have hs := hchecks.state
    unfold LoanState.build at hs
    obtain ⟨d, hd, hs⟩ := bind_ok_peel _ _ _ hs
    obtain ⟨i, hi, hs⟩ := bind_ok_peel _ _ _ hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst hs
    exact Number.OnGrid.sub (Number.OnGrid.sub ht hpr hsb hd) hm hsb hi
  have hsum := Vault.exceedsOpenLimit_false_sum v _ hv hYg hig hi0 hchecks.open_zone
  have hyu : r.pool'.yieldUnrealized = yu' := by
    rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hpool]
  have hy := hsums.yield
  have hyle : yu'.toRat ≤ v.yieldUnrealized.toRat + loanState.interestDue.toRat := by
    cases pending
    · simp only [Loan.createChange, Bool.false_eq_true, ↓reduceIte] at hy
      have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
      have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
      have h63 : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent < 2 ^ 63 * 10 ^ v.baseExponent :=
        mul_lt_mul_of_pos_right (by norm_num) hp10
      rw [Number.OnGrid.add_exact hYg hig hY0 hi0 (by linarith) hsr hy]
    · simp only [Loan.createChange, ↓reduceIte, Number.operator_add_zero_right, Except.ok.injEq] at hy
      rw [← hy]; linarith
  rw [hyu]
  linarith

/-- An accept stays inside the Open zone. It keeps AssetsDeployed and adds to YieldUnrealized exactly the
interest the Open-limit check read. -/
private lemma Loan.accept_open_bound (loan : Loan) (v : Vault) (t : UInt32) (r : LoanWithPool Vault)
    (hv : Vault.OnBaseGrid v) (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (hls : loan.loanScale = v.baseExponent) (hi0 : 0 ≤ loan.toExact.interestDue)
    (hc : loan.canAccept v t = .ok .tesSUCCESS) (h : (loan.accept v).run = .ok (.ok r)) :
    v.assetsDeployed.toRat + r.pool'.yieldUnrealized.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  have hbase := Vault.baseExponent_scale_range v
  have hsr : minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  obtain ⟨i, hi, ho⟩ := Loan.canAccept_open loan v t hc
  have hig := Loan.interestDue_onGrid loan i hi
  rw [hls] at hig
  obtain ⟨y, hy, hyg, hyv, -, -⟩ := Loan.accept_yieldValue loan v t r hc h
  have hyi : y = i := Number.isNormalized.toRat_inj hyg.1 hig.1 (by rw [hyv, Loan.interestDue_toExact loan i hi])
  subst hyi
  have hy0 : 0 ≤ y.toRat := by rw [hyv]; exact hi0
  have hsum := Vault.exceedsOpenLimit_false_sum v _ hv hYg hig hy0 ho
  have h63 : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent < 2 ^ 63 * 10 ^ v.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hp10
  rw [Number.OnGrid.add_exact hYg hig hY0 hy0 (by linarith) hsr hy]
  linarith

/-- What every reachable ledger keeps about YieldUnrealized: AssetsDeployed + YieldUnrealized is at most the Open
limit, and YieldUnrealized is the sum of interestDue over the active loans. -/
structure LendingLedger.YieldSumInv (l : LendingLedger) : Prop where
  reachable : l.Reachable
  bound : l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat ≤ l.openLimit
  sum : l.vault.yieldUnrealized.toRat = l.interestSum (!·.isPending)

/-- A loan effect keeps the invariant when it moves YieldUnrealized by its slot and stays in the bound. -/
private lemma LendingLedger.YieldSumInv.commitLoan {l : LendingLedger} (hinv : l.YieldSumInv) {u : LoanEffect}
    (hr' : (l.commitLoan u).Reachable) (hs : Vault.KeepsSettings l.vault u.vault)
    (hsum : u.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? u.loanIndex) =
      l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) u.loan)
    (hbound : u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤ l.openLimit) :
    (l.commitLoan u).YieldSumInv := by
  have hc := l.interestSum_commitLoan u (!·.isPending)
  refine ⟨hr', ?_, ?_⟩
  · show u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤
      9 * 10 ^ 15 * (10 : ℚ) ^ u.vault.baseExponent
    rw [hs.baseExponent_eq]; exact hbound
  · show u.vault.yieldUnrealized.toRat = _
    have := hinv.sum
    linarith

/-- A loan effect that does not raise its slot's principal plus interest keeps the bound. AssetsDeployed is the
sum of PrincipalOutstanding on both ledgers. -/
private lemma LendingLedger.YieldSumInv.bound_of_slot {l : LendingLedger} (hinv : l.YieldSumInv) {u : LoanEffect}
    (hr' : (l.commitLoan u).Reachable)
    (hsum : u.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? u.loanIndex) =
      l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) u.loan)
    (hslot : LoanEntry.principalIf (fun _ => true) u.loan + LoanEntry.interestIf (!·.isPending) u.loan ≤
      LoanEntry.principalIf (fun _ => true) (l.loan? u.loanIndex) +
        LoanEntry.interestIf (!·.isPending) (l.loan? u.loanIndex)) :
    u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤ l.openLimit := by
  have hd' : u.vault.assetsDeployed.toRat = (l.commitLoan u).principalSum (fun _ => true) :=
    hr'.debtInv.deployed
  have hd := hinv.reachable.debtInv.deployed
  have hc := l.principalSum_commitLoan u (fun _ => true)
  have := hinv.bound
  linarith

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.YieldSumInv.loan_step {l : LendingLedger} (hinv : l.YieldSumInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u))
    (hr' : (l.commitLoan u).Reachable) : (l.commitLoan u).YieldSumInv := by
  have hr := hinv.reachable
  have hs := l.applyLoan_keepsSettings tx u hu
  have hscale := hr.scaleInv
  have hbase := Vault.baseExponent_scale_range l.vault
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  obtain ⟨hAAg, hADg, -, -, hYg, -⟩ := LendingLedger.base_grid_proof l hr hr.holdsAsset.maxValue_le
  have hv : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hY0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hopen : l.openLimit < 2 ^ 63 * 10 ^ l.vault.baseExponent := by
    unfold LendingLedger.openLimit; exact mul_lt_mul_of_pos_right (by norm_num) hb10
  have hbound := hinv.bound
  have hYlt : l.vault.yieldUnrealized.toRat < 2 ^ 63 * 10 ^ l.vault.baseExponent := by linarith
  -- the Open limit plus half a unit is below `2^63` base units
  have hlim : ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * 10 ^ (l.vault.baseExponent - 1) <
      2 ^ 63 * 10 ^ l.vault.baseExponent := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    push_cast
    nlinarith
  have hdep := hr.debtInv.deployed
  have hdep' : u.vault.assetsDeployed.toRat = (l.commitLoan u).principalSum (fun _ => true) :=
    hr'.debtInv.deployed
  have hcP := l.principalSum_commitLoan u (fun _ => true)
  have hreach : ∀ (i : Nat) (e : LoanEntry) (broker : LoanBroker) (loan : Loan), l.loan? i = some e →
      l.broker? e.brokerIndex = some broker → e.loan.withBroker broker = .ok loan →
      ∃ t, t ≤ l.now ∧ loan.Reachable t := fun i e broker loan he hb hw => by
    obtain ⟨s, hls⟩ := hr.loansInv
    obtain ⟨t, hle, hrl⟩ := hls.reachable i e he
    exact ⟨t, hle, hrl.withBroker (hscale.broker_asset he hb) hw⟩
  have hls : ∀ (i : Nat) (e : LoanEntry) (broker : LoanBroker) (loan : Loan), l.loan? i = some e →
      e.loan.withBroker broker = .ok loan → loan.loanScale = l.vault.baseExponent := fun i e broker loan he hw => by
    rw [show loan.loanScale = e.loan.loanScale from (congrArg RawLoan.loanScale (Loan.withBroker_eq hw) :)]
    exact hscale.loanScale i e he
  have hsame : ∀ (e : LoanEntry) (broker : LoanBroker) (loan : Loan), e.loan.withBroker broker = .ok loan →
      loan.toExact.interestDue = e.loan.toExact.interestDue ∧ loan.isPending = e.loan.isPending ∧
        loan.principalOutstanding = e.loan.principalOutstanding :=
    fun e broker loan hw => by
      have hraw := Loan.withBroker_eq hw
      exact ⟨Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
        (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :),
        (congrArg RawLoan.isPending hraw :), (congrArg RawLoan.principalOutstanding hraw :)⟩
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    have hnt := hscale.brokers i broker hb
    obtain ⟨-, -, hPOr, hpend, -⟩ := Loan.create_reserved broker l.vault principal rates fees _ ao twoStep r hpn
      hpos hst hnt hr.reservedInv.grid hcr
    obtain ⟨y, hadd, hyg, hy0, hyv, hylt⟩ := Loan.create_yieldValue broker l.vault principal rates fees _ ao twoStep
      r hpn hpos hst hnt hr.reservedInv.grid hcr
    have hyv' := Number.OnGrid.add_exact hYg hyg hY0 hy0 (by linarith) hsb hadd
    have hob := Loan.create_open_bound broker l.vault principal rates fees _ ao twoStep r hv hYg
      hr.reservedInv.grid hpn hpos hst hnt hcr
    have hnone : l.loan? l.loans.length = none := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_none (le_refl _)]; rfl
    refine hinv.commitLoan hr' hs ?_ ?_
    · show r.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? l.loans.length) =
        l.vault.yieldUnrealized.toRat +
          LoanEntry.interestIf (!·.isPending) (some { brokerIndex := i, loan := r.loan' })
      rw [hnone, hyv', hyv]
      cases twoStep <;> simp [LoanEntry.interestIf, hpend]
    · rw [hdep']
      have hc' : (l.commitLoan (LoanEffect.ofCreate i l.loans.length r)).principalSum (fun _ => true) =
          l.principalSum (fun _ => true) + principal.toRat := by
        have := hcP
        rw [show (LoanEffect.ofCreate i l.loans.length r).loanIndex = l.loans.length from rfl, hnone,
          show (LoanEffect.ofCreate i l.loans.length r).loan = some { brokerIndex := i, loan := r.loan' } from rfl]
          at this
        simp only [LoanEntry.principalIf, if_true, add_zero] at this
        rw [this, hPOr]
      rw [hc', ← hdep]
      show _ + _ + r.pool'.yieldUnrealized.toRat ≤ _
      exact hob
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hrr, rfl⟩ := l.applyLoan_accept_inv u i hu
    obtain ⟨hint, hpe, hpo⟩ := hsame e broker loan hw
    obtain ⟨t, -, hrl⟩ := hreach i e broker loan he hb hw
    have hep : e.loan.isPending = true := by rw [← hpe]; exact Loan.canAccept_pending loan l.vault l.now hc
    obtain ⟨-, hp', hPO', -⟩ := Loan.accept_reserved loan l.vault r hrr
    obtain ⟨y, hadd, hyg, hyv, hylt, hint'⟩ := Loan.accept_yieldValue loan l.vault l.now r hc hrr
    rw [hls i e broker loan he hw] at hyg
    have hi0 : 0 ≤ loan.toExact.interestDue := Loan.Reachable.interestDue_nonneg hrl
    have hy0 : 0 ≤ y.toRat := by rw [hyv]; exact hi0
    have hyv' := Number.OnGrid.add_exact hYg hyg hY0 hy0 (by linarith) hsb hadd
    have hob := Loan.accept_open_bound loan l.vault l.now r hv hYg (hls i e broker loan he hw) hi0 hc hrr
    refine hinv.commitLoan hr' hs ?_ ?_
    · show r.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? i) =
        l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' })
      rw [he, hyv', hyv]
      simp only [LoanEntry.interestIf, hep, hp', Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        add_zero]
      rw [hint']
    · rw [hdep']
      have hc' : (l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool')).principalSum (fun _ => true) =
          l.principalSum (fun _ => true) := by
        have := hcP
        rw [show (LoanEffect.ofLoan i e r.loan' r.pool').loanIndex = i from rfl, he,
          show (LoanEffect.ofLoan i e r.loan' r.pool').loan = some { e with loan := r.loan' } from rfl] at this
        simp only [LoanEntry.principalIf, if_true] at this
        rw [hPO', hpo] at this
        linarith
      rw [hc', ← hdep]
      exact hob
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hrr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    obtain ⟨hint, hpe, hpo⟩ := hsame e broker loan hw
    obtain ⟨t, -, hrl⟩ := hreach i e broker loan he hb hw
    have hnp := Loan.canManage_not_pending loan action l.now hc
    have hep : e.loan.isPending = false := by rw [← hpe]; exact hnp
    have hp' : r.loan'.isPending = false := by rw [Loan.manage_isPending loan action _ _ r hrr]; exact hnp
    have hold : LoanEntry.interestIf (!·.isPending) (l.loan? i) = loan.toExact.interestDue := by
      rw [he]; simp only [LoanEntry.interestIf, hep, Bool.not_false, ↓reduceIte]; rw [hint]
    have hnew : LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' }) =
        r.loan'.toExact.interestDue := by
      simp only [LoanEntry.interestIf, hp', Bool.not_false, ↓reduceIte]
    have hold' : LoanEntry.principalIf (fun _ => true) (l.loan? i) = loan.principalOutstanding.toRat := by
      rw [he]; simp only [LoanEntry.principalIf, if_true]; rw [hpo]
    have hnew' : LoanEntry.principalIf (fun _ => true) (some { e with loan := r.loan' }) =
        r.loan'.principalOutstanding.toRat := by
      simp only [LoanEntry.principalIf, if_true]
    have hi0 : 0 ≤ loan.toExact.interestDue := Loan.Reachable.interestDue_nonneg hrl
    have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    have hidx : (LoanEffect.ofLoan i e r.loan' r.pool').loanIndex = i := rfl
    have hlo : (LoanEffect.ofLoan i e r.loan' r.pool').loan = some { e with loan := r.loan' } := rfl
    cases action with
    | impair =>
      have hsum : r.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? i) =
          l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' }) := by
        rw [hold, hnew, Loan.manageImpair_yield loan l.vault l.now r hrr,
          Loan.manageImpair_interest loan l.vault l.now r hrr]
      obtain ⟨-, -, -, hPO'⟩ := Loan.manageImpair_lossStep loan l.vault l.now r hrr
      refine hinv.commitLoan hr' hs hsum (hinv.bound_of_slot hr' hsum ?_)
      rw [hidx, hlo, hold, hnew, hold', hnew', hPO', Loan.manageImpair_interest loan l.vault l.now r hrr]
    | unimpair =>
      have hsum : r.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? i) =
          l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' }) := by
        rw [hold, hnew, Loan.manageUnimpair_yield loan l.vault r hrr, Loan.manageUnimpair_interest loan l.vault r hrr]
      obtain ⟨-, -, -, hPO'⟩ := Loan.manageUnimpair_lossStep loan l.vault r hrr
      refine hinv.commitLoan hr' hs hsum (hinv.bound_of_slot hr' hsum ?_)
      rw [hidx, hlo, hold, hnew, hold', hnew', hPO', Loan.manageUnimpair_interest loan l.vault r hrr]
    | default =>
      simp only [Loan.manage] at hrr
      unfold_ter at hrr
      walk_ok
      rename_i rd hd
      obtain ⟨y, hadd, hyg, hyv, hint'⟩ := Loan.manageDefault_yieldValue loan l.vault rd hd
      obtain ⟨-, -, hPO'⟩ := Loan.manageDefault_debtStep loan l.vault rd hd
      rw [hls i e broker loan he hw] at hyg
      have hy0 : 0 ≤ y.toRat := by rw [hyv]; exact hi0
      have hyle : y.toRat ≤ l.vault.yieldUnrealized.toRat := by
        have := (hr.interestIf_le_sum (!·.isPending) i).2
        rw [hold] at this
        rw [hyv, hinv.sum]; exact this
      have hv' := Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.yieldUnrealized_norm hyg.1
        (hYg.nat hY0) (hyg.nat hy0) hyle hYlt hsb hadd
      have hsum : rd.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? i) =
          l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (some { e with loan := rd.loan' }) := by
        rw [hold, hnew, hv', hint', ← hyv]
        ring
      refine hinv.commitLoan hr' hs hsum (hinv.bound_of_slot hr' hsum ?_)
      rw [show (LoanEffect.ofLoan i e rd.loan' rd.pool').loanIndex = i from rfl,
        show (LoanEffect.ofLoan i e rd.loan' rd.pool').loan = some { e with loan := rd.loan' } from rfl, hold, hold',
        hnew, hnew', hPO', hint', Number.toRat_zero]
      linarith
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hrr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    obtain ⟨hint, hpe, hpo⟩ := hsame e broker loan hw
    obtain ⟨t, hle, hrl⟩ := hreach i e broker loan he hb hw
    have hnp := Loan.canPay_not_pending loan paymentType hc
    have hep : e.loan.isPending = false := by rw [← hpe]; exact hnp
    have hp' : r.loan'.isPending = false := by rw [Loan.pay_isPending loan _ _ _ _ r hrr]; exact hnp
    have hrl' := hrl.pay hle paymentType l.vault amount r hc hrr
    have hi0 := Loan.Reachable.interestDue_nonneg hrl
    have hi0' := Loan.Reachable.interestDue_nonneg hrl'
    obtain ⟨y, hadd, hyg, hyv⟩ := Loan.pay_yieldValue loan l.vault paymentType amount l.now r hrr hi0 hi0'
    have hlsc := hls i e broker loan he hw
    rw [hlsc] at hyg
    have howe := Loan.pay_owed_le loan l.vault paymentType amount l.now r (by rw [hlsc]; omega)
      (fun _ => by rw [hlsc]; exact hbase.2) hi0 hrr
    have hold : LoanEntry.interestIf (!·.isPending) (l.loan? i) = loan.toExact.interestDue := by
      rw [he]; simp only [LoanEntry.interestIf, hep, Bool.not_false, ↓reduceIte]; rw [hint]
    have hnew : LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' }) =
        r.loan'.toExact.interestDue := by
      simp only [LoanEntry.interestIf, hp', Bool.not_false, ↓reduceIte]
    have hold' : LoanEntry.principalIf (fun _ => true) (l.loan? i) = loan.principalOutstanding.toRat := by
      rw [he]; simp only [LoanEntry.principalIf, if_true]; rw [hpo]
    have hnew' : LoanEntry.principalIf (fun _ => true) (some { e with loan := r.loan' }) =
        r.loan'.principalOutstanding.toRat := by
      simp only [LoanEntry.principalIf, if_true]
    have hle' : loan.toExact.interestDue ≤ l.vault.yieldUnrealized.toRat := by
      have := (hr.interestIf_le_sum (!·.isPending) i).2
      rw [hold] at this
      rw [hinv.sum]; exact this
    have hPAD : loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
      have := l.principalIf_le_sum (fun _ => true) i
      rw [hold'] at this
      rw [hdep]; exact this
    have hP0' : 0 ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
    -- the new YieldUnrealized is between zero and the Open limit, so the sum is exact
    obtain ⟨hYn, n, hn⟩ := hYg
    obtain ⟨hyn, d, hd⟩ := hyg
    have hnd : 0 ≤ n + d := by
      have : (0 : ℚ) ≤ ((n + d : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        push_cast; rw [add_mul, ← hn, ← hd, hyv]; linarith
      exact_mod_cast nonneg_of_mul_nonneg_left this hb10
    have hn63 : n + d < 2 ^ 63 := by
      have : ((n + d : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        push_cast; rw [add_mul, ← hn, ← hd, hyv]; push_cast at hopen; linarith
      exact_mod_cast lt_of_mul_lt_mul_right this hb10.le
    have hv := Number.operator_add_toRat_of_grid _ _ _ n d _ hYn hyn hn hd ⟨by omega, hn63⟩ hsb hadd
    have hv' : r.pool'.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat + y.toRat := by
      rw [hv, hn, hd]; push_cast; ring
    have hsum : r.pool'.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? i) =
        l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (some { e with loan := r.loan' }) := by
      rw [hold, hnew, hv', hyv]
      ring
    refine hinv.commitLoan hr' hs hsum (hinv.bound_of_slot hr' hsum ?_)
    rw [show (LoanEffect.ofLoan i e r.loan' r.pool').loanIndex = i from rfl,
      show (LoanEffect.ofLoan i e r.loan' r.pool').loan = some { e with loan := r.loan' } from rfl, hold, hold',
      hnew, hnew']
    exact howe
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hrr, hu'⟩ := l.applyLoan_delete_inv u i hu
    obtain ⟨hint, hpe, hpo⟩ := hsame e broker loan hw
    have hvu : u.vault = r.pool' := by rw [hu']
    have hi : u.loanIndex = i := by rw [hu']
    have hlo : u.loan = none := by rw [hu']
    have hY := Loan.delete_yield loan l.vault r hrr
    have hsum : u.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) (l.loan? u.loanIndex) =
        l.vault.yieldUnrealized.toRat + LoanEntry.interestIf (!·.isPending) u.loan := by
      rw [hvu, hi, hlo, he, hY]
      simp only [LoanEntry.interestIf, add_zero]
      cases hp : loan.isPending
      · have hep : e.loan.isPending = false := by rw [← hpe]; exact hp
        rw [if_pos (by rw [hep]; decide), ← hint, Loan.delete_active_interest loan hc hp, add_zero]
      · have hep : e.loan.isPending = true := by rw [← hpe]; exact hp
        rw [if_neg (by rw [hep]; decide), add_zero]
    refine hinv.commitLoan hr' hs hsum (hinv.bound_of_slot hr' hsum ?_)
    have h0 := (hr.interestIf_le_sum (!·.isPending) i).1
    have hP0 : 0 ≤ LoanEntry.principalIf (fun _ => true) (l.loan? i) := by
      rw [he]; simp only [LoanEntry.principalIf, if_true]; exact e.loan.exact.principalOutstanding_nonneg
    rw [hi, hlo, show LoanEntry.principalIf (fun _ => true) none = 0 from rfl,
      show LoanEntry.interestIf (!·.isPending) none = 0 from rfl]
    linarith
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.YieldSumInv.step {l l' : LendingLedger} (hinv : l.YieldSumInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.YieldSumInv := by
  have hr' : l'.Reachable := by
    obtain ⟨g, txs, hg, hreach, -⟩ := hinv.reachable
    exact ⟨g, txs ++ [tx], hg, hreach.step tx h, fun _ _ => trivial⟩
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    refine ⟨hr', ?_, ?_⟩
    · show (l.commitVault u).vault.assetsDeployed.toRat + (l.commitVault u).vault.yieldUnrealized.toRat ≤
        9 * 10 ^ 15 * (10 : ℚ) ^ (l.commitVault u).vault.baseExponent
      rw [hrest.2, hk.assetsDeployed, hk.yieldUnrealized, hbe]
      exact hinv.bound
    · rw [hrest.2, hk.yieldUnrealized, LendingLedger.interestSum_of_loans hrest.1]
      exact hinv.sum
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hr', hinv.bound, hinv.sum⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hpre hu hr'
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hr', hinv.bound, hinv.sum⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hr', hinv.bound, hinv.sum⟩

/-- A genesis ledger has no yield, nothing lent out and no loans. -/
private lemma LendingLedger.Genesis.yieldSumInv {g : LendingLedger} (hg : g.Genesis) : g.YieldSumInv := by
  obtain ⟨-, h2, h3⟩ := LendingLedger.Genesis.empty hg
  refine ⟨⟨g, [], hg, .refl, fun _ h => absurd h List.not_mem_nil⟩, ?_, ?_⟩
  · rw [h2, h3, add_zero]; unfold LendingLedger.openLimit; positivity
  · rw [h3]; unfold LendingLedger.interestSum; rw [hg.no_loans]; rfl

/-- Every reachable ledger keeps the invariant. -/
lemma LendingLedger.Reachable.yieldSumInv {l : LendingLedger} (hr : l.Reachable) : l.YieldSumInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.yieldSumInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- Proof body of the YieldUnrealized line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.yield_scheduled_proof (l : LendingLedger) (hr : l.Reachable) :
    l.vault.yieldUnrealized.toRat = l.interestSum (!·.isPending) :=
  hr.yieldSumInv.sum

/-- On a reachable ledger AssetsDeployed + YieldUnrealized is at most the Open limit. -/
lemma LendingLedger.Reachable.deployed_yield_le {l : LendingLedger} (hr : l.Reachable) :
    l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat ≤ l.openLimit :=
  hr.yieldSumInv.bound

/-- On a reachable ledger YieldUnrealized is below `10^16` base units. -/
lemma LendingLedger.Reachable.yield_lt {l : LendingLedger} (hr : l.Reachable) :
    l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
  have h := hr.deployed_yield_le
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  unfold LendingLedger.openLimit at h
  nlinarith

/-- On a reachable ledger an active stored loan's interestDue is at most YieldUnrealized. -/
lemma LendingLedger.Reachable.interest_le_yield {l : LendingLedger} (hr : l.Reachable) {i : Nat} {e : LoanEntry}
    (he : l.loan? i = some e) (hp : e.loan.isPending = false) :
    e.loan.toExact.interestDue ≤ l.vault.yieldUnrealized.toRat := by
  have := (hr.interestIf_le_sum (!·.isPending) i).2
  rw [he] at this
  simp only [LoanEntry.interestIf, hp, Bool.not_false, ↓reduceIte] at this
  rw [hr.yieldSumInv.sum]
  exact this

end XRPL.Model.Lending
