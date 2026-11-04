import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Loan.Common.OrderCreates
import XRPL.Properties.Lending.Loan.Common.YieldValue

/-! # Amounts that fit the asset on a reachable ledger

On a reachable ledger the vault balances, each DebtTotal and each principal are whole numbers of base units.
A loan transaction that passed its checks writes sums below `10^16` units, so the asset stores them exactly. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.create_room Loan.create_units atExponent_of_int open_bound_lt
  from XRPL.Properties.Lending.Loan.Common.OrderCreates

/-- A whole number of base units, at most `10^16` of them, is a value the asset of the vault stores exactly. -/
lemma Vault.representable_of_units (v : Vault) (hasset : Vault.HoldsAsset v) (n : ℕ) (hn : n ≤ 10 ^ 16) :
    STAmount.Representable v.numericType ((n : ℚ) * 10 ^ v.baseExponent) := by
  have hb := Vault.baseExponent_scale_range v
  rcases hasset with h | h | h
  · rw [h]
    rcases lt_or_eq_of_le hn with hlt | heq
    · exact STAmount.representable_fractional_of_units n _ hlt (by omega) (by omega)
    · refine Or.inr ⟨10 ^ 15, v.baseExponent + 1, by norm_num, by norm_num, by omega, by omega, ?_⟩
      rw [heq, zpow_add₀ (by norm_num)]
      push_cast
      ring
  · have hb0 : v.baseExponent = 0 := Vault.baseExponent_integral v (by rw [h]; rfl)
    rw [hb0, zpow_zero, mul_one, h]
    have hmax : (100000000000000000 : UInt64).toNat = 10 ^ 17 := by decide
    exact Or.inr ⟨by decide, n, by rw [hmax]; omega, by omega, rfl⟩
  · have hb0 : v.baseExponent = 0 := Vault.baseExponent_integral v (by rw [h]; rfl)
    rw [hb0, zpow_zero, mul_one, h]
    have hmax : (9223372036854775807 : UInt64).toNat = 2 ^ 63 - 1 := by decide
    exact Or.inr ⟨by decide, n, by rw [hmax]; omega, by omega, rfl⟩

/-- On a reachable ledger a value of `z` base units, from `0` to `10^16` units, is a value the asset stores
exactly. -/
lemma LendingLedger.Reachable.representable {l : LendingLedger} (hr : l.Reachable) (x : ℚ) (z : ℤ)
    (hx : x = (z : ℚ) * 10 ^ l.vault.baseExponent) (h0 : 0 ≤ x)
    (hle : x ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    STAmount.Representable l.vault.numericType x := by
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := le_of_mul_le_mul_right (by rw [zero_mul, ← hx]; exact h0) hp
    exact_mod_cast this
  have hz16 : z ≤ 10 ^ 16 := by
    have : (z : ℚ) ≤ 10 ^ 16 := le_of_mul_le_mul_right (by rw [← hx]; exact hle) hp
    exact_mod_cast this
  have h := Vault.representable_of_units l.vault hr.holdsAsset z.toNat (by omega)
  rwa [show ((z.toNat : ℕ) : ℚ) = (z : ℚ) by exact_mod_cast Int.toNat_of_nonneg hz0, ← hx] at h

/-- A create on a reachable ledger reads its vault and broker on the base grid. Each balance is a whole
number of base units below `10^16`, as the create passed the Open-limit check. -/
lemma LendingLedger.Reachable.createGrid {l : LendingLedger} (hr : l.Reachable) {j : Nat} {broker : LoanBroker}
    (hb : l.broker? j = some broker) {principal : Number} {rates : LoanRates} {fees : LoanFees}
    {schedule : LoanSchedule} {allowsOverpayment pending : Bool} {r : LoanWithPool Vault}
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker l.vault principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    Loan.CreateGrid broker l.vault := by
  obtain ⟨hroom, hyield⟩ := Loan.create_room broker l.vault principal rates fees schedule allowsOverpayment pending
    r hp hpos hst hok
  have hex := l.vault.exact
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := hex.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := hex.assetsDeployed_nonneg
  have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := hex.assetsReserved_nonneg
  have hARD : l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := hex.assetsReserved_le
  have hYU0 : 0 ≤ l.vault.yieldUnrealized.toRat := hex.yieldUnrealized_nonneg
  have hdt := hr.debtInv.debt j broker hb
  have hdtle : broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hdt, hr.debtInv.deployed]; exact l.brokerPrincipal_le j
  have hdt0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  obtain ⟨na, hna⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  rw [← hr.debtInv.deployed] at hnd
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨ny, hny⟩ := hr.yieldGridInv.grid.nat hYU0
  obtain ⟨nt, hnt⟩ := hr.scaleInv.brokerPrincipal_grid j
  exact ⟨atExponent_of_int _ na _ (by rw [hna]; push_cast; ring) hAA0 (by linarith),
    atExponent_of_int _ nd _ (by rw [hnd]; push_cast; ring) hAD0 (by linarith),
    atExponent_of_int _ nr _ (by rw [hnr]; push_cast; ring) hAR0 (by linarith),
    atExponent_of_int _ ny _ (by rw [hny]; push_cast; ring) hYU0 hyield,
    atExponent_of_int _ nt _ (by rw [hdt, hnt]; push_cast; ring) hdt0 (by linarith)⟩

/-- A create on a reachable ledger leaves room. PrincipalRequested is whole base units within AssetsAvailable,
AssetsAvailable plus AssetsDeployed is below `10^16` base units, and DebtTotal is at most AssetsDeployed. -/
private lemma LendingLedger.Reachable.create_room {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {broker : LoanBroker} (hb : l.broker? j = some broker) {principal : Number} {rates : LoanRates}
    {fees : LoanFees} {schedule : LoanSchedule} {allowsOverpayment pending : Bool} {r : LoanWithPool Vault}
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker l.vault principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    (∃ n : ℕ, principal.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent) ∧
      principal.toRat ≤ l.vault.assetsAvailable.toRat ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
  obtain ⟨n, -, hn, -⟩ := Loan.create_units broker l.vault principal rates fees schedule allowsOverpayment pending r
    hp hpos hst (hr.scaleInv.brokers j broker hb) hr.reservedInv.grid hok
  obtain ⟨hroom, -⟩ := Loan.create_room broker l.vault principal rates fees schedule allowsOverpayment pending
    r hp hpos hst hok
  refine ⟨⟨n, hn⟩, (Loan.create_inside_open_zone broker l.vault principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hok).2, hroom, ?_⟩
  rw [hr.debtInv.debt j broker hb, hr.debtInv.deployed]; exact l.brokerPrincipal_le j

/-- On a reachable ledger a create keeps DebtTotal plus PrincipalRequested below `10^16` base units. -/
lemma LendingLedger.Reachable.create_debt_room {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {broker : LoanBroker} (hb : l.broker? j = some broker) {principal : Number} {rates : LoanRates}
    {fees : LoanFees} {schedule : LoanSchedule} {allowsOverpayment pending : Bool} {r : LoanWithPool Vault}
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker l.vault principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    broker.debtTotal.toRat + principal.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
  obtain ⟨-, hfunds, hroom, hdt⟩ := hr.create_room hb hp hpos hst hok
  linarith

/-- What a create writes fits the asset. On a reachable ledger AssetsAvailable less PrincipalRequested,
AssetsReserved plus it and DebtTotal plus it are whole base units below `10^16`. -/
lemma LendingLedger.Reachable.create_fits {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {broker : LoanBroker} (hb : l.broker? j = some broker) {principal : Number} {rates : LoanRates}
    {fees : LoanFees} {schedule : LoanSchedule} {allowsOverpayment pending : Bool} {r : LoanWithPool Vault}
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker l.vault principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    STAmount.Representable l.vault.numericType (l.vault.assetsAvailable.toRat - principal.toRat) ∧
      STAmount.Representable l.vault.numericType (l.vault.assetsReserved.toRat + principal.toRat) ∧
      STAmount.Representable broker.numericType (broker.debtTotal.toRat + principal.toRat) := by
  obtain ⟨⟨n, hn⟩, hfunds, hroom, hdt⟩ := hr.create_room hb hp hpos hst hok
  have hex := l.vault.exact
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := hex.assetsDeployed_nonneg
  have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := hex.assetsReserved_nonneg
  have hARD : l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := hex.assetsReserved_le
  have hdt0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  obtain ⟨na, hna⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨nt, hnt⟩ := hr.scaleInv.brokerPrincipal_grid j
  rw [← hr.debtInv.debt j broker hb] at hnt
  refine ⟨hr.representable _ ((na : ℤ) - n) (by rw [hna, hn]; push_cast; ring) (by linarith) (by linarith),
    hr.representable _ ((nr : ℤ) + n) (by rw [hnr, hn]; push_cast; ring) (by linarith) (by linarith), ?_⟩
  rw [hr.scaleInv.brokers j broker hb]
  exact hr.representable _ ((nt : ℤ) + n) (by rw [hnt, hn]; push_cast; ring) (by linarith) (by linarith)


/-- A list of slots with a single loan on broker `j` sums that loan's principal for `j`. -/
private lemma sum_principalOn_single (j : Nat) (e : LoanEntry) (hj : e.brokerIndex = j) :
    ∀ (xs : List (Option LoanEntry)) (i : Nat), xs[i]? = some (some e) →
      xs.countP (fun o => o.any (·.brokerIndex == j)) = 1 →
      (xs.map (LoanEntry.principalOn j)).sum = e.loan.principalOutstanding.toRat := by
  have hoff : ∀ o : Option LoanEntry, o.any (·.brokerIndex == j) = false → LoanEntry.principalOn j o = 0 := by
    intro o ho
    cases o with
    | none => rfl
    | some e' =>
      simp only [Option.any_some, beq_eq_false_iff_ne] at ho
      simp [LoanEntry.principalOn, ho]
  intro xs
  induction xs with
  | nil => intro i hi; simp at hi
  | cons o os ih =>
    intro i hi hc
    rw [List.countP_cons] at hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have hp : (some e).any (·.brokerIndex == j) = true := by simp [hj]
      rw [if_pos hp] at hc
      have h0 : ∀ o' ∈ os, o'.any (·.brokerIndex == j) = false := by
        intro o' ho'
        have := (List.countP_eq_zero (p := fun o : Option LoanEntry => o.any (·.brokerIndex == j))).mp
          (by omega) o' ho'
        simpa using this
      have hsum : (os.map (LoanEntry.principalOn j)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hx
        exact hoff o' (h0 o' ho')
      rw [List.map_cons, List.sum_cons, hsum, add_zero]
      simp [LoanEntry.principalOn, hj]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      have hpos : 0 < os.countP (fun o => o.any (·.brokerIndex == j)) :=
        List.countP_pos_iff.mpr ⟨some e, List.mem_of_getElem? hi, by simp [hj]⟩
      have ho : o.any (·.brokerIndex == j) = false := by
        cases h : o.any (·.brokerIndex == j)
        · rfl
        · rw [h, if_pos rfl] at hc; omega
      rw [ho] at hc
      rw [List.map_cons, List.sum_cons, hoff o ho, zero_add]
      exact ih k hi (by simpa using hc)

/-- The broker's last loan carries its whole DebtTotal. On a reachable ledger a broker with LoanCount 1
owes just the principal of that loan. -/
lemma LendingLedger.Reachable.lastLoan_debt {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (hlast : loan.broker.loanCount = 1) :
    loan.broker.debtTotal.toRat = loan.principalOutstanding.toRat := by
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  rw [hlb] at hlast ⊢
  rw [hpo, hr.debtInv.debt _ b hb]
  have hc := hr.loanCountInv.counted _ b hb
  rw [hlast] at hc
  obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
  exact sum_principalOn_single e.brokerIndex e rfl l.loans i (by rw [List.getElem?_eq_getElem hi, hei])
    (show l.loansOf e.brokerIndex = 1 by rw [← hc]; rfl)

/-- On a reachable ledger the asset stores AssetsReserved less the principal of a stored pending loan. -/
private lemma LendingLedger.Reachable.reserved_sub_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat}
    {e : LoanEntry} (he : l.loan? i = some e) (hp : e.loan.isPending = true) :
    STAmount.Representable l.vault.numericType
      (l.vault.assetsReserved.toRat - e.loan.principalOutstanding.toRat) := by
  -- AssetsReserved is the sum of the pending principals
  have hle : e.loan.principalOutstanding.toRat ≤ l.vault.assetsReserved.toRat := by
    have := l.principalIf_le_sum (·.isPending) i
    rw [he] at this
    simp only [LoanEntry.principalIf, hp, if_true] at this
    rw [hr.reservedInv.sum]; exact this
  have hp0 : 0 ≤ e.loan.principalOutstanding.toRat := e.loan.exact.principalOutstanding_nonneg
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨mp, hmp⟩ := hr.scaleInv.principal_grid he
  have hbound := hr.reservedInv.bound
  exact hr.representable _ ((nr : ℤ) - mp) (by rw [hnr, hmp]; push_cast; ring) (by linarith) (by linarith)

/-- What an accept on a reachable ledger writes fits the asset. AssetsReserved less the loan's principal,
and YieldUnrealized plus its interest, are whole base units from `0` to `10^16`. -/
lemma LendingLedger.Reachable.accept_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {interestDue : Number} {r : LoanWithPool Vault}
    (hc : loan.canAccept l.vault l.now = .ok .tesSUCCESS) (hi : loan.interestDue = .ok interestDue)
    (hok : (loan.accept l.vault).run = .ok (.ok r)) :
    STAmount.Representable l.vault.numericType (l.vault.assetsReserved.toRat - loan.principalOutstanding.toRat) ∧
      STAmount.Representable l.vault.numericType (l.vault.yieldUnrealized.toRat + interestDue.toRat) := by
  have hls := (hr.loanAt_scale hat).1
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hpend : e.loan.isPending = true := by
    rw [← (congrArg RawLoan.isPending hraw :)]; exact Loan.canAccept_pending loan l.vault l.now hc
  refine ⟨by rw [hpo]; exact hr.reserved_sub_fits he hpend, ?_⟩
  set s := l.vault.baseExponent with hs
  have hp10 : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hbase := Vault.baseExponent_scale_range l.vault
  have hsb : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  obtain ⟨y, hadd, hyg, hyv, hopen, -⟩ := Loan.accept_yieldValue loan l.vault l.now r hc hok
  have hiy : interestDue.toRat = y.toRat := by rw [hyv, Loan.interestDue_toExact loan interestDue hi]
  rw [hiy]
  rw [hls] at hyg
  obtain ⟨hyN, k, hk⟩ := hyg
  obtain ⟨ny, hny⟩ := hr.yieldGridInv.grid.nat l.vault.exact.yieldUnrealized_nonneg
  -- the interest is at least zero, the lawfulness check, so at least minus one unit
  have hk1 : -1 ≤ k := by
    have htol := loan.exact.interest_nonneg
    rw [← hyv] at htol
    have h1 : -(10 : ℚ) ^ s ≤ y.toRat := by linarith
    rw [hk] at h1
    have : ((-1 : ℤ) : ℚ) ≤ k := le_of_mul_le_mul_right (by push_cast; linarith) hp10
    exact_mod_cast this
  have hlim := open_bound_lt s
  have hlt : ((ny : ℤ) + k : ℤ) < 10 ^ 16 := by
    have : (((ny : ℤ) + k : ℤ) : ℚ) * 10 ^ s < 10 ^ 16 * 10 ^ s := by
      push_cast; rw [add_mul, ← hny, ← hk]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp10.le
  have hsum := Number.operator_add_toRat_of_grid _ _ _ ny k s l.vault.wf.yieldUnrealized_norm hyN
    (by rw [hny]; norm_cast) hk ⟨by omega, by omega⟩ hsb hadd
  have hY0 : 0 ≤ r.pool'.yieldUnrealized.toRat := r.pool'.exact.yieldUnrealized_nonneg
  have hval : l.vault.yieldUnrealized.toRat + y.toRat = (((ny : ℤ) + k : ℤ) : ℚ) * 10 ^ s := by
    rw [hny, hk]; push_cast; ring
  exact hr.representable _ ((ny : ℤ) + k) hval (by rw [hval, ← hsum]; exact hY0) (by linarith)

/-- What a pending delete on a reachable ledger writes fits the asset, AssetsAvailable aside. The asset
stores PrincipalOutstanding and AssetsReserved, AssetsDeployed and DebtTotal less it. -/
lemma LendingLedger.Reachable.deletePending_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (hp : loan.isPending = true) :
    STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false ∧
      STAmount.Representable l.vault.numericType (l.vault.assetsReserved.toRat - loan.principalOutstanding.toRat) ∧
      STAmount.Representable l.vault.numericType (l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat) ∧
      STAmount.Representable loan.broker.numericType
        (loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat) := by
  have hnt := (hr.loanAt_scale hat).2
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  have hlb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hpend : e.loan.isPending = true := by rw [← (congrArg RawLoan.isPending hraw :)]; exact hp
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨mp, hmp⟩ := hr.scaleInv.principal_grid he
  rw [← hpo] at hmp
  -- AssetsDeployed is the sum of all principals, DebtTotal the sum of the broker's
  have hdeployed := hr.debtInv.deployed
  have hAD : loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
    have := l.principalIf_le_sum (fun _ => true) i
    rw [he] at this
    simp only [LoanEntry.principalIf, if_true] at this
    rw [hdeployed, hpo]; exact this
  have hdt := hr.debtInv.debt _ b hb
  have hDT : loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat := by
    have := l.principalOn_le_sum e.brokerIndex i
    rw [he] at this
    simp only [LoanEntry.principalOn, if_true] at this
    rw [hlb, hdt, hpo]; exact this
  have hDTle : loan.broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hlb, hdt, hdeployed]; exact l.brokerPrincipal_le _
  have hbound := hr.lossInv.deployed
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  rw [← hdeployed] at hnd
  obtain ⟨nt, hnt'⟩ := hr.scaleInv.brokerPrincipal_grid e.brokerIndex
  rw [← hdt, ← hlb] at hnt'
  refine ⟨?_, by rw [hpo]; exact hr.reserved_sub_fits he hpend,
    hr.representable _ ((nd : ℤ) - mp) (by rw [hnd, hmp]; push_cast; ring) (by linarith) (by linarith), ?_⟩
  · rw [hnt]
    refine (STAmount.isRounded_eq_false_iff _ _ loan.wf.principalOutstanding_norm hp0).mpr ?_
    rw [hpo]; exact hr.reservedInv.exact i e he hpend
  · rw [hnt]
    exact hr.representable _ ((nt : ℤ) - mp) (by rw [hnt', hmp]; push_cast; ring) (by linarith) (by linarith)

end XRPL.Model.Lending
