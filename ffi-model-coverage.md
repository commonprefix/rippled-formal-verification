# Lean model and C++ coverage by the FFI tests

Measured 2026-10-21 in `rfv-ffi` on the transaction model (`XRPL/Model/Vault`, `XRPL/Model/Lending`,
`XRPL/Model/Lending1_1`) under the 14 FFI transaction suites (`LeanVault*`, `LeanLoanBroker*`, `LeanLoan*`).
The protocol layer (`Number`, `STAmount`, rounding) is fuzzed by its own suites and is not measured here.

**Result: 210 of 261 branch arms hit (80.5%); 36 of 38 do-blocks
entered** (re-measured 2026-11-04 on the model rebased onto #52, after the overpayment search below and the C++-guided cases). The pass started at
166/258 (64.3%); every arm reachable through a transaction is now exercised.
The 51 arms still unhit are classified below: none of them can be reached by a transaction under the
current amendments, or they are numeric corner cases the capping logic prevents.

## Method

Lean has no coverage tooling, so `lean-coverage/instrument.py` rewrites a scratch copy of the model: every branch
arm (`if`/`else` arms, `match` arms, `let … | alt` early exits) gets a `dbgTrace "COV n"` marker, as a statement
in do-blocks, as an expression wrapper elsewhere, and as a block wrapper for pure multi-line arms; a `:= do`
header gets an "entry" marker. The scratch tree is built with `lake build XRPLModel:static`, a scratch
`xrpld-cov` is linked against that archive with the real link line (regenerated from `link.txt` after every
test-file change, since it lists the object files), the suites run on it, and `lean-coverage/report.py` matches
the markers on stderr against the manifest. Line numbers refer to the unmodified model files. Known blind spot:
an inline `if` nested inside a one-line match arm counts as one arm.

```bash
S=/tmp/lean-cov; rm -rf $S/fv; cp -a formal_verification $S/fv; rm $S/fv/.lake/build/lib/libXRPL_XRPLModel.a
python3 lean-coverage/instrument.py $S/fv            # writes $S/fv/cov-manifest.json
(cd $S/fv && PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH lake build XRPLModel:static)
sed -e "s#$PWD/formal_verification/.lake/build/lib/libXRPL_XRPLModel.a#$S/fv/.lake/build/lib/libXRPL_XRPLModel.a#" \
    -e "s# -o xrpld # -o $S/xrpld-cov #" build/CMakeFiles/xrpld.dir/link.txt > $S/link.sh
(cd build && bash $S/link.sh)
$S/xrpld-cov --unittest=LeanVault,LeanVaultCreate,LeanVaultSet,LeanVaultDelete,LeanVaultDeposit,LeanVaultWithdraw,LeanVaultClawback,LeanVaultClosedEnded,LeanLoanBroker,LeanLoanBrokerCover,LeanLoan,LeanLoanSet,LeanLoanPay,LeanLoanManage 2> $S/run.err > $S/run.out
python3 lean-coverage/report.py $S/fv/cov-manifest.json $S/run.err
```

## Per file

| File | Arms | Hit | % | Entries hit |
|---|---|---|---|---|
| Lending/Amortization.lean | 9 | 5 | 56% | 0/0 |
| Lending/AssetPool.lean | 0 | 0 | - | 1/1 |
| Lending/Interest.lean | 18 | 13 | 72% | 0/0 |
| Lending/Loan/Loan.lean | 9 | 8 | 89% | 1/1 |
| Lending/Loan/LoanAccept.lean | 6 | 4 | 67% | 1/1 |
| Lending/Loan/LoanDelete.lean | 6 | 6 | 100% | 1/1 |
| Lending/Loan/LoanManage.lean | 12 | 12 | 100% | 1/1 |
| Lending/Loan/LoanPay.lean | 36 | 24 | 67% | 5/5 |
| Lending/Loan/LoanSet.lean | 31 | 26 | 84% | 0/0 |
| Lending/Loan/LoanState.lean | 9 | 4 | 44% | 7/9 |
| Lending/LoanBroker/BrokerCover.lean | 5 | 5 | 100% | 1/1 |
| Lending/LoanBroker/LoanBroker.lean | 2 | 2 | 100% | 0/0 |
| Lending/LoanBroker/LoanBrokerCoverClawback.lean | 8 | 8 | 100% | 0/0 |
| Lending/LoanBroker/LoanBrokerCoverDeposit.lean | 2 | 2 | 100% | 0/0 |
| Lending/LoanBroker/LoanBrokerCoverWithdraw.lean | 3 | 3 | 100% | 0/0 |
| Lending/LoanBroker/LoanBrokerDelete.lean | 3 | 1 | 33% | 1/1 |
| Lending/LoanBroker/LoanBrokerSet.lean | 6 | 6 | 100% | 0/0 |
| Lending1_1/AssetPool.lean | 0 | 0 | - | 1/1 |
| Vault/Vault.lean | 9 | 9 | 100% | 0/0 |
| Vault/VaultBalances.lean | 7 | 4 | 57% | 5/5 |
| Vault/VaultBurn.lean | 3 | 2 | 67% | 2/2 |
| Vault/VaultClawback.lean | 11 | 7 | 64% | 0/0 |
| Vault/VaultCreate.lean | 8 | 8 | 100% | 0/0 |
| Vault/VaultDelete.lean | 3 | 3 | 100% | 1/1 |
| Vault/VaultDeposit.lean | 15 | 13 | 87% | 4/4 |
| Vault/VaultSet.lean | 9 | 9 | 100% | 0/0 |
| Vault/VaultWithdraw.lean | 31 | 26 | 84% | 4/4 |

## The arms still unhit, classified

**Defensive: ruled out by an earlier check or an invariant (39).** Every `tecINTERNAL` / `tefINTERNAL` arm
(VaultClawback L35, VaultDeposit L69, VaultWithdraw L136, LoanPay L254/L373/L453/L466, LoanSet L111); the
negative-amount guard in `settlePayment` (LoanPay L284, an unreachable check in C++ as well); the
overflow `catch` arms (`tecPATH_DRY` / `throwThe Error e`: VaultBalances L51/L53, VaultClawback L48/L50,
VaultDeposit L81, VaultWithdraw L74/L128); doApply re-checks of what preclaim already rejected (LoanPay
`tecKILLED` at L372/L452/L464, the loop guard at L344, which only fires after 100 instalments in one transaction); a loss above the deployed assets (VaultBalances L69) and a debt without loans
(LoanBrokerDelete L18/L22), both excluded by the lawfulness invariants, as is an insolvent vault without shares
(VaultBurn L21); a loan on an open-ended pool (LoanSet L44: a broker needs a closed-ended vault); accepting a
proposal in Subscription or Redemption (LoanAccept L19/L20: a proposal is created in Investment and must end
before Redemption); the zero-principal / zero-count / zero-rate guards of the interest helpers reached only
through callers that already handle those cases (Amortization L11/L13/L23/L34, Interest L20/L22/L32/L75/L82,
Loan L107, LoanState L62).

**Dead under the current amendments or by arithmetic (6).** LoanSet L110 (`interest expected but none`): the
total is rounded upward at the loan scale, so any positive rate leaves one grid unit of interest. LoanSet
L114/L118 (first instalment pays no principal, rounded payment zero): the same rounding makes the payment at
least one grid unit and the principal share positive. VaultWithdraw L56 (`truncateShares = false`) has no
caller. VaultClawback L64 (debit
too small to change the stored total) cannot follow the grid clamp that precedes it. LoanPay L403 (overpayment
tail rounding to nothing): the amount is already rounded to the loan scale, so a positive remainder is at least
one unit.

**Numeric corner cases (6).** A model-only random search (`lean-coverage/Search.lean`: 4,000 random loans,
about 250,000 regular and overpayments, amounts rounded to what an IOU amount can carry) reached four of the ten
arms this class used to hold: the re-amortization guard failure (LoanPay L227), the interest-rise guard (L233),
the dropped-overpayment exit (L411) and the management-fee delta floor (LoanState L107). Each is now an FFI
replay case on which C++ agrees. Still unhit: the principal-did-not-fall guard (LoanPay L232) and the principal
and interest delta floors (LoanState L105/L106), never triggered by the search; the `reduceByExcess` helper
(LoanState L112/L117 and the two do-blocks at L111/L121), which `scheduledComponents` rules out by construction
up to Number rounding: interest and fee are capped by the room left in the payment, so the total never exceeds
the payment, and a value outstanding at or below the payment takes the final-instalment branch instead; and
LoanPay L251 (a payment whose credit rounds to nothing on a coarsened vault): the only loan a coarsened vault
holds is the one that coarsened it, and its instalments are far above the coarsened grid.

## Cases added in this pass (all green on both sides)

Vault: an IOU cap off the grid; a 17-digit deposit total; a closed-ended withdrawal whose net payout exceeds
the available assets; a deposit whose shares are worth less than a grid unit; a one-share MPT withdrawal paying
nothing; withdrawals by shares and by assets from a fully impaired two-holder vault; an owner burn with a partial
share amount.

Broker: a cover deposit leaving the base exponent; a broker update without a cap.

Loan: an MPT lending fixture (LoanSet with interest and fees, regular, late and full payments, a fee off the
grid); a `LeanLoan` lawful-state suite (17 cases); LoanSet with an unrepresentable fee, a tiny rate over 2 and
over 50 instalments (binomial series and its early convergence), interest past the open limit, and a coarsened
vault refusing a loan (late interest on a loan of most of a vault at its open limit); LoanAccept past the open
limit; LoanDelete beside another loan; LoanManage on pending, defaulted and paid-off loans; LoanPay on pending
and paid-off loans, late without a rate or fee, late below the instalment, full without a close rate, full when
late, full on a zero-interest loan, full after an instalment (paid ahead, and past its due date), three
interest-bearing instalments in turn, the service fee topping up a drained cover, an overpayment clearing the
whole loan, an overpayment extra consumed by a 100% overpayment fee. After the #52 rebase: a holder redeeming
more shares than they own (the model's new holder-shares check, wired through the FFI). From the search: three
overpayment histories replayed through the FFI (re-amortization guards fail, interest would rise, management-fee
delta floored at zero).

C++-guided (2026-11-04: unhit C++ branches that the model also decides). Vault: unblocking deposits on a vault
that cannot block them; an XRP cap above the native maximum; a 30-year investment period and one second less;
a deposit landing exactly on the cap; a donation to an insolvent vault (FV_M2_7, now agreed by both sides, moved
from disabled to regression); clawing everything from one of two holders, amount zero and amount omitted;
clawing every share of a coarsened vault whose deployed assets round away (`tecHAS_OBLIGATIONS`, VaultClawback
L39, previously classed as dead); withdrawing from an empty vault by assets and by shares. Lending: defaults on
an MPT loan (plain and impaired) and on a broker without cover; MPT cover deposit, withdraw and clawback;
regular and overpayment stopping at 100 instalments; a full payment below the amount due; the three LoanSet
time-limit checks (grace, interval, count); an MPT principal above the MPT maximum; a debt maximum not
representable as an amount, on create and update.

# C++ coverage of the same code by the FFI tests

Measured 2026-11-04 with gcov on the vault and lending transactors and their helpers
(`src/libxrpl/tx/transactors/{vault,lending}/`, `VaultHelpers.cpp`, `LendingHelpers.cpp`) while the same 14
FFI suites run (388 cases, 0 failures). Throw branches, unreachable branches and non-code lines are excluded,
as in the repo's own `coverage` target.

**Result: 3159 of 3989 lines (79%); 4437 of 6505 branches (68%)** (before the C++-guided cases: 3131 lines, 4387 branches). The full report, with per-line HTML, is in
`cpp-coverage/` (`index.html`, `summary.txt` for branches, `lines.txt` for lines, `coverage.json`).

| File | Lines | Line % | Branches | Branch % |
|---|---|---|---|---|
| helpers/LendingHelpers.cpp | 618/733 | 84% | 748/982 | 76% |
| helpers/VaultHelpers.cpp | 276/322 | 85% | 344/443 | 77% |
| lending/LoanAccept.cpp | 89/115 | 77% | 100/156 | 64% |
| lending/LoanBrokerCoverClawback.cpp | 126/172 | 73% | 132/226 | 58% |
| lending/LoanBrokerCoverDeposit.cpp | 67/95 | 70% | 76/122 | 62% |
| lending/LoanBrokerCoverWithdraw.cpp | 93/131 | 71% | 110/191 | 57% |
| lending/LoanBrokerDelete.cpp | 66/84 | 78% | 82/134 | 61% |
| lending/LoanBrokerSet.cpp | 130/170 | 76% | 240/356 | 67% |
| lending/LoanDelete.cpp | 86/99 | 86% | 95/139 | 68% |
| lending/LoanManage.cpp | 156/250 | 62% | 215/414 | 51% |
| lending/LoanPay.cpp | 268/348 | 77% | 438/681 | 64% |
| lending/LoanSet.cpp | 391/463 | 84% | 552/771 | 71% |
| vault/VaultClawback.cpp | 179/221 | 81% | 259/382 | 67% |
| vault/VaultCreate.cpp | 142/187 | 75% | 247/332 | 74% |
| vault/VaultDelete.cpp | 64/72 | 88% | 108/146 | 74% |
| vault/VaultDeposit.cpp | 146/195 | 74% | 228/350 | 65% |
| vault/VaultSet.cpp | 71/101 | 70% | 132/218 | 60% |
| vault/VaultWithdraw.cpp | 191/231 | 82% | 331/462 | 71% |
| **TOTAL** | 3159/3989 | 79% | 4437/6505 | 68% |

The C++ figure is lower than the model's because the FFI tests only exercise what the model models. Sampling the
unhit regions, they are almost all one of:

- **Vault versions other than FixedPrecision.** The Legacy and CashBasis accounting paths (for example the
  non-FixedPrecision default in `LoanManage.cpp`, from L264) are never taken: every FFI vault is FixedPrecision,
  the only version the model describes.
- **Preflight field validation** (`tem*` returns, such as the LoanSet range checks from L870): the model starts
  after preflight.
- **Ledger and permission checks outside the model**: missing objects, wrong submitter or owner, frozen or
  unauthorized holders, permissioned domains, destination checks.
- **Defensive code** excluded from rippled's own coverage (`LCOV_EXCL`) or mirrored by an unhit model arm, such
  as the zero-credit terminal payment in `LoanPay.cpp` (L603), the C++ side of the model's LoanPay L251.

Rerun (needs `build-cov/`, configured as Release with `-O0 --coverage` on the existing Conan toolchain; the
repo's `coverage` option forces a Debug build, for which there are no Conan packages):

```bash
cmake -S . -B build-cov -DCMAKE_TOOLCHAIN_FILE=$PWD/build/build/generators/conan_toolchain.cmake \
    -DCMAKE_BUILD_TYPE=Release -Dxrpld=ON -Dtests=ON -Dformal_verification=ON -Dunity=OFF \
    "-DCMAKE_CXX_FLAGS=-m64 --coverage" "-DCMAKE_C_FLAGS=-m64 --coverage" \
    "-DCMAKE_CXX_FLAGS_RELEASE=-O0 -DNDEBUG" "-DCMAKE_C_FLAGS_RELEASE=-O0 -DNDEBUG" \
    "-DCMAKE_EXE_LINKER_FLAGS=--coverage"
lean-coverage/cpp-coverage.sh cpp-coverage   # builds, runs the 14 suites, writes the report
```

## Branch arms never hit

### Lending/Amortization.lean
- L11 (then): `return Number.zero`
- L13 (arm): `(Number.ofInt64 1).operator_div paymentsRemainingNum .to_nearest`
- L23 (then): `return Number.zero`
- L34 (then): `return Number.zero`

### Lending/Interest.lean
- L20 (then): `return Number.zero`
- L22 (then): `return Number.zero  -- not overdue`
- L32 (then): `return Number.zero`
- L75 (then): `return Number.zero`
- L82 (then): `return Number.zero`

### Lending/Loan/Loan.lean
- L107 (match): `false`

### Lending/Loan/LoanAccept.lean
- L19 (match): `return .tecTOO_SOON`
- L20 (match): `return .tecEXPIRED`

### Lending/Loan/LoanPay.lean
- L232 (then): `return none`
- L251 (arm): `throw .tecPRECISION_LOSS`
- L254 (arm): `throw .tecINTERNAL`
- L284 (arm): `throw .tecLIMIT_EXCEEDED`
- L344 (then): `return payment`
- L372 (arm): `throw .tecKILLED`
- L373 (then): `throw .tecINTERNAL`
- L403 (then): `return payment`
- L452 (arm): `throw .tecKILLED`
- L453 (then): `throw .tecINTERNAL`
- L464 (arm): `throw .tecKILLED`
- L466 (then): `throw .tecINTERNAL`

### Lending/Loan/LoanSet.lean
- L44 (match): `pure ()`
- L110 (then): `return .tecPRECISION_LOSS`
- L111 (then): `return .tecINTERNAL`
- L114 (then): `return .tecPRECISION_LOSS`
- L118 (then): `return .tecPRECISION_LOSS`

### Lending/Loan/LoanState.lean
- L62 (arm): `return {`
- L105 (then): `Number.zero`
- L106 (then): `Number.zero`
- L112 (arm): `let part := Number.min value excess`
- L117 (arm): `return (value, excess)`

### Lending/LoanBroker/LoanBrokerDelete.lean
- L18 (arm): `let nt := lb.numericType`
- L22 (arm): `return .tecHAS_OBLIGATIONS`

### Vault/VaultBalances.lean
- L51 (arm): `return .tecPATH_DRY`
- L53 (arm): `throw e`
- L69 (arm): `throw .tecLIMIT_EXCEEDED`

### Vault/VaultBurn.lean
- L21 (arm): `throw .tecPRECISION_LOSS`

### Vault/VaultClawback.lean
- L35 (arm): `throw .tecINTERNAL`
- L48 (arm): `throw .tecPATH_DRY`
- L50 (arm): `throwThe Error e`
- L64 (arm): `throw dustCheck`

### Vault/VaultDeposit.lean
- L69 (arm): `throw .tecINTERNAL`
- L81 (arm): `throwThe Error e`

### Vault/VaultWithdraw.lean
- L56 (match): `pure sharesNumber`
- L74 (arm): `throwThe Error e`
- L128 (then): `throw .tecPATH_DRY`
- L128 (else): `throwThe Error e`
- L136 (arm): `throw .tefINTERNAL`


## Do-blocks never entered

- Lending/Loan/LoanState.lean L111: `if excess.operator_gt Number.zero then`
- Lending/Loan/LoanState.lean L121: `let (interest, excess) ← reduceCapped deltas.interest excess`
