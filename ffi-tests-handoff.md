# FFI tests: Vault port (done), LoanBroker/Loan tests (to do)

Handoff for the FFI differential tests in `rfv-ffi`. The FFI tests run the Lean model (`formal_verification/`) and
the C++ transactors on the same state, through `@[export]` Lean functions called from beast unit tests in
`src/test/formal_verification/`, and compare TER codes and resulting state.

Status (2026-10-20):

- Vault FFI ported to the FixedPrecision lending model, 7 vault suites green (158 cases, 5375 checks).
- `LeanVaultClosedEnded` (new, 23 cases): the phase matrix (open-ended / Subscription / Investment / Redemption)
  for deposit, donation and withdraw, every early-exit fee branch (no field, 0, 5%, 100%, final withdrawal,
  payout rounding to zero before and after the grid clamp), and one closed-ended clawback / set / delete each.
  All green on both sides.
- Review fixes (2026-10-20, all vault suites green, 203 cases): the withdraw and clawback harnesses derive the
  loss waiver from sole-shareholdership (`holderOwnsAllShares`) like C++; deposit/clawback/set comparators read the
  C++ post-state before `env.close()`; `VaultFFI::read` throws when the derived total overflows; `leanVaultUpdate`
  compares VaultSet post-state (cap and block/unblock flags, `tecNO_PERMISSION` without the owner flag); new cases
  for deposits blocked by the owner (`tecLOCKED`), yield in the open-limit capacity, create with a scale on XRP/MPT
  (preflight only, model normalizes to 0: `outsideModel`), zero and negative maximum, and a share supply above
  INT64_MAX. Closed-ended suite adds exact-boundary phases (`closeExactlyAt`, schedule dates aligned to the close
  time resolution), the fee-dependent availability check (staged deployed assets), by-shares and inexact-fee
  withdrawals. Stale "known discrepancy" headers corrected: every enabled case passes on both sides.
- Leftovers (2026-10-20): clawback headers and the FV_M2_3 / FV_M2_11 comments reworded to the properties now held;
  `testSharesToAssets` passes the derived waiver. The disabled two-deposit originals of FV_M2_4 / FV_M2_12 were
  removed: their 9,999,999,999.999999 seed is above the scale-6 open limit (9e9), so the staged cases are the
  permanent form, no longer "temporary reconstructions".
- Model gap on record: `Vault.create` accepts a scale on an integral asset (forces it to 0) where C++ preflight
  returns temMALFORMED; the create suite documents it with `outsideModel`. Closing it means rejecting a nonzero
  scale for an integral numeric type in `Vault.create` or in the lawfulness clauses.
- LoanBroker FFI tests: **done** (2026-10-21). `XRPL/FFI/Lending/LoanBroker.lean`, `ffi/lending/LoanBrokerFFI.h`,
  `tx/lending/LendingTestHelpers.h` (`setUpBrokerVault`, `depositCover`, `issueLoan`, `readLoanBrokerState`),
  suites `LeanLoanBroker` (lawful state, set create/update, delete) and `LeanLoanBrokerCover` (deposit, withdraw,
  clawback): 51 cases green. Harness rule: the model's doApply functions assume preclaim passed (`tecINTERNAL` on
  a failed precondition), so run them only when the model's preclaim returns tesSUCCESS.
- Lean model branch coverage (2026-10-21): 202/258 arms (78.3%) after covering every transaction-reachable arm;
  the 56 left are defensive (39), dead by arithmetic or amendment (7) or capping-prevented numerics (10). Tooling
  in `lean-coverage/`, report and classified list in `ffi-model-coverage.md`. New: MPT lending fixture
  (`LendingAsset::mpt`), `LeanLoan` lawful-state suite, coarsened-vault case. Whole group: 18 suites, 411 cases.
- Review fixes on the lending port (2026-10-21): `Loan.canCreate`/`canAccept` now take the parent close time for
  expiry and phase (the one-step start date still comes from the ledger close time via `LoanSchedule.build`), in
  both trees; boundary cases added (proposal at / one second after the parent close time, LoanSet exactly at the
  subscription and redemption dates, accept exactly at the start date); `expectLoanMatches` compares the
  configuration fields too; the model's MPT multiply carries a note that C++ takes that path only under MPTokensV2.
  Out of the model by design (fixtures keep them satisfied): fee-to-owner needs an unfrozen, authorized owner;
  LoanPay checks the borrower's balance; LoanManage and LoanDelete check the submitter.
- Rebased onto #52 (2026-10-23): `lean_vault_withdraw` passes the holder's share balance (new `holderShares`
  argument of `Vault.withdraw`, C++ `accountHolds` check), new case for over-redemption; three `LeanLoan` cases
  flipped to lawful because #52 dropped the payment-count and due-date clauses from the loan invariant. Coverage
  re-measured: 204/261 (78.2%). Whole group: 18 suites, 417 cases, 0 failures.
- Coverage rerun (2026-11-04): Lean model 209/261 arms (80.1%) after a model-only overpayment search
  (`lean-coverage/Search.lean`) found 4 more reachable arms, now FFI replay cases in `LeanLoanPay`; C++ 78% lines /
  67% branches of the vault and lending code (`build-cov/`, `lean-coverage/cpp-coverage.sh`, report in
  `cpp-coverage/`). The regular `build/` had a GC'd ccache path, repointed with sed.
- 2026-11-04 (later): 27 FFI cases from unhit C++ branches the model also decides (vault and lending, list in
  `ffi-model-coverage.md`); Lean 210/261, C++ 79% lines / 68% branches. FV_M2_7 (donation to an insolvent vault)
  now agrees on both sides and runs as a regression test. Possible model gaps, not tested: AssetsMaximum not
  representable is `tecPRECISION_LOSS` in the model vs `temMALFORMED` in C++ VaultCreate preflight; the model
  drops an EarlyExitFeeRate on an open-ended vault where C++ returns `temMALFORMED`; VaultSet with a negative cap
  or both block flags is `tem*` in C++ but not rejected as such by the model.
- Loan FFI tests: **done** (2026-10-21). `XRPL/FFI/Lending/Loan.lean`, `ffi/lending/LoanFFI.h`, helpers extended
  (`readLoanState` with the carried payment total, `LoanParams`/`loanSetTx`/`submitLoanSet`, `closeAt`,
  `ledgerCloseTime`, `expectLoan/Vault/BrokerMatches`, `modelVerdict`). Suites `LeanLoanSet` (one-step, two-step,
  accept, delete), `LeanLoanPay` (regular, late, full, overpayment, impaired) and `LeanLoanManage` (impair,
  unimpair, default): 42 cases green. Whole group: 17 suites, 0 failures.
- The `LeanSTAmount` MPT multiply divergence is settled by running that suite under MPTokensV2 (section 5).

Nothing is committed. All changes are in the working tree (`git status`).

---

## 1. Build and run

The repo's `nix develop` shell cannot be built inside the sclaude sandbox (no nix daemon; the rust-overlay `cargo`
derivation fails). The build below uses the sandbox's own toolchain (gcc 16.2, cmake 4.4, conan 2.32) and the Lean
4.30.0 toolchain from `~/.elan`. The model does **not** build on Lean 4.34.1 yet; 4.30.0 is pinned in
`formal_verification/lean-toolchain`.

Already set up (no need to redo unless the sandbox is rebuilt):

- `~/.conan2`: `lean4/4.30.0` is an `export-pkg` of `~/.elan/toolchains/leanprover--lean4---v4.30.0` (recipe copy in a
  scratch dir with a `toolchain` symlink, `conan export-pkg . --version 4.30.0`). `lean4-deps/4.30.0` built from
  `external/lean4-deps` (mathlib, 8477 objects). All C++ deps built for gcc 16 / Release.
- `rfv-ffi/build`: configured with `formal_verification=ON`, Release.

Every command needs this environment:

```bash
env -u LD_LIBRARY_PATH -u LEAN_CC \
    XRPL_DEVSHELL=gcc-plain XRPLD_NO_PATCH_NIX_BINARY=1 \
    PATH=/home/v3lmx/work/ripple/.conan2-test/shim:$PATH \
    <command>
```

- `LD_LIBRARY_PATH` from the sandbox points at the Lean 4.28 runtime: it must be unset.
- `XRPL_DEVSHELL=gcc-plain`: `cmake/XrplSanity.cmake` refuses a Nix compiler outside a dev shell.
- `.conan2-test/shim` provides `tar` and `gawk` (only needed for `conan install` of deps).

Build and run (cap parallelism at `-j6`: 30 GB RAM, higher OOMs the machine):

```bash
cd rfv-ffi/build
make -j6 xrpld                      # also rebuilds the Lean archive (lake build XRPLModel:static)
./xrpld --unittest=formal_verification
./xrpld --unittest=LeanVaultDeposit # one suite
```

Fast Lean-only check (from `formal_verification/`): `lake build XRPL.FFI.FFI` (uses `~/.elan` 4.30 when the toolchain
bin dir is on PATH, e.g. `PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH`).

Adding a new `.cpp` test file: the test glob is `CONFIGURE_DEPENDS`, `make` re-runs cmake by itself.

Sandbox repairs done along the way (redo if they break again):

- elan 4.30 `bin/cc` and `bin/llvm-ar` pointed at GC'd nix-store paths; repointed to the live `gcc-wrapper-16.2.0`
  (`cc`) and its `ar`.
- `~/.conan2` remote `xrplf` moved from `conan.ripplex.io` (dead) to `https://conan.xrplf.org/repository/conan/`.
- `b2` (Boost build tool) cached binary had a GC'd interpreter: rebuilt with `--build 'b2/*'`.

## 2. What was done: Vault port

Root cause of the failing vault tests: commit `d81c415f5` (Lending model changes, Fixed precision) reworked the Vault
model, but `formal_verification/XRPL/FFI/Vault/*.lean` was never ported, so `XRPLModel:static` did not compile and
`xrpld` could not link. The C++ headers hand-declared the old ABI.

Model changes the port follows (see the commit for detail):

- `RawVault.assetsTotal` is derived (`assetsAvailable + assetsDeployed`, `Except Error Number`). New fields
  `assetsDeployed`, `yieldUnrealized`, `schedule` (closed-ended dates), `earlyExitFeeRate`, `ownerCanBlockDeposit`,
  `depositBlocked`. Max IOU scale 10.
- Operations return `TerExcept α = ExceptT TER (Except Error) α`; the old result structs are gone. Deposit/withdraw
  take `parentCloseTime`; clawback takes `waiveUnrealizedLoss`. `canVaultSet` became `canVaultUpdate`.
- Fixed precision: amounts clamp to the vault base grid `10^-scale`; inflows past the open limit
  `9e15 * 10^-scale` are `tecLIMIT_EXCEEDED`.

### Lean (`formal_verification/XRPL/FFI/Vault/`)

- `Vault.lean`: `lean_vault_build` takes all raw fields (schedule as two `Option UInt32`, both or neither, else
  `.badInput`; `scheduleOf` helper); getters for every field, `lean_vault_assets_total` returns `Except Error Number`.
  Generic `terCode`/`terValue` plus monomorphic `lean_ter_{amount,vault,vault_amounts}_{code,value}` and
  `lean_vault_amounts_{assets,shares,vault}`.
- Every `TerExcept` export returns its `.run`: `Except Error (Except TER α)` (outer = model error, inner = TER).
- `VaultDeposit/Withdraw/Clawback/Burn/Set/Delete.lean` ported; new `VaultCreate.lean`
  (`lean_can_vault_create`, `lean_vault_create`), imported in `FFI.lean`.

### C++ (`src/test/formal_verification/`)

- `ffi/vault/VaultFFI.h`: `Vault` DTO mirrors the model (`assetsTotal` is read back only, never sent).
  `TerExceptFFI`, `readVaultResult`, `readAmountResult`, `readTerCode` decode the nested `Except`.
  Result structs: `LeanVaultResult` (deposit/withdraw/clawback), `LeanAmountResult` (rounded deposit, canBurnShares),
  `LawfulTerResult` (set/delete/create checks).
- Per-tx headers ported; new `ffi/vault/VaultCreateFFI.h`.
- `tx/vault/VaultTestHelpers.h`:
  - `readVaultState` reads every new field; the total comes from C++ `getAssetsTotal`, not the `sfAssetsTotal` cache;
    throws if the vault is missing (a failed setup is then a test failure, not a segfault).
  - `updateVaultState` also writes `sfAssetsDeployed = total - available`.
  - `parentCloseTime(env)`, `kOpenLimitUnits`, `roundToVaultGrid`, `stageSoleHolderVault` (moved from the clawback
    test), `stageVaultHolding` (sets the vault pseudo-account's trust-line balance).
- Tests: call sites ported; `LeanVault_test` rewritten for the new invariants; new `LeanVaultCreate_test` (13 cases).

### Test changes (expectations follow new C++ and model behaviour, both sides agree)

- Fixtures shrunk under the open limit; open-limit boundary cases added (XRP, IOU holder/issuer, MPT).
- Large-total precision findings (FV_M2_4, FV_M2_12, FV_M2_15 withdraw) now staged directly.
- FV_M2_15 deposit and FV_M2_19 create are regression tests (17-digit totals/caps now rejected).
- FV_M2_13 and the staged full exit expect `tecHAS_OBLIGATIONS` (a loss implies deployed assets); a lent-out partial
  withdrawal case still covers `tecINSUFFICIENT_FUNDS`.
- Applied-delta fixture moved to scale 10, expectations recalibrated.
- `testSharesToAssets` compares the withdraw payout (clamped) with C++, and the conversion to within one grid step.
- FV_M2_14 (donation loss gap) removed at the user's request: obsolete, the total is derived now.
- FV_M2_16 (all-but-one-share drain) now reproduces on **both** sides from a staged state past the open limit;
  the test passes because they agree.

## 3. Lessons (apply them to the loan tests)

- **Open limit**: a deposit (vault or broker cover) cannot push past 9e15 grid units. Large totals only via staging.
- **Staging lives on the open ledger**: `env.close()` discards it and replays the tx against the unstaged ledger.
  For a staged `tesSUCCESS` comparison, read the C++ post-state **before** `env.close()` (see `compareWithdraw`).
- **Staged IOU totals need backing funds**: also stage the pseudo-account trust line (`stageVaultHolding`), otherwise
  C++ payouts hit `doWithdraw: negative balance` → `tefINTERNAL`.
- **Staged loss needs deployed assets** (`lossUnrealized ≤ assetsDeployed` is a model invariant and a C++ invariant).
- **A missing SLE after a failed setup segfaults** unless guarded; prefer `readXState` helpers that throw.
- **Output ordering**: beast prints a testcase name lazily, so stderr debug lines can appear before their header.
  There is no gdb in the sandbox; bisect crashes with `fprintf(stderr, ...)`.
- Designated-initializer returns trigger `-Wmissing-field-initializers` with gcc 16; the existing headers already do
  this, leave it.
- Keep Lean comments minimal and do not reference C++ files in Lean code.

## 4. LoanBroker and Loan FFI tests (done; the original plan follows)

Lessons from doing it:

- The model's doApply functions assume preclaim passed, so a harness compares the model's preclaim TER with C++,
  and runs the model's doApply only when that preclaim is tesSUCCESS (`modelVerdict`). Some rejections live in
  doApply on both sides (LoanSet `tecINSUFFICIENT_FUNDS`/`tecLIMIT_EXCEEDED`, impair `tecTOO_SOON`); they compare
  through the apply TER.
- Every fund-moving result reaches C++ as `LoanWithAmounts` (zero amounts for accept/impair/unimpair);
  `amountToPool` is checked against the vault's `assetsAvailable` delta and `amountToBroker` against the broker
  cover delta plus the owner's balance delta.
- One-step LoanSet stamps `startDate` with the open ledger's `header().closeTime` (`ledgerCloseTime`), not the
  parent close time; LoanPay/LoanManage/LoanAccept use the parent close time (`parentCloseTime`).
- `sfPaymentTotal` is not on the Loan entry: the test carries it (`readLoanState(..., paymentTotal)`).
- A 1e-6 principal with interest still amortizes on both sides (the grid rounds the total up and leaves one unit
  of interest); the `tecPRECISION_LOSS` branch needs a schedule the grid cannot honour (1e-6 in 3 instalments).


Goal: one differential test per model branch (each TER the model returns, plus the success path with a state
comparison). Basics, not edge cases.

### 4.1 Model surface

The lending functions are generic over `[AssetPool α]`; the only instance is `AssetPool Vault`
(`Model/Lending1_1/AssetPool.lean`). Export everything **monomorphic at `α := Vault`**.

LoanBroker (`Model/Lending/LoanBroker/`):

| Tx | Check (preclaim) | Apply |
|---|---|---|
| LoanBrokerSet create | `LoanBroker.canCreate pool debtMaximum nt : Except Error TER` | `LoanBroker.create tx nt : Except Error LoanBroker` |
| LoanBrokerSet update | `lb.canUpdate pool debtMaximum` | `lb.update debtMaximum` |
| CoverDeposit | `lb.canCoverDeposit pool amount` | `lb.coverDeposit pool amount : TerExcept LoanBrokerCoverResult` |
| CoverWithdraw | `lb.canCoverWithdraw pool amount` | `lb.coverWithdraw pool amount` |
| CoverClawback | `lb.canCoverClawback pool (Option amount)` | `lb.coverClawback pool (Option amount)` |
| LoanBrokerDelete | `lb.canDelete pool` | `lb.roundedCoverAvailable : Except Error STAmount` |

Loan (`Model/Lending/Loan/`):

| Tx | Check | Apply |
|---|---|---|
| LoanSet | `Loan.canCreate broker pool principal fees schedule ledgerCloseTime twoStep` | `Loan.createImmediate` / `Loan.createPending broker pool principal rates fees schedule allowsOverpayment : TerExcept (LoanWithPool Vault)` |
| LoanAccept | `loan.canAccept pool ledgerCloseTime` | `loan.accept pool` |
| LoanPay | `loan.canPay paymentType : TER` | `loan.{regular,late,full,overpayment}Payment pool amount now : TerExcept (LoanWithAmounts Vault)` |
| LoanManage | `loan.canManage action now : TER` | `loan.manageImpair pool now`, `manageUnimpair pool`, `manageDefault pool` |
| LoanDelete | `loan.canDelete : TER` | `loan.delete pool : TerExcept (LoanBrokerWithPool Vault)` |

A `Loan` embeds its `LoanBroker` (`RawLoan.broker`). `LoanWithAmounts` adds `amountToPool`, `amountToBroker`.

### 4.2 FFI layer to add

Lean, new `formal_verification/XRPL/FFI/Lending/` (import each in `FFI.lean`):

- `LoanBroker.lean`: `lean_loan_broker_build` (raw fields → `RawLoanBroker.to_lawful`), getters, and the per-tx
  exports above. Result accessors for `LoanBrokerCoverResult` (`amount'`, `loanBroker'`) and
  `LoanBrokerWithPool Vault` (`broker'`, `pool'`).
- `Loan.lean`: `lean_loan_build` from flat fields (rates, fees, schedule, accounting, due dates, the four flags, and a
  built `LoanBroker` handle), getters, per-tx exports, accessors for `LoanWithPool Vault` / `LoanWithAmounts Vault`.
  Enums (`LoanPaymentType`, `LoanManageAction`) as `UInt8` tags.
- Reuse the `TerExcept` pattern: `.run`, plus `terCode`/`terValue` monomorphic accessors. Consider moving
  `terCode`/`terValue`/`scheduleOf` from `FFI/Vault/Vault.lean` to `FFI/CommonFFI.lean`.
- Check `lake build XRPL.FFI.FFI` early, then `lake build XRPLModel:static`.

C++, new `src/test/formal_verification/ffi/lending/` and `tx/lending/`:

- `LoanBrokerFFI.h` / `LoanFFI.h`: DTOs + `build`/`read`, like `VaultFFI.h`. Reuse `TerExceptFFI`, `readTerCode`.
- `tx/lending/LendingTestHelpers.h`: fixtures and `readLoanBrokerState` / `readLoanState`.
- Suites: `LeanLoanBroker_test.cpp` (set/update/delete), `LeanLoanBrokerCover_test.cpp` (deposit/withdraw/clawback),
  `LeanLoanSet_test.cpp` (+ accept), `LeanLoanPay_test.cpp`, `LeanLoanManage_test.cpp` (+ delete).
- Each comparison: read state (vault + broker [+ loan]) → call model → submit tx → read C++ state before close →
  compare TER, then on success compare vault totals, broker (`debtTotal`, `coverAvailable`, loan count) and loan fields.

SLE → model mapping to settle first:

- LoanBroker: `sfDebtTotal`, `sfDebtMaximum`, `sfCoverAvailable`, `sfManagementFeeRate`, `sfCoverRateMinimum`,
  `sfCoverRateLiquidation`; `numericType` from the vault asset; `loanCount`: verify which field C++ uses
  (`sfOwnerCount` on the broker is the likely one).
- Loan: rates/fees/dates/accounting fields map 1:1; `isPending/isImpaired/isDefault/allowsOverpayment` from
  `lsfLoanPending/Impaired/Default/Overpayment`. **`paymentTotal` is not on the Loan SLE** (`sfPaymentTotal` is a
  LoanSet tx field only): the test must carry it from the LoanSet it submitted. Same check for any other model field
  missing from the SLE.

Fixtures (templates already in the repo):

- `LeanVaultWithdraw_test.cpp::testWithdrawWaiveLoss` builds a closed-ended vault, a broker, a loan (with
  `Sig(sfCounterpartySignature, lender)`), advances time and impairs it. Start from it.
- `jtx::Vault::createClosedEnded` / `closePastSubscription` for phases; `loan_broker::{set,coverDeposit,
  coverWithdraw,coverClawback,del}` and `loan::{set,manage,...}` in `src/test/jtx/TestHelpers.h`.
- `src/test/app/lending/LoanTestBase.h`, `LoanFixedPrecisionBase.h`, `LoanPayFixedPrecisionBase.h` and the
  `*FixedPrecision_test.cpp` suites already drive these transactions on FixedPrecision vaults: reuse their setup.
- `LoanBroker.canCreate` requires a closed-ended vault (an open-ended one is `tecNO_PERMISSION`).

### 4.3 Test cases (one per branch)

LoanBroker:

1. Set create: success (compare broker); open-ended vault → `tecNO_PERMISSION`; `debtMaximum` off the vault grid →
   `tecPRECISION_LOSS`; a field breaking the broker invariant (e.g. management fee rate > 10%) → C++ `tem*` and model
   `notLawful`.
2. Set update: success; `debtMaximum` below `debtTotal` (needs a loan) → `tecLIMIT_EXCEEDED`; off grid →
   `tecPRECISION_LOSS`.
3. CoverDeposit: success (compare `coverAvailable`); sub-grid dust → `tecPRECISION_LOSS`; past the open limit or off
   the base exponent → `tecLIMIT_EXCEEDED`.
4. CoverWithdraw: success; more than available → `tecINSUFFICIENT_FUNDS`; below the minimum cover for the debt →
   `tecINSUFFICIENT_FUNDS`; dust → `tecPRECISION_LOSS`.
5. CoverClawback: amount absent / zero (claws all excess); amount above the excess (clamped); no excess cover →
   `tecINSUFFICIENT_FUNDS`; dust → `tecPRECISION_LOSS`.
6. Delete: with a loan → `tecHAS_OBLIGATIONS`; success (compare the returned cover amount).

Loan:

7. LoanSet: success one-step (compare loan, vault `assetsAvailable/Deployed/Reserved/yield`, broker `debtTotal` and
   loan count); Subscription phase → `tecTOO_SOON`; Redemption → `tecEXPIRED`; final payment within 60 s of the
   redemption date → `tecNO_PERMISSION`; principal above `assetsAvailable` → `tecINSUFFICIENT_FUNDS`; above
   `debtMaximum` → `tecLIMIT_EXCEEDED`; not enough broker cover → `tecINSUFFICIENT_FUNDS`; a fee off the grid →
   `tecPRECISION_LOSS`; principal too small to amortize → `tecPRECISION_LOSS`; schedule past `maxTime` →
   `tecKILLED`; two-step with an expired start date → `tecEXPIRED`.
8. LoanAccept: success (pending → active, compare vault reserved/yield); not pending → `tecNO_PERMISSION`; after the
   start date → `tecEXPIRED`.
9. LoanPay: one regular instalment (compare loan, `amountToPool`, `amountToBroker`, vault, broker); several
   instalments in one tx; amount below one instalment → `tecINSUFFICIENT_PAYMENT`; regular payment when late →
   `tecEXPIRED`; late payment success and before due → `tecTOO_SOON`; full payment success, with 1 payment left →
   `tecKILLED`; overpayment success and without `lsfLoanOverpayment` → `tecNO_PERMISSION`; final instalment closes the
   loan; payment on an impaired loan unimpairs it.
10. LoanManage: impair success (compare vault loss); impair an impaired loan / unimpair an unimpaired one →
    `tecNO_PERMISSION`; default before the grace period ends → `tecTOO_SOON`; default success (compare the amount
    covered from broker cover and the vault loss).
11. LoanDelete: active loan with payments left → `tecHAS_OBLIGATIONS`; paid-off loan success; pending loan success
    (compare vault and broker).

Suggested order: FFI build/getters with a lawful-state test (like `LeanVault_test`) → LoanBroker set/delete → cover
transactions → LoanSet → Accept → Pay → Manage → Delete.

Done when: all new suites pass, any C++/model disagreement is either fixed in the FFI/test or documented as a
finding with both values, and `./xrpld --unittest=formal_verification` shows no new failures.

## 5. LeanSTAmount `fuzz_mul_round` (settled 2026-10-21: amendment enabled in the test)

6024 failures, all MPT result types: the model returned a value where C++ threw. Cause: the model's
`STAmount.mulRoundImpl` routes an int64 target through `roundNumberResult` (exact Number product), which mirrors the
C++ Number path gated on **MPTokensV2** (XLS-82, `Supported::No`, in development, unrelated to the lending and
fixCleanup amendments). Without rules, C++ takes the legacy uint64 path where `muldivRound` throws on the intermediate
overflow. Decision: keep the model on the V2 path and run `LeanSTAmount` under those rules. `runTests` now installs a
`CurrentTransactionRulesGuard` with every supported amendment plus `featureMPTokensV2`. The rules must include
SingleAssetVault/LendingProtocol: a set with only MPTokensV2 sends `STAmount::operator=(Number)` down its legacy
branch and the suite segfaults. The model edit tried on 2026-10-20 (deleting the int64 branch) was reverted in both
`rfv-ffi` and `rfv-stable`. Result: 21 cases, 0 failures.
