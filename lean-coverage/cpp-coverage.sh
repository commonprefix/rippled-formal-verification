#!/usr/bin/env bash
# C++ line/branch coverage of the vault and lending code under the FFI transaction suites.
# Needs build-cov/ configured with --coverage (see ffi-model-coverage.md). Writes the report to $1.
set -euo pipefail
out=${1:-cpp-coverage}
root=$(cd "$(dirname "$0")/.." && pwd)
suites=LeanVault,LeanVaultCreate,LeanVaultSet,LeanVaultDelete,LeanVaultDeposit,LeanVaultWithdraw,LeanVaultClawback,LeanVaultClosedEnded,LeanLoanBroker,LeanLoanBrokerCover,LeanLoan,LeanLoanSet,LeanLoanPay,LeanLoanManage
gcov=${GCOV:-$(ls /nix/store/*gcc-16.2.0/bin/gcov | head -1)}
gcovr=${GCOVR:-$(ls /nix/store/*gcovr*/bin/gcovr | head -1)}

cd "$root/build-cov"
make -j5 xrpld
find . -name '*.gcda' -delete
./xrpld --unittest="$suites" | tail -1

cd "$root"
mkdir -p "$out"
filter=(--filter 'src/libxrpl/tx/transactors/vault/' --filter 'src/libxrpl/tx/transactors/lending/'
        --filter 'src/libxrpl/ledger/helpers/VaultHelpers\.cpp' --filter 'src/libxrpl/ledger/helpers/LendingHelpers\.cpp')
"$gcovr" --root . --object-directory build-cov --gcov-executable "$gcov" "${filter[@]}" \
    --exclude-throw-branches --exclude-unreachable-branches --exclude-noncode-lines -j 6 \
    --txt "$out/summary.txt" --txt-metric branch --html-details "$out/index.html" --json "$out/coverage.json"
"$gcovr" --root . --object-directory build-cov --gcov-executable "$gcov" "${filter[@]}" \
    --exclude-throw-branches --exclude-unreachable-branches --exclude-noncode-lines -j 6 \
    --txt "$out/lines.txt"
