# Merged PRs

PRs merged into the `ripple/lending-protocol-fv` branch.

| PR                                                  | Title                                                                        | Author     | Branch                                                    | Merged     |
| --------------------------------------------------- | ---------------------------------------------------------------------------- | ---------- | --------------------------------------------------------- | ---------- |
| [#7817](https://github.com/XRPLF/rippled/pull/7817) | feat: Implement LoanBroker cash-basis accounting                             | @Tapanito  | `tapanito/lending-cash-basis`                             | 2026-07-27 |
| [#6383](https://github.com/XRPLF/rippled/pull/6383) | feat: Add tfVaultDonate feature                                              | @Tapanito  | `tapanito/vault-donation`                                 | 2026-07-27 |
| [#7820](https://github.com/XRPLF/rippled/pull/7820) | feat: Split LoanSet and LoanAccept                                           | @a1q123456 | `a1q123456/split-loan-set-and-loan-accept-implementation` | 2026-07-27 |
| [#8013](https://github.com/XRPLF/rippled/pull/8013) | fix: Exempt vault and loan broker accounts from IOU authorization            | @tyalymov  | `tialymov/FN-85-vault_iou_require_auth`                   | 2026-08-14 |
| [#8014](https://github.com/XRPLF/rippled/pull/8014) | fix: Reject vault deposits that move nothing from the depositor              | @tyalymov  | `tialymov/FN-86-deposit_share_truncation_sub_ulp`         | 2026-08-14 |
| [#8015](https://github.com/XRPLF/rippled/pull/8015) | fix: Return specific and consistent errors from vault_info                   | @tyalymov  | `tialymov/FN-84-vault_info_error_diagnostics`             | 2026-08-14 |
| [#7932](https://github.com/XRPLF/rippled/pull/7932) | fix: Exempt loan default from asset freeze                                   | @tyalymov  | `tialymov/FN-23-loan_default_freeze_guard`                | 2026-08-14 |
| [#7877](https://github.com/XRPLF/rippled/pull/7877) | fix: Remove credentials pinned to Vault, LoanBroker, and AMM pseudo-accounts | @tyalymov  | `FN-36-credential_pins_pseudo_account`                    | 2026-08-14 |
| [#7977](https://github.com/XRPLF/rippled/pull/7977) | fix: Tighten destination checks on vault withdrawal                          | @tyalymov  | `tialymov/FN-69-withdraw_destination_domain_check`        | 2026-08-14 |
| [#7950](https://github.com/XRPLF/rippled/pull/7950) | fix: Reject VaultWithdraw fixed-share amounts that round to zero             | @Tapanito  | `tapanito/lending-bugfix`                                 | 2026-08-14 |
| [#6528](https://github.com/XRPLF/rippled/pull/6528) | feat: Make VaultID conditional on LoanBrokerSet                              | @Tapanito  | `tapanito/loan-broker-set`                                | 2026-08-14 |
| [#6361](https://github.com/XRPLF/rippled/pull/6361) | Adds functionality to block vault deposits                                   | @Tapanito  | `tapanito/vault-block-deposit`                            | 2026-08-14 |
