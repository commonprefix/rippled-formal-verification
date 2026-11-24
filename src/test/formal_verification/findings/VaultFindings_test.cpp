#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/formal_verification/findings/LendingFindingsHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/escrow.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/beast/utility/Journal.h>
#include <xrpl/json/json_value.h>
#include <xrpl/ledger/ApplyView.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/ledger/helpers/VaultHelpers.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/UintTypes.h>

#include <array>
#include <chrono>
#include <cstdint>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace xrpl {

// One failing test per open bug in STAmount, in the vault transactions and in other transactions
// on vault shares. A test is enabled by uncommenting its call in run().
class VaultFindings_test : public LoanManageFixedPrecisionBase
{
    // Funds the accounts and pays the depositor an MPT that the issuer can claw back.
    static AssetAccounts
    setupClawbackMpt(test::jtx::Env& env, Number const& depositorFunds)
    {
        using namespace test::jtx;

        AssetAccounts accounts;
        env.fund(XRP(1'000'000), accounts.issuer, accounts.owner, accounts.depositor);
        env.close();

        MPTTester mpt{env, accounts.issuer, kMptInitNoFund};
        mpt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        accounts.asset = mpt.issuanceID();
        mpt.authorize({.account = accounts.owner});
        mpt.authorize({.account = accounts.depositor});
        env(pay(accounts.issuer, accounts.depositor, accounts.asset(depositorFunds)));
        env.close();
        return accounts;
    }

    // Creates an open-ended vault and takes the depositor's first deposit.
    static Keylet
    createVaultWithDeposit(
        test::jtx::Env& env,
        AssetAccounts const& accounts,
        Number const& firstDeposit)
    {
        using namespace test::jtx;

        Vault const vault{env};
        auto const [create, vaultKeylet] =
            vault.create({.owner = accounts.owner, .asset = accounts.asset});
        env(create);
        env.close();
        env(vault.deposit(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(firstDeposit)}));
        env.close();
        return vaultKeylet;
    }

    // A closed-ended vault in its Investment phase with one deposit from each holder, and its
    // broker with no cover and no fees. openLoan lends to the first holder.
    static LendingFixture
    createVaultAndBroker(
        test::jtx::Env& env,
        test::jtx::Account const& owner,
        std::vector<test::jtx::Account> const& holders,
        PrettyAsset const& asset,
        Number const& depositPerHolder)
    {
        using namespace test::jtx;

        auto const setup = makeClosedEndedVault(env, owner, asset, 60, 1'000'000);
        for (auto const& holder : holders)
        {
            env(setup.vault.deposit(
                {.depositor = holder, .id = setup.keylet.key, .amount = asset(depositPerHolder)}));
        }
        env.close();
        env.close(Tp{D{setup.sub + 1}});

        Keylet const brokerKeylet =
            keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        env(loan_broker::set(owner, setup.keylet.key));
        env.close();
        return {
            .vault = setup.vault,
            .vaultKeylet = setup.keylet,
            .brokerKeylet = brokerKeylet,
            .redemptionDate = Tp{D{setup.red}},
            .owner = owner,
            .depositor = holders.front(),
        };
    }

    // A closed-ended vault that lent its deposit as loan A at LateInterestRate 100%. Loan A was
    // paid two years late, so AssetsTotal is past 10^18.
    static Keylet
    setupLateInterestVault(
        test::jtx::Env& env,
        AssetAccounts const& accounts,
        Number const& deposit)
    {
        using namespace test::jtx;
        using namespace std::chrono_literals;

        // The depositor is the borrower and pays the late interest from these funds.
        env(pay(accounts.issuer, accounts.depositor, accounts.asset(Number{2, 18})));
        auto const fixture = setupLendingVault(
            env, accounts.owner, accounts.depositor, accounts.asset, deposit, 24h);
        std::uint32_t const paymentTotal = 150;
        Keylet const loanA = openLoanWithLateInterest(env, fixture, deposit, paymentTotal, 60);

        env.close(Tp{D{env.le(loanA)->at(sfStartDate)}} + 2 * 365 * 24h);
        // More than any installment with its late interest.
        STAmount const latePayment = accounts.asset(Number{3, 16}).value();
        for (std::uint32_t installment = 1; installment <= paymentTotal; ++installment)
        {
            env(loan::pay(accounts.depositor, loanA.key, latePayment, tfLoanLatePayment));
            env.close();
        }
        return fixture.vaultKeylet;
    }

    // The vault's share. Registers its issuer, the pseudo-account, so env.balance can read shares.
    static Asset
    shareOf(test::jtx::Env& env, Keylet const& vaultKeylet)
    {
        auto const vaultSle = env.le(vaultKeylet);
        env.memoize(test::jtx::Account{"vault", vaultSle->at(sfAccount)});
        return MPTIssue{vaultSle->at(sfShareMPTID)};
    }

    // The holder's part of AssetsTotal: its shares * AssetsTotal / SharesTotal.
    static Number
    shareValue(test::jtx::Env& env, Keylet const& vaultKeylet, test::jtx::Account const& holder)
    {
        auto const vaultSle = env.le(vaultKeylet);
        Number const sharesTotal =
            env.le(keylet::mptokenIssuance(vaultSle->at(sfShareMPTID)))->at(sfOutstandingAmount);
        Number const holderShares = env.balance(holder, shareOf(env, vaultKeylet)).value();
        return holderShares * Number{vaultSle->at(sfAssetsTotal)} / sharesTotal;
    }

    // Overwrites AssetsTotal and AssetsAvailable in the open ledger. The shares stay as they are.
    void
    stageVaultAssets(test::jtx::Env& env, Keylet const& vaultKeylet, Number const& assets)
    {
        BEAST_EXPECT(env.app().getOpenLedger().modify([&](OpenView& view, beast::Journal) {
            Sandbox sandbox{&view, TapNone};
            auto const vaultSle = sandbox.peek(vaultKeylet);
            if (!vaultSle)
                return false;
            vaultSle->at(sfAssetsTotal) = assets;
            vaultSle->at(sfAssetsAvailable) = assets;
            sandbox.update(vaultSle);
            sandbox.apply(view);
            return true;
        }));
    }

    // FV_M2_2: multiply() and divide() round a negative result in the wrong direction.
    void
    testMulDivRoundNegative()
    {
        testcase("FV_M2_2 MulDivRoundNegative");
        using Mode = Number::RoundingMode;

        Asset const xrp{xrpIssue()};
        Asset const mpt{MPTIssue{MPTID{}}};
        Asset const iou{noIssue()};

        // 1. Products that are not whole. Upward is 1 ULP above the Downward result given here.
        STAmount const minusSixPointTwo{iou, 62ULL, -1, true};
        STAmount const minusSixPointThree{iou, 63ULL, -1, true};
        STAmount const two{iou, 2ULL, 0, false};
        STAmount const minusFourNinths{iou, 4'444'444'444'444'444ULL, -16, true};
        STAmount const minusSixNinths{iou, 6'666'666'666'666'666ULL, -16, true};
        STAmount const eleven{iou, 11ULL, 0, false};
        using Product = std::tuple<std::string, STAmount, STAmount, Asset, std::int64_t>;
        auto const products = std::to_array<Product>({
            {"XRP -6.2 * 2", minusSixPointTwo, two, xrp, -13},
            {"XRP -6.3 * 2", minusSixPointThree, two, xrp, -13},
            {"MPT -6.2 * 2", minusSixPointTwo, two, mpt, -13},
            {"MPT -6.3 * 2", minusSixPointThree, two, mpt, -13},
            {"IOU -0.44...4 * 11", minusFourNinths, eleven, iou, -4'888'888'888'888'889},
            {"IOU -0.66...6 * 11", minusSixNinths, eleven, iou, -7'333'333'333'333'333},
        });
        for (auto const& [label, lhs, rhs, asset, roundedDown] : products)
        {
            for (Mode const mode : {Mode::Downward, Mode::Upward})
            {
                NumberRoundModeGuard const guard{mode};
                bool const isDownward = mode == Mode::Downward;
                STAmount const product = multiply(lhs, rhs, asset);
                std::int64_t const result =
                    product.signum() * static_cast<std::int64_t>(product.mantissa());
                // BUG: Downward returns the Upward result and Upward returns the Downward result.
                BEAST_EXPECTS(
                    result == (isDownward ? roundedDown : roundedDown + 1),
                    label + (isDownward ? " Downward: " : " Upward: ") + std::to_string(result));
            }
        }

        // 2. IOU quotients that are not exact at 16 digits.
        STAmount const nine{iou, 9ULL, 0, false};
        STAmount const minusFour{iou, 4ULL, 0, true};
        STAmount const minusSix{iou, 6ULL, 0, true};
        using Quotient = std::tuple<std::string, STAmount, Mode, std::int64_t>;
        auto const quotients = std::to_array<Quotient>({
            {"-4 / 9 ToNearest", minusFour, Mode::ToNearest, -4'444'444'444'444'444},
            {"-6 / 9 TowardsZero", minusSix, Mode::TowardsZero, -6'666'666'666'666'666},
            {"-6 / 9 Downward", minusSix, Mode::Downward, -6'666'666'666'666'667},
            {"-6 / 9 Upward", minusSix, Mode::Upward, -6'666'666'666'666'666},
        });
        for (auto const& [label, numerator, mode, expected] : quotients)
        {
            NumberRoundModeGuard const guard{mode};
            STAmount const quotient = divide(numerator, nine, iou);
            std::int64_t const result =
                quotient.signum() * static_cast<std::int64_t>(quotient.mantissa());
            // BUG: the result is 1 ULP further from zero.
            BEAST_EXPECTS(result == expected, "IOU " + label + ": " + std::to_string(result));
        }
    }

    // FV_M2_3: a VaultDeposit is charged less than its new shares are worth.
    void
    testVaultDepositOvervaluedShares()
    {
        testcase("FV_M2_3 VaultDepositOvervaluedShares");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts const accounts{.asset = xrpIssue()};
        env.fund(XRP(10'000), accounts.owner, accounts.depositor);
        env.close();

        // 1. The depositor's 3 drops mint 3 shares. The owner donates 2 drops.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, Number{3});
        env(Vault::deposit(
            {.depositor = accounts.owner,
             .id = vaultKeylet.key,
             .amount = accounts.asset(2),
             .flags = tfVaultDonate}));
        env.close();
        Number const valueBefore = shareValue(env, vaultKeylet, accounts.depositor);
        BEAST_EXPECT(valueBefore == Number{5});

        // 2. The owner deposits 4 drops and gets 2 shares for 3 drops.
        env(Vault::deposit(
            {.depositor = accounts.owner, .id = vaultKeylet.key, .amount = accounts.asset(4)}));
        env.close();
        Number const valueAfter = shareValue(env, vaultKeylet, accounts.depositor);

        // BUG: the depositor's 3 shares are worth 4.8 drops after the owner's deposit.
        BEAST_EXPECTS(
            valueAfter >= valueBefore,
            "the depositor's shares went from " + to_string(valueBefore) + " to " +
                to_string(valueAfter));
    }

    // FV_M2_3: a VaultWithdraw pays shares' worth rounded to nearest, at the other holders' cost.
    void
    testVaultWithdrawOvervaluedShares()
    {
        testcase("FV_M2_3 VaultWithdrawOvervaluedShares");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts const accounts{.asset = xrpIssue()};
        env.fund(XRP(10'000), accounts.owner, accounts.depositor);
        env.close();

        // 1. The depositor and the owner hold 4 shares each. The vault is staged to 6 drops.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, Number{4});
        env(Vault::deposit(
            {.depositor = accounts.owner, .id = vaultKeylet.key, .amount = accounts.asset(4)}));
        env.close();
        stageVaultAssets(env, vaultKeylet, Number{6});
        Number const valueBefore = shareValue(env, vaultKeylet, accounts.owner);
        BEAST_EXPECT(valueBefore == Number{3});

        // 2. The depositor withdraws its 4 shares one at a time. Each withdrawal pays 1 drop.
        STAmount const oneShare{shareOf(env, vaultKeylet), Number{1}};
        for (int withdrawal = 1; withdrawal <= 4; ++withdrawal)
        {
            env(Vault::withdraw(
                {.depositor = accounts.depositor, .id = vaultKeylet.key, .amount = oneShare}));
        }
        Number const valueAfter = shareValue(env, vaultKeylet, accounts.owner);

        // BUG: the owner's 4 shares are worth 2 drops after the depositor's withdrawals.
        BEAST_EXPECTS(
            valueAfter >= valueBefore,
            "the owner's shares went from " + to_string(valueBefore) + " to " +
                to_string(valueAfter));
    }

    // FV_M2_3: an IOU VaultDeposit is charged its shares' worth rounded down to the vault scale.
    void
    testVaultDepositChargeFloored()
    {
        testcase("FV_M2_3 VaultDepositChargeFloored");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const accounts = setupIou(env, {.ownerFunds = Number{30}});
        Account const holder{"holder"};
        fundIouHolder(env, holder, accounts, Number{1'000}, Number{70});

        // 1. A Scale 2 vault, base unit 0.01 USD. The holder's 70 USD mint 7,000 shares and the
        //    owner donates 30 USD, so a share is worth 0.0143 USD.
        auto const [vault, vaultKeylet] = createScaledVault(env, accounts.owner, accounts.asset, 2);
        env(vault.deposit(
            {.depositor = holder, .id = vaultKeylet.key, .amount = accounts.asset(70)}));
        env(vault.deposit(
            {.depositor = accounts.owner,
             .id = vaultKeylet.key,
             .amount = accounts.asset(30),
             .flags = tfVaultDonate}));
        env.close();
        Number const holderValueBefore = shareValue(env, vaultKeylet, holder);
        BEAST_EXPECT(holderValueBefore == Number{100});

        // 2. The depositor deposits 0.03 USD and gets 2 shares worth 0.0286 USD.
        STAmount const deposit = accounts.asset(Number{3, -2});
        Number const fundsBefore = env.balance(accounts.depositor, accounts.asset).value();
        env(vault.deposit(
            {.depositor = accounts.depositor, .id = vaultKeylet.key, .amount = deposit}));
        env.close();
        Number const charged =
            fundsBefore - env.balance(accounts.depositor, accounts.asset).value();
        Number const sharesWorth = shareValue(env, vaultKeylet, accounts.depositor);
        // BUG: the deposit is charged 0.02 USD.
        BEAST_EXPECTS(
            charged >= sharesWorth,
            "charged " + to_string(charged) + " for shares worth " + to_string(sharesWorth));

        // 3. The depositor deposits 0.03 USD 99 more times and then withdraws all its shares.
        for (int count = 1; count < 100; ++count)
        {
            env(vault.deposit(
                {.depositor = accounts.depositor, .id = vaultKeylet.key, .amount = deposit}));
            env.close();
        }
        env(vault.withdraw(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = env.balance(accounts.depositor, shareOf(env, vaultKeylet)).value()}));
        env.close();

        Number const fundsAfter = env.balance(accounts.depositor, accounts.asset).value();
        // BUG: the depositor ends 0.83 USD up.
        BEAST_EXPECTS(
            fundsAfter <= fundsBefore,
            "the depositor went from " + to_string(fundsBefore) + " to " + to_string(fundsAfter));
        Number const holderValueAfter = shareValue(env, vaultKeylet, holder);
        // BUG: the holder's shares are worth 99.17 USD.
        BEAST_EXPECTS(
            holderValueAfter >= holderValueBefore,
            "the holder's shares went from " + to_string(holderValueBefore) + " to " +
                to_string(holderValueAfter));
    }

    // FV_M2_20: at 1 unit per share a deposit, withdrawal or clawback of 5,005 moves 5,004.
    void
    testVaultShareCountRounding()
    {
        testcase("FV_M2_20 VaultShareCountRounding");
        using namespace test::jtx;

        Number const vaultSize{4'577'096'644'444'257LL};
        Number const amount{5'005};
        {
            // 1. An MPT vault of 4,577,096,644,444,257 units and shares takes a deposit of 5,005.
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const accounts = setupClawbackMpt(env, vaultSize + amount);
            Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, vaultSize);
            Asset const share = shareOf(env, vaultKeylet);
            Number const unitsBefore = env.balance(accounts.depositor, accounts.asset).value();
            Number const sharesBefore = env.balance(accounts.depositor, share).value();
            env(Vault::deposit(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(amount)}));
            env.close();
            Number const minted = env.balance(accounts.depositor, share).value() - sharesBefore;
            Number const charged =
                unitsBefore - env.balance(accounts.depositor, accounts.asset).value();

            // BUG: the deposit mints 5,004 shares.
            BEAST_EXPECTS(minted == amount, "the deposit minted " + to_string(minted));
            // BUG: the deposit is charged 5,004.
            BEAST_EXPECTS(charged == amount, "the deposit was charged " + to_string(charged));
        }
        {
            // 2. A vault of the same size pays a withdrawal of 5,005.
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const accounts = setupClawbackMpt(env, vaultSize);
            Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, vaultSize);
            Number const unitsBefore = env.balance(accounts.depositor, accounts.asset).value();
            env(Vault::withdraw(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(amount)}));
            env.close();
            Number const paid =
                env.balance(accounts.depositor, accounts.asset).value() - unitsBefore;

            // BUG: the withdrawal pays 5,004.
            BEAST_EXPECTS(paid == amount, "the withdrawal paid " + to_string(paid));
        }
        {
            // 3. A vault of the same size takes a clawback of 5,005.
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const accounts = setupClawbackMpt(env, vaultSize);
            Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, vaultSize);
            Number const vaultBefore = snapshotVault(env, vaultKeylet, accounts.asset).vaultBalance;
            env(Vault::clawback(
                {.issuer = accounts.issuer,
                 .id = vaultKeylet.key,
                 .holder = accounts.depositor,
                 .amount = accounts.asset(amount).value()}));
            env.close();
            Number const recovered =
                vaultBefore - snapshotVault(env, vaultKeylet, accounts.asset).vaultBalance;

            // BUG: the clawback recovers 5,004.
            BEAST_EXPECTS(recovered == amount, "the clawback recovered " + to_string(recovered));
        }
        {
            // 4. A vault of 6,564,360,495 units and shares takes a clawback of 6,564,364,663.
            Env env{*this, all_ | featureLendingProtocolV1_1};
            Number const smallVaultSize{6'564'360'495LL};
            auto const accounts = setupClawbackMpt(env, smallVaultSize);
            Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, smallVaultSize);
            env(Vault::clawback(
                {.issuer = accounts.issuer,
                 .id = vaultKeylet.key,
                 .holder = accounts.depositor,
                 .amount = accounts.asset(Number{6'564'364'663LL}).value()}));
            env.close();
            Number const sharesLeft =
                env.balance(accounts.depositor, shareOf(env, vaultKeylet)).value();

            // BUG: the clawback leaves the depositor 1 share and the vault 1 unit.
            BEAST_EXPECTS(
                sharesLeft == Number{0}, "the clawback left " + to_string(sharesLeft) + " shares");
        }
    }

    // FV_M2_21: an IOU VaultDeposit of 10^15 base units is charged more than its shares are worth.
    void
    testVaultDepositOvercharge()
    {
        testcase("FV_M2_21 VaultDepositOvercharge");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const firstDeposit{2'000'000'000'000'000LL};
        Number const donation{1'000'000'000'000'000LL};
        Number const deposit{1'000'000'000'000'004LL};
        Number const trustLimit{1, 16};
        auto const accounts = setupIou(
            env,
            {.depositorTrust = trustLimit,
             .ownerTrust = trustLimit,
             .depositorFunds = firstDeposit + deposit,
             .ownerFunds = donation});

        // 1. An IOU vault at Scale 0 takes a first deposit and a donation. A share is worth 1.5.
        auto const [vault, vaultKeylet] = createScaledVault(env, accounts.owner, accounts.asset, 0);
        env(vault.deposit(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(firstDeposit)}));
        env.close();
        env(vault.deposit(
            {.depositor = accounts.owner,
             .id = vaultKeylet.key,
             .amount = accounts.asset(donation),
             .flags = tfVaultDonate}));
        env.close();

        // 2. The deposit mints 666,666,666,666,669 shares, worth 1,000,000,000,000,003.5.
        Number const unitsBefore = env.balance(accounts.depositor, accounts.asset).value();
        env(vault.deposit(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(deposit)}));
        env.close();
        Number const charged =
            unitsBefore - env.balance(accounts.depositor, accounts.asset).value();

        // BUG: the deposit is charged 1,000,000,000,000,004.
        BEAST_EXPECTS(
            charged == Number{1'000'000'000'000'003LL},
            "the deposit was charged " + to_string(charged));
    }

    // FV_M2_22: an MPT VaultDeposit far above the Open limit returns tecINTERNAL.
    void
    testVaultDepositInternalError()
    {
        testcase("FV_M2_22 VaultDepositInternalError");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const firstDeposit{2};
        Number const largeDeposit{5'000'000'000'000'000'003LL};
        auto const accounts = setupClawbackMpt(env, firstDeposit + largeDeposit);

        // 1. An MPT vault takes 2 units and mints 2 shares.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, firstDeposit);

        // 2. A deposit of 5,000,000,000,000,000,003. The Open limit is 9,000,000,000,000,000.
        // BUG: the deposit returns tecINTERNAL.
        env(Vault::deposit(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(largeDeposit)}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M2_23: an IOU VaultDeposit far above the Open limit returns tecPATH_DRY.
    void
    testVaultDepositPathDry()
    {
        testcase("FV_M2_23 VaultDepositPathDry");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const firstDeposit{10};
        Number const largeDeposit{1'000'000'000};
        auto const accounts = setupIou(
            env,
            {.depositorTrust = Number{2'000'000'000},
             .depositorFunds = firstDeposit + largeDeposit});

        // 1. An IOU vault at Scale 10 takes 10 and mints 10^11 shares.
        auto const [vault, vaultKeylet] =
            createScaledVault(env, accounts.owner, accounts.asset, 10);
        env(vault.deposit(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(firstDeposit)}));
        env.close();

        // 2. A deposit of 1,000,000,000. The Open limit is 900,000.
        // BUG: the deposit returns tecPATH_DRY.
        env(vault.deposit(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(largeDeposit)}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M2_24: a VaultDeposit that takes SharesTotal past 2^63 - 1 returns tecPATH_DRY.
    void
    testVaultDepositSharesOverflow()
    {
        testcase("FV_M2_24 VaultDepositSharesOverflow");
        using namespace test::jtx;

        Env env{
            *this,
            (all_ | featureLendingProtocolV1_1) - featureLendingProtocolV1_2 - fixCleanup3_4_0};
        Number const deposit{5};
        auto const accounts = setupIou(env);

        // 1. An IOU vault at Scale 18, created without LendingProtocolV1_2 and fixCleanup3_4_0.
        //    It is not a fixed precision vault and has no Open limit.
        auto const [vault, vaultKeylet] =
            createScaledVault(env, accounts.owner, accounts.asset, 18);
        BEAST_EXPECT(getVaultVersion(env.le(vaultKeylet)) != VaultVersion::FixedPrecision);

        // 2. A deposit of 5 mints 5 * 10^18 shares.
        env(vault.deposit(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(deposit)}));
        env.close();
        Number const minted = env.balance(accounts.depositor, shareOf(env, vaultKeylet)).value();
        BEAST_EXPECT(minted == (Number{5, 18}));

        // 3. LendingProtocolV1_2 and fixCleanup3_4_0 are enabled.
        env.enableFeature(featureLendingProtocolV1_2);
        env.enableFeature(fixCleanup3_4_0);
        env.close();
        BEAST_EXPECT(env.enabled(featureLendingProtocolV1_2) && env.enabled(fixCleanup3_4_0));

        // 4. A second deposit of 5 takes SharesTotal to 10^19, above 2^63 - 1.
        // BUG: the deposit returns tecPATH_DRY.
        env(vault.deposit(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(deposit)}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M2_25: an XRP VaultWithdraw of shares worth over 10^17 drops returns tefEXCEPTION.
    void
    testVaultWithdrawXRPRange()
    {
        testcase("FV_M2_25 VaultWithdrawXRPRange");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts const accounts{.asset = xrpIssue()};
        Account const outsider{"outsider"};
        env.fund(XRP(10'000), accounts.owner, accounts.depositor, outsider);
        env.close();

        // 1. The depositor's 100 drops mint 100 shares, so a share is worth 1 drop.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, Number{100});
        Asset const share = shareOf(env, vaultKeylet);

        // 2. 10^17 shares are worth 10^17 drops. The outsider holds no shares.
        env(Vault::withdraw(
                {.depositor = outsider,
                 .id = vaultKeylet.key,
                 .amount = STAmount{share, Number{100'000'000'000'000'000}}}),
            Ter(tecINSUFFICIENT_FUNDS));
        env.close();

        // 3. One share more is worth 10^17 + 1 drops.
        // BUG: the result is tefEXCEPTION.
        env(Vault::withdraw(
                {.depositor = outsider,
                 .id = vaultKeylet.key,
                 .amount = STAmount{share, Number{100'000'000'000'000'001}}}),
            Ter(tecINSUFFICIENT_FUNDS));
        env.close();
    }

    // FV_M2_26: vault shares can be escrowed when the vault's MPT asset has no CanEscrow.
    void
    testShareEscrowAssetForbidsEscrow()
    {
        testcase("FV_M2_26 ShareEscrowAssetForbidsEscrow");
        using namespace test::jtx;
        using namespace std::chrono_literals;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const deposit{100};
        Account const recipient{"recipient"};
        auto const accounts = setupClawbackMpt(env, deposit);
        env.fund(XRP(1'000'000), recipient);
        env.close();

        // 1. A vault of an MPT with CanClawback and no CanEscrow takes 100 and mints 100 shares.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, deposit);
        Asset const share = shareOf(env, vaultKeylet);

        // 2. The depositor escrows 60 shares for the recipient.
        // BUG: EscrowCreate returns tesSUCCESS.
        env(escrow::create(accounts.depositor, recipient, STAmount{share, Number{60}}),
            escrow::kFinishTime(env.now() + 1'000s),
            Ter(tecNO_PERMISSION));
        env.close();

        // 3. The issuer claws back all shares of the depositor. The owner deletes the vault.
        env(Vault::clawback(
            {.issuer = accounts.issuer, .id = vaultKeylet.key, .holder = accounts.depositor}));
        env.close();
        // BUG: VaultDelete returns tecHAS_OBLIGATIONS. The 60 escrowed shares remain.
        env(Vault::del({.owner = accounts.owner, .id = vaultKeylet.key}), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M2_27: a holder that deleted its MPToken escapes a lock and withdraws to a third party.
    void
    testWithdrawAfterHolderDeletesMPToken()
    {
        testcase("FV_M2_27 WithdrawAfterHolderDeletesMPToken");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const deposit{100};
        AssetAccounts accounts;
        Account const thirdParty{"thirdParty"};
        env.fund(XRP(1'000'000), accounts.issuer, accounts.owner, accounts.depositor, thirdParty);
        env.close();

        // 1. An MPT with CanLock. The depositor holds 100 and the third party an empty MPToken.
        MPTTester mpt{env, accounts.issuer, kMptInitNoFund};
        mpt.create({.flags = tfMPTCanLock | tfMPTCanTransfer});
        accounts.asset = mpt.issuanceID();
        mpt.authorize({.account = accounts.depositor});
        mpt.authorize({.account = thirdParty});
        env(pay(accounts.issuer, accounts.depositor, accounts.asset(deposit)));
        env.close();

        // 2. A vault takes the depositor's whole balance.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, deposit);

        // 3. The depositor deletes its MPToken of the asset.
        mpt.authorize({.account = accounts.depositor, .flags = tfMPTUnauthorize});
        env.close();

        // 4. The issuer locks the depositor. There is no MPToken to lock.
        mpt.set(
            {.account = accounts.issuer,
             .holder = accounts.depositor,
             .flags = tfMPTLock,
             .err = tecOBJECT_NOT_FOUND});
        env.close();

        // 5. The depositor withdraws the 100 to the third party.
        json::Value withdraw = Vault::withdraw(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(deposit)});
        withdraw[sfDestination] = thirdParty.human();
        // BUG: VaultWithdraw returns tesSUCCESS.
        env(withdraw, Ter(tecLOCKED));
        env.close();
    }

    // FV_M2_28: without MPTokensV2 a share Payment between NoRipple holders returns terNO_RIPPLE.
    void
    testSharePaymentNoRipple()
    {
        testcase("FV_M2_28 SharePaymentNoRipple");
        using namespace test::jtx;

        Env env{*this, (all_ | featureLendingProtocolV1_1) - featureMPTokensV2};
        Number const deposit{100};
        Account const recipient{"recipient"};
        auto const accounts = setupIou(env, {.depositorFunds = deposit});
        env.fund(XRP(1'000'000), recipient);
        env.close();
        env(trust(recipient, accounts.asset(1'000)));
        env.close();

        // 1. An IOU vault takes the depositor's 100. The recipient creates its share MPToken.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, deposit);
        Asset const share = shareOf(env, vaultKeylet);
        env(MPTTester::authorizeJV(
            {.account = recipient, .id = env.le(vaultKeylet)->at(sfShareMPTID)}));
        env.close();

        // 2. The issuer disables rippling on its trust lines with the depositor and the recipient.
        env(trust(accounts.issuer, accounts.depositor["USD"](0), tfSetNoRipple));
        env(trust(accounts.issuer, recipient["USD"](0), tfSetNoRipple));
        env.close();

        // 3. The depositor pays 10 shares to the recipient.
        env(pay(accounts.depositor, recipient, STAmount{share, Number{10}}), Ter(std::ignore));
        // BUG: the Payment returns terNO_RIPPLE.
        BEAST_EXPECTS(isTecClaim(env.ter()), "the Payment returned " + transToken(env.ter()));
    }

    // FV_M2_31: an unauthorized MPT holder still withdraws its deposit to a third party.
    void
    testWithdrawByUnauthorizedHolder()
    {
        testcase("FV_M2_31 WithdrawByUnauthorizedHolder");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts accounts;
        Account const thirdParty{"thirdParty"};
        env.fund(XRP(1'000'000), accounts.issuer, accounts.owner, accounts.depositor, thirdParty);
        env.close();

        // 1. An MPT with RequireAuth. The issuer authorizes the depositor and the third party.
        MPTTester mpt{env, accounts.issuer, kMptInitNoFund};
        mpt.create(
            {.authorize = Holders{accounts.depositor, thirdParty},
             .pay = {{Holders{accounts.depositor}, 1'000}},
             .flags = tfMPTCanTransfer | tfMPTRequireAuth,
             .authHolder = true});
        accounts.asset = mpt.issuanceID();

        // 2. The depositor puts its 1,000 in a vault.
        Keylet const vaultKeylet = createVaultWithDeposit(env, accounts, Number{1'000});

        // 3. The issuer unauthorizes the depositor. A withdrawal to itself is refused.
        mpt.authorize({.holder = accounts.depositor, .flags = tfMPTUnauthorize});
        env(Vault::withdraw(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = accounts.asset(100)}),
            Ter(tecNO_AUTH));
        env.close();

        // 4. The depositor withdraws 100 to the third party.
        json::Value withdraw = Vault::withdraw(
            {.depositor = accounts.depositor,
             .id = vaultKeylet.key,
             .amount = accounts.asset(100)});
        withdraw[sfDestination] = thirdParty.human();
        // BUG: VaultWithdraw returns tesSUCCESS and the third party receives 100.
        env(withdraw, Ter(tecNO_AUTH));
        env.close();
    }

    // FV_M2_31: an unauthorized MPT broker owner still withdraws its cover to a third party.
    void
    testCoverWithdrawByUnauthorizedOwner()
    {
        testcase("FV_M2_31 CoverWithdrawByUnauthorizedOwner");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts accounts;
        Account const thirdParty{"thirdParty"};
        env.fund(XRP(1'000'000), accounts.issuer, accounts.owner, accounts.depositor, thirdParty);
        env.close();

        // 1. An MPT with RequireAuth. The owner, the depositor and the third party are authorized.
        MPTTester mpt{env, accounts.issuer, kMptInitNoFund};
        mpt.create(
            {.authorize = Holders{accounts.owner, accounts.depositor, thirdParty},
             .pay = {{Holders{accounts.owner, accounts.depositor}, 1'000}},
             .flags = tfMPTCanTransfer | tfMPTRequireAuth,
             .authHolder = true});
        accounts.asset = mpt.issuanceID();

        // 2. A lending vault with the depositor's 1,000. The owner's 1,000 is the broker's cover.
        auto const fixture = setupLendingVault(
            env, accounts.owner, accounts.depositor, accounts.asset, Number{1'000});
        env(loan_broker::coverDeposit(
            accounts.owner, fixture.brokerKeylet.key, accounts.asset(1'000).value()));
        env.close();

        // 3. The issuer unauthorizes the owner. A withdrawal of the cover to itself is refused.
        mpt.authorize({.holder = accounts.owner, .flags = tfMPTUnauthorize});
        env(loan_broker::coverWithdraw(
                accounts.owner, fixture.brokerKeylet.key, accounts.asset(1'000).value()),
            Ter(tecNO_AUTH));
        env.close();

        // 4. The owner withdraws the whole cover to the third party.
        // BUG: LoanBrokerCoverWithdraw returns tesSUCCESS and the third party receives 1,000.
        env(loan_broker::coverWithdraw(
                accounts.owner, fixture.brokerKeylet.key, accounts.asset(1'000).value()),
            loan_broker::kDestination(thirdParty),
            Ter(tecNO_AUTH));
        env.close();
    }

    // FV_M2_32: a VaultWithdraw to another account fails on its limit though the payout fits.
    void
    testVaultWithdrawDestinationLimit()
    {
        testcase("FV_M2_32 VaultWithdrawDestinationLimit");
        using namespace test::jtx;
        using namespace std::chrono_literals;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(env, {.ownerFunds = Number{100}});
        Account const carol{"carol"};
        Account const dave{"dave"};
        env.fund(XRP(1'000'000), carol, dave);
        env.close();
        env(trust(carol, asset(Number{15, -1})));
        env(trust(dave, asset(Number{15, -1})));
        env.close();

        // 1. A closed-ended vault with Scale 1. The depositor gets 40 shares for 4 USD and the
        //    owner donates 2 USD, so one share is worth 0.15 USD.
        Vault const vault{env};
        auto [tx, vaultKeylet, subscriptionDate] =
            vault.createClosedEnded({.owner = owner, .asset = asset, .investmentWindow = 1000s});
        tx[sfScale] = 1;
        env(tx);
        env.close();
        env(vault.deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = asset(4)}));
        env(vault.deposit(
            {.depositor = owner,
             .id = vaultKeylet.key,
             .amount = asset(2),
             .flags = tfVaultDonate}));
        env.close();
        MPTIssue const share{env.le(vaultKeylet)->at(sfShareMPTID)};
        vault.closePastSubscription(subscriptionDate);
        env.close(subscriptionDate + 1000s + 1s);

        // 2. 10 shares to carol, whose limit is 1.5 USD, pay her 1.5 USD.
        json::Value toCarol = Vault::withdraw(
            {.depositor = depositor, .id = vaultKeylet.key, .amount = STAmount{share, 10}});
        toCarol[sfDestination] = carol.human();
        env(toCarol);
        env.close();
        BEAST_EXPECT(env.balance(carol, asset) == asset(Number{15, -1}));

        // 3. 1.6 USD to dave, whose limit is 1.5 USD, rounds down to 10 shares and pays 1.5 USD.
        json::Value toDave = Vault::withdraw(
            {.depositor = depositor, .id = vaultKeylet.key, .amount = asset(Number{16, -1})});
        toDave[sfDestination] = dave.human();
        // BUG: the result is tecNO_LINE.
        env(toDave, Ter(tesSUCCESS));
        env.close();
    }

    // FV_M2_32: an early-exit VaultWithdraw fails on the destination limit though the payout fits.
    void
    testEarlyExitDestinationLimit()
    {
        testcase("FV_M2_32 EarlyExitDestinationLimit");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(env);
        Account const dave{"dave"};
        env.fund(XRP(1'000'000), dave);
        env.close();
        env(trust(dave, asset(1)));
        env.close();

        // 1. A Scale 1 closed-ended vault, early-exit fee 50%. 4 USD buy the depositor 40 shares.
        Vault const vault{env};
        auto [tx, vaultKeylet, subscriptionDate] =
            vault.createClosedEnded({.owner = owner, .asset = asset, .earlyExitFeeRate = 50'000});
        tx[sfScale] = 1;
        env(tx);
        env.close();
        env(vault.deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = asset(4)}));
        env.close();
        MPTIssue const share{env.le(vaultKeylet)->at(sfShareMPTID)};
        vault.closePastSubscription(subscriptionDate);

        // 2. In the Investment phase 20 shares to dave, whose limit is 1 USD, are worth 2 USD and
        //    pay 1 USD after the fee.
        json::Value toDave = Vault::withdraw(
            {.depositor = depositor, .id = vaultKeylet.key, .amount = STAmount{share, 20}});
        toDave[sfDestination] = dave.human();
        // BUG: the result is tecNO_LINE.
        env(toDave, Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_24: two holders whose shares are each worth less than one base unit can't redeem them.
    void
    testVaultDustHoldersLocked()
    {
        testcase("FV_M4_24 VaultDustHoldersLocked");
        using namespace test::jtx;
        using namespace std::chrono_literals;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        Number const holderDeposit{1'000};
        Number const trustLimit{10'000};
        Number const baseUnit{1, -6};
        Account const holderA{"holderA"};
        Account const holderB{"holderB"};
        auto const accounts = setupIou(env, {.ownerOnly = true});
        fundIouHolder(env, holderA, accounts, trustLimit, holderDeposit);
        fundIouHolder(env, holderB, accounts, trustLimit, holderDeposit);

        // 1. A closed-ended IOU vault at Scale 6 takes 1,000 from holder A and 1,000 from holder B.
        auto const fixture = createVaultAndBroker(
            env, accounts.owner, {holderA, holderB}, accounts.asset, holderDeposit);

        // 2. Loan A lends 1,999.999999 in one installment and is defaulted with no cover.
        Keylet const loanA = openLoan(env, fixture, 2 * holderDeposit - baseUnit, 1);
        defaultAfterGrace(env, accounts.owner, loanA);
        env(loan::del(accounts.owner, loanA.key));
        env(loan_broker::del(accounts.owner, fixture.brokerKeylet.key));
        env.close();

        // 3. The vault reaches its Redemption phase with AssetsTotal 0.000001, one base unit.
        env.close(fixture.redemptionDate + 1s);
        BEAST_EXPECT(Number{env.le(fixture.vaultKeylet)->at(sfAssetsTotal)} == baseUnit);

        // 4. Each holder redeems all its shares.
        Asset const share = shareOf(env, fixture.vaultKeylet);
        for (auto const& holder : {holderA, holderB})
        {
            // BUG: the withdrawal returns tecPRECISION_LOSS.
            env(Vault::withdraw(
                    {.depositor = holder,
                     .id = fixture.vaultKeylet.key,
                     .amount = env.balance(holder, share)}),
                Ter(tesSUCCESS));
            env.close();
        }

        // 5. The owner deletes the vault.
        // BUG: VaultDelete returns tecHAS_OBLIGATIONS.
        env(Vault::del({.owner = accounts.owner, .id = fixture.vaultKeylet.key}), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_36: a full VaultClawback on an MPT vault grown by late interest returns tecINTERNAL.
    void
    testVaultClawbackMptRounding()
    {
        testcase("FV_M4_36 VaultClawbackMptRounding");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT vault takes 8,999,999,999,999,942 and grows by late interest.
        Number const deposit{8'999'999'999'999'942LL};
        auto const accounts = setupClawbackMpt(env, deposit);
        Keylet const vaultKeylet = setupLateInterestVault(env, accounts, deposit);
        BEAST_EXPECT(
            Number{env.le(vaultKeylet)->at(sfAssetsTotal)} == Number{1'367'945'414'764'070'474LL});

        // 2. The issuer claws back every share of the depositor.
        // BUG: the clawback returns tecINTERNAL.
        env(Vault::clawback(
                {.issuer = accounts.issuer,
                 .id = vaultKeylet.key,
                 .holder = accounts.depositor,
                 .amount = accounts.asset(0).value()}),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_37: the last holder of an MPT vault grown by late interest can't withdraw all shares.
    void
    testVaultWithdrawMptAllShares()
    {
        testcase("FV_M4_37 VaultWithdrawMptAllShares");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT vault takes 8,999,999,999,999,942 and grows by late interest.
        Number const deposit{8'999'999'999'999'942LL};
        auto const accounts = setupClawbackMpt(env, deposit);
        Keylet const vaultKeylet = setupLateInterestVault(env, accounts, deposit);
        BEAST_EXPECT(
            Number{env.le(vaultKeylet)->at(sfAssetsTotal)} == Number{1'367'945'414'764'070'474LL});

        // 2. The depositor, who holds every share, withdraws all of them.
        // BUG: the withdrawal returns tecINSUFFICIENT_FUNDS.
        env(Vault::withdraw(
                {.depositor = accounts.depositor,
                 .id = vaultKeylet.key,
                 .amount = env.balance(accounts.depositor, shareOf(env, vaultKeylet))}),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_38: a full MPT VaultClawback that leaves 1 unit fails with tecINVARIANT_FAILED.
    void
    testVaultClawbackMptRemainder()
    {
        testcase("FV_M4_38 VaultClawbackMptRemainder");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT vault takes 8,999,999,999,999,916 and grows by late interest.
        Number const deposit{8'999'999'999'999'916LL};
        auto const accounts = setupClawbackMpt(env, deposit);
        Keylet const vaultKeylet = setupLateInterestVault(env, accounts, deposit);
        BEAST_EXPECT(
            Number{env.le(vaultKeylet)->at(sfAssetsTotal)} == Number{1'367'945'414'764'066'518LL});

        // 2. The issuer claws back every share of the depositor.
        // BUG: the clawback returns tecINVARIANT_FAILED.
        env(Vault::clawback(
                {.issuer = accounts.issuer,
                 .id = vaultKeylet.key,
                 .holder = accounts.depositor,
                 .amount = accounts.asset(0).value()}),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_43: on an MPT vault past 10^18 units a withdrawal or clawback pays 1 unit too much.
    void
    testVaultWithdrawAboveRequested()
    {
        testcase("FV_M4_43 VaultWithdrawAboveRequested");
        using namespace test::jtx;

        Number const requested{1'188'634'584'658'890'914LL};
        for (bool const isClawback : {false, true})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};

            // 1. An MPT vault takes 8,999,999,999,999,942 and grows by late interest.
            Number const deposit{8'999'999'999'999'942LL};
            auto const accounts = setupClawbackMpt(env, deposit);
            Keylet const vaultKeylet = setupLateInterestVault(env, accounts, deposit);

            // 2. The depositor withdraws 1,188,634,584,658,890,914, or the issuer claws it back.
            Number const vaultBefore = snapshotVault(env, vaultKeylet, accounts.asset).vaultBalance;
            STAmount const amount = accounts.asset(requested).value();
            env(isClawback ? Vault::clawback(
                                 {.issuer = accounts.issuer,
                                  .id = vaultKeylet.key,
                                  .holder = accounts.depositor,
                                  .amount = amount})
                           : Vault::withdraw(
                                 {.depositor = accounts.depositor,
                                  .id = vaultKeylet.key,
                                  .amount = amount}));
            env.close();
            Number const paid =
                vaultBefore - snapshotVault(env, vaultKeylet, accounts.asset).vaultBalance;

            // BUG: the vault pays out 1,188,634,584,658,890,915.
            BEAST_EXPECTS(
                paid <= requested,
                std::string{isClawback ? "the clawback" : "the withdrawal"} + " paid out " +
                    to_string(paid));
        }
    }

    // FV_M4_52: an XRP donation that takes AssetsTotal above 10^17 drops returns tefEXCEPTION.
    void
    testVaultDonateXRPRange()
    {
        testcase("FV_M4_52 VaultDonateXRPRange");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};
        AssetAccounts const accounts{.asset = xrpIssue()};
        env.fund(XRP(4'700'000'000LL), accounts.owner);
        env.fund(XRP(94'700'000'000LL), accounts.depositor);
        env.close();

        // 1. An XRP vault with 9 * 10^15 drops, all of it lent in loans A and B.
        auto const fixture = setupLendingVault(
            env,
            accounts.owner,
            accounts.depositor,
            accounts.asset,
            Number{9'000'000'000'000'000LL},
            std::chrono::seconds{946'000'000});
        Number const principal{4'500'000'000'000'000LL};
        Keylet const loanA = openLoanWithLateInterest(env, fixture, principal);
        openLoanWithLateInterest(env, fixture, principal);

        // 2. Loan A is paid 20 years late. Its late interest takes AssetsTotal to 9.9 * 10^16
        //    drops, of which loan B still owes 4.5 * 10^15.
        std::chrono::seconds const twentyYears{20 * 365 * 24 * 60 * 60};
        env.close(Tp{D{env.le(loanA)->at(sfNextPaymentDueDate)}} + twentyYears);
        Number const paidLate{94'600'000'000'000'000LL};
        env(loan::pay(
            accounts.depositor, loanA.key, accounts.asset(paidLate).value(), tfLoanLatePayment));
        env.close();

        // 3. A donation that keeps AssetsTotal below 10^17 drops is above the Open limit.
        env(Vault::deposit(
                {.depositor = accounts.owner,
                 .id = fixture.vaultKeylet.key,
                 .amount = accounts.asset(Number{400'000'000'000'000LL}),
                 .flags = tfVaultDonate}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 4. A donation of 4.5 * 10^15 drops takes AssetsTotal above 10^17 drops.
        // BUG: the result is tefEXCEPTION.
        env(Vault::deposit(
                {.depositor = accounts.owner,
                 .id = fixture.vaultKeylet.key,
                 .amount = accounts.asset(principal),
                 .flags = tfVaultDonate}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M4_60: an MPT donation that takes AssetsTotal above 2^63 - 1 returns tefEXCEPTION.
    void
    testVaultDonateMPTRange()
    {
        testcase("FV_M4_60 VaultDonateMPTRange");
        using namespace test::jtx;

        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT that allows 2^63 - 1 units. The depositor holds 9.5 * 10^16 of them and the
        //    vault owner 9.128 * 10^18.
        auto const [issuer, owner, depositor, asset] = setupMpt(
            env,
            {.maxAmt = kMaxMpTokenAmount,
             .withDepositor = true,
             .holderFunds = 95'000'000'000'000'000ULL});
        Number const ownerFunds{9'128'000'000'000'000'000LL};
        env(pay(issuer, owner, asset(ownerFunds)));
        env.close();

        // 2. A vault with 9 * 10^15 units, all of it lent in loans A and B.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{9'000'000'000'000'000LL},
            std::chrono::seconds{946'000'000});
        Number const principal{4'500'000'000'000'000LL};
        Keylet const loanA = openLoanWithLateInterest(env, fixture, principal);
        openLoanWithLateInterest(env, fixture, principal);

        // 3. Loan A is paid 20 years late. Its late interest takes AssetsTotal to 9.9 * 10^16
        //    units, of which loan B still owes 4.5 * 10^15.
        std::uint32_t const dueDate = env.le(loanA)->at(sfNextPaymentDueDate);
        std::chrono::seconds const twentyYears{20 * 365 * 24 * 60 * 60};
        env.close(NetClock::time_point{NetClock::duration{dueDate}} + twentyYears);
        Number const paidLate{94'600'000'000'000'000LL};
        env(loan::pay(depositor, loanA.key, asset(paidLate), tfLoanLatePayment));
        env.close();

        // 4. A donation that keeps AssetsTotal below 2^63 - 1 is above the Open limit.
        env(Vault::deposit(
                {.depositor = owner,
                 .id = fixture.vaultKeylet.key,
                 .amount = asset(Number{9'000'000'000'000'000'000LL}),
                 .flags = tfVaultDonate}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 5. A donation of 9.128 * 10^18 units takes AssetsTotal above 2^63 - 1. The vault would
        //    hold 9.2225 * 10^18 units, which is below it.
        // BUG: the result is tefEXCEPTION.
        env(Vault::deposit(
                {.depositor = owner,
                 .id = fixture.vaultKeylet.key,
                 .amount = asset(ownerFunds),
                 .flags = tfVaultDonate}),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

public:
    void
    run() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testMulDivRoundNegative();                // FV_M2_2
        // testVaultDepositOvervaluedShares();       // FV_M2_3
        // testVaultWithdrawOvervaluedShares();      // FV_M2_3
        // testVaultDepositChargeFloored();          // FV_M2_3
        // testVaultShareCountRounding();            // FV_M2_20
        // testVaultDepositOvercharge();             // FV_M2_21
        // testVaultDepositInternalError();          // FV_M2_22
        // testVaultDepositPathDry();                // FV_M2_23
        // testVaultDepositSharesOverflow();         // FV_M2_24, without fixed precision vaults
        // testVaultWithdrawXRPRange();              // FV_M2_25
        // testShareEscrowAssetForbidsEscrow();      // FV_M2_26
        // testWithdrawAfterHolderDeletesMPToken();  // FV_M2_27
        // testSharePaymentNoRipple();               // FV_M2_28, without MPTokensV2
        // testWithdrawByUnauthorizedHolder();       // FV_M2_31
        // testCoverWithdrawByUnauthorizedOwner();   // FV_M2_31
        // testVaultWithdrawDestinationLimit();      // FV_M2_32
        // testEarlyExitDestinationLimit();          // FV_M2_32
        // testVaultDustHoldersLocked();             // FV_M4_24
        // testVaultClawbackMptRounding();           // FV_M4_36
        // testVaultWithdrawMptAllShares();          // FV_M4_37
        // testVaultClawbackMptRemainder();          // FV_M4_38
        // testVaultWithdrawAboveRequested();        // FV_M4_43
        // testVaultDonateXRPRange();                // FV_M4_52
        // testVaultDonateMPTRange();                // FV_M4_60
        // clang-format on

        // Keeps a run of this suite alone from reporting "No tests run".
        pass();
    }
};

BEAST_DEFINE_TESTSUITE(VaultFindings, formal_verification, xrpl);

}  // namespace xrpl
