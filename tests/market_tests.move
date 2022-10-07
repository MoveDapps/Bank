#[test_only]
module mala::market_test {
    use sui::sui::SUI;
    use sui::object::ID;
    use sui::object;
    use sui::coin;
    use sui::test_scenario::{Self, Scenario, SharedWrapper};

    use mala::market::{Self, Market, SubMarket, AdminCap};
    use mala::market::{deposit_collateral};

    struct USDC has drop {}

    #[test]
    public fun test_market_creation() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Test admin cap and create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            let (market_wrapper, admin_cap) = get_market(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);

            // Check that admin cap owned by sender has the correct market id.
            assert!(object::id(market)
                == market::get_admincap_marketid(&admin_cap), 1);

            // Create a SUI SubMarket.
            market::create_sub_market<SUI>(market, &mut admin_cap, test_scenario::ctx(scenario));
            
            return_market(scenario, market_wrapper, admin_cap);
        };

        // Check parent - child relation between Market and SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            let (market_wrapper, admin_cap) = get_market(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);

            let sub_market = test_scenario::take_child_object<Market, SubMarket<SUI>>(scenario, market);

            market::check_child<SUI>(market, &sub_market);
           
            // using return_owned even though the child is not owned
            test_scenario::return_owned(scenario, sub_market);
            return_market(scenario, market_wrapper, admin_cap);
        };
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    public fun test_submarket_creation_with_invalid_admincap() {
        let sender = @0xBAAB;

        // Create Market 1.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Record ID for admin cap 1.
        let admin_cap_1_id: ID;
        test_scenario::next_tx(scenario, &sender);
        {
            let admin_cap = test_scenario::take_owned<AdminCap>(scenario);
            admin_cap_1_id = object::id(&admin_cap);
            test_scenario::return_owned(scenario, admin_cap);
        };

        // Create Market 2.
        test_scenario::next_tx(scenario, &sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Fail with EAdminOnly error code because wrong admin_cap tried to create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            let market_wrapper = test_scenario::take_last_created_shared<Market>(scenario);
            let market_2 = test_scenario::borrow_mut(&mut market_wrapper);

            let admin_cap_1 = test_scenario::take_owned_by_id(scenario, admin_cap_1_id);

            market::create_sub_market<SUI>(market_2, &mut admin_cap_1, test_scenario::ctx(scenario));

            test_scenario::return_shared(scenario, market_wrapper);
            test_scenario::return_owned(scenario, admin_cap_1);
        }
    }

    #[test]
    public fun test_deposit() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin<SUI>(scenario, 100);
        }
    }

    #[test]
    #[expected_failure(abort_code = 3)]
    public fun test_deposit_fails_for_invalid_submarket() {
        let sender = @0xBAAB;

        // Create Market 1.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin<USDC>(scenario, 100);
        }
    }

    // *** Helper Methods *** 

    fun deposit_coin<T>(scenario: &mut Scenario, amount: u64) {
        let (market_wrapper, admin_cap, submarket) = get_market_submarket<T>(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        let coin = coin::mint_for_testing<T>(amount, test_scenario::ctx(scenario));
        deposit_collateral<T>(market, &mut submarket, coin, test_scenario::ctx(scenario));

        return_market_submarket(scenario, market_wrapper, admin_cap, submarket);
    }

    fun create_submarket<T>(scenario: &mut Scenario) {
        let (market_wrapper, admin_cap) = get_market(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        market::create_sub_market<T>(market, &mut admin_cap, test_scenario::ctx(scenario));

        return_market(scenario, market_wrapper, admin_cap);
    }

    fun get_market(scenario: &mut Scenario) : (SharedWrapper<Market>, AdminCap) {
        let market_wrapper = test_scenario::take_shared<Market>(scenario);
        let admin_cap = test_scenario::take_owned<AdminCap>(scenario);
        (market_wrapper, admin_cap)
    }

    fun return_market(scenario: &mut Scenario, market_wrapper: SharedWrapper<Market>, admin_cap: AdminCap) {
        test_scenario::return_shared(scenario, market_wrapper);
        test_scenario::return_owned(scenario, admin_cap);
    }

    fun get_submarket<T>(scenario: &mut Scenario, market_wrapper: &mut SharedWrapper<Market>) : SubMarket<T> {
        let market = test_scenario::borrow_mut(market_wrapper);
        test_scenario::take_child_object<Market, SubMarket<T>>(scenario, market)
    }

    fun return_submarket<T>(scenario: &mut Scenario, submarket: SubMarket<T>) {
        test_scenario::return_owned(scenario, submarket);
    }

    fun get_market_submarket<T>(scenario: &mut Scenario)
    : (SharedWrapper<Market>, AdminCap, SubMarket<T>) {
        let (market_wrapper, admin_cap) = get_market(scenario);
        let submarket = get_submarket<T>(scenario, &mut market_wrapper);
        (market_wrapper, admin_cap, submarket)
    }

    fun return_market_submarket<T>(
        scenario: &mut Scenario, market_wrapper: SharedWrapper<Market>, admin_cap: AdminCap,
        submarket: SubMarket<T>) {
        return_market(scenario, market_wrapper, admin_cap);
        return_submarket<T>(scenario, submarket);
    }
}