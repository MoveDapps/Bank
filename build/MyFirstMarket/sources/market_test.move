#[test_only]
module market_address::market_test {
    use std::debug;

    use sui::sui::SUI;
    use sui::object::ID;
    use sui::test_scenario::{Self, Scenario, SharedWrapper};

    use market_address::market::{Self, Market, SubMarket, AdminCap};

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
            assert!(market::get_market_id(market)
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

            let sub_market_wrapper =
                test_scenario::take_shared<SubMarket<SUI>>(scenario);
            let sub_market = test_scenario::borrow_mut(&mut sub_market_wrapper);

            market::check_child<SUI>(market, sub_market);
           
            test_scenario::return_shared(scenario, sub_market_wrapper);
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
            admin_cap_1_id = market::get_admincap_id(&admin_cap);
            test_scenario::return_owned(scenario, admin_cap);
        };

        debug::print(&admin_cap_1_id);

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

    fun get_market(scenario: &mut Scenario) : (SharedWrapper<Market>, AdminCap) {
        let market_wrapper = test_scenario::take_shared<Market>(scenario);
        let admin_cap = test_scenario::take_owned<AdminCap>(scenario);
        (market_wrapper, admin_cap)
    }

    fun get_last_created_market_id(scenario: &mut Scenario): ID {
        let market_wrapper = test_scenario::take_last_created_shared(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);
        let market_id = market::get_market_id(market);

        test_scenario::return_shared(scenario, market_wrapper);
        
        market_id
    }

    fun return_market(scenario: &mut Scenario, market_wrapper: SharedWrapper<Market>, admin_cap: AdminCap) {
        test_scenario::return_shared(scenario, market_wrapper);
        test_scenario::return_owned(scenario, admin_cap);
    }
}