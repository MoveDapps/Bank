#[test_only]
module market_address::market_test {
    use sui::sui::SUI;
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

    fun get_market(scenario: &mut Scenario) : (SharedWrapper<Market>, AdminCap) {
        let market_wrapper = test_scenario::take_shared<Market>(scenario);
        let admin_cap = test_scenario::take_owned<AdminCap>(scenario);
        (market_wrapper, admin_cap)
    }

    fun return_market(scenario: &mut Scenario, market_wrapper: SharedWrapper<Market>, admin_cap: AdminCap) {
        test_scenario::return_shared(scenario, market_wrapper);
        test_scenario::return_owned(scenario, admin_cap);
    }
}