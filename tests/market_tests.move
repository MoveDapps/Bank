#[test_only]
module mala::market_test {
    use sui::sui::SUI;
    //use sui::object::ID;
    //use sui::object;
    use sui::coin;
    use sui::test_scenario::{Self, Scenario, SharedWrapper};

    use mala::market::{Self, Pool, SubMarket};
    use mala::market::{deposit_collateral};

    struct USDC has drop {}

    #[test]
    public fun market_creation() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Test admin cap and create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            let market_wrapper = test_scenario::take_shared<Pool>(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);

            // Create a SUI SubMarket.
            market::create_sub_market<SUI>(market, test_scenario::ctx(scenario));
        
            test_scenario::return_shared(scenario, market_wrapper);
        };

        // Check parent - child relation between Market and SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            let market_wrapper = test_scenario::take_shared<Pool>(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);

            let sub_market = test_scenario::take_child_object<Pool, SubMarket<SUI>>(scenario, market);

            market::check_child<SUI>(market, &sub_market);
           
            // using return_owned even though the child is not owned
            test_scenario::return_owned(scenario, sub_market);
            test_scenario::return_shared(scenario, market_wrapper);
        };
    }

    #[test]
    #[expected_failure]
    public fun fail_submarket_creation_by_non_admin() {
        let admin = @0xBAAB;
        let non_admin = @0xABBA;

        // Create Market.
        let scenario = &mut test_scenario::begin(&admin);
        {
            market::create_market(test_scenario::ctx(scenario));
        };

        // Test admin cap and create SubMarket.
        test_scenario::next_tx(scenario, &non_admin);
        {
            let market_wrapper = test_scenario::take_shared<Pool>(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);

            // Create a SUI SubMarket.
            market::create_sub_market<SUI>(market, test_scenario::ctx(scenario));
        
            test_scenario::return_shared(scenario, market_wrapper);
        };
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
        let (market_wrapper, submarket) = get_market_submarket<T>(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        let coin = coin::mint_for_testing<T>(amount, test_scenario::ctx(scenario));
        deposit_collateral<T>(market, &mut submarket, coin, test_scenario::ctx(scenario));

        return_market_submarket(scenario, market_wrapper, submarket);
    }

    fun create_submarket<T>(scenario: &mut Scenario) {
        let market_wrapper = test_scenario::take_shared<Pool>(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        market::create_sub_market<T>(market, test_scenario::ctx(scenario));

        test_scenario::return_shared(scenario, market_wrapper);
    }

    fun get_submarket<T>(scenario: &mut Scenario, market_wrapper: &mut SharedWrapper<Pool>) : SubMarket<T> {
        let market = test_scenario::borrow_mut(market_wrapper);
        test_scenario::take_child_object<Pool, SubMarket<T>>(scenario, market)
    }

    fun get_market_submarket<T>(scenario: &mut Scenario)
    : (SharedWrapper<Pool>, SubMarket<T>) {
        let market_wrapper = test_scenario::take_shared<Pool>(scenario);
        let submarket = get_submarket<T>(scenario, &mut market_wrapper);
        (market_wrapper, submarket)
    }

    fun return_market_submarket<T>(
        scenario: &mut Scenario, market_wrapper: SharedWrapper<Pool>, submarket: SubMarket<T>) {
        test_scenario::return_shared(scenario, market_wrapper);
        test_scenario::return_owned(scenario, submarket);
    }
}