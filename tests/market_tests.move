#[test_only]
module mala::market_test {
    use sui::sui::SUI;
    use sui::coin;
    use sui::transfer;
    use sui::test_scenario::{Self, Scenario};

    use mala::market::{Self, Pool, SubMarket};
    use mala::market::{deposit_collateral};
    use mala::fake_usdc::{USDC};

    //use sui::object::{Self};
    //use std::debug;

    #[test]
    public fun market_creation() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Test admin cap and create SubMarket.
        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            // Create a SUI SubMarket.
            market::create_sub_market<SUI>(&mut market, test_scenario::ctx(scenario));
        
            test_scenario::return_shared(market);
        };

        // Check parent - child relation between Market and SubMarket.
        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            let sub_market = test_scenario::take_shared<SubMarket<SUI>>(scenario);

            market::check_child<SUI>(&mut market, &sub_market);
           
            // using return_owned even though the child is not owned
            test_scenario::return_shared(sub_market);
            test_scenario::return_shared(market);
        };

        test_scenario::end(scenario_val);
    }

    #[test]
    #[expected_failure]
    public fun fail_submarket_creation_by_non_admin() {
        let admin = @0xBAAB;
        let non_admin = @0xABBA;

        // Create Market.
        let scenario_val = test_scenario::begin(admin);
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Test admin cap and create SubMarket.
        test_scenario::next_tx(scenario, non_admin);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            // Create a SUI SubMarket.
            market::create_sub_market<SUI>(&mut market, test_scenario::ctx(scenario));
        
            test_scenario::return_shared(market);
        };
        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_deposit() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            deposit_coin_into_latest_market<SUI>(scenario, 100);
        };

        // Test that the deposit settled in the previous transaction.
        test_scenario::next_tx(scenario, sender);
        {
            let (market_wrapper, submarket) = get_latest_market_submarket<SUI>(scenario);
            let unused_col = market::get_unused_col(sender, &submarket);
            assert!(unused_col == 100, 1);

            test_scenario::return_shared(market_wrapper);
            test_scenario::return_shared(submarket);
        };
        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_borrow() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SUI Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Create USDC Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            create_submarket<USDC>(scenario);
        };

        // Deposit to SUI Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            deposit_coin_into_latest_market<SUI>(scenario, 100);
        };

        // Deposit to USDC Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            deposit_coin_into_latest_market<USDC>(scenario, 100);
        };

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            let sui_submarket = test_scenario::take_shared<SubMarket<SUI>>(scenario);
            let usdc_submarket = test_scenario::take_shared<SubMarket<USDC>>(scenario);
            let borrowed_coin = market::borrow<SUI, USDC>(50, 100, &mut sui_submarket, &mut usdc_submarket, &mut market, test_scenario::ctx(scenario));

            let borrowed_value = coin::value<SUI>(&borrowed_coin);
            
            //debug::print(&borrowed_value);
            
            assert!(borrowed_value == 50, 1);

            transfer::transfer(borrowed_coin, sender);
            test_scenario::return_shared(market);
            test_scenario::return_shared(sui_submarket);
            test_scenario::return_shared(usdc_submarket);
        };
        test_scenario::end(scenario_val);
    }

    #[test]
    #[expected_failure(abort_code = 3)]
    public fun test_deposit_fails_for_invalid_submarket() {
        let sender = @0xBAAB;

        // Create Market 1.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, sender);
        {
            deposit_coin_into_latest_market<USDC>(scenario, 100);
        };
        test_scenario::end(scenario_val);
    }

    // *** Helper Methods *** 

    fun deposit_coin_into_latest_market<T>(scenario: &mut Scenario, amount: u64) {
        let (market, submarket) = get_latest_market_submarket<T>(scenario);

        let coin = coin::mint_for_testing<T>(amount, test_scenario::ctx(scenario));
        deposit_collateral<T>(&mut market, &mut submarket, coin, test_scenario::ctx(scenario));

        test_scenario::return_shared(market);
        test_scenario::return_shared(submarket);
    }

    fun create_submarket<T>(scenario: &mut Scenario) {
        let market = test_scenario::take_shared<Pool>(scenario);

        market::create_sub_market<T>(&mut market, test_scenario::ctx(scenario));
        //debug::print(&object::id(market));
        //debug::print(market::get_submarket_list(market));

        test_scenario::return_shared(market);
    }

    fun get_latest_market_submarket<T>(scenario: &mut Scenario)
    : (Pool, SubMarket<T>) {
        let market = test_scenario::take_shared<Pool>(scenario);
        let submarket = test_scenario::take_shared<SubMarket<T>>(scenario);
        (market, submarket)
    }
}