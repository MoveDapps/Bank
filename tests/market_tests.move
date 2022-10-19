#[test_only]
module mala::market_test {
    use sui::sui::SUI;
    use sui::coin;
    use sui::transfer;
    use sui::test_scenario::{Self, Scenario, SharedWrapper};

    use mala::market::{Self, Pool, SubMarket};
    use mala::market::{deposit_collateral};
    use mala::fake_usdc::{USDC};

    //use sui::object::{Self};
    //use std::debug;

    #[test]
    public fun market_creation() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_pool(test_scenario::ctx(scenario));
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
            market::create_pool(test_scenario::ctx(scenario));
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
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin_into_latest_market<SUI>(scenario, 100);
        };

        // Test that the deposit settled in the previous transaction.
        test_scenario::next_tx(scenario, &sender);
        {
            let (market_wrapper, submarket) = get_latest_market_submarket<SUI>(scenario);
            let unused_col = market::get_unused_col(sender, &submarket);
            assert!(unused_col == 100, 1);
            return_market_submarket(scenario, market_wrapper, submarket);
        }
    }

    #[test]
    public fun test_borrow() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SUI Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Create USDC Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<USDC>(scenario);
        };

        // Deposit to SUI Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin_into_latest_market<SUI>(scenario, 100);
        };

        // Deposit to USDC Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin_into_latest_market<USDC>(scenario, 100);
        };

        test_scenario::next_tx(scenario, &sender);
        {
            let market_wrapper = test_scenario::take_shared<Pool>(scenario);
            let market = test_scenario::borrow_mut(&mut market_wrapper);
            let sui_submarket = test_scenario::take_child_object<Pool, SubMarket<SUI>>(scenario, market);
            let usdc_submarket = test_scenario::take_child_object<Pool, SubMarket<USDC>>(scenario, market);
            let borrowed_coin = market::borrow<SUI, USDC>(50, 100, &mut sui_submarket, &mut usdc_submarket, market, test_scenario::ctx(scenario));

            let borrowed_value = coin::value<SUI>(&borrowed_coin);
            
            //debug::print(&borrowed_value);
            
            assert!(borrowed_value == 50, 1);

            transfer::transfer(borrowed_coin, sender);
            test_scenario::return_shared(scenario, market_wrapper);
            test_scenario::return_owned(scenario, sui_submarket);
            test_scenario::return_owned(scenario, usdc_submarket);
        };
    }

    #[test]
    #[expected_failure(abort_code = 3)]
    public fun test_deposit_fails_for_invalid_submarket() {
        let sender = @0xBAAB;

        // Create Market 1.
        let scenario = &mut test_scenario::begin(&sender);
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        // Create SubMarket.
        test_scenario::next_tx(scenario, &sender);
        {
            create_submarket<SUI>(scenario);
        };

        // Deposit to Submarket.
        test_scenario::next_tx(scenario, &sender);
        {
            deposit_coin_into_latest_market<USDC>(scenario, 100);
        }
    }

    // *** Helper Methods *** 

    fun deposit_coin_into_latest_market<T>(scenario: &mut Scenario, amount: u64) {
        let (market_wrapper, submarket) = get_latest_market_submarket<T>(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        let coin = coin::mint_for_testing<T>(amount, test_scenario::ctx(scenario));
        deposit_collateral<T>(market, &mut submarket, coin, test_scenario::ctx(scenario));

        return_market_submarket(scenario, market_wrapper, submarket);
    }

    fun create_submarket<T>(scenario: &mut Scenario) {
        let market_wrapper = test_scenario::take_shared<Pool>(scenario);
        let market = test_scenario::borrow_mut(&mut market_wrapper);

        market::create_sub_market<T>(market, test_scenario::ctx(scenario));
        //debug::print(&object::id(market));
        //debug::print(market::get_submarket_list(market));

        test_scenario::return_shared(scenario, market_wrapper);
    }

    fun get_submarket<T>(scenario: &mut Scenario, market_wrapper: &mut SharedWrapper<Pool>) : SubMarket<T> {
        let market = test_scenario::borrow_mut(market_wrapper);
        test_scenario::take_child_object<Pool, SubMarket<T>>(scenario, market)
    }

    fun get_latest_market_submarket<T>(scenario: &mut Scenario)
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