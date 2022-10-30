#[test_only]
module mala::market_test {
    use sui::sui::SUI;
    use sui::coin;
    use sui::test_scenario::{Self, Scenario};

    use mala::market::{Self, Pool};
    use mala::market::{deposit_collateral};
    use mala::fake_usdc::{USDC};
    use sui::vec_map::{Self};

    //use sui::object::{Self};
    //use std::debug;

    #[test]
    public fun market_creation() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);

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
        
        create_pool(scenario, &admin);
        create_submarket<SUI>(scenario, &non_admin);

        test_scenario::end(scenario_val);
    }

    #[test]
    #[expected_failure]
    public fun multiple_submarket_same_coin() {
        let admin = @0xBAAB;

        let scenario_val = test_scenario::begin(admin);

        // Create pool.
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &admin);
        create_submarket<SUI>(scenario, &admin);
        create_submarket<USDC>(scenario, &admin);
        create_submarket<SUI>(scenario, &admin);

        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_deposit() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);
        deposit_coin_into_market<SUI>(scenario, 100, &sender);

        // Test that the deposit settled in the previous transaction.
        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            let unused_col = market::get_unused_col_from_market<SUI>(sender, &market);
            assert!(unused_col == 100, 1);
            test_scenario::return_shared(market);
        };
        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_borrow() {
        let sender = @0xBAAB;

        // Create Market.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);
        create_submarket<USDC>(scenario, &sender);

        deposit_coin_into_market<SUI>(scenario, 100, &sender);
        deposit_coin_into_market<USDC>(scenario, 100, &sender);

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            
            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 100, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);
            
            market::borrow<SUI, USDC>(50, 100, &mut market, test_scenario::ctx(scenario));
            
            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 0, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);

            test_scenario::return_shared(market);
        };

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            market::borrow<USDC, SUI>(40, 80, &mut market, test_scenario::ctx(scenario));
            
            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 0, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 20, 1);

            test_scenario::return_shared(market);
        };

        test_scenario::end(scenario_val);
    }

    #[test]
    #[expected_failure]
    public fun test_borrow_more_than_collateral() {
        let sender = @0xBAAB;
        let scenario_val = test_scenario::begin(sender);
        
        let scenario = &mut scenario_val;
        {
            market::create_pool(test_scenario::ctx(scenario));
        };

        create_submarket<SUI>(scenario, &sender);
        create_submarket<USDC>(scenario, &sender);

        deposit_coin_into_market<SUI>(scenario, 100, &sender);
        deposit_coin_into_market<USDC>(scenario, 100, &sender);

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            
            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 100, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);
            
            market::borrow<SUI, USDC>(51, 100, &mut market, test_scenario::ctx(scenario));

            test_scenario::return_shared(market);
        };
        
        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_borrow_record() {
        let sender = @0xBAAB;
        let scenario_val = test_scenario::begin(sender);
        
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);
        create_submarket<USDC>(scenario, &sender);

        deposit_coin_into_market<SUI>(scenario, 100, &sender);
        deposit_coin_into_market<USDC>(scenario, 100, &sender);

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            assert!(market::get_borrow_records_length(&market) == 0, 1);
            
            market::borrow<SUI, USDC>(1, 2, &mut market, test_scenario::ctx(scenario));
            assert!(market::get_borrow_records_length(&market) == 1, 1);

            // Multiple borrows of the same type and by the same sender creates 1 borrow record.
            market::borrow<SUI, USDC>(1, 2, &mut market, test_scenario::ctx(scenario));
            assert!(market::get_borrow_records_length(&market) == 1, 1);

            // Different borrow pair creates a new borrow record.
            market::borrow<USDC, SUI>(1, 2, &mut market, test_scenario::ctx(scenario));
            assert!(market::get_borrow_records_length(&market) == 2, 1);

            test_scenario::return_shared(market);
        };

        test_scenario::end(scenario_val);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    public fun test_deposit_fails_for_invalid_submarket(){
        let sender = @0xBAAB;

        // Create Market 1.
        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);
        deposit_coin_into_market<USDC>(scenario, 100, &sender);
        
        test_scenario::end(scenario_val);
    }

    #[test]
    public fun test_repay(){
        let sender = @0xBAAB;

        let scenario_val = test_scenario::begin(sender);
        let scenario = &mut scenario_val;
        
        create_pool(scenario, &sender);
        create_submarket<SUI>(scenario, &sender);
        create_submarket<USDC>(scenario, &sender);
        deposit_coin_into_market<SUI>(scenario, 100, &sender);
        deposit_coin_into_market<USDC>(scenario, 100, &sender);

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 100, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);

            market::borrow<SUI, USDC>(1, 2, &mut market, test_scenario::ctx(scenario));

            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 98, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);

            test_scenario::return_shared(market);
        };

        let effects = test_scenario::transferred_to_account(
            &test_scenario::next_tx(scenario, sender)
        );

        let (_, owner) = vec_map::get_entry_by_idx(&effects, 0);
        assert!(*owner == sender, 1);

        test_scenario::next_tx(scenario, sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 98, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);

            let repay_coin = coin::mint_for_testing<SUI>(1, test_scenario::ctx(scenario));

            market::repay<SUI, USDC>(repay_coin, 2, &mut market, test_scenario::ctx(scenario));

            assert!(market::get_unused_col_from_market<USDC>(sender, &market) == 100, 1);
            assert!(market::get_unused_col_from_market<SUI>(sender, &market) == 100, 1);

            test_scenario::return_shared(market);
        };

        test_scenario::end(scenario_val);
    }
    
    // *** Helper Methods *** 
    fun deposit_coin_into_market<T>(scenario: &mut Scenario, amount: u64, sender: &address) {
        test_scenario::next_tx(scenario, *sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);

            deposit_collateral<T>(
                &mut market,
                coin::mint_for_testing<T>(amount, test_scenario::ctx(scenario)),
                test_scenario::ctx(scenario)
            );

            test_scenario::return_shared(market);
        };
    }

    fun create_submarket<T>(scenario: &mut Scenario, sender: &address) {
        test_scenario::next_tx(scenario, *sender);
        {
            let market = test_scenario::take_shared<Pool>(scenario);
            market::create_sub_market<T>(&mut market, test_scenario::ctx(scenario));
            test_scenario::return_shared(market);
        };
    }

    fun create_pool(scenario: &mut Scenario, sender: &address) {
        test_scenario::next_tx(scenario, *sender);
        {
            market::create_pool(test_scenario::ctx(scenario))
        };
    }
}