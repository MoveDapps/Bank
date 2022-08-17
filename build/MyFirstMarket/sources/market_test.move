#[test_only]
module market_address::market_test {
    use market_address::data::{MoneyMarketInfo, MoneyMarket, Self};
    use market_address::market::{Self};
    
    #[test]
    public fun test_module_init() {
        use sui::test_scenario;
        use sui::coin;
        use sui::transfer;
        use sui::sui::SUI;

        let initializer = @0xABBA;
        let random = @0xABBB;

        // test initialization
        let scenario = &mut test_scenario::begin(&initializer);
        {
            market::initialize(test_scenario::ctx(scenario));
        };

        // test initializer owned MoneyMarketInfo object and corresponding shared
        // money_market object exists.
        test_scenario::next_tx(scenario, &initializer);
        {
            let money_market_info = test_scenario::take_owned<MoneyMarketInfo>(scenario);
            let money_market_wrapper = test_scenario::take_shared<MoneyMarket<SUI>>(scenario);
            
            let money_market = test_scenario::borrow_mut(&mut money_market_wrapper);
            assert!(data::get_money_market_id(money_market) == data::get_pool_id(&money_market_info), 1);

            let ctx = test_scenario::ctx(scenario);
            let first_deposit = coin::mint_for_testing<SUI>(5, ctx);
            let second_deposit = coin::mint_for_testing<SUI>(50, ctx);
            
            // deposit 5 SUI coins twice
            data::deposit(money_market, first_deposit, test_scenario::ctx(scenario));
            data::deposit(money_market, second_deposit, test_scenario::ctx(scenario));
            
            // check that initializer balance is eual to the two deposits.
            assert!(data::get_deposit_balance_by_address(money_market, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(data::get_deposit_balance_by_address(money_market, &random) == 0, 1);

            assert!(data::get_total_pool_balance(money_market) == 55, 1);

            test_scenario::return_shared(scenario, money_market_wrapper);
            test_scenario::return_owned(scenario, money_market_info);
        };

        // test borrowing.
        test_scenario::next_tx(scenario, &initializer);
        {
            let money_market_info = test_scenario::take_owned<MoneyMarketInfo>(scenario);
            let money_market_wrapper = test_scenario::take_shared<MoneyMarket<SUI>>(scenario);
            
            let money_market = test_scenario::borrow_mut(&mut money_market_wrapper);
            assert!(data::get_money_market_id(money_market) == data::get_pool_id(&money_market_info), 1);
            
            // check that initializer balance is eual to the two deposits.
            assert!(data::get_deposit_balance_by_address(money_market, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(data::get_deposit_balance_by_address(money_market, &random) == 0, 1);

            assert!(data::get_total_pool_balance(money_market) == 55, 1);

            let borrowed_fund = data::borrow(money_market, 23, test_scenario::ctx(scenario));
            assert!(data::get_total_pool_balance(money_market) == 55 - 23, 1);

            transfer::transfer(borrowed_fund, initializer);
            test_scenario::return_shared(scenario, money_market_wrapper);
            test_scenario::return_owned(scenario, money_market_info);
        };
    }
}