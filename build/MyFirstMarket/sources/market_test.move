#[test_only]
module market_address::market_test {
    use market_address::data::{PoolInfo, LendingPool, Self};
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

        // test initializer owned PoolInfo object and corresponding shared
        // lending_pool object exists.
        test_scenario::next_tx(scenario, &initializer);
        {
            let pool_info = test_scenario::take_owned<PoolInfo>(scenario);
            let lending_pool_wrapper = test_scenario::take_shared<LendingPool>(scenario);
            
            let lending_pool = test_scenario::borrow_mut(&mut lending_pool_wrapper);
            assert!(data::get_lending_pool_id(lending_pool) == data::get_pool_id(&pool_info), 1);

            let ctx = test_scenario::ctx(scenario);
            let first_deposit = coin::mint_for_testing<SUI>(5, ctx);
            let second_deposit = coin::mint_for_testing<SUI>(50, ctx);
            
            // deposit 5 SUI coins twice
            data::deposit(lending_pool, first_deposit, test_scenario::ctx(scenario));
            data::deposit(lending_pool, second_deposit, test_scenario::ctx(scenario));
            
            // check that initializer balance is eual to the two deposits.
            assert!(data::get_deposit_balance_by_address(lending_pool, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(data::get_deposit_balance_by_address(lending_pool, &random) == 0, 1);

            assert!(data::get_total_pool_balance(lending_pool) == 55, 1);

            test_scenario::return_shared(scenario, lending_pool_wrapper);
            test_scenario::return_owned(scenario, pool_info);
        };

        // test borrowing.
        test_scenario::next_tx(scenario, &initializer);
        {
            let pool_info = test_scenario::take_owned<PoolInfo>(scenario);
            let lending_pool_wrapper = test_scenario::take_shared<LendingPool>(scenario);
            
            let lending_pool = test_scenario::borrow_mut(&mut lending_pool_wrapper);
            assert!(data::get_lending_pool_id(lending_pool) == data::get_pool_id(&pool_info), 1);
            
            // check that initializer balance is eual to the two deposits.
            assert!(data::get_deposit_balance_by_address(lending_pool, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(data::get_deposit_balance_by_address(lending_pool, &random) == 0, 1);

            assert!(data::get_total_pool_balance(lending_pool) == 55, 1);

            let borrowed_fund = data::borrow(lending_pool, 23, test_scenario::ctx(scenario));
            assert!(data::get_total_pool_balance(lending_pool) == 55 - 23, 1);

            transfer::transfer(borrowed_fund, initializer);
            test_scenario::return_shared(scenario, lending_pool_wrapper);
            test_scenario::return_owned(scenario, pool_info);
        };
    }
}