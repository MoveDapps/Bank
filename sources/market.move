module market_address::market {
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::object::{Self, ID, Info};
    use sui::tx_context::TxContext;
    use sui::vec_map::{Self, VecMap};
    use sui::sui::SUI;

    //use std::debug;

    const BORROW_UTILIZATION: u64 = 50;
    const EBorrowTooBig: u64 = 100;
    
    // Lending Pool for SUI coins.
    // All addresses deposited to the pool will exist in pool_balance_records.
    struct LendingPool has key {
        info: Info,
        pool_balance: Balance<SUI>,
        pool_balance_records: VecMap<address, u64>,
        pool_borrow_records: VecMap<address, u64>,
    }

    // Lending Pool info to be passed to the initializer.
    struct PoolInfo has key {
        info: Info,
        lending_pool_id: ID,
    }

    public fun pool_id(self: &PoolInfo): ID {
        self.lending_pool_id
    }

    public fun lending_pool_info(self: &LendingPool): ID {
        *object::info_id(&self.info)
    }

    // Module initializer to be executed when this module is published.
    public fun initialize(ctx: &mut TxContext) {
        use sui::transfer;
        use sui::tx_context;

        let info = object::new(ctx);
        let lending_pool_id = *object::info_id(&info);

        let lending_pool = LendingPool {
            info: info,
            pool_balance: balance::zero(),
            pool_balance_records: vec_map::empty(),
            pool_borrow_records: vec_map::empty(),
        };

        let pool_info = PoolInfo {
            info: object::new(ctx),
            lending_pool_id: lending_pool_id,
        };
        
        transfer::share_object(lending_pool);
        transfer::transfer(pool_info, tx_context::sender(ctx));
    }

    public entry fun deposit(lending_pool: &mut LendingPool, deposit_coin: Coin<SUI>, ctx: &mut TxContext) {
        use sui::tx_context;

        let pool_balance_records = &mut lending_pool.pool_balance_records;
        let sender_address = tx_context::sender(ctx);
        let deposit_balance = coin::into_balance(deposit_coin);
        let deposit_value = balance::value(&deposit_balance);

        balance::join(&mut lending_pool.pool_balance, deposit_balance);

        if(!vec_map::contains(pool_balance_records, &sender_address)) {
            vec_map::insert(
                pool_balance_records,
                sender_address,
                deposit_value
            );
        }
        else {
            let current_balance = vec_map::get_mut(
                pool_balance_records,
                &sender_address
            );

            *current_balance = *current_balance + deposit_value;
        }
    }

    public fun borrow_limit(lending_pool: &LendingPool, borrower_address: &address): u64 {
        let deposit_balance = get_pool_balance_by_address(lending_pool, borrower_address);

        let borrowed_balance;
        if(!vec_map::contains(&lending_pool.pool_borrow_records, borrower_address)) {
            borrowed_balance = 0u64;
        }
        else {
            borrowed_balance = *vec_map::get(&lending_pool.pool_borrow_records, borrower_address);
        };

        let limit: u64 = (deposit_balance * BORROW_UTILIZATION) / 100;

        //debug::print(&borrowed_balance);
        //debug::print(&limit);

        limit - borrowed_balance
    }

    public fun borrow(lending_pool: &mut LendingPool, borrow_amount: u64, ctx: &mut TxContext): Coin<SUI> {
        use sui::tx_context;
        let sender_address = tx_context::sender(ctx);

        assert!(borrow_limit(lending_pool, &sender_address) >= borrow_amount, EBorrowTooBig);

        let pool_borrow_records = &mut lending_pool.pool_borrow_records;
        if(!vec_map::contains(pool_borrow_records, &sender_address)) {
            vec_map::insert(
                pool_borrow_records,
                sender_address,
                borrow_amount
            );
        }
        else {
            let current_balance = vec_map::get_mut(
                pool_borrow_records,
                &sender_address
            );

            *current_balance = *current_balance + borrow_amount;
        };

        coin::take(&mut lending_pool.pool_balance, borrow_amount, ctx)
    }

    /// === Reads ===

    /// Return the maximum amount available for borrowing
    public fun get_pool_balance_by_address(lending_pool: &LendingPool, key_address: &address): u64 {
        if(!vec_map::contains(&lending_pool.pool_balance_records, key_address)) {
            0u64
        }
        else {
            *vec_map::get(&lending_pool.pool_balance_records, key_address)
        }
    }

    public fun get_total_pool_balance(lending_pool: &LendingPool): u64 {
        balance::value(&lending_pool.pool_balance)
    }
/*
    #[test]
    public fun test_module_init() {
        use sui::test_scenario;
        use sui::coin;
        use sui::transfer;

        let initializer = @0xABBA;
        let random = @0xABBB;

        // test initialization
        let scenario = &mut test_scenario::begin(&initializer);
        {
            init(test_scenario::ctx(scenario));
        };

        // test initializer owned PoolInfo object and corresponding shared
        // lending_pool object exists.
        test_scenario::next_tx(scenario, &initializer);
        {
            let pool_info = test_scenario::take_owned<PoolInfo>(scenario);
            let lending_pool_wrapper = test_scenario::take_shared<LendingPool>(scenario);
            
            let lending_pool = test_scenario::borrow_mut(&mut lending_pool_wrapper);
            assert!(*object::info_id(&lending_pool.info) == pool_id(&pool_info), 1);

            let ctx = test_scenario::ctx(scenario);
            let first_deposit = coin::mint_for_testing<SUI>(5, ctx);
            let second_deposit = coin::mint_for_testing<SUI>(50, ctx);
            
            // deposit 5 SUI coins twice
            deposit(lending_pool, first_deposit, test_scenario::ctx(scenario));
            deposit(lending_pool, second_deposit, test_scenario::ctx(scenario));
            
            // check that initializer balance is eual to the two deposits.
            assert!(get_pool_balance_by_address(lending_pool, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(get_pool_balance_by_address(lending_pool, &random) == 0, 1);

            assert!(get_total_pool_balance(lending_pool) == 55, 1);

            test_scenario::return_shared(scenario, lending_pool_wrapper);
            test_scenario::return_owned(scenario, pool_info);
        };

        // test borrowing.
        test_scenario::next_tx(scenario, &initializer);
        {
            let pool_info = test_scenario::take_owned<PoolInfo>(scenario);
            let lending_pool_wrapper = test_scenario::take_shared<LendingPool>(scenario);
            
            let lending_pool = test_scenario::borrow_mut(&mut lending_pool_wrapper);
            assert!(*object::info_id(&lending_pool.info) == pool_id(&pool_info), 1);
            
            // check that initializer balance is eual to the two deposits.
            assert!(get_pool_balance_by_address(lending_pool, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(get_pool_balance_by_address(lending_pool, &random) == 0, 1);

            assert!(get_total_pool_balance(lending_pool) == 55, 1);

            let borrowed_fund = borrow(lending_pool, 23, test_scenario::ctx(scenario));
            assert!(get_total_pool_balance(lending_pool) == 55 - 23, 1);

            transfer::transfer(borrowed_fund, initializer);
            test_scenario::return_shared(scenario, lending_pool_wrapper);
            test_scenario::return_owned(scenario, pool_info);
        };
    }
*/
}