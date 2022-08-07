module market_address::market {
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::object::{Self, ID, Info};
    use sui::tx_context::TxContext;
    use sui::vec_map::{Self, VecMap};
    use sui::sui::SUI;
    
    // Lending Pool for SUI coins.
    // All addresses deposited to the pool will exist in pool_balance.
    struct LendingPool has key {
        info: Info,
        pool_balance: VecMap<address, Balance<SUI>>,
    }

    // Lending Pool info to be passed to the initializer.
    struct PoolInfo has key {
        info: Info,
        lending_pool_id: ID,
    }

    public fun pool_id(self: &PoolInfo): ID {
        self.lending_pool_id
    }

    // Module initializer to be executed when this module is published.
    fun init(ctx: &mut TxContext) {
        use sui::transfer;
        use sui::tx_context;

        let info = object::new(ctx);
        let lending_pool_id = *object::info_id(&info);

        let lending_pool = LendingPool {
            info: info,
            pool_balance: vec_map::empty(),
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

        let pool_balances = &mut lending_pool.pool_balance;
        let sender_address = tx_context::sender(ctx);

        if(!vec_map::contains(pool_balances, &sender_address)) {
            let deposit_balance = coin::into_balance(deposit_coin);

            vec_map::insert(
                pool_balances,
                sender_address,
                deposit_balance
            );
        }
        else {
            let current_balance = vec_map::get_mut(
                pool_balances,
                &sender_address
            );

            coin::put(current_balance, deposit_coin);
        }
    }

    /// === Reads ===

    /// Return the maximum amount available for borrowing
    public fun get_pool_balances(lending_pool: &LendingPool): &VecMap<address, Balance<SUI>> {
        &lending_pool.pool_balance
    }

    public fun get_pool_balance_ref_by_address(lending_pool: &LendingPool, key_address: &address): &Balance<SUI> {
        let pool_balances = get_pool_balances(lending_pool);
        
        vec_map::get(pool_balances, key_address)
    }

    public fun get_pool_balance_value_by_address(lending_pool: &LendingPool, key_address: &address): u64 {
        if(!vec_map::contains(&lending_pool.pool_balance, key_address)) {
            0u64
        }
        else {
            balance::value(get_pool_balance_ref_by_address(lending_pool, key_address))
        }
    }

    #[test]
    public fun test_module_init() {
        use sui::test_scenario;
        use sui::coin;

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
            assert!(get_pool_balance_value_by_address(lending_pool, &initializer) == 55, 1);
            // check that a random address has 0 deposits.
            assert!(get_pool_balance_value_by_address(lending_pool, &random) == 90, 1);

            test_scenario::return_shared(scenario, lending_pool_wrapper);
            test_scenario::return_owned(scenario, pool_info);
        };
    }
}