module market_address::market {
    use sui::balance::Balance;
    use sui::coin::{Self, Coin};
    use sui::object::{Self, ID, Info};
    use sui::tx_context::TxContext;
    use sui::vec_map::{Self, VecMap};
    use sui::sui::SUI;
    
    // Lending Pool for SUI coins.
    // All addresses deposited to the pool will exist in poolBalance.
    struct LendingPool has key {
        info: Info,
        poolBalance: VecMap<address, Balance<SUI>>,
    }

    // Lending Pool info to be passed to the initializer.
    struct PoolInfo has key {
        info: Info,
        lendingPoolId: ID,
    }

    public fun poolId(self: &PoolInfo): ID {
        self.lendingPoolId
    }

    // Module initializer to be executed when this module is published.
    fun init(ctx: &mut TxContext) {
        use sui::transfer;
        use sui::tx_context;

        let info = object::new(ctx);
        let lendingPoolId = *object::info_id(&info);

        let lendingPool = LendingPool {
            info: info,
            poolBalance: vec_map::empty(),
        };

        let poolInfo = PoolInfo {
            info: object::new(ctx),
            lendingPoolId: lendingPoolId,
        };
        
        transfer::share_object(lendingPool);
        transfer::transfer(poolInfo, tx_context::sender(ctx));
    }

    public entry fun deposit(lendingPool: &mut LendingPool, depositCoin: Coin<SUI>, ctx: &mut TxContext) {
        use sui::tx_context;
        vec_map::insert(&mut lendingPool.poolBalance, tx_context::sender(ctx), coin::into_balance(depositCoin));
    }

    #[test]
    public fun test_module_init() {
        use sui::test_scenario;

        let initializer = @0xABBA;

        // test initialization
        let scenario = &mut test_scenario::begin(&initializer);
        {
            init(test_scenario::ctx(scenario));
        };

        // test initializer owned PoolInfo object and corresponding shared
        // lendingPool object exists.
        test_scenario::next_tx(scenario, &initializer);
        {
            let poolInfo = test_scenario::take_owned<PoolInfo>(scenario);

            let lendingPoolId = poolId(&poolInfo);
            let lendingPoolWrapper = test_scenario::take_shared<LendingPool>(scenario);
            let lendingPool = test_scenario::borrow_mut(&mut lendingPoolWrapper);
            
            assert!(*object::info_id(&lendingPool.info) == lendingPoolId, 1);
            
            test_scenario::return_shared(scenario, lendingPoolWrapper);
            test_scenario::return_owned(scenario, poolInfo);
        };
    }
}