module market_address::market {
    use sui::balance::Balance;
    //use sui::coin::{Self, Coin};
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

    // Module initializer to be executed when this module is published.
    fun init(ctx: &mut TxContext) {
        use sui::transfer;
        use sui::tx_context;

        let info = object::new(ctx);
        let lendingPoolId = *object::info_id(&info);

        let lendingPool = LendingPool {
            info: info,
            poolBalance: vec_map::empty(),
            //coin::into_balance(coin::zero(ctx)),
        };

        let poolInfo = PoolInfo {
            info: object::new(ctx),
            lendingPoolId: lendingPoolId,
        };
        
        transfer::share_object(lendingPool);
        transfer::transfer(poolInfo, tx_context::sender(ctx));
    }

    //public entry fun deposit(payment: Coin<SUI>, ctx: &mut TxContext) {
    //    coin::put(&mut self.to_lend, coin);
    //}
}