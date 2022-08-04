module market_address::market {
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    //use sui::id::{Self, UID};
    use sui::object::{Self, ID, Info};
    use sui::tx_context::TxContext;
    use sui::vec_map::{Self, VecMap};
    //use sui::id::VersionedID;
    //use sui::transfer;
    //use sui::tx_context::{Self, TxContext};
    use sui::sui::{Self, SUI};
    
    // Lending Pool for SUI coins.
    // All addresses deposited to the pool will exist in poolBalance.
    struct LendingPool has key {
        id: Info,
        poolBalance:  VecMap<address, Balance<SUI>>,
    }

    struct PoolInfo has key {
        lendingPoolId: ID,
    }

    /*struct DespositReceipt has key {
        id: VersionedID,
        lending_pool_id: VersionedID,
        depositedAmount: u64,
    }*/

    // Module initializer to be executed when this module is published.
    fun init(ctx: &mut TxContext) {
        use sui::transfer;
        use sui::tx_context;

        let info = object::new(ctx);
        let lendingPoolId = *object::info_id(&info);

        let lendingPool = LendingPool {
            id: info,
            poolBalance: vec_map::empty(),
            //coin::into_balance(coin::zero(ctx)),
        };

        let poolInfo = PoolInfo {
            lendingPoolId: lendingPoolId,
        };
        
        transfer::share_object(lendingPool);
        transfer::transfer(poolInfo, tx_context::sender(ctx));
    }

    //public entry fun deposit(payment: Coin<SUI>, ctx: &mut TxContext) {
    //    coin::put(&mut self.to_lend, coin);
    //}
}