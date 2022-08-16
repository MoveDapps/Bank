/*
 * Market module will be used to initialize lending pools with a specific basket of coins.
 * Coins to include in a specific pool basket will be determined by the DAO.
 * One way to categorize basket of coins for a pool is risk.
 * High risk pools can contain higher volatility coins. Lower risk pool will contain stablecoins, BTC etc.
 *
 * In this specific example, only SUI coins are used for the basket.
 */

module market_address::market {
    use sui::balance::{Self};
    use sui::coin::{Coin};
    use sui::object::{Self};
    use sui::tx_context::{Self, TxContext};
    use sui::vec_map::{Self};
    use sui::sui::SUI;
    use sui::transfer;

    use market_address::data::{Self, LendingPool};

    // Percentage of the deposit value that can be borrowed. Will be dynamic eventually.
    const BORROW_UTILIZATION: u64 = 50;
    const EBorrowTooBig: u64 = 100;

    // Method to be executed when this module is published.
    public fun initialize(ctx: &mut TxContext) {
        let info = object::new(ctx);
        let lending_pool_id = *object::info_id(&info);

        let lending_pool = data::create_lending_pool<SUI> (
            info,
            balance::zero(),
            vec_map::empty(),
            vec_map::empty(),
        );

        let pool_info = data::create_pool_info(object::new(ctx), lending_pool_id);
        
        transfer::share_object(lending_pool);
        transfer::transfer(pool_info, tx_context::sender(ctx));
    }

    // Deposit SUI coins to the Lending Pool.
    public entry fun deposit(
        lending_pool: &mut LendingPool<SUI>,
        deposit_coin: Coin<SUI>,
        ctx: &mut TxContext
    ) {
        data::deposit(lending_pool, deposit_coin, ctx);
    }

    // Borrow SUI coins from the Lending Pool.
    public fun borrow(
        lending_pool: &mut LendingPool<SUI>,
        borrow_amount: u64,
        ctx: &mut TxContext
    ): Coin<SUI> {
        data::borrow(lending_pool, borrow_amount, ctx)
    }
}
