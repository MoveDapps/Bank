/*
 * Market module will be used to initialize lending pools with a specific basket of coins.
 * Coins to include in a specific pool basket will be determined by the DAO.
 * One way to categorize basket of coins for a pool is risk.
 * High risk pools can contain higher volatility coins. Lower risk pool will contain stablecoins, BTC etc.
 *
 * In this specific example, only SUI coins are used for the basket.
 */

module market_address::market {
    use sui::coin::{Coin};
    use sui::tx_context::{Self, TxContext};
    use sui::sui::SUI;
    use sui::transfer;

    use market_address::data::{Self, MoneyMarket};

    // Percentage of the deposit value that can be borrowed. Will be dynamic eventually.
    const BORROW_UTILIZATION: u64 = 50;
    const EBorrowTooBig: u64 = 100;

    // Method to be executed when this module is published.
    public fun initialize(ctx: &mut TxContext) {
        let (money_market, money_market_info) = data::create_money_market<SUI>(ctx);
        transfer::share_object(money_market);
        transfer::transfer(money_market_info, tx_context::sender(ctx));
    }

    // Deposit SUI coins to the Lending Pool.
    public entry fun deposit(
        money_market: &mut MoneyMarket<SUI>,
        deposit_coin: Coin<SUI>,
        ctx: &mut TxContext
    ) {
        data::deposit(money_market, deposit_coin, ctx);
    }

    // Borrow SUI coins from the Lending Pool.
    public fun borrow(
        money_market: &mut MoneyMarket<SUI>,
        borrow_amount: u64,
        ctx: &mut TxContext
    ): Coin<SUI> {
        data::borrow(money_market, borrow_amount, ctx)
    }
}
