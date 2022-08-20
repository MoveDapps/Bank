module market_address::market {
    use sui::tx_context::{Self, TxContext};
    use sui::transfer;
    use sui::object::{Self, ID, UID};
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use std::errors;
    use sui::vec_set::{Self, VecSet};

    struct Market has key {
        id: UID,
        submarket_ids: VecSet<ID>
    }

    struct SubMarket<phantom T> has key {
        id: UID,
        balance: Balance<T>,
    }

    struct AdminCap has key {
        id: UID,
        market_id: ID
    }

    /* Error codes */
    const EAdminOnly: u64 = 1;
    const EChildObjectOnly: u64 = 2;

    public entry fun create_market(ctx: &mut TxContext) {
        let market = Market{id: object::new(ctx), submarket_ids: vec_set::empty()};
        let admin_cap = AdminCap{id: object::new(ctx), market_id: get_market_id(&market)};
        
        // Share market globally, so that anyone can deposit or borrow.
        transfer::share_object(market);
        // Transfer admin capability to the tx sender.
        transfer::transfer(admin_cap, tx_context::sender(ctx));
    }

    public entry fun create_sub_market<T>(market: &mut Market, admin_cap: &mut AdminCap, ctx: &mut TxContext) {
        let sub_market = SubMarket<T>{
            id: object::new(ctx),
            balance: balance::zero()
        };
        
        // Only an admin can create a sub market recognized by this market.
        check_admin(market, admin_cap);
        // SubMarket objects are owned by Market objects.
        transfer::transfer_to_object(sub_market, market);
    }

    public entry fun deposit_collateral<T>(
        market: &mut Market, sub_market: &mut SubMarket<T>, collateral: Coin<T>, ctx: &mut TxContext
    ) {
        // Check if SubMarket is owned by Market.
        check_child(market, sub_market);
        coin::put(&mut sub_market.balance, collateral);
    }

    fun check_admin(market: &Market, admin_cap: &AdminCap) {
        assert!(object::borrow_id(market) == &admin_cap.market_id, errors::invalid_argument(EAdminOnly));
    }

    fun check_child<T>(market: &Market, sub_market: &SubMarket<T>) {
        assert!(
            vec_set::contains(&market.submarket_ids, &get_submarket_id(sub_market)) == true,
            errors::invalid_argument(EChildObjectOnly)
        )
    }

    /* === Reads === */
    fun get_market_id(market: &Market) : ID {
        object::uid_to_inner(&market.id)
    }

    fun get_submarket_id<T>(sub_market: &SubMarket<T>) : ID {
        object::uid_to_inner(&sub_market.id)
    }
}
