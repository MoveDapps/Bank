module mala::market {
    use std::errors;
    use std::vector::{Self};
    //use std::debug;

    use sui::tx_context::{Self, TxContext};
    use sui::transfer;
    use sui::object::{Self, ID, UID};
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::vec_set::{Self, VecSet};
    use sui::vec_map::{Self, VecMap};

    use mala::calculator::{Self};

    struct Market has key {
        id: UID,
        submarket_ids: VecSet<ID>,
        borrow_record_ids: vector<ID>
    }

    struct SubMarket<phantom T> has key {
        id: UID,
        balance: Balance<T>,
        collaterals: VecMap<address, ColData>
    }

    struct AdminCap has key {
        id: UID,
        market_id: ID
    }

    // Info on collateral usage info by address, to be stored in submarkets.
    struct ColData has store {
        gross: u64,
        utilized: u64
    }

    // Borrow records to run liquidation against.
    struct BorrowRecord<phantom B, phantom C> has key {
        id: UID,
        borrower: address,
        col_amount: u64,
        bor_amount: u64
    }

    /* Error codes */
    const EAdminOnly: u64 = 1;
    const EChildObjectOnly: u64 = 2;
    const EValidCollateralOnly: u64 = 3;
    const EInvalidColData: u64 = 4;
    const EBorrowTooBig: u64 = 5;
    const ECollateralTooBig: u64 = 6;
    const ENotEnoughCollateral: u64 = 7;
    const EInvalidSender: u64 = 8;

    public entry fun create_market(ctx: &mut TxContext) {
        let market = Market{
            id: object::new(ctx),
            submarket_ids: vec_set::empty(),
            borrow_record_ids: vector::empty()
        };
        let admin_cap = AdminCap{id: object::new(ctx), market_id: get_market_id(&market)};
        
        // Share market globally, so that anyone can deposit or borrow.
        transfer::share_object(market);
        // Transfer admin capability to the tx sender.
        transfer::transfer(admin_cap, tx_context::sender(ctx));
    }

    public entry fun create_sub_market<T>(market: &mut Market, admin_cap: &mut AdminCap, ctx: &mut TxContext) {
        let sub_market = SubMarket<T>{
            id: object::new(ctx),
            balance: balance::zero(),
            collaterals: vec_map::empty()
        };
        
        // Only an admin can create a sub market recognized by this market.
        check_admin(market, admin_cap);
        // SubMarket objects are owned by Market objects.
        vec_set::insert(&mut market.submarket_ids, get_submarket_id<T>(&sub_market));
        // Transfer the Submarket ownership to Market.
        transfer::transfer_to_object(sub_market, market);
    }

    public entry fun deposit_collateral<T>(
        market: &mut Market, sub_market: &mut SubMarket<T>, collateral: Coin<T>, ctx: &mut TxContext
    ) {
        // Check if SubMarket is owned by Market.
        check_child(market, sub_market);

        let collateral_balance = coin::into_balance(collateral);
        let collateral_value = balance::value(&collateral_balance);

        assert!(collateral_value > 0, errors::invalid_argument(EValidCollateralOnly));

        balance::join(&mut sub_market.balance, collateral_balance);
        add_col_value(&mut sub_market.collaterals, tx_context::sender(ctx), collateral_value);
    }

    // B type coin will be borrowed against C collateral.
    public fun borrow<B, C>(
        bor_amount: u64, col_amount: u64,
        bor_market: &mut SubMarket<B>, col_market: &mut SubMarket<C>, market: &mut Market, ctx: &mut TxContext
    ) : Coin<B> {
        // Check if submarkets are owned by market.
        check_child(market, bor_market);
        check_child(market, col_market);

        // Check if borrow market has enough funds.
        assert!(balance::value(&bor_market.balance) >= bor_amount, errors::invalid_argument(EBorrowTooBig));

        let unused_col = get_unused_col(&tx_context::sender(ctx), col_market);
        // Check if there's enough unused collateral.
        assert!(unused_col >= col_amount, errors::invalid_argument(ECollateralTooBig));
        
        // Check that col_amount is greater or equal to minimum required collateral.
        let minimum_required_col = calculator::required_collateral_amount<B, C>(bor_amount);
        assert!(col_amount >= minimum_required_col, errors::invalid_argument(ENotEnoughCollateral));

        record_new_utilization(&mut col_market.collaterals, &tx_context::sender(ctx), col_amount);
 
        // Create borrow record for liquidation bot.
        let borrow_record = BorrowRecord<B, C> {
            id: object::new(ctx),
            borrower: tx_context::sender(ctx),
            col_amount: col_amount,
            bor_amount: bor_amount
        };

        // The borrow record should be owned by and recorded inside the market.
        vector::push_back(&mut market.borrow_record_ids, object::uid_to_inner(&borrow_record.id));
        transfer::transfer_to_object(borrow_record, market);

        coin::take(&mut bor_market.balance, col_amount, ctx)
    }

    /* === Utils === */
    fun check_admin(market: &Market, admin_cap: &AdminCap) {
        //assert!(object::borrow_id(market) == &admin_cap.market_id, errors::invalid_argument(EAdminOnly));
        assert!(object::borrow_id(market) == &admin_cap.market_id, EAdminOnly);
    }

    public fun check_child<T>(market: &Market, sub_market: &SubMarket<T>) {
        assert!(
            vec_set::contains(&market.submarket_ids, &get_submarket_id(sub_market)) == true,
            errors::invalid_argument(EChildObjectOnly)
        )
    }

    // Adds to collateral gross value.
    fun add_col_value(collaterals: &mut VecMap<address, ColData>, sender: address, value: u64) {
        if(!vec_map::contains(collaterals, &sender)) {
            let col_data = ColData{gross: 0, utilized: 0};
            vec_map::insert(collaterals, sender, col_data);
        };

        let col_data = vec_map::get_mut(collaterals, &sender);
        col_data.gross = col_data.gross + value;
    }

    fun record_new_utilization(collaterals: &mut VecMap<address, ColData>, sender: &address, value: u64) {
        assert!(vec_map::contains(collaterals, sender) == true, errors::invalid_argument(EInvalidSender));
        let col_data = vec_map::get_mut(collaterals, sender);
        
        assert!(col_data.gross >= value + col_data.utilized, errors::invalid_argument(ECollateralTooBig));
        col_data.utilized = col_data.utilized + value;
    }

    /* === Reads === */
    public fun get_market_id(market: &Market) : ID {
        object::uid_to_inner(&market.id)
    }

    #[test_only]
    public fun get_admincap_marketid(admin_cap: &AdminCap) : ID {
        admin_cap.market_id
    }

    #[test_only]
    public fun get_admincap_id(admin_cap: &AdminCap) : ID {
        object::uid_to_inner(&admin_cap.id)
    }

    fun get_submarket_id<T>(sub_market: &SubMarket<T>) : ID {
        object::uid_to_inner(&sub_market.id)
    }

    fun get_unused_col<T>(sender: &address, sub_market: &SubMarket<T>) : u64 {
        // Return immediately if sender doesn't have a collateral is this sub market.
        if(!vec_map::contains(&sub_market.collaterals, sender)) {
            0u64
        } else {
            let col_data = vec_map::get(&sub_market.collaterals, sender);
        
            assert!(col_data.gross >= col_data.utilized, errors::invalid_state(EInvalidColData));
            assert!(col_data.gross > 0, errors::invalid_state(EInvalidColData));
            assert!(col_data.utilized >= 0, errors::invalid_state(EInvalidColData));

            col_data.gross - col_data.utilized
        }
    }
}
