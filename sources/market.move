module mala::market {
    use std::vector::{Self};
    use std::bcs::{Self};
    use std::ascii::{Self, String};
    use std::type_name::{Self};
    //use std::string::{Self, String};

    use sui::tx_context::{Self, TxContext};
    use sui::transfer;
    use sui::object::{Self, ID, UID};
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::vec_set::{Self, VecSet};
    use sui::vec_map::{Self, VecMap};

    use mala::calculator::{Self};

    use std::debug;

    struct Pool has key {
        id: UID,
        admin_address: address,
        submarket_ids: VecSet<ID>,
        borrow_record_ids: VecMap<vector<u8>, ID>
    }

    struct SubMarket<phantom T> has key {
        id: UID,
        balance: Balance<T>,
        collaterals: VecMap<address, ColData>
    }

    // Info on collateral usage info by address, to be stored in submarkets.
    struct ColData has store {
        gross: u64,
        utilized: u64
    }

    // TODO: convert borrow record to top level object after dynamic loading support. (e.g. no store cap, only key)
    // Borrow records to run liquidation against. To be stored in markets.
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

    public entry fun create_pool(ctx: &mut TxContext) {
        let market = Pool{
            id: object::new(ctx),
            admin_address: tx_context::sender(ctx),
            submarket_ids: vec_set::empty(),
            borrow_record_ids: vec_map::empty()
        };
        
        // Share market globally, so that anyone can deposit or borrow.
        transfer::share_object(market);
    }

    public entry fun create_sub_market<T>(market: &mut Pool, ctx: &mut TxContext) {
        // Only an admin can create a sub market recognized by this market.
        check_admin(market, tx_context::sender(ctx));

        let sub_market = SubMarket<T>{
            id: object::new(ctx),
            balance: balance::zero(),
            collaterals: vec_map::empty()
        };

        // SubMarket objects are owned by Market objects.
        vec_set::insert(&mut market.submarket_ids, object::id(&sub_market));
        // Transfer the Submarket ownership to Market.
        transfer::share_object(sub_market);
        
        // TODO - change it to transfer to object
        // transfer::transfer_to_object(sub_market, market);
    }

    public entry fun deposit_collateral<T>(
        market: &mut Pool, sub_market: &mut SubMarket<T>, collateral: Coin<T>, ctx: &mut TxContext
    ) {
        // Check if SubMarket is owned by Market.
        check_child(market, sub_market);

        let collateral_balance = coin::into_balance(collateral);
        let collateral_value = balance::value(&collateral_balance);

        assert!(collateral_value > 0, EValidCollateralOnly);

        balance::join(&mut sub_market.balance, collateral_balance);
        add_col_value(&mut sub_market.collaterals, tx_context::sender(ctx), collateral_value);
    }

    // B type coin will be borrowed against C collateral.
    public fun borrow<B, C>(
        bor_amount: u64, col_amount: u64,
        bor_market: &mut SubMarket<B>, col_market: &mut SubMarket<C>, market: &mut Pool, ctx: &mut TxContext
    ) : Coin<B> {
        // Check if submarkets are owned by market.
        check_child(market, bor_market);
        check_child(market, col_market);

        // Check if borrow market has enough funds.
        assert!(balance::value(&bor_market.balance) >= bor_amount, EBorrowTooBig);

        let unused_col = get_unused_col<C>(tx_context::sender(ctx), col_market);
        // Check if there's enough unused collateral.
        assert!(unused_col >= col_amount, ECollateralTooBig);
        
        // Check that col_amount is greater or equal to minimum required collateral.
        let minimum_required_col = calculator::required_collateral_amount<B, C>(bor_amount);
        assert!(col_amount >= minimum_required_col, ENotEnoughCollateral);

        record_new_utilization(&mut col_market.collaterals, &tx_context::sender(ctx), col_amount);

        // Build key with address + type of B + type of C
        let address_bytes = bcs::to_bytes<address>(&tx_context::sender(ctx));
        let borrow_record_type_string = type_name::into_string(type_name::get<BorrowRecord<B, C>>());

        //debug::print(&ascii::all_characters_printable(&borrow_record_type_string));
        //debug::print(&borrow_record_type_string);

        let borrow_record_type = ascii::into_bytes(borrow_record_type_string);

        vector::append<u8>(&mut address_bytes, borrow_record_type);

        // The borrow record should be owned by and recorded inside the market.
        if(!vec_map::contains(&market.borrow_record_ids, &address_bytes)) {
            // Create borrow record for liquidation bot.
            let borrow_record = BorrowRecord<B, C> {
                id: object::new(ctx),
                borrower: tx_context::sender(ctx),
                col_amount: col_amount,
                bor_amount: bor_amount
            };

            vec_map::insert(
                &mut market.borrow_record_ids,
                address_bytes,
                object::uid_to_inner(&borrow_record.id)
            );

            transfer::share_object(borrow_record);
        } else {
            // Need to dynamically load the borrow record which doesn't exist yet.
        };

        coin::take(&mut bor_market.balance, bor_amount, ctx)
    }

    /* === Utils === */
    fun check_admin(market: &Pool, sender_address: address) {
        assert!(market.admin_address == sender_address, EAdminOnly);
    }

    public fun check_child<T>(market: &Pool, sub_market: &SubMarket<T>) {
        assert!(
            vec_set::contains(&market.submarket_ids, &object::id(sub_market)) == true,
            EChildObjectOnly
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
        assert!(vec_map::contains(collaterals, sender) == true, EInvalidSender);
        let col_data = vec_map::get_mut(collaterals, sender);
        
        assert!(col_data.gross >= value + col_data.utilized, ECollateralTooBig);
        col_data.utilized = col_data.utilized + value;
    }

    /* === Reads === */
    public fun get_unused_col<T>(sender: address, sub_market: &SubMarket<T>) : u64 {
        // Return immediately if sender doesn't have a collateral is this sub market.
        if(!vec_map::contains(&sub_market.collaterals, &sender)) {
            0u64
        } else {
            let col_data = vec_map::get(&sub_market.collaterals, &sender);
        
            assert!(col_data.gross >= col_data.utilized, EInvalidColData);
            assert!(col_data.gross > 0, EInvalidColData);
            assert!(col_data.utilized >= 0, EInvalidColData);

            col_data.gross - col_data.utilized
        }
    }

    #[test_only]
    public fun get_submarket_list(market : &Pool) : &VecSet<ID> {
        &market.submarket_ids
    }
}
