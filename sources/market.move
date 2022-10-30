module mala::market {
    use std::vector::{Self};
    use std::bcs::{Self};
    use std::ascii::{Self};
    use std::type_name::{Self, TypeName};

    use sui::tx_context::{Self, TxContext};
    use sui::transfer;
    use sui::object::{Self, ID, UID};
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::vec_map::{Self, VecMap};

    use sui::dynamic_object_field as dynamic_field;

    use mala::calculator::{Self};

    //use std::debug;

    struct Pool has key {
        id: UID,
        admin_address: address,
        // Only one submarket allowed per coin type.
        submarket_ids: VecMap<TypeName, ID>,
        borrow_record_ids: VecMap<vector<u8>, ID>
    }

    struct SubMarket<phantom T> has key, store {
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
    struct BorrowRecord<phantom B, phantom C> has key, store {
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
    const ERepayingForWrongBorrow: u64 = 9;
    const ERepayTooSmall: u64 = 10;

    public entry fun create_pool(ctx: &mut TxContext) {
        let market = Pool{
            id: object::new(ctx),
            admin_address: tx_context::sender(ctx),
            submarket_ids: vec_map::empty(),
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

        // This will error out if same type is attempted twice.
        vec_map::insert(&mut market.submarket_ids, type_name::get<T>(), object::id(&sub_market));
        // Transfer the Submarket ownership to Market.
        dynamic_field::add(
            &mut market.id,
            object::id(&sub_market),
            sub_market
        );
    }

    public entry fun deposit_collateral<T>(
        market: &mut Pool, collateral: Coin<T>, ctx: &mut TxContext
    ){
        let sub_market_id = vec_map::get(&market.submarket_ids, &type_name::get<T>());
        let sub_market = dynamic_field::borrow_mut<ID, SubMarket<T>>(
            &mut market.id,
            *sub_market_id
        );

        let collateral_balance = coin::into_balance(collateral);
        let collateral_value = balance::value(&collateral_balance);

        assert!(collateral_value > 0, EValidCollateralOnly);

        balance::join(&mut sub_market.balance, collateral_balance);
        add_col_value(
            &mut sub_market.collaterals,
            tx_context::sender(ctx),
            collateral_value
        );
    }

    // B type coin will be borrowed against C collateral.
    public fun borrow<B, C>(
        bor_amount: u64,
        col_amount: u64,
        market: &mut Pool,
        ctx: &mut TxContext
    ){
        let bor_market_id = vec_map::get(&mut market.submarket_ids, &type_name::get<B>());
        let col_market_id = vec_map::get(&mut market.submarket_ids, &type_name::get<C>());

        let bor_market = dynamic_field::remove<ID, SubMarket<B>>(
            &mut market.id,
            *bor_market_id
        );

        let col_market = dynamic_field::borrow_mut<ID, SubMarket<C>>(
            &mut market.id,
            *col_market_id
        );

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
        let address_bytes = build_borrow_record_bytes<B, C>(ctx);

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

            dynamic_field::add(
                &mut market.id,
                object::id(&borrow_record),
                borrow_record
            );
        } else {
            // Increase borrow and col amount for an existing <B, C> borrow record pair.

            let borrow_record_id = vec_map::get(
                &market.borrow_record_ids,
                &address_bytes
            );

            let borrow_record = dynamic_field::borrow_mut<ID, BorrowRecord<B,C>>(
                &mut market.id,
                *borrow_record_id
            );

            borrow_record.bor_amount = borrow_record.bor_amount + bor_amount;
            borrow_record.col_amount = borrow_record.col_amount + col_amount;
        };

        let borrowed_coin = coin::take(&mut bor_market.balance, bor_amount, ctx);

        // As borrow market was removed.
        dynamic_field::add(
            &mut market.id,
            object::id(&bor_market),
            bor_market
        );

        // Transfer the borrowed coin to sender. No fancy business.
        transfer::transfer(borrowed_coin, tx_context::sender(ctx));
    }

    public entry fun repay<B, C>(
        repay_coin : Coin<B>,
        col_to_release : u64,
        market: &mut Pool,
        ctx: &mut TxContext
    ){
        let repay_balance = coin::into_balance(repay_coin);
        let repay_value = balance::value(&repay_balance);

        // Grab the corresponding borrow record.
        // see if col_to_release is released, if borrow_record would be underwater.

        let borrow_record_id = vec_map::get(
            &market.borrow_record_ids,
            &build_borrow_record_bytes<B, C>(ctx)
        );

        let borrow_record = dynamic_field::borrow<ID, BorrowRecord<B,C>>(
            &market.id,
            *borrow_record_id
        );

        assert!(borrow_record.borrower == tx_context::sender(ctx), ERepayingForWrongBorrow);
        assert!(borrow_record.bor_amount >= repay_value, 1);
        assert!( borrow_record.col_amount >= col_to_release, 1);

        let borrow_after_repay = borrow_record.bor_amount - repay_value;
        let col_after_repay = borrow_record.col_amount - col_to_release;

        assert!(is_healthy<B, C>(move borrow_after_repay, move col_after_repay) == true, ERepayTooSmall);

        // The numbers make sense, deposit the coin and release the collateral.
        let borrow_submarket_id = vec_map::get(
            &market.submarket_ids,
            &type_name::get<B>()
        );
        let borrow_submarket = dynamic_field::remove<ID, SubMarket<B>>(
            &mut market.id,
            *borrow_submarket_id
        );

        let col_submarket_id = vec_map::get(
            &market.submarket_ids,
            &type_name::get<C>()
        );
        let col_submarket = dynamic_field::remove<ID, SubMarket<C>>(
            &mut market.id,
            *col_submarket_id
        );


        record_repay(
            &mut col_submarket.collaterals,
            &tx_context::sender(ctx),
            col_to_release
        );
        coin::put<B>(
            &mut borrow_submarket.balance,
            coin::from_balance(repay_balance, ctx)
        );

        // Add the submarkets back to the market.add
        dynamic_field::add(
            &mut market.id,
            object::id(&borrow_submarket),
            borrow_submarket
        );
        dynamic_field::add(
            &mut market.id,
            object::id(&col_submarket),
            col_submarket
        );
    }

    /* === Utils === */
    fun check_admin(market: &Pool, sender_address: address) {
        assert!(market.admin_address == sender_address, EAdminOnly);
    }

    // Check if a borrow_amount is healthy for a collateral amount.
    // For the current market conditions.
    fun is_healthy<B, C>(bor_amount: u64, col_amount: u64) : bool {
        let min_col = calculator::required_collateral_amount<B, C>(bor_amount);
        return col_amount >= min_col
    }

    fun build_borrow_record_bytes<B, C>(ctx: &mut TxContext) : vector<u8> {
        let address_bytes = bcs::to_bytes<address>(&tx_context::sender(ctx));
        let borrow_record_type_string = type_name::into_string(type_name::get<BorrowRecord<B, C>>());

        let borrow_record_type = ascii::into_bytes(borrow_record_type_string);
        vector::append<u8>(&mut address_bytes, borrow_record_type);

        address_bytes
    }

    // Adds to collateral gross value.
    fun add_col_value(
        collaterals: &mut VecMap<address, ColData>,
        sender: address,
        value: u64
    ){
        if(!vec_map::contains(collaterals, &sender)) {
            let col_data = ColData{gross: 0, utilized: 0};
            vec_map::insert(collaterals, sender, col_data);
        };

        let col_data = vec_map::get_mut(collaterals, &sender);
        col_data.gross = col_data.gross + value;
    }

    fun record_new_utilization(
        collaterals: &mut VecMap<address, ColData>,
        sender: &address,
        value: u64
    ){
        assert!(vec_map::contains(collaterals, sender) == true, EInvalidSender);
        let col_data = vec_map::get_mut(collaterals, sender);
        
        assert!(col_data.gross >= value + col_data.utilized, ECollateralTooBig);
        col_data.utilized = col_data.utilized + value;
    }

    fun record_repay(
        collaterals: &mut VecMap<address, ColData>,
        sender: &address,
        value: u64
    ){
        let col_data = vec_map::get_mut(collaterals, sender);
        
        assert!(col_data.utilized >= value, ECollateralTooBig);
        col_data.utilized = col_data.utilized - value;
    }

    /* === Reads === */
    #[test_only]
    public fun get_unused_col_from_market<T>(sender: address, market: &Pool) : u64 {
        let sub_market_id = vec_map::get(&market.submarket_ids, &type_name::get<T>());
        let sub_market = dynamic_field::borrow<ID, SubMarket<T>>(
            & market.id,
            *sub_market_id
        );

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
    public fun get_borrow_records_length(pool : &Pool) : u64 {
        vec_map::size<vector<u8>, ID>(&pool.borrow_record_ids)
    }

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
}
