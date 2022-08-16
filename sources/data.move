module market_address::data {
    use sui::balance::{Self, Balance};
    use sui::coin::{Self, Coin};
    use sui::object::{Self, ID, Info};
    use sui::tx_context::{Self, TxContext};
    use sui::vec_map::{Self, VecMap};
    use sui::sui::SUI;

    // Percentage of the deposit value that can be borrowed. Will be dynamic eventually.
    const BORROW_UTILIZATION: u64 = 50;
    const EBorrowTooBig: u64 = 100;
    
    // Lending Pool for SUI coins.
    struct LendingPool has key, store {
        info: Info,
        pool_balance: Balance<SUI>,

        // Record of deposit amounts by different addresses.
        pool_deposit_records: VecMap<address, u64>,

        // Record of borrowed amounts by different addresses.
        pool_borrow_records: VecMap<address, u64>,
    }

    // Lending Pool info to be passed to the initializer address.
    struct PoolInfo has key, store {
        info: Info,
        lending_pool_id: ID,
    }

    public fun create_lending_pool(
        info: Info,
        pool_balance: Balance<SUI>,
        pool_deposit_records: VecMap<address, u64>,
        pool_borrow_records: VecMap<address, u64>,
    ) : LendingPool {
        LendingPool {info, pool_balance, pool_deposit_records, pool_borrow_records}
    }

    public fun create_pool_info (info: Info, lending_pool_id: ID): PoolInfo {
        PoolInfo {info, lending_pool_id}
    }

    /* ==== Reads start here ==== */

    public fun get_pool_id(self: &PoolInfo): ID {
        self.lending_pool_id
    }

    public fun get_lending_pool_id(self: &LendingPool): ID {
        *object::info_id(&self.info)
    }

    // Return the maximum amount available for borrowing to this address.
    public fun get_deposit_balance_by_address(
        lending_pool: &LendingPool,
        key_address: &address
    ): u64 {
        if(!vec_map::contains(&lending_pool.pool_deposit_records, key_address)) {
            0u64
        }
        else {
            *vec_map::get(&lending_pool.pool_deposit_records, key_address)
        }
    }

    public fun get_borrow_limit(lending_pool: &LendingPool, borrower_address: &address): u64 {
        let deposit_balance
            = get_deposit_balance_by_address(lending_pool, borrower_address);

        let borrowed_balance;
        if(!vec_map::contains(&lending_pool.pool_borrow_records, borrower_address)) {
            borrowed_balance = 0u64;
        }
        else {
            borrowed_balance = *vec_map::get(&lending_pool.pool_borrow_records, borrower_address);
        };

        let limit: u64 = (deposit_balance * BORROW_UTILIZATION) / 100;

        limit - borrowed_balance
    }

    #[test_only]
    public fun get_total_pool_balance(lending_pool: &LendingPool): u64 {
        balance::value(&lending_pool.pool_balance)
    }

    /* ==== Reads end here ==== */

    public entry fun deposit(
        lending_pool: &mut LendingPool,
        deposit_coin: Coin<SUI>,
        ctx: &mut TxContext
    ) {
        let pool_deposit_records = &mut lending_pool.pool_deposit_records;
        let sender_address = tx_context::sender(ctx);
        let deposit_balance = coin::into_balance(deposit_coin);
        let deposit_value = balance::value(&deposit_balance);

        balance::join(&mut lending_pool.pool_balance, deposit_balance);

        if(!vec_map::contains(pool_deposit_records, &sender_address)) {
            vec_map::insert(
                pool_deposit_records,
                sender_address,
                deposit_value
            );
        }
        else {
            let current_balance = vec_map::get_mut(
                pool_deposit_records,
                &sender_address
            );

            *current_balance = *current_balance + deposit_value;
        }
    }

    // Borrow SUI coins from the Lending Pool.
    public fun borrow(
        lending_pool: &mut LendingPool,
        borrow_amount: u64,
        ctx: &mut TxContext
    ): Coin<SUI> {
        let sender_address = tx_context::sender(ctx);

        assert!(get_borrow_limit(lending_pool, &sender_address) >= borrow_amount, EBorrowTooBig);

        let pool_borrow_records = &mut lending_pool.pool_borrow_records;
        if(!vec_map::contains(pool_borrow_records, &sender_address)) {
            vec_map::insert(
                pool_borrow_records,
                sender_address,
                borrow_amount
            );
        }
        else {
            let current_balance = vec_map::get_mut(
                pool_borrow_records,
                &sender_address
            );

            *current_balance = *current_balance + borrow_amount;
        };

        coin::take(&mut lending_pool.pool_balance, borrow_amount, ctx)
    }
}