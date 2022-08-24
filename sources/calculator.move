module mala::calculator {
    use mala::oracle;

    const CollateralMultiplier: u64 = 2;

    // Calculates how much collateral of type C to borrow bor_amount of type B
    // returns amount of minimum C coins needed
    // Not an entry fun because it needs to return a value.
    public fun required_collateral_amount<B, C>(bor_amount: u64) : u64 {
        let required_col_usd_value = oracle::usd_value<B>(bor_amount) * CollateralMultiplier;

        required_col_usd_value / oracle::usd_value<C>(1)
    }
}