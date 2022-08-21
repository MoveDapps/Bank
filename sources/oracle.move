module market_address::oracle {
    // Fake oracle. Assumes USD value of ALL coins are 1.
    // Not an entry fun because it needs to return a value.
    public fun usd_value<T>(amount: u64) : u64 {
        return amount
    }
}