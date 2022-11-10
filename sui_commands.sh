sui client call --package {PACKAGE} --module market --function deposit_collateral --gas-budget 30000 --type-args {COIN_TYPE} --args {MARKET} {COIN}
sui client call --package {PACKAGE} --module market --function withdraw --gas-budget 30000 --type-args {COIN_TYPE} --args {MARKET} {AMOUNT}

