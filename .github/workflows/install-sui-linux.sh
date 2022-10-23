#!/bin/bash
sudo apt-get update
sudo apt install curl
sudo apt-get install git-all

# install make
./bootstrap
make
make install

sudo apt-get install libssl-dev
sudo apt-get install libclang-dev

# install rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
rustup update stable


# install sui binary
cargo install --locked --git https://github.com/MystenLabs/sui.git --branch devnet sui sui-node