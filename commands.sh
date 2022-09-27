
- sui client publish --path /Users/bidhan/Development/Sui/bank --gas-budget 30000

----- Certificate ----
Transaction Hash: dXTxxJfXz2YL2OeR7X1/LbDqJdV4pFtPwEVgovxRGvw=
Transaction Signature: AA==@VwzzOcDfHn4Z6bcOIrLd4DTqyhBw7rdz/Imu8oKVhd5Qz6jRUNJ/ET13niwX6cIJ686zGDfxv8OUO3/D8aJ/DQ==@Xf7cd3i8TBKGSwnofQn2bd6hKh+jrZ0yj5i17jLK/BA=
Signed Authorities Bitmap: RoaringBitmap<[1, 2, 3]>
Transaction Kind : Publish
----- Transaction Effects ----
Status : Success
Created Objects:
  - ID: 0xe31b3a3d8f88867bebff66cae56ac0da8f4b636d , Owner: Immutable
Mutated Objects:
  - ID: 0x033fc19a85bcfea36e3be78817e7cf4aa8b75173 , Owner: Account Address ( 0x507c7507068cc6e4267495f7bd437d6b7151bbee )
----- Publish Results ----
The newly published package object ID: 0xe31b3a3d8f88867bebff66cae56ac0da8f4b636d

Updated Gas : Coin { id: 0x033fc19a85bcfea36e3be78817e7cf4aa8b75173, value: 42358 }


- export package_id=‘0xe31b3a3d8f88867bebff66cae56ac0da8f4b636d’

- sui client call --package $package_id --module market --function create_market --gas-budget 30000

Created Objects:
  - ID: 0x3b37260f66e4e1e673ce24a13fd22d3928a76876 , Owner: Account Address ( 0x507c7507068cc6e4267495f7bd437d6b7151bbee )
  - ID: 0x6b9560e6cb5d4072b2adc678800568092bc2732e , Owner: Shared
Mutated Objects:
  - ID: 0x033fc19a85bcfea36e3be78817e7cf4aa8b75173 , Owner: Account Address ( 0x507c7507068cc6e4267495f7bd437d6b7151bbee )


- export admin_cap='0x3b37260f66e4e1e673ce24a13fd22d3928a76876'
- export market_address='0x6b9560e6cb5d4072b2adc678800568092bc2732e'
- sui client call --package $package_id --module market --function create_sub_market --gas-budget 30000 --args $market_address $admin_cap --type-args 0x2::sui::SUI

Created Objects:
  - ID: 0x88fd8643c7c6059d42a08721bf228ddcbaeead70 , Owner: Object ID: ( 0x6b9560e6cb5d4072b2adc678800568092bc2732e )
Mutated Objects:
  - ID: 0x033fc19a85bcfea36e3be78817e7cf4aa8b75173 , Owner: Account Address ( 0x507c7507068cc6e4267495f7bd437d6b7151bbee )
  - ID: 0x3b37260f66e4e1e673ce24a13fd22d3928a76876 , Owner: Account Address ( 0x507c7507068cc6e4267495f7bd437d6b7151bbee )
  - ID: 0x6b9560e6cb5d4072b2adc678800568092bc2732e , Owner: Shared

- export submarket_address='0x88fd8643c7c6059d42a08721bf228ddcbaeead70'
- 
