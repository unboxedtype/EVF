include "../../../src/BaseTypes.dfy"
  
module Flex
{
  import opened BaseTypes
// Processing native funds value ...
// struct TonsConfig {
//   // ... for executing tip3 transfer
//   uint128 transfer_tip3;
//   // ... to return tip3 ownership
//   uint128 return_ownership;
//   // ... to deploy tip3 trading pair
//   uint128 trading_pair_deploy;
//   // .. to send answer message from Price
//   uint128 order_answer;
//   // ... to process processQueue function
//   //  (also is used for buyTip3/onTip3LendOwnership/cancelSell/cancelBuy estimations)
//   uint128 process_queue;
//   // ... to send notification about completed deal (IFlexNotify)
//   uint128 send_notify;
// };
  datatype TonsConfig =
    TonsConfig(transfer_tip3:uint128,
    return_ownership:uint128,
    trading_pair_deploy:uint128,
    order_answer:uint128,
    process_queue:uint128,
    send_notify:uint128)
}
