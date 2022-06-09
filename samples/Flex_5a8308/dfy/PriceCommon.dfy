include "../../../src/BaseTypes.dfy"
include "../../../src/Queue.dfy"

include "Flex.dfy"

module PriceCommon
{
  import opened BaseTypes
  import opened Flex
  import opened Queue

  datatype SellArgs = SellArgs(
    amount: uint128,
    receive_wallet: address
  )

  datatype OrderInfo = OrderInfo(
    original_amount:uint128,
    amount:uint128,
    account:uint128,
    tip3_wallet:addr_std_fixed,
    client_addr:addr_std_fixed,
    order_finish_time:uint32,
    ghost id: nat
  )

  type OrderInfoWithIdx = (unsigned, OrderInfo)

  datatype OrderRet = OrderRet(
    err_code:uint32,
    processed:uint128,
    enqueued:uint128
  )

  datatype Tip3Config = Tip3Config(
    name:string,
    symbol:string,
    decimals:uint8,
    root_public_key:uint256,
    root_address:addr_std_compact
  )

  datatype DPrice = DPrice(
    price_:uint128,
    sells_amount_:uint128,
    buys_amount_:uint128,
    flex_:addr_std_fixed,
    min_amount_:uint128,
    deals_limit_:uint8,
    notify_addr_: address,
    workchain_id_:int8,
    tons_cfg_:TonsConfig,
    tip3_code:cell,
    tip3cfg_:Tip3Config,
    sells_:queue<OrderInfo>,
    buys_:queue<OrderInfo>,

    ghost next_id_: nat // introduced to track correspondence between
    // orders and messages produced during the order processing
  )
}
