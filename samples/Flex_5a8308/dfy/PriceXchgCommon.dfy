include "../../../src/BaseTypes.dfy"
include "../../../src/Queue.dfy"

include "Flex.dfy"
include "PriceCommon.dfy"

module PriceXchgCommon
{
  import opened BaseTypes
  import opened Flex
  import opened Queue
  import opened PriceCommon

  datatype RationalPrice = RationalPrice(num:uint128, denum:uint128)
  {
    function method numerator():uint128 { this.num }
    function method denominator():uint128 { this.denum }
  }

  type price_t = RationalPrice

  datatype PayloadArgs =
    PayloadArgs(
      sell:bool,
      amount:uint128,
      receive_tip3_wallet:addr_std_fixed,
      client_addr: addr_std_fixed
    )

  datatype OrderInfoXchg = OrderInfoXchg(
    original_amount:uint128,
    amount:uint128,
    account:uint128,
    tip3_wallet_provide:addr_std_fixed,
    tip3_wallet_receive:addr_std_fixed,
    client_addr:addr_std_fixed,
    order_finish_time:uint32,
    ghost id: nat
  )

  type OrderInfoXchgWithIdx = (unsigned, OrderInfoXchg)

  datatype DetailsInfoXchg = DetailsInfoXchg(
    price_num: uint128,
    price_denum: uint128,
    min_amount: uint128,
    sell_amount: uint128,
    buy_amount: uint128
  )

  datatype DPriceXchg = DPriceXchg(
    price_: price_t,
    sells_amount_:uint128,
    buys_amount_:uint128,
    flex_:addr_std_fixed,
    min_amount_:uint128,
    deals_limit_:uint8,
    notify_addr_: address,
    workchain_id_:int8,
    tons_cfg_:TonsConfig,
    tip3_code_:cell,
    major_tip3cfg_:Tip3Config,
    minor_tip3cfg_:Tip3Config,
    sells_:queue<OrderInfoXchg>,
    buys_:queue<OrderInfoXchg>,

    ghost next_id_: nat // introduced to track correspondence between
    // orders and messages produced during the order processing
  )
}
