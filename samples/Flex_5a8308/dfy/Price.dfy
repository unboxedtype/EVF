include "../../../src/TONContract.dfy"
include "../../../src/Queue.dfy"
  
include "PriceCommon.dfy"
include "Flex.dfy"
include "FlexTypes.dfy"
include "TONTokenWallet.dfy"

module PriceModule refines TONModule
{
  import opened T = FlexTypes
  import opened PriceCommon
  import opened Flex
  import opened Queue

  import TTW = TONTokenWalletModule

  const ok:unsigned := 0;

  // error_codes from ec struct
  const ec_out_of_tons:unsigned                := 100;
  const ec_deals_limit:unsigned                := 101;
  const ec_not_enough_tons_to_process:unsigned := 102;
  const ec_not_enough_tokens_amount:unsigned   := 103;
  const ec_too_big_tokens_amount:unsigned      := 104;
  const ec_different_workchain_id              := 105;
  const ec_unverified_tip3_wallet:unsigned     := 106;
  const ec_canceled:unsigned                   := 107;
  const ec_expired:unsigned                    := 108;

  const safe_delay_period:uint64 := 5 * 60;

  datatype process_ret = process_ret(
    sells_amont:uint128,
    sells_:queue<OrderInfo>,
    buys_amount:uint128,
    buys_:queue<OrderInfo>,
    ret_:option<OrderRet>
  )

  function method calc_cost(amount:uint128, price:uint128): option<uint128>
  {
    // Obvious for you, but not for Dafny: non-linear arithmetic is hard.
    assume ( (amount as nat) * (price as nat) <= MAX_UINT256_NAT );
    var tons_cost:unsigned := (amount as nat * price as nat) as unsigned;
    // check if tons_cost consumed more than 128 bits.
    if (tons_cost > MAX_UINT128 as unsigned) then
      None
    else
      Value(tons_cost as uint128)
  }

  class ContractStateVariables ...
  {
    var d:DPrice;

    constructor ()
    {
      d := DPrice(0, 0, 0, address.Default(), 0, 0,
        address.Default(), 0, TonsConfig(0, 0, 0, 0, 0, 0),
        0, Tip3Config("", "", 0, 0, address.Default()), [], [], 0);
    }

    predicate initial_values ...
    {
      d.buys_ == [] && d.sells_ == []
    }
  }

  class TONContract ...
  {
    method backup_state ...
      ensures tmp_st.d == st.d
    {
      tmp_st.d := st.d;
    }

    method rollback_state ...
      ensures st.d == tmp_st.d
    {
      st.d := tmp_st.d;
    }

    predicate constructor_post ...
    {
      st.d.buys_ == [] && st.d.sells_ == []
    }

    method execute_constructor() returns (r:Status)
      ensures action_queue == []
      ensures deferred_queue == []
      ensures msg().body.val.ctor.Price? <==> r == Success
      ensures unchanged (st)
    {
      if (msg().body.val.ctor.Price?) {
        /* constructor for Price is absent, so it always succeed. */
        return Success;
      }
      return Failure(UnknownFunctionId);
    }

    method execute_ctor_method() returns (r:Status)
      ensures internal_message() &&
      msg().body.val.cm.buyTip3? &&
      buyTip3_pre(
        msg().body.val.cm.amount,
        msg().body.val.cm.order_finish_time) ==>
      r == Success &&
      buyTip3_comp(
        msg().body.val.cm.amount,
        msg().body.val.cm.order_finish_time)
    {
      r := Failure(UnknownFunctionId);
      // the match should be exhaustive.
      var m := msg().body.val.cm;
      match m {
        case buyTip3(amount, my_tip3_addr, order_finish_time) =>
          if (internal_message()) {
            var _, _, _, _ :- buyTip3(amount, my_tip3_addr, order_finish_time);
            return Success;
          } else {
            return Failure(UnknownFunctionId);
          }
        case _ =>
          return Failure(UnknownFunctionId);
      }
      return Success;
    }

    function method is_active_time(order_finish_time:uint32): bool
      reads `unix_blocktime
    {
      assume (tvm_now() as nat + safe_delay_period as nat < MAX_UINT64_NAT);
      tvm_now() + safe_delay_period < order_finish_time as uint64
    }

    // The minimum amount of coins needed to process the buy
    // order request. The communication expenses between
    // different system components needs to be covered by
    // this fee.
    function method {:fuel addL, 5} buyTip3MinValue(buy_cost:uint128):uint128
      reads `st, st`d
    {
      // The original expression was:
      // buy_cost + tons_cfg_.process_queue + tons_cfg_.transfer_tip3 +
      // tons_cfg_.send_notify + tons_cfg_.order_answer;
      // We use add(X,Y) because we assume that no uint128 overflow
      // might be expected here.

      addL([buy_cost,
        st.d.tons_cfg_.process_queue,
        st.d.tons_cfg_.transfer_tip3,
        st.d.tons_cfg_.send_notify,
        st.d.tons_cfg_.order_answer])
    }

    method process_queue_impl(tip3root:address, notify_addr:address,
      price:uint128, deals_limit:uint8, tons_cfg:TonsConfig,
      sell_idx:unsigned, buy_idx:unsigned, sells_amount:uint128,
      sells:queue<OrderInfo>, buys_amount:uint128, buys:queue<OrderInfo>)
    returns (
      r: process_ret,
      ghost or: seq<OrderInfo>,
      ghost po: seq<OrderInfo>,
      ghost fo_buy: seq<OrderInfo>,
      ghost fo_sell: seq<OrderInfo>
    )
      /* PQI.PRE.1 */
      requires forall ord :: ord in buys ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in sells ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in buys ==> ord.id < st.d.next_id_
      requires forall ord :: ord in sells ==> ord.id < st.d.next_id_

      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures |action_queue| >= |old(action_queue)| + |or|
      ensures |action_queue| <= |old(action_queue)| + |or| + 6 * deals_limit as int + 2
      ensures unchanged (`deferred_queue)
      /* PQI.POST.1 */
      ensures forall ord :: ord in r.buys_ ==> ord.original_amount >= ord.amount
      ensures forall ord :: ord in r.sells_ ==> ord.original_amount >= ord.amount
      /* MTE03 */
      ensures forall ord :: ord in po ==> is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in r.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in r.sells_ ==> ord.id < st.d.next_id_
    {
      var dlr := new dealer(this, tip3root, notify_addr, price, deals_limit as unsigned,
        tons_cfg, sells_amount, sells, buys_amount, buys, None);
      or, po, fo_buy, fo_sell := dlr.process_queue(sell_idx, buy_idx);
      return process_ret( dlr.sells_amount_, dlr.sells_, dlr.buys_amount_, dlr.buys_, dlr.ret_ ), or, po, fo_buy, fo_sell;
    }

    twostate predicate buyTip3_pre(amount:uint128, order_finish_time:uint32)
      requires message_opt.has_val()
      reads `message_opt, `st, st`d, `unix_blocktime
    {
      amount >= old(st.d.min_amount_) &&
        var cost := calc_cost(amount, old(st.d.price_));
        cost.has_val() &&
          var value_gr := TON_CPP_int_value_get();
          value_gr > buyTip3MinValue(cost.val) &&
          is_active_time(order_finish_time)
    }

    twostate predicate buyTip3_comp(amount:uint128, order_finish_time:uint32)
    {
      /* We still do not know what should be in the queues,
         because of the following found issues:
         https://github.com/tonlabs/flex/issues/22
         https://github.com/tonlabs/flex/issues/23
         https://github.com/tonlabs/flex/issues/25
       */
      true
    }

    twostate predicate buyTip3_act(amount:uint128, order_finish_time:uint32)
    {
      true
    }

    function method onTip3LendOwnershipMinValue(): uint128
      reads st, `st
    {
      addL([st.d.tons_cfg_.process_queue,
        st.d.tons_cfg_.transfer_tip3,
        st.d.tons_cfg_.send_notify,
        st.d.tons_cfg_.return_ownership,
        st.d.tons_cfg_.order_answer])
    }

    method verify_tip3_addr(tip3_wallet: address, wallet_pubkey: uint256,
      internal_owner: uint256) returns (r:bool)
    {
      var expected_address := expected_wallet_address(wallet_pubkey, internal_owner);
      // originally, here you see the following:
      // return std::get<addr_std>(tip3_wallet()).address == expected_address;
      // the .address part is very unfortunate; it is used to extract the
      // ID field of the address. It seems, there is some mess with naming.
      return tip3_wallet.id == expected_address;
    }

    method expected_wallet_address(wallet_pubkey:uint256, internal_owner:uint256)
      returns (r:uint256)
    {
      var owner_addr:option<address>;
      if (internal_owner != 0) {
        owner_addr :=
          Value(address.make_std(st.d.workchain_id_, internal_owner));
      }
      var _, addr_id := TTW.prepare_internal_wallet_state_init_and_addr(
        st.d.tip3cfg_.name,
        st.d.tip3cfg_.symbol,
        st.d.tip3cfg_.decimals,
        st.d.tip3cfg_.root_public_key,
        wallet_pubkey,
        st.d.tip3cfg_.root_address,
        owner_addr,
        st.d.tip3_code,
        st.d.workchain_id_
      ); // .second == addr_id
      return addr_id;
    }


    // [[internal, noaccept, answer_id]]
    method {:fuel addL, 5} onTip3LendOwnership(
      answer_addr:address,
      balance:uint128,
      lend_finish_time:uint32,
      pubkey:uint256,
      internal_owner:address,
      payload:SellArgs)
      returns (
        ghost or: seq<OrderInfo>,
        ghost po: seq<OrderInfo>,
        ghost fo_buy: seq<OrderInfo>,
        ghost fo_sell: seq<OrderInfo>
      )
      requires message_opt.has_val()
      requires internal_message()
      requires forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      requires forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_

      modifies `return_address, `return_value, `action_queue,
      `deferred_queue, `act_counter, `act_last, st, `return_flag

      /* MTE03 */
      ensures forall ord :: ord in po ==> is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_
    {
      or := [];
      po := [];
      fo_buy := [];
      fo_sell := [];

      var r0, tip3_wallet, value := int_sender_and_value();
      assert (r0 == Success);
      var wallet_in := tip3_wallet;
      var ret_owner_gr:Grams := st.d.tons_cfg_.return_ownership;

      // In the source code, they use: set_int_sender
      // We use more meaningful set_int_return_address, which is
      // just a synonym.
      set_int_return_address(answer_addr);
      set_int_return_value(st.d.tons_cfg_.order_answer);

      var min_value := onTip3LendOwnershipMinValue();
      var args := parse(payload);
      var amount := args.amount;
      var err:unsigned := 0;

      var vr := verify_tip3_addr(tip3_wallet, pubkey, internal_owner.id);
      var cost := calc_cost(amount, st.d.price_);

      if (value < min_value) {
        err := ec_not_enough_tons_to_process;
      } else if (!vr) {
        err := ec_unverified_tip3_wallet;
      } else if (amount < st.d.min_amount_) {
        err := ec_not_enough_tokens_amount;
      } else if (balance < amount) {
        err := ec_too_big_tokens_amount;
      } else if (!cost.has_val()) {
        err := ec_too_big_tokens_amount;
      } else if (!is_active_time(lend_finish_time)) {
        err := ec_expired;
      }

      if (err > 0) {
        var ord_ret := on_sell_fail(err, wallet_in, amount);
        TON_CPP_return(returnOnTip3LendOwnership(ord_ret));
        return or, po, fo_buy, fo_sell;
      }

      assert (value >= onTip3LendOwnershipMinValue());

      var account:uint128 := value - st.d.tons_cfg_.process_queue -
        st.d.tons_cfg_.order_answer;
      var sell := OrderInfo(amount, amount, account, tip3_wallet,
        args.receive_wallet, lend_finish_time, st.d.next_id_);
      st.d := st.d.(sells_ := push(st.d.sells_, sell));
      st.d := st.d.(sells_amount_ := add(st.d.sells_amount_,sell.amount));
      st.d := st.d.(next_id_ := st.d.next_id_ + 1);

      // Notify an external observer about the OrderAdded event
      var m := onOrderAdded(true, st.d.tip3cfg_.root_address, st.d.price_,
        sell.amount, st.d.sells_amount_);
      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);
      // Run the Matching Engine with the new order. The older orders
      // are executed first.
      var r2, elem_idx := Queue.back_with_idx(st.d.sells_);
      assert (r2 == Success);
      assume (elem_idx.0 < MAX_UINT128_NAT);
      var pr;
      pr, or, po, fo_buy, fo_sell :=
        process_queue_impl(st.d.tip3cfg_.root_address, st.d.notify_addr_,
        st.d.price_, st.d.deals_limit_, st.d.tons_cfg_,
        elem_idx.0 as unsigned, 0, st.d.sells_amount_, st.d.sells_,
        st.d.buys_amount_, st.d.buys_);
      // or - expired orders, removed from the queues without matching.
      // po - fully or partially processed orders

      // After the matching engine does the matching, update the
      // buy and sells queues and respective amounts.
      var process_ret(sells_amount, sells, buys_amount, buys, ret) := pr;
      st.d := st.d.(sells_ := sells);
      st.d := st.d.(buys_ := buys);
      st.d := st.d.(sells_amount_ := sells_amount);
      st.d := st.d.(buys_amount_ := buys_amount);

      // If we run out of orders, destroy the contract.
      if (Queue.empty(st.d.sells_) && Queue.empty(st.d.buys_)) {
        // the message goes into deferred_queue because
        // SEND_ALL_GAS flag is set.
        suicide(st.d.flex_);
      }

      if (ret.has_val()) {
        TON_CPP_return(returnOnTip3LendOwnership(ret.val));
        return or, po, fo_buy, fo_sell;
      }

      TON_CPP_return(returnOnTip3LendOwnership(OrderRet(ok as uint32, 0, sell.amount)));
      return or, po, fo_buy, fo_sell;
    }

    twostate predicate on_sell_fail_comp()
      reads `st, `action_queue, `deferred_queue, `return_flag, st`d
    {
      /* TODO: this predicate is not finished! */
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == st.d.tons_cfg_.return_ownership &&
        m1.msg.msg.body.val.cm == returnOwnership() &&
      (if empty(st.d.sells_) && empty(st.d.buys_) then
        return_flag == SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY
       else
        return_flag == SEND_ALL_GAS
      )
    }

    // Helper function. Not a part of the Price interface.
    method on_sell_fail(ec:unsigned, wallet_in:address, amount:uint128)
      returns (or:OrderRet)
      requires message_opt.has_val()
      requires internal_message()
      modifies `action_queue, `deferred_queue, `act_counter, `act_last,
      `return_flag
      // ensures on_sell_fail_comp()
    {
      // Notify an external observer about the OrderAdded event
      method_call(wallet_in, st.d.tons_cfg_.return_ownership, returnOwnership());
      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        set_int_return_flag(SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY);
      } else {
        var r0, incoming_value := int_value();
        assert (r0 == Success);
        var rawreserve_flag_up_to := rawreserve_at_most;
        /* This is obvious, because the balance includes the int_value
           at Compute phase. */
        assume (tvm_balance() >= incoming_value);
        tvm_rawreserve(tvm_balance() - incoming_value, rawreserve_flag_up_to);
        set_int_return_flag(SEND_ALL_GAS);
      }
      assume (ec as nat < MAX_UINT32_NAT);
      return OrderRet(ec as uint32, 0, 0);
    }

    // the function generates the following messages:
    //  onOrderAdded notification
    //  All messages that are due to process_queue
    //  answer message with OrderRet value
    // May contain 1 deferred message: suicide
    method {:fuel addL, 5} buyTip3(amount:uint128, receive_tip3_wallet:address,
      order_finish_time:uint32)
      returns (
        r:Status,
        ghost or: seq<OrderInfo>,
        ghost po: seq<OrderInfo>,
        ghost fo_buy: seq<OrderInfo>,
        ghost fo_sell: seq<OrderInfo>
      )
      requires message_opt.has_val()
      requires internal_message()
      requires return_op_default_values()

      requires forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      requires forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_

      requires forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount

      modifies st`d, `action_queue, `deferred_queue, `act_counter, `return_value, `act_last
      ensures buyTip3_pre(amount, order_finish_time) <==> r == Success
      ensures r == Success ==>
      |action_queue| >= |old(action_queue)| + |or| + 2 &&
      |action_queue| <= |old(action_queue)| + |or| +
      6 * st.d.deals_limit_ as int + 4 &&
      |deferred_queue| >= |old(deferred_queue)| &&
      |deferred_queue| <= |old(deferred_queue)| + 1
      ensures r == Success ==>
       (forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount)  &&
       (forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount)
      /* MTE03 */
      ensures r == Success ==> forall ord :: ord in po ==> is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_
    {
      var sender, value_gr :- int_sender_and_value();
      :- require(amount >= st.d.min_amount_, ec_not_enough_tokens_amount);
      var cost := calc_cost(amount, st.d.price_);
      :- require(cost.has_val(), ec_too_big_tokens_amount);
      :- require(value_gr > buyTip3MinValue(cost.val),
        ec_not_enough_tons_to_process);
      :- require(is_active_time(order_finish_time), ec_expired);

      // How many coins to attach when sending the return answer message
      // with OrderRet structure.
      set_int_return_value(st.d.tons_cfg_.order_answer);

      // Insert the BuyOrder into the buy queue
      var account:uint128 :=
        value_gr - st.d.tons_cfg_.process_queue - st.d.tons_cfg_.order_answer;
      var buy := OrderInfo(/* original_amount */ amount, amount, account,
        receive_tip3_wallet, sender, order_finish_time, st.d.next_id_);

      st.d := st.d.(buys_ := Queue.push(st.d.buys_, buy));
      st.d := st.d.(buys_amount_ := add(st.d.buys_amount_, buy.amount));
      st.d := st.d.(next_id_ := st.d.next_id_ + 1);

      // Notify an external observer about the OrderAdded event
      var m := onOrderAdded(false, st.d.tip3cfg_.root_address, st.d.price_,
        buy.amount, st.d.buys_amount_);
      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);
      // Run the Matching Engine with the new order. The older orders
      // are executed first.
      var elem_idx :- Queue.back_with_idx(st.d.buys_);
      assume (elem_idx.0 < MAX_UINT128_NAT);
      var pr;
      pr, or, po, fo_buy, fo_sell :=
        process_queue_impl(st.d.tip3cfg_.root_address, st.d.notify_addr_,
        st.d.price_, st.d.deals_limit_, st.d.tons_cfg_, 0,
        elem_idx.0 as unsigned, st.d.sells_amount_, st.d.sells_,
        st.d.buys_amount_, st.d.buys_);

      // After the matching engine does the matching, update the
      // buy and sells queues and respective amounts.
      var process_ret(sells_amount, sells, buys_amount, buys, ret) := pr;
      st.d := st.d.(sells_ := sells);
      st.d := st.d.(buys_ := buys);
      st.d := st.d.(sells_amount_ := sells_amount);
      st.d := st.d.(buys_amount_ := buys_amount);

      // If we run out of orders, destroy the contract.
      if (Queue.empty(st.d.sells_) && Queue.empty(st.d.buys_)) {
        // the message goes into deferred_queue because
        // SEND_ALL_GAS flag is set.
        suicide(st.d.flex_);
      }

      if (ret.has_val()) {
        TON_CPP_return(returnBuyTip3(ret.val));
        return Success, or, po, fo_buy, fo_sell;
      }

      TON_CPP_return(returnBuyTip3(OrderRet(ok as uint32, 0, buy.amount)));
      return Success, or, po, fo_buy, fo_sell;
    }


    method processQueue()
      requires message_opt.has_val()
      requires internal_message()

      requires forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      requires forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_

      modifies `return_address, `return_value, `action_queue,
      `deferred_queue, `act_counter, `act_last, st, `return_flag

      ensures forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount
      ensures forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount

      ensures forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_
    {
      if (empty(st.d.sells_) || empty(st.d.buys_)) {
        return;
      }
      var pr, or, po, fo_buy, fo_sell :=
        process_queue_impl(st.d.tip3cfg_.root_address, st.d.notify_addr_,
        st.d.price_, st.d.deals_limit_, st.d.tons_cfg_, 0, 0,
        st.d.sells_amount_, st.d.sells_, st.d.buys_amount_, st.d.buys_);

      var process_ret(sells_amount, sells, buys_amount, buys, ret) := pr;

      st.d := st.d.(sells_ := sells);
      st.d := st.d.(buys_ := buys);
      st.d := st.d.(sells_amount_ := sells_amount);
      st.d := st.d.(buys_amount_ := buys_amount);

      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        suicide(st.d.flex_);
      }
    }

    method cancel_order_impl(orders:queue<OrderInfo>, client_addr:address,
      all_amount:uint128, sell:bool, return_ownership:Grams,
      process_queue:Grams, incoming_val:Grams)
      returns (s:Status, r:(queue<OrderInfo>, uint128))
      modifies `action_queue, `deferred_queue, `act_last, `act_counter
      ensures all_amount >= r.1
    {
      var orders1 := orders;
      var all_amount1 := all_amount;
      var i := 0;
      var is_first := true;

      while (i < |orders1|)
        decreases |orders1| - i
        invariant all_amount1 <= all_amount
      {
        var it := orders1[i];
        var ord := it; // *it
        if (ord.client_addr == client_addr) {
          var minus_val := if (is_first) then process_queue else 0;
          if (sell) {
            method_call(ord.tip3_wallet, return_ownership, returnOwnership());
            minus_val := add(minus_val, return_ownership);
          }
          var plus_val :=
            add(ord.account, if (is_first) then incoming_val else 0);
          is_first := false;
          if (plus_val > minus_val) {
            var ret_val:Grams := plus_val - minus_val;
            var ret := OrderRet(ec_canceled as uint32,
              assume (ord.original_amount > ord.amount);
              ord.original_amount - ord.amount, 0);
            var m := onOrderFinished(ret, sell);
            method_call(ord.client_addr, ret_val, m);
          }

          all_amount1 :=
            assume (all_amount1 >= ord.amount);
            all_amount1 - ord.amount;
          var b;
          b, orders1 := erase(orders1, i); // orders.erase(it)
        }
        else {
          i := i + 1;
        }
      }

      return Success, (orders1, all_amount1);
    }

    method cancelSell() returns (s:Status)
      requires message_opt.has_val()
      modifies st, `action_queue, `deferred_queue, `act_last, `act_counter
    {
      var canceled_amount := st.d.sells_amount_;
      var client_addr :- int_sender();
      var value :- int_value();
      var r :-
        cancel_order_impl(st.d.sells_, client_addr,
        st.d.sells_amount_, true,
        st.d.tons_cfg_.return_ownership,
        st.d.tons_cfg_.process_queue,
        value);
      var (sells, sells_amount) := r;
      st.d := st.d.(sells_ := sells);
      st.d := st.d.(sells_amount_ := sells_amount);
      canceled_amount := canceled_amount - sells_amount;
      var m := onOrderCanceled(true, st.d.tip3cfg_.root_address,
        st.d.price_, canceled_amount, st.d.sells_amount_);

      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);

      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        suicide(st.d.flex_);
      }
      return Success;
    }

    method cancelBuy() returns (s:Status)
      requires message_opt.has_val()
      modifies st, `action_queue, `deferred_queue, `act_last, `act_counter
    {
      var canceled_amount := st.d.buys_amount_;
      var client_addr :- int_sender();
      var value :- int_value();
      var r :-
        cancel_order_impl(st.d.buys_, client_addr,
        st.d.buys_amount_, false,
        st.d.tons_cfg_.return_ownership,
        st.d.tons_cfg_.process_queue,
        value);
      var (buys, buys_amount) := r;
      st.d := st.d.(buys_ := buys);
      st.d := st.d.(buys_amount_ := buys_amount);
      canceled_amount := canceled_amount - buys_amount;
      var m := onOrderCanceled(false, st.d.tip3cfg_.root_address,
        st.d.price_, canceled_amount, st.d.buys_amount_);

      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);

      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        suicide(st.d.flex_);
      }
      return Success;
    }

    method prepare_price_state_init_and_addr(price_data:DPrice, price_code:cell)
      returns (init:StateInit, id:uint256)
    {
      var price_data_cl:cell :=
        prepare_persistent_data(/* hdr */ None, price_data);
      var price_init:StateInit := StateInit_Price(/* price_code_cl */);
      var price_init_cl:cell := build_make_cell(price_init);
      return price_init, tvm_hash(price_init_cl);
    }

    method tvm_compute_phase ...
      ensures internal_message() &&
      deployCall_message() &&
      !old(constructed) &&
      msg().body.val.ctor.Price? &&
      msg().body.val.cm.buyTip3? &&
      buyTip3_pre(msg().body.val.cm.amount,
          msg().body.val.cm.order_finish_time)
      ==>
      r == Success &&
      buyTip3_comp(msg().body.val.cm.amount,
         msg().body.val.cm.order_finish_time) //&&
    //  tvm_action_phase1_pre(action_queue, old(balance)) &&
    //  tvm_action_phase2_pre(deferred_queue)

    // method msg_dispatcher...
    //  ensures
    //  old(status) == T.Uninit &&
    //  deployCall_message() &&
    //  internal_message() &&
    //  msg().info.answer_addr == None &&
    //  msg().info.answer_id == None &&
    //  msg().body.val.ctor.Price? &&
    //  msg().body.val.cm.buyTip3? &&
    //  buyTip3_pre(msg().body.val.cm.amount, msg().body.val.cm.order_finish_time) &&
    //  !old(constructed) ==>
    //  r == Success // && buyTip3_act(msg().body.val.cm.amount, msg().body.val.c
      // m.order_finish_time)
  }

  // TODO: why not to move dealer into another module, not to
  // make a mess here. It should also improve the verification time.

  // Answer: currently, it is a bit complicated due to dependence on the
  // TONContract Price defined in the same module. If we separate the class
  // into another module, then there are some type ambiguities arise that
  // are not easily fixed.
  class dealer
  {
    const ctx_:TONContract;
    const price_: uint128; // the price level is fixed.
    const tip3root_: address;
    const notify_addr_: address;
    const deals_limit_:unsigned;
    const tons_cfg_: TonsConfig;

    var sells_amount_:uint128;
    var sells_:queue<OrderInfo>;
    var buys_amount_:uint128;
    var buys_:queue<OrderInfo>;
    var ret_:option<OrderRet>;

    constructor   (ctx:TONContract, tip3root:address, notify_addr:address,
      price:uint128, deals_limit:unsigned, tons_cfg:TonsConfig,
      sells_amount:uint128, sells:queue<OrderInfo>, buys_amount:uint128,
      buys:queue<OrderInfo>, ret:option<OrderRet>)
      ensures unchanged (ctx)
      ensures ctx_ == ctx
      ensures deals_limit_ == deals_limit
      ensures sells_ == sells
      ensures buys_ == buys
      ensures buys_amount_ == buys_amount
      ensures sells_amount_ == sells_amount
    {
      ctx_ := ctx;
      tip3root_ := tip3root;
      notify_addr_ := notify_addr;
      price_ := price;
      deals_limit_ := deals_limit;
      tons_cfg_ := tons_cfg;
      sells_amount_ := sells_amount;
      sells_ := sells;
      buys_amount_ := buys_amount;
      buys_ := buys;
      ret_ := ret;
    }

    method make_deal(sell:Ref<OrderInfo>, buy:Ref<OrderInfo>)
      returns (r:(/*sell_out_of_tons1:*/bool, /*buy_out_of_tons1:*/bool, /*deal_amount1:*/uint128))
      requires sell != buy
      /* MD.PRE.10 */
      requires ctx_.is_active_time(sell.st.order_finish_time)
      requires ctx_.is_active_time(buy.st.order_finish_time)
      /* MD.PRE.2 */
      requires sell.st.original_amount >= sell.st.amount
      requires buy.st.original_amount >= buy.st.amount

      requires buy.st.id < ctx_.st.d.next_id_
      requires sell.st.id < ctx_.st.d.next_id_

      modifies sell, buy, ctx_`action_queue, ctx_`deferred_queue,
      ctx_`act_counter, ctx_`act_last

      ensures sell != buy
      /* MD.POST.0 */
      ensures unchanged (ctx_`deferred_queue)
      /* MD.POST.1 */
      ensures var deal_amount := min(old(sell.st.amount), old(buy.st.amount));
         sell.st.amount == old(sell.st.amount) - deal_amount &&
          buy.st.amount == old(buy.st.amount) - deal_amount
      /* MD.POST.2 */
      ensures
      var deal_amount := min(old(sell.st.amount), old(buy.st.amount));
      var last_tip3_sell := old(sell.st.amount) == deal_amount;
      var cost := calc_cost(deal_amount, price_);
      assume (cost.has_val());
      var sell_costs :=
        if (!last_tip3_sell) then
          0
        else
          addL([0, tons_cfg_.transfer_tip3, tons_cfg_.send_notify]);
      var buy_costs :=
        if (!last_tip3_sell) then
          addL([cost.val, tons_cfg_.transfer_tip3, tons_cfg_.send_notify])
        else
          cost.val;
      var sell_out_of_tons := old(sell.st.account) < sell_costs;
      var buy_out_of_tons := old(buy.st.account) < buy_costs;
      if (!sell_out_of_tons && !buy_out_of_tons) then
        |ctx_.action_queue| == |old(ctx_.action_queue)| + 3
      else
        ctx_.action_queue == old(ctx_.action_queue)
      /* MD.POST.5 */
      ensures |ctx_.action_queue| >= |old(ctx_.action_queue)|
      /* MD.POST.3 */
      ensures |ctx_.action_queue| <= |old(ctx_.action_queue)| + 3
      /* MD.POST.6 */
      ensures sell.st.original_amount >= sell.st.amount
      ensures buy.st.original_amount >= buy.st.amount
      /* MD.POST.10 */
      ensures ctx_.is_active_time(sell.st.order_finish_time)
      ensures ctx_.is_active_time(buy.st.order_finish_time)

      ensures buy.st.id < ctx_.st.d.next_id_
      ensures sell.st.id < ctx_.st.d.next_id_

      /* MTE02. */
      // 1) If the deal is closed, the notification message is sent.
      // 2) If the notification message is sent, the deal is closed.
      // 3) It is the only place in the system where the notification
      //    onDealCompleted is sent
      // Hence, we have the MTE02 property:
      // "The deal notification is sent exactly once (in case of a successful deal)."
      ensures (!r.0 && !r.1) <==>
      exists m1, m2, m3 :: ctx_.action_queue == old(ctx_.action_queue) + [m1] + [m2] + [m3] &&
      m1.Action_SendMessage? &&
      m1.msg.msg.OrdinaryMessage? &&
      m1.msg.msg.body.has_val() &&
      m1.msg.msg.body.val.call? &&
      m1.msg.msg.body.val.cm.transfer_TONTokenWallet? &&
      m2.Action_SendMessage? &&
      m2.msg.msg.OrdinaryMessage? &&
      m2.msg.msg.body == None &&
      m3.Action_SendMessage? &&
      m3.msg.msg.OrdinaryMessage? &&
      m3.msg.msg.body.has_val() &&
      m3.msg.msg.body.val.call? &&
      m3.msg.msg.body.val.cm.onDealCompleted? &&
      m3.msg.msg.info.dest == notify_addr_
    {
      var deal_amount := min(sell.st.amount, buy.st.amount);
      var last_tip3_sell := sell.st.amount == deal_amount;
      sell.st := sell.st.(amount := sell.st.amount - deal_amount);
      buy.st := buy.st.(amount := buy.st.amount - deal_amount);
      var cost := calc_cost(deal_amount, price_);

      // https://github.com/tonlabs/flex/issues/20
      assume (cost.has_val());

      var sell_costs := 0 as uint128;
      var buy_costs := cost.val;

      if (last_tip3_sell) {
        // we expect no overflow here.
        sell_costs := addL([sell_costs, tons_cfg_.transfer_tip3, tons_cfg_.send_notify]);
      }
      else {
        buy_costs := addL([buy_costs, tons_cfg_.transfer_tip3, tons_cfg_.send_notify]);
      }
      var sell_out_of_tons := sell.st.account < sell_costs;
      var buy_out_of_tons := buy.st.account < buy_costs;
      if (sell_out_of_tons || buy_out_of_tons) {
        return (sell_out_of_tons, buy_out_of_tons, 0);
      }

      sell.st := sell.st.(account := sell.st.account - sell_costs);
      buy.st := buy.st.(account := buy.st.account - buy_costs);

      // Ask TONTokenWallet to perform the tokens transfer on the sellers
      // wallet.
      var m := transfer_TONTokenWallet(sell.st.tip3_wallet, buy.st.tip3_wallet,
        deal_amount, 0, false);
      ctx_.method_call(sell.st.tip3_wallet, tons_cfg_.transfer_tip3, m);

      ctx_.tvm_transfer(sell.st.client_addr, cost.val, true,
        SENDER_WANTS_TO_PAY_FEES_SEPARATELY);

      // Notify about the deal completed.
      var m1 := onDealCompleted(tip3root_, price_, deal_amount);
      ctx_.method_call(notify_addr_, tons_cfg_.send_notify, m1);
      return (false, false, deal_amount);
    }

    predicate is_active_time_pure(now:uint64, order_finish_time:uint32)
    {
      add(now as uint128, safe_delay_period as uint128) < order_finish_time as uint128
    }

    // Extract the current active order on sell or on buy.  The cur_order
    // input  is for  greater convinience  for a  caller side,  if it  is
    // present (optional contains Value),  then then function returns it,
    // together with other params.  Otherwise,  it traverses the queue of
    // orders, removing all  expired ones.  In case the  order is expired
    // and removed, the order observer (INotify) gets notified about this
    // event.  The all_amount  param is an accumulated sum  of all orders
    // amount.   It gets  decreased  in case  some order  is  found to  be
    // expired by the  amount of that expired order.   The function works
    // both for sell  and buy orders, and the direction  is controlled by
    // the 'sell' boolean.
    method extract_active_order(cur_order:option<OrderInfoWithIdx>,
      orders:queue<OrderInfo>, all_amount:uint128, sell:bool)
      returns (r:(/* cur_order */ option<OrderInfoWithIdx>,
                  /* orders */ queue<OrderInfo>,
                  /* all_amount */ uint128),
               ghost removed_orders: seq<OrderInfo>,
               ghost actions_added: seq<Action>)
      /* EAO.PRE.2 */
      // Needed to establish the EAO.POST.2
      requires cur_order.has_val() ==> Queue.len(orders) > 0
      /* EAO.PRE.18 */
      requires cur_order.has_val() ==> ctx_.is_active_time(cur_order.val.1.order_finish_time)
      /* EAO.PRE.15 */
      requires forall ord :: ord in orders ==> ord.original_amount >= ord.amount
      /* EAO.PRE.16 */
      requires cur_order.has_val() ==> cur_order.val.1.original_amount >= cur_order.val.1.amount

      requires cur_order.has_val() ==> cur_order.val.1.id < ctx_.st.d.next_id_
      requires forall ord :: ord in orders ==> ord.id < ctx_.st.d.next_id_

      modifies ctx_`action_queue, ctx_`deferred_queue, ctx_`act_counter, ctx_`act_last
      /* EAO.POST.1 */
      // This post-condition is needed to establish the fact that
      // if this function returns some non-empty cur_order, then the
      // orders queue must be non-empty and the cur_order is exactly
      // the front element of the queue.
      ensures cur_order.has_val() ==>
      r.0 == cur_order &&
      r.1 == orders &&
      r.2 == all_amount &&
      unchanged(ctx_`action_queue)
      /* EAO.POST.2 */
      ensures cur_order == None && Queue.empty(orders) ==>
      r.0 == None && r.1 == [] && r.2 == all_amount
      /* EAO.POST.3 */
      ensures Queue.len(r.1) <= Queue.len(orders)
      /* EAO.POST.5 */
      ensures unchanged (ctx_`deferred_queue)
      /* EAO.POST.8 */
      ensures cur_order == None && !Queue.empty(orders) && r.0.has_val() ==>
      var ords := r.1;
      Queue.len(ords) > 0 && r.0.val.1 == ords[0]
      /* EAO.POST.9 */
      ensures r.0 == None ==> Queue.empty(r.1)
      /* EAO.POST.11 */
      ensures |ctx_.action_queue| == |old(ctx_.action_queue)| + |removed_orders|
      /* EAO.POST.12 */
      // TODO: why not to use set-in operation instead of idx?
      ensures forall i :: 0 <= i < |removed_orders| ==>
      var act := ctx_.action_queue[|old(ctx_.action_queue)| + i];
      act.Action_SendMessage? &&
        act.msg.msg.is_msg_int() &&
        act.msg.msg.info.value == removed_orders[i].account
      /* EAO.POST.13 */
      ensures ctx_.action_queue == old(ctx_.action_queue) + actions_added
      /* EAO.POST.14 */
      ensures forall i :: 0 <= i < |actions_added| ==>
      var act := actions_added[i];
      act.Action_SendMessage? &&
        act.msg.msg.is_msg_int() &&
        act.msg.msg.info.value == removed_orders[i].account
      /* EAO.POST.15 */
      ensures forall ord :: ord in r.1 ==> ord.original_amount >= ord.amount
      /* EAO.POST.16 */
      ensures r.0.has_val() ==>
      r.0.val.1.original_amount >= r.0.val.1.amount &&
      ctx_.is_active_time(r.0.val.1.order_finish_time)

      ensures r.0.has_val() ==> r.0.val.1.id < ctx_.st.d.next_id_
      ensures forall ord :: ord in r.1 ==> ord.id < ctx_.st.d.next_id_
    {
      // We can't mutate input params variables as in TON C++, so we
      // introduce new variables with similar names.
      var cur_order1 := cur_order;
      var all_amount1 := all_amount;
      var orders1 := orders;
      ghost var removed_orders1 := [];

      if (cur_order.has_val()) {
        /* EAO.POST.1 */
        /* EAO.POST.6 : implied by precondition EAO.PRE.1 */
        return (cur_order1, orders1, all_amount1), removed_orders1, [];
      }

      // 1) All inactive orders get removed.
      // 2) all_amount value is decreased by the removed orders amount.
      //  INV: old(all_amount) == all_amount1 + sum(i, removed_orders[i]._amount)
      // 3) For each removed order, the notification message is generated
      //    and put into the ctx_.action_queue.
      // 4) Not a single deferred message is generated.

      ghost var old_removed_orders1 := removed_orders1;
      ghost var old_action_queue := old(ctx_.action_queue);
      ghost var last_ord:option<OrderInfo> := None;

      actions_added := [];
      ghost var old_actions_added := [];

      ghost var b := false;

      while ( !Queue.empty(orders1) )
      decreases |orders1|
      /* EAO.POST.2 */
      invariant Queue.empty(orders) ==>
      cur_order1 == cur_order && all_amount1 == all_amount
      /* EAO.POST.5 */
      invariant unchanged (ctx_`deferred_queue)
      invariant cur_order1 != None ==> Queue.len(orders1) > 0 &&
      cur_order1.val.1 == orders1[0] &&
      ctx_.is_active_time(cur_order1.val.1.order_finish_time)
      /* EAO.POST.12 */
      invariant
        if (b) then
          |ctx_.action_queue| == |old_action_queue| + 1 &&
          |removed_orders1| == |old_removed_orders1| + 1
        else
          |ctx_.action_queue| == |old_action_queue| &&
          |removed_orders1| == |old_removed_orders1|
      /* EAO.POST.11 */
      invariant |ctx_.action_queue| == |old(ctx_.action_queue)| + |removed_orders1|
      /* EAO.POST.12 */
      invariant
      if (b) then
        ctx_.act_last.has_val() &&
        last_ord.has_val() &&
        var act := ctx_.act_last.val;
        act.Action_SendMessage? &&
        act.msg.msg.is_msg_int() &&
        ctx_.action_queue == old_action_queue + [act] &&
        actions_added == old_actions_added + [act] &&
        act.msg.msg.info.value == last_ord.val.account &&
        removed_orders1 == old_removed_orders1 + [last_ord.val]
      else
        actions_added == old_actions_added &&
        ctx_.action_queue == old_action_queue &&
        removed_orders1 == old_removed_orders1
      /* EAO.POST.12 */
      invariant old_action_queue == old(ctx_.action_queue) + old_actions_added
      /* EAO.POST.12 */
      invariant ctx_.action_queue == old(ctx_.action_queue) + actions_added
      /* EAO.POST.12 */
      invariant |removed_orders1| == |actions_added|
      /* EAO.POST.12 */
      invariant forall a :: a in actions_added ==>
      a.Action_SendMessage? && a.msg.msg.is_msg_int()
      /* EAO.POST.12 */
      invariant forall i :: 0 <= i < |removed_orders1| ==>
      removed_orders1[i].account == actions_added[i].msg.msg.info.value
      /* EAO.POST.15 */
      invariant forall ord :: ord in orders1 ==> ord.original_amount >= ord.amount

      invariant forall ord :: ord in orders1 ==> ord.id < ctx_.st.d.next_id_
      {
        // If the order queue is non-empty, and the order at
        // the queue front is expired, then, by the end of loop iteration,
        // the removed_orders will increase by that order,
        // and the orders1 will decrease by the same order,
        // and the action_queue will increase by the message
        // with that order.
        // Otherwise, all queues stay the same.

        old_removed_orders1 := removed_orders1;
        old_action_queue := ctx_.action_queue;
        old_actions_added := actions_added;

        label L: {
          cur_order1 := Queue.front_with_idx_opt(orders1);
          var ord := cur_order1.val.1; /* .1 == .second */
          last_ord := Value(ord);
          if (!ctx_.is_active_time(ord.order_finish_time)) {
            b := true;
            removed_orders1 := Queue.push(removed_orders1, ord);
            all_amount1 :=
              assume (all_amount1 >= last_ord.val.amount);
              all_amount1 - ord.amount;

            var ret := OrderRet(ec_expired as uint32,
              ord.original_amount - ord.amount, 0);
            var m := onOrderFinished(ret, sell);
            ctx_.method_call(ord.client_addr, ord.account, m);
            actions_added := actions_added + [ctx_.act_last.val];

            assert (Queue.len(orders1) > 0);
            var r0; // this call will never fail, because
            // |orders1| > 0 at this point.
            r0, orders1 := Queue.pop(orders1);
            assert (r0 == Success);
            cur_order1 := None; // optional<T>::reset()
            break L; // continue statement is modeled this way
          }
          b := false;
          break;
        }
      } /* END WHILE */

      return (cur_order1, orders1, all_amount1), removed_orders1, actions_added;
    }

    method process_queue(sell_idx:unsigned, buy_idx:unsigned)
      returns (
        ghost or:seq<OrderInfo>, // expired orders (removed from the queue)
        ghost po:seq<OrderInfo>,  // orders processed (fully or partially) by
        // the Matching Engine.
        ghost fo_buy:seq<OrderInfo>, // finished buy orders
        ghost fo_sell:seq<OrderInfo> // finished sell orders
      )
      /* PQ.PRE.4 */
      requires forall ord :: ord in buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in sells_ ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in buys_ ==> ord.id < ctx_.st.d.next_id_
      requires forall ord :: ord in sells_ ==> ord.id < ctx_.st.d.next_id_

      modifies `buys_, `sells_, `sells_amount_, `buys_amount_, `ret_,
      ctx_`action_queue, ctx_`deferred_queue, ctx_`act_counter, ctx_`act_last
      /* PQ.POST.3 */
      ensures |ctx_.action_queue| >= |old(ctx_.action_queue)| + |or|
      /* PQ.POST.1 */
      ensures |ctx_.action_queue| <= |old(ctx_.action_queue)| +
      |or| + 6 * deals_limit_ as int + 2
      /* PQ.POST.2 */
      ensures unchanged (ctx_`deferred_queue)
      /* PQ.POST.4 */
      ensures forall ord :: ord in buys_ ==> ord.original_amount >= ord.amount
      ensures forall ord :: ord in sells_ ==> ord.original_amount >= ord.amount

      /* MTE03 */
      ensures forall ord :: ord in po ==> ctx_.is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in buys_ ==> ord.id < ctx_.st.d.next_id_
      ensures forall ord :: ord in sells_ ==> ord.id < ctx_.st.d.next_id_
    {
      // https://en.cppreference.com/w/cpp/utility/optional/optional
      // By default, the constructed option does not contain value.
      var sell_opt:option<OrderInfoWithIdx> := None;
      var buy_opt:option<OrderInfoWithIdx> := None;
      var deals_count:unsigned := 0;

      ghost var removed_orders_buy:seq<OrderInfo> := [];
      ghost var removed_orders_sell:seq<OrderInfo> := [];
      ghost var processed_orders_buy:seq<OrderInfo> := [];
      ghost var processed_orders_sell:seq<OrderInfo> := [];

      // To simplify the arithmetic predicates, we assume
      // that deals_limit_ is bounded at least by this huge
      // constant. In practice, deals_limit_ would be far less
      // than 255.
      assume (deals_limit_ as nat <= MAX_UINT64_NAT);

      ghost var old_action_queue := ctx_.action_queue;

      while (true)
        decreases Queue.len(buys_) + Queue.len(sells_), sell_opt, buy_opt
        /* to establish EAO.PRE.2 */
        invariant sell_opt.has_val() ==> Queue.len(sells_) > 0
        /* to establish EAO.PRE.2 */
        invariant buy_opt.has_val() ==> Queue.len(buys_) > 0
        /* for PQ.POST.1 */
        invariant deals_count <= (deals_limit_ + 1) as unsigned
        /* for PQ.POST.1 */
        invariant deals_count <= deals_limit_ ==>
        |ctx_.action_queue| <= |old(ctx_.action_queue)| +
        |removed_orders_buy| + |removed_orders_sell| +
        6 * deals_count as int
        /* for PQ.POST.1 */
        invariant deals_count == (deals_limit_ + 1) as unsigned ==>
        |ctx_.action_queue| <= |old(ctx_.action_queue)| +
        |removed_orders_buy| + |removed_orders_sell| +
        6 * deals_limit_ as int + 1
        /* for PQ.POST.1 */
        invariant |ctx_.action_queue| <= |old(ctx_.action_queue)| +
        |removed_orders_buy| + |removed_orders_sell| +
        6 * deals_limit_ as int + 1
        /* for PQ.POST.2 */
        invariant unchanged (ctx_`deferred_queue)
        /* for PQ.POST.3 */
        invariant |ctx_.action_queue| >= |old(ctx_.action_queue)| +
        |removed_orders_buy| + |removed_orders_sell|
        invariant forall ord :: ord in buys_ ==> ord.original_amount >= ord.amount
        invariant forall ord :: ord in sells_ ==> ord.original_amount >= ord.amount
        invariant sell_opt.has_val() ==> sell_opt.val.1.original_amount >= sell_opt.val.1.amount
        invariant buy_opt.has_val() ==> buy_opt.val.1.original_amount >= buy_opt.val.1.amount
        invariant sell_opt.has_val() ==> ctx_.is_active_time(sell_opt.val.1.order_finish_time)
        invariant buy_opt.has_val() ==> ctx_.is_active_time(buy_opt.val.1.order_finish_time)
        invariant forall ord :: ord in processed_orders_sell ==> ctx_.is_active_time(ord.order_finish_time)
        invariant forall ord :: ord in processed_orders_buy ==> ctx_.is_active_time(ord.order_finish_time)

        invariant buy_opt.has_val() ==> buy_opt.val.1.id < ctx_.st.d.next_id_
        invariant sell_opt.has_val() ==> sell_opt.val.1.id < ctx_.st.d.next_id_
        invariant forall ord :: ord in buys_ ==> ord.id < ctx_.st.d.next_id_
        invariant forall ord :: ord in sells_ ==> ord.id < ctx_.st.d.next_id_
      {
        assert (sell_opt.has_val() ==> Queue.len(sells_) > 0);
        label L: // label is needed to model C++ 'continue' statement
                 // that Dafny lacks currently.
        {
          old_action_queue := ctx_.action_queue;
          var sell_tie, or1, acts1 :=
            extract_active_order(sell_opt, sells_, sells_amount_, true);

          sell_opt := sell_tie.0;
          sells_ := sell_tie.1;
          sells_amount_ := sell_tie.2;
          removed_orders_sell := removed_orders_sell + or1;

          var buy_tie, or2, acts2 :=
            extract_active_order(buy_opt, buys_, buys_amount_, false);

          buy_opt := buy_tie.0;
          buys_ := buy_tie.1;
          buys_amount_ := buy_tie.2;
          removed_orders_buy := removed_orders_buy + or2;

          if (!sell_opt.has_val() || !buy_opt.has_val()) {
            break;
          }
          // Having sell_opt and buy_opt means the queues are
          // not empty, because those values are received
          // from the front of the queue.
          assert (!Queue.empty(buys_));
          assert (!Queue.empty(sells_));

          /* MTE03. The order has a life time that is defined by the
             lending period field. The orders with expired lending
             period will not be matched.  */
          assert ( ctx_.is_active_time(sell_opt.val.1.order_finish_time) );
          assert ( ctx_.is_active_time(buy_opt.val.1.order_finish_time) );

          processed_orders_buy := processed_orders_buy + [buy_opt.val.1];
          processed_orders_sell := processed_orders_sell + [buy_opt.val.1];

          // Now we have active orders on buy and sell in our possesion.
          // By the end of this method at least one of those have to be
          // exhausted, and lead to the queue shrinking. It is important
          // because we prove WHILE-* termination this way.

          var (sell_idx_cur, sellOrderInfo) := sell_opt.val;
          var (buy_idx_cur, buyOrderInfo) := buy_opt.val;

          assert (sell_opt.val.1.id < ctx_.st.d.next_id_);
          assert (buy_opt.val.1.id < ctx_.st.d.next_id_);

          var sell:Ref<OrderInfo> := new Ref(sellOrderInfo);
          var buy:Ref<OrderInfo> := new Ref(buyOrderInfo);

          assert (sell.st.id < ctx_.st.d.next_id_);
          assert (buy.st.id < ctx_.st.d.next_id_);

          var sell_out_of_tons := false;
          var buy_out_of_tons := false;
          var deal_amount := 0;

          assume (deals_count as nat + 1 < MAX_UINT32_NAT);

          deals_count := deals_count + 1; // ++deals_count;

          if (deals_count > deals_limit_) {
            var half_process_queue := tons_cfg_.process_queue / 2;
            var safe_extra := add(tons_cfg_.return_ownership,
              tons_cfg_.order_answer);
            if (sell.st.account < add(half_process_queue, safe_extra)) {
              sell_out_of_tons := true;
            }
            if (buy.st.account < add(half_process_queue, safe_extra)) {
              buy_out_of_tons := true;
            }
            if (!sell_out_of_tons && !buy_out_of_tons) {
              sell.st :=
                sell.st.(account := sell.st.account - half_process_queue);
              buy.st :=
                buy.st.(account := buy.st.account - half_process_queue);
                // IPricePtr(tvm_myaddr())(tons_cfg_.process_queue).processQueue();
              assert (sell.st.original_amount >= sell.st.amount);
              // This is a message to oneself, to continue the processing
              // of the queue in case it is not finished at this point.
              ctx_.method_call(ctx_.tvm_myaddr(), tons_cfg_.process_queue,
                processQueue());
              if (sell_idx == sell_idx_cur) {
                ret_ :=
                  Value(OrderRet(ec_deals_limit as uint32,
                    sell.st.original_amount - sell.st.amount, sell.st.amount)
                  );
              }
              if (buy_idx == buy_idx_cur) {
                ret_ :=
                  Value(OrderRet(ec_deals_limit as uint32,
                    buy.st.original_amount - buy.st.amount, buy.st.amount)
                  );
              }
              // break;
            }
            // Break is moved out of the condition, to prevent the following issue:
            // https://github.com/tonlabs/flex/issues/22
            break;
          }

          // ==== make deal ===
          if (!sell_out_of_tons && !buy_out_of_tons) {
            var deal_tie := make_deal(sell, buy);
            // Here, the action queue may grow for another 3 messages.
            // Or stay the same.
            sell_out_of_tons := deal_tie.0;
            buy_out_of_tons := deal_tie.1;
            deal_amount := deal_tie.2;
          }

          // ==== if one of sides is out of tons ====
          if (sell_out_of_tons) {
            assert (Queue.len(sells_) > 0);
            var r0;
            r0, sells_ := Queue.pop(sells_);
            assert (r0 == Success);
            var ret := Value(OrderRet(ec_out_of_tons as uint32,
              sell.st.original_amount - sell.st.amount, 0));
            if (sell_idx == sell_idx_cur) {
              ret_ := ret;
            }

            if (sell.st.account > tons_cfg_.return_ownership) {
              sell.st :=
                sell.st.(account := sell.st.account - tons_cfg_.return_ownership);
              ctx_.method_call(sell.st.tip3_wallet,
                tons_cfg_.return_ownership,
                returnOwnership());
              ctx_.method_call(sell.st.client_addr, sell.st.account,
                onOrderFinished(ret.val, true));
              fo_sell := fo_sell + [sell.st];
            }
            sell_opt := None; // sell_opt.reset()
          }

          if (buy_out_of_tons) {
            assert (Queue.len(buys_) > 0);
            var r0;
            r0, buys_ := Queue.pop(buys_);
            assert (r0 == Success);
            var ret :=
              Value(OrderRet(ec_out_of_tons as uint32,
              buy.st.original_amount - buy.st.amount, 0));
            if (buy_idx == buy_idx_cur) {
              ret_ := ret;
            }
            ctx_.method_call(buy.st.client_addr, buy.st.account,
              onOrderFinished(ret.val, false));
            fo_buy := fo_buy + [buy.st];
            buy_opt := None;
          }

          if (sell_out_of_tons || buy_out_of_tons) {
            break L; // continue;
          }

          sell_opt := Value(sell_opt.val.(1 := sell.st));
          buy_opt := Value(buy_opt.val.(1 := buy.st));

          sells_amount_ :=
            assume (sells_amount_ >= deal_amount);
            sells_amount_ - deal_amount;
          buys_amount_ :=
            assume (buys_amount_ >= deal_amount);
            buys_amount_ - deal_amount;

          // ==== if one of sides is out of tokens amount ====
          if (sell.st.amount == 0) {
            assert (Queue.len(sells_) > 0);
            var r0;
            r0, sells_ := Queue.pop(sells_);
            assert (r0 == Success);
            var ret := Value(OrderRet(ok as uint32, sell.st.original_amount, 0));
            if (sell_idx == sell_idx_cur) {
              ret_ := ret;
            }
            ctx_.method_call(sell.st.client_addr, sell.st.account,
              onOrderFinished(ret.val, true));
            sell_opt := None;
            fo_sell := fo_sell + [sell.st];
          }

          if (buy.st.amount == 0) {
            assert (Queue.len(buys_) > 0);
            var r0;
            r0, buys_ := Queue.pop(buys_);
            assert (r0 == Success);
            var ret := Value(OrderRet(ok as uint32, buy.st.original_amount, 0));
            if (buy_idx == buy_idx_cur) {
              ret_ := ret;
            }
            ctx_.method_call(buy.st.client_addr, buy.st.account,
              onOrderFinished(ret.val, false));
            buy_opt := None;
            fo_buy := fo_buy + [buy.st];
          }
        }
      } /* END WHILE */

      //assert (|ctx_.action_queue| <= |old(ctx_.action_queue)| +
      //|removed_orders_buy| + |removed_orders_sell| +
      //6 * deals_limit_ as int + 2); // TODO: why + 2 ?

      if (sell_opt.has_val() && sell_opt.val.1.amount != 0) {
        // If the last sell order is not fully processed, modify its amount
        var sell := sell_opt.val.1; // ->second
        assert (Queue.len(sells_) > 0);
        var r0;
        r0, sells_ := Queue.change_front(sells_, sell);
        assert (r0 == Success);
        if (sell_idx == sell_opt.val.0) {
          ret_ := Value(OrderRet(ok as uint32,
            sell.original_amount - sell.amount, sell.amount));
        }
      }

      if (buy_opt.has_val() && buy_opt.val.1.amount != 0) {
        // If the last buy order is not fully processed, modify its amount
        var buy := buy_opt.val.1;
        assert (Queue.len(buys_) > 0);
        var r0;
        r0, buys_ := Queue.change_front(buys_, buy);
        assert (r0 == Success);
        if (buy_idx == buy_opt.val.0) {
          ret_ := Value(OrderRet(ok as uint32,
            buy.original_amount - buy.amount, buy.amount));
        }
      }
      // Number of removed expired orders. This is needed to estimate
      // the upper bound on number of generated messages.
      or := removed_orders_buy + removed_orders_sell;
      po := processed_orders_buy + processed_orders_sell;
      return or, po, fo_buy, fo_sell;
    }
  }
}
