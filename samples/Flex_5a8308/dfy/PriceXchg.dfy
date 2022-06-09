include "../../../src/TONContract.dfy"
include "../../../src/Queue.dfy"

include "PriceXchgCommon.dfy"
include "Flex.dfy"
include "FlexTypes.dfy"
include "TONTokenWallet.dfy"

module PriceXchgModule refines TONModule
{
  import opened T = FlexTypes
  import opened PriceXchgCommon
  import opened Flex
  import opened Queue
  import opened PriceCommon

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
    sells_:queue<OrderInfoXchg>,
    buys_amount:uint128,
    buys_:queue<OrderInfoXchg>,
    ret_:option<OrderRet>
  )

  function method minor_cost(amount:uint128, price:price_t): option<uint128>
    requires price.denominator() != 0
  {
    var cost:unsigned :=
      builtin_tvm_muldirv(amount, price.numerator(), price.denominator());
    // overflow check
    if (cost > MAX_UINT128 as unsigned) then
      None
    else
      Value(cost as uint128)
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
    const price_: price_t; // the price level is fixed.
    const tip3root_sell_: address;
    const tip3root_buy_: address;
    const notify_addr_: address;
    const deals_limit_:unsigned;
    const tons_cfg_: TonsConfig;

    var sells_amount_:uint128;
    var sells_:queue<OrderInfoXchg>;
    var buys_amount_:uint128;
    var buys_:queue<OrderInfoXchg>;
    var ret_:option<OrderRet>;

    constructor(ctx:TONContract, tip3root_sell:address, tip3root_buy:address,
      notify_addr:address,
      price:price_t, deals_limit:unsigned, tons_cfg:TonsConfig,
      sells_amount:uint128, sells:queue<OrderInfoXchg>, buys_amount:uint128,
      buys:queue<OrderInfoXchg>, ret:option<OrderRet>)
      ensures unchanged (ctx)
      ensures ctx_ == ctx
      ensures deals_limit_ == deals_limit
      ensures sells_ == sells
      ensures buys_ == buys
      ensures buys_amount_ == buys_amount
      ensures sells_amount_ == sells_amount
      ensures price_ == price
    {
      ctx_ := ctx;
      tip3root_sell_ := tip3root_sell;
      tip3root_buy_ := tip3root_buy;
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

    method make_deal(sell:Ref<OrderInfoXchg>, buy:Ref<OrderInfoXchg>)
      returns (sell_out_of_tons1:bool, buy_out_of_tons1:bool, deal_amount1:uint128)
      requires sell != buy

      requires price_.denominator() != 0
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

      /* MD.POST.11 */
      ensures !sell_out_of_tons1 && !buy_out_of_tons1 ==>
       sell.st.amount == 0 || buy.st.amount == 0
    {
      var deal_amount := min(sell.st.amount, buy.st.amount);

      var last_tip3_sell := sell.st.amount == deal_amount;
      var last_tip3_buy := buy.st.amount == deal_amount;

      // we have to assure that price_.denominator() != 0
      // https://github.com/tonlabs/flex/issues/26
      assert (price_.denominator() != 0);
      var buy_payment := minor_cost(deal_amount, price_);

      if (buy_payment == None) {
        return true, true, 0;
      }

      // https://github.com/tonlabs/flex/issues/20
      assert (buy_payment.has_val());

      var sell_ton_costs:uint128 := 0 as uint128;
      var buy_ton_costs:uint128 := 0 as uint128;
      // originally, it was :
      // tons_cfg_.transfer_tip3 * 2 + tons_cfg_.send_notify;
      var transaction_costs :=
        addL([tons_cfg_.transfer_tip3, tons_cfg_.transfer_tip3,
              tons_cfg_.send_notify]);

      if (last_tip3_sell) {
        // we expect no overflow here.
        sell_ton_costs := add(sell_ton_costs, transaction_costs);
      }
      else {
        buy_ton_costs := add(buy_ton_costs, transaction_costs);
      }

      var sell_out_of_tons := sell.st.account < sell_ton_costs;
      var buy_out_of_tons := buy.st.account < buy_ton_costs;
      if (sell_out_of_tons || buy_out_of_tons) {
        return sell_out_of_tons, buy_out_of_tons, 0;
      }

      sell.st := sell.st.(amount := sell.st.amount - deal_amount);
      buy.st := buy.st.(amount := buy.st.amount - deal_amount);

      sell.st := sell.st.(account := sell.st.account - sell_ton_costs);
      buy.st := buy.st.(account := buy.st.account - buy_ton_costs);

      var m1 := transfer_TONTokenWallet(sell.st.tip3_wallet_provide, buy.st.tip3_wallet_receive,
        deal_amount, 0, last_tip3_sell);
      var m2 := transfer_TONTokenWallet(buy.st.tip3_wallet_provide, sell.st.tip3_wallet_receive,
        buy_payment.val, 0, last_tip3_buy);
      ctx_.method_call(sell.st.tip3_wallet_provide, tons_cfg_.transfer_tip3, m1);
      ctx_.method_call(buy.st.tip3_wallet_provide, tons_cfg_.transfer_tip3, m2);

      var m3 := onXchgDealCompleted(tip3root_sell_, tip3root_buy_,
        price_.numerator(), price_.denominator(), deal_amount);
      ctx_.method_call(notify_addr_, tons_cfg_.send_notify, m3);

      return false, false, deal_amount;
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
    method extract_active_order(cur_order:option<OrderInfoXchgWithIdx>,
      orders:queue<OrderInfoXchg>, all_amount:uint128, sell:bool)
      returns (r:(/* cur_order */ option<OrderInfoXchgWithIdx>,
                  /* orders */ queue<OrderInfoXchg>,
                  /* all_amount */ uint128),
               ghost removed_orders: seq<OrderInfoXchg>,
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
      ghost var last_ord:option<OrderInfoXchg> := None;
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

            var r0;
            r0, orders1 := Queue.pop(orders1);
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
        ghost or:seq<OrderInfoXchg>, // expired orders (removed from the queue)
        ghost po:seq<OrderInfoXchg>,  // orders processed (fully or partially) by
        // the Matching Engine.
        ghost fo_buy:seq<OrderInfoXchg>, // finished buy orders
        ghost fo_sell:seq<OrderInfoXchg> // finished sell orders
      )
      requires price_.denominator() != 0

      /* PQ.PRE.4 */
      requires forall ord :: ord in buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in sells_ ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in buys_ ==> ord.id < ctx_.st.d.next_id_
      requires forall ord :: ord in sells_ ==> ord.id < ctx_.st.d.next_id_

      modifies `buys_, `sells_, `sells_amount_, `buys_amount_, `ret_,
      ctx_`action_queue, ctx_`deferred_queue, ctx_`act_counter, ctx_`act_last

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
      var sell_opt:option<OrderInfoXchgWithIdx> := None;
      var buy_opt:option<OrderInfoXchgWithIdx> := None;

      var deals_count:unsigned := 0;

      ghost var removed_orders_buy:seq<OrderInfoXchg> := [];
      ghost var removed_orders_sell:seq<OrderInfoXchg> := [];
      ghost var processed_orders_buy:seq<OrderInfoXchg> := [];
      ghost var processed_orders_sell:seq<OrderInfoXchg> := [];

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
        invariant unchanged (ctx_`deferred_queue)
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

          var sell:Ref<OrderInfoXchg> := new Ref(sellOrderInfo);
          var buy:Ref<OrderInfoXchg> := new Ref(buyOrderInfo);

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
                ret_ := Value(OrderRet(ec_deals_limit as uint32,
                  sell.st.original_amount - sell.st.amount, sell.st.amount)
                );
              }
              if (buy_idx == buy_idx_cur) {
                ret_ := Value(OrderRet(ec_deals_limit as uint32,
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
            sell_out_of_tons, buy_out_of_tons, deal_amount := make_deal(sell, buy);
          }

          // ==== if one of sides is out of tons ====
          if (sell_out_of_tons) {
            assert (Queue.len(sells_) > 0);
            var r0;
            r0, sells_ := Queue.pop(sells_);
            var ret := Value(OrderRet(ec_out_of_tons as uint32,
              sell.st.original_amount - sell.st.amount, 0));
            if (sell_idx == sell_idx_cur) {
              ret_ := ret;
            }

            if (sell.st.account > tons_cfg_.return_ownership) {
              sell.st :=
                sell.st.(account := sell.st.account - tons_cfg_.return_ownership);
              ctx_.method_call(sell.st.tip3_wallet_provide,
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
            var ret :=
              Value(OrderRet(ec_out_of_tons as uint32,
              buy.st.original_amount - buy.st.amount, 0));
            if (buy_idx == buy_idx_cur) {
              ret_ := ret;
            }

            // Here, we fixed the check. Originally, it was:
            // "if (sell.account > tons_cfg)"
            // this is wrong. The error was approved by the Flex developers.
            if (buy.st.account > tons_cfg_.return_ownership) {
              ctx_.method_call(buy.st.tip3_wallet_provide,
                tons_cfg_.return_ownership, returnOwnership());
              ctx_.method_call(buy.st.client_addr, buy.st.account,
                onOrderFinished(ret.val, false));
              fo_buy := fo_buy + [buy.st];
            }
            buy_opt := None;
          }

          if (sell_out_of_tons || buy_out_of_tons) {
            assert (sell_opt == None || buy_opt == None);
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

          assert (sell.st.amount == 0 || buy.st.amount == 0);

          // ==== if one of sides is out of tokens amount ====
          if (sell.st.amount == 0) {
            assert (Queue.len(sells_) > 0);
            var r0;
            r0, sells_ := Queue.pop(sells_);
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

      if (sell_opt.has_val() && sell_opt.val.1.amount != 0) {
        // If the last sell order is not fully processed, modify its amount
        var sell := sell_opt.val.1; // ->second
        assert (Queue.len(sells_) > 0);
        var r0;
        r0, sells_ := Queue.change_front(sells_, sell);
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

  class ContractStateVariables ...
  {
    var d:DPriceXchg;

    constructor()
    {
      var defConf := Tip3Config("", "", 0, 0, address.Default());
      d := DPriceXchg(RationalPrice(0, 0), 0, 0, address.Default(), 0, 0,
        address.Default(), 0, TonsConfig(0, 0, 0, 0, 0, 0),
        0, defConf, defConf, [], [], 0);
    }

    predicate initial_values ...
    {
      d.buys_ == [] && d.sells_ == []
    }
  }

  class TONContract ...
  {
    method {:fuel addL, 5} onTip3LendOwnership(
      answer_addr:address,
      balance:uint128,
      lend_finish_time:uint32,
      pubkey:uint256,
      internal_owner:address,
      payload:PayloadArgs)
      returns (
        r:Status,
        ghost or: seq<OrderInfoXchg>,
        ghost po: seq<OrderInfoXchg>,
        ghost fo_buy: seq<OrderInfoXchg>,
        ghost fo_sell: seq<OrderInfoXchg>
      )
      requires internal_message()

      requires forall ord :: ord in st.d.buys_ ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in st.d.sells_ ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      requires forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_

      modifies `return_address, `return_value, `action_queue,
      `deferred_queue, `act_counter, `act_last, st, `return_flag

      /* MTE03 */
      ensures r == Success ==> forall ord :: ord in po ==> is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in st.d.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in st.d.sells_ ==> ord.id < st.d.next_id_
    {
      or := [];
      po := [];
      fo_buy := [];
      fo_sell := [];

      var r0, tip3_wallet, value := int_sender_and_value();
      var wallet_in := tip3_wallet;
      var ret_owner_gr:Grams := st.d.tons_cfg_.return_ownership;

      // In the source code, they use: set_int_sender
      // We use more meaningful set_int_return_address, which is
      // just a synonym.
      set_int_return_address(answer_addr);
      set_int_return_value(st.d.tons_cfg_.order_answer);

      var min_value := onTip3LendOwnershipMinValue();
      var args := parse<PayloadArgs>(payload);
      var is_sell := args.sell;
      var amount := args.amount;

      // https://github.com/tonlabs/flex/issues/26
      assume (st.d.price_.denominator() != 0);

      var minor_amount := minor_cost(amount, st.d.price_);
      var err:unsigned := 0;
      var internal_owner_std := internal_owner.id;

      var vr1 := verify_tip3_addr(st.d.major_tip3cfg_, tip3_wallet, pubkey, internal_owner_std);
      var vr2 := verify_tip3_addr(st.d.minor_tip3cfg_, tip3_wallet, pubkey, internal_owner_std);

      if (value < min_value) {
        err := ec_not_enough_tons_to_process;
      } else if ( if is_sell then !vr1 else !vr2 ) {
        err := ec_unverified_tip3_wallet;
      } else if (minor_amount == None) {
        err := ec_too_big_tokens_amount;
      } else if (amount < st.d.min_amount_) {
        err := ec_not_enough_tokens_amount;
      } else if (balance < (if is_sell then amount else minor_amount.val)) {
        err := ec_too_big_tokens_amount;
      } else if (!is_active_time(lend_finish_time)) {
        err := ec_expired;
      }

      if (err > 0) {
        var ord_ret := on_ord_fail(err, wallet_in);
        TON_CPP_return(returnOnTip3LendOwnership(ord_ret));
        return Success, or, po, fo_buy, fo_sell;
      }

      assert (value >= onTip3LendOwnershipMinValue());

      var account:uint128 := value - st.d.tons_cfg_.process_queue -
        st.d.tons_cfg_.order_answer;
      var ord := OrderInfoXchg(amount, amount, account, tip3_wallet,
        args.receive_tip3_wallet, args.client_addr, lend_finish_time,
        /* ghost */ st.d.next_id_);

      var sell_idx:unsigned := 0;
      var buy_idx:unsigned := 0;
      var notify_amount:uint128;

      if (is_sell) {
        st.d := st.d.(sells_ := Queue.push(st.d.sells_, ord));
        st.d := st.d.(sells_amount_ := add(st.d.sells_amount_,ord.amount));
        assume (Queue.len(st.d.sells_) < MAX_UINT64_NAT);
        var tmp :- Queue.back_with_idx(st.d.sells_);
        sell_idx := tmp.0 as unsigned;
        notify_amount := st.d.sells_amount_;
        st.d := st.d.(next_id_ := st.d.next_id_ + 1);
      }
      else {
        st.d := st.d.(buys_ := push(st.d.buys_, ord));
        st.d := st.d.(buys_amount_ := add(st.d.buys_amount_, ord.amount));
        assume (Queue.len(st.d.buys_) < MAX_UINT64_NAT);
        var tmp :- Queue.back_with_idx(st.d.buys_);
        buy_idx := tmp.0 as unsigned;
        notify_amount := st.d.buys_amount_;
        st.d := st.d.(next_id_ := st.d.next_id_ + 1);
      }

      // Notify an external observer about the OrderAdded event
      var m := onXchgOrderAdded(is_sell, st.d.major_tip3cfg_.root_address,
         st.d.minor_tip3cfg_.root_address, st.d.price_.numerator(),
         st.d.price_.denominator(), ord.amount, notify_amount);
      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);
      // Run the Matching Engine with the new order. The older orders
      // are executed first.

      var pr;
      pr, or, po, fo_buy, fo_sell :=
        process_queue_impl(st.d.major_tip3cfg_.root_address,
        st.d.minor_tip3cfg_.root_address,
        st.d.notify_addr_,
        st.d.price_, st.d.deals_limit_, st.d.tons_cfg_,
        sell_idx, buy_idx, st.d.sells_amount_, st.d.sells_,
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
        return Success, or, po, fo_buy, fo_sell;
      }

      TON_CPP_return(returnOnTip3LendOwnership(
        OrderRet(ok as uint32, 0, ord.amount)));

      return Success, or, po, fo_buy, fo_sell;
    }

    method processQueue() returns (s:Status)
      requires message_opt.has_val()
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
        return Success;
      }
      // https://github.com/tonlabs/flex/issues/26
      assume (st.d.price_.denominator() != 0);
      var pr, or, po, fo_buy, fo_sell :=
        process_queue_impl(st.d.major_tip3cfg_.root_address, st.d.minor_tip3cfg_.root_address,
        st.d.notify_addr_, st.d.price_, st.d.deals_limit_, st.d.tons_cfg_, 0, 0,
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
      canceled_amount := canceled_amount - st.d.sells_amount_;

      var m := onXchgOrderCanceled(true, st.d.major_tip3cfg_.root_address,
        st.d.minor_tip3cfg_.root_address,
        st.d.price_.numerator(), st.d.price_.denominator(),
        canceled_amount, st.d.sells_amount_);

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
      canceled_amount := canceled_amount - st.d.buys_amount_;

      var m := onXchgOrderCanceled(false, st.d.major_tip3cfg_.root_address,
        st.d.minor_tip3cfg_.root_address,
        st.d.price_.numerator(), st.d.price_.denominator(), canceled_amount,
        st.d.buys_amount_);
      method_call(st.d.notify_addr_, st.d.tons_cfg_.send_notify, m);

      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        suicide(st.d.flex_);
      }
      return Success;
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

    method verify_tip3_addr(cfg:Tip3Config, tip3_wallet: address, wallet_pubkey: uint256,
      internal_owner: uint256) returns (r:bool)
    {
      var expected_address := expected_wallet_address(cfg, wallet_pubkey, internal_owner);
      // originally, here you see the following:
      // return std::get<addr_std>(tip3_wallet()).address == expected_address;
      // the .address part is very unfortunate; it is used to extract the
      // ID field of the address. It seems, there is some mess with naming.
      return tip3_wallet.id == expected_address;
    }

    method expected_wallet_address(cfg:Tip3Config, wallet_pubkey:uint256, internal_owner:uint256)
      returns (r:uint256)
    {
      var owner_addr:option<address>;
      if (internal_owner != 0) {
        owner_addr :=
          Value(address.make_std(st.d.workchain_id_, internal_owner));
      }
      var _, addr_id := TTW.prepare_internal_wallet_state_init_and_addr(
        cfg.name,
        cfg.symbol,
        cfg.decimals,
        cfg.root_public_key,
        wallet_pubkey,
        cfg.root_address,
        owner_addr,
        st.d.tip3_code_,
        st.d.workchain_id_
      ); // .second == addr_id
      return addr_id;
    }

    // Helper function. Not a part of the PriceXchg interface.
    method on_ord_fail(ec:unsigned, wallet_in:address)
      returns (or:OrderRet)
      requires internal_message()
      modifies `action_queue, `deferred_queue, `act_counter, `act_last,
      `return_flag
    {
      // Notify an external observer about the OrderAdded event
      method_call(wallet_in, st.d.tons_cfg_.return_ownership, returnOwnership());
      if (empty(st.d.sells_) && empty(st.d.buys_)) {
        set_int_return_flag(SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY);
      } else {
        var r0, incoming_value := int_value();
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

    function method is_active_time(order_finish_time:uint32): bool
      reads `unix_blocktime
    {
      assume (tvm_now() as nat + safe_delay_period as nat < MAX_UINT64_NAT);
      tvm_now() + safe_delay_period < order_finish_time as uint64
    }

    method process_queue_impl(tip3root_sell:address, tip3root_buy:address,
      notify_addr:address, price:price_t, deals_limit:uint8,
      tons_cfg:TonsConfig, sell_idx:unsigned, buy_idx:unsigned,
      sells_amount:uint128, sells:queue<OrderInfoXchg>,
      buys_amount:uint128, buys:queue<OrderInfoXchg>)
      returns (
       r: process_ret,
       ghost or: seq<OrderInfoXchg>,
       ghost po: seq<OrderInfoXchg>,
       ghost fo_buy: seq<OrderInfoXchg>,
       ghost fo_sell: seq<OrderInfoXchg>
      )
      requires price.denominator() != 0
      /* PQI.PRE.1 */
      requires forall ord :: ord in buys ==> ord.original_amount >= ord.amount
      requires forall ord :: ord in sells ==> ord.original_amount >= ord.amount

      requires forall ord :: ord in buys ==> ord.id < st.d.next_id_
      requires forall ord :: ord in sells ==> ord.id < st.d.next_id_

      modifies `action_queue, `deferred_queue, `act_counter, `act_last

      ensures unchanged (`deferred_queue)
      /* PQI.POST.1 */
      ensures forall ord :: ord in r.buys_ ==> ord.original_amount >= ord.amount
      ensures forall ord :: ord in r.sells_ ==> ord.original_amount >= ord.amount
      /* MTE03 */
      ensures forall ord :: ord in po ==> is_active_time(ord.order_finish_time)

      ensures forall ord :: ord in r.buys_ ==> ord.id < st.d.next_id_
      ensures forall ord :: ord in r.sells_ ==> ord.id < st.d.next_id_
    {
      var dlr :=
        new dealer(this, tip3root_sell, tip3root_buy, notify_addr, price,
        deals_limit as unsigned,
        tons_cfg, sells_amount, sells, buys_amount, buys, None);
      or, po, fo_buy, fo_sell := dlr.process_queue(sell_idx, buy_idx);
      return process_ret( dlr.sells_amount_, dlr.sells_,
        dlr.buys_amount_, dlr.buys_, dlr.ret_ ), or, po, fo_buy, fo_sell;
    }


    method cancel_order_impl(orders:queue<OrderInfoXchg>, client_addr:address,
      all_amount:uint128, sell:bool, return_ownership:Grams,
      process_queue:Grams, incoming_val:Grams)
      returns (s:Status, r:(queue<OrderInfoXchg>, uint128))
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
          method_call(ord.tip3_wallet_provide, return_ownership, returnOwnership());
          minus_val := add(minus_val, return_ownership);

          var plus_val :=
            add(ord.account, if (is_first) then incoming_val else 0);
          is_first := false;
          if (plus_val > minus_val) {
            var ret_val:Grams := plus_val - minus_val;
            var ret := OrderRet(ec_canceled as uint32,
              assume (ord.original_amount > ord.amount);
              ord.original_amount - ord.amount, 0);
            method_call(ord.client_addr, ret_val, onOrderFinished(ret, sell));
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
      ensures msg().body.val.ctor.PriceXchg? <==> r == Success
      ensures unchanged (st)
    {
      if (msg().body.val.ctor.PriceXchg?) {
        /* constructor for Price is absent, so it always succeed. */
        return Success;
      }
      return Failure(UnknownFunctionId);
    }
  }
}
