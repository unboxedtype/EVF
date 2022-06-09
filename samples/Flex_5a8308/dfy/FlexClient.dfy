include "../../../src/TONContract.dfy"

include "FlexTypes.dfy"
include "PriceCommon.dfy"
include "PriceXchgCommon.dfy"
include "Flex.dfy"
include "XchgPair.dfy"
include "TONTokenWallet.dfy"

module FlexClientModule refines TONModule
{
  import opened T = FlexTypes
  import opened PriceCommon
  import opened PriceXchgCommon
  import opened Flex
  import opened XchgPairModule
  import opened TONTokenWalletModule

  class ContractStateVariables ...
  {
    var owner_: uint256;
    var trading_pair_code_: cell;
    var xchg_pair_code_: cell;
    var workchain_id_: int8;
    var tons_cfg_: TonsConfig;
    var flex_: addr_std_compact; // addr_std_compact?
    var notify_addr_: addr_std_compact;
    var ext_wallet_code_: optcell;
    var flex_wallet_code_: optcell;
    var flex_wrapper_code_: optcell;

    constructor()
    {
      owner_ := 0;
      trading_pair_code_ := 0;
      xchg_pair_code_ := 0;
      workchain_id_ := 0;
      tons_cfg_ := TonsConfig(0, 0, 0, 0, 0, 0);
      flex_ := address.Default();
      notify_addr_ := address.Default();
      ext_wallet_code_ := None;
      flex_wallet_code_ := None;
      flex_wrapper_code_ := None;
    }

    predicate initial_values()
    {
      owner_ == 0 &&
        trading_pair_code_ == 0 &&
        xchg_pair_code_ == 0 &&
        workchain_id_ == 0 &&
        tons_cfg_ == TonsConfig(0, 0, 0, 0, 0, 0) &&
        flex_ == address.Default() &&
        notify_addr_ == address.Default() &&
        ext_wallet_code_ == None &&
        flex_wallet_code_ == None &&
        flex_wrapper_code_ == None
    }
  }

  class TONContract ...
  {
    // error_codes
    const error_code_message_sender_is_not_my_owner:uint := 100;
    const error_code_missed_ext_wallet_code:uint := 101;
    const error_code_missed_flex_wallet_code:uint := 102;
    const error_code_missed_flex_wrapper_code:uint := 103;
    const error_code_zero_owner_pubkey:uint := 104;

    twostate predicate setFlexCfg_pre()
      reads `message_opt
    {
      msg_pubkey() == old(st.owner_)
    }

    twostate predicate setFlexCfg_comp()
    {
      unchanged (`action_queue, `deferred_queue, `act_counter, `act_last)
    }

    // [[external, noaccept]]
    method setFlexCfg(tons_cfg: TonsConfig, flex:addr_std_compact, notify_addr:addr_std_compact) returns (s:Status)
      requires external_message()
      modifies st
      ensures setFlexCfg_pre() <==> s == Success
      ensures s == Success ==> setFlexCfg_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      tvm_accept();
      st.tons_cfg_ := tons_cfg;
      st.flex_ := flex;
      st.notify_addr_ := notify_addr;
      assert (msg_pubkey() == st.owner_);
      return Success;
    }

    twostate predicate setExtWalletCode_pre()
      reads `message_opt
    {
      msg_pubkey() == old(st.owner_)
    }

    twostate predicate setExtWalletCode_comp()
    {
      unchanged (`action_queue, `deferred_queue, `act_counter, `act_last)
    }

    // [[external, noaccept]]
    method setExtWalletCode(ext_wallet_code: cell) returns (s:Status)
      requires external_message()
      modifies st
      ensures setExtWalletCode_pre() <==> s == Success
      ensures s == Success ==> setExtWalletCode_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      tvm_accept();
      st.ext_wallet_code_ := Value(ext_wallet_code);
      return Success;
    }

    twostate predicate setFlexWalletCode_pre()
      reads `message_opt, `st
    {
      external_call_message() &&
      msg_pubkey() == old(st.owner_)
    }

    twostate predicate setFlexWalletCode_comp(flex_wallet_code:cell)
      reads st, `st, `action_queue, `deferred_queue
    {
      st.flex_wallet_code_ == Value(flex_wallet_code) &&
        unchanged (`action_queue) &&
        unchanged (`deferred_queue) &&
        st.owner_ == old(st.owner_)
    }

    twostate predicate setFlexWalletCode_act(flex_wallet_code:cell)
      reads st, `st, `g_action_queue, `g_deferred_queue
    {
      |g_action_queue| == 0 &&
      |g_deferred_queue| == 0 &&
      st.flex_wallet_code_ == Value(flex_wallet_code) &&
      st.owner_ == old(st.owner_)
    }

      // [[external, noaccept]]
    method setFlexWalletCode(flex_wallet_code:cell) returns (r:Status)
      requires external_call_message()
      modifies st
      ensures setFlexWalletCode_pre() <==> r == Success
      ensures r == Success ==> setFlexWalletCode_comp(flex_wallet_code)
    {
      :- require(msg_pubkey() == st.owner_,
        error_code_message_sender_is_not_my_owner);
      tvm_accept();
      st.flex_wallet_code_ := Value(flex_wallet_code);
      return Success;
    }

    twostate predicate setFlexWrapperCode_pre()
      reads `message_opt
    {
      msg_pubkey() == old(st.owner_)
    }

    twostate predicate setFlexWrapperCode_comp()
    {
      unchanged (`action_queue, `deferred_queue, `act_counter, `act_last)
    }

    method setFlexWrapperCode(flex_wrapper_code: cell) returns (s:Status)
      requires external_call_message()
      modifies st
      ensures setFlexWrapperCode_pre() <==> s == Success
      ensures s == Success ==> setFlexWrapperCode_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      tvm_accept();
      st.flex_wrapper_code_ := Value(flex_wrapper_code);
      return Success;
    }

    // The Post-Condition for deployTradingPair method, Computation phase.
    twostate predicate deployTradingPair_comp(deploy_value: Grams, deploy_min_value: Grams)
      reads `action_queue, `return_flag, `deferred_queue
    {
      exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.is_int_msgfl() && // internal message
        m1.msg.msg.info.value == deploy_value &&
        m1.msg.msg.info.bounce == true &&
        m1.msg.flags == TON_CPP_DEFAULT_MSG_FLAGS &&
        m1.msg.msg.is_msg_deployCall() &&
        m1.msg.msg.info.answer_id == None &&
        m1.msg.msg.info.answer_addr == None &&
        m1.msg.msg.info.dest ==
        calc_address_from_stateinit(m1.msg.msg.body.val.init) &&
        m1.msg.msg.info.src == address_this &&
        m1.msg.msg.body.val.init.StateInit_TradingPair? &&
        m1.msg.msg.body.val.ctor.TradingPair? &&
        m1.msg.msg.body.val.cm.onDeploy? &&
        m1.msg.msg.body.val.cm.deploy_value == deploy_min_value &&
        m2.Action_SendMessage? &&
        m2.msg.flags == TON_CPP_DEFAULT_MSG_FLAGS &&
        m2.msg.is_event_msgfl() &&
        unchanged(`deferred_queue)
    }

    // The Post-Condition for deployTradingPair method, Action phase.
    twostate predicate deployTradingPair_act(deploy_value:Grams, deploy_min_value: Grams)
      reads `int_msg_queue, `g_action_queue, `g_deferred_queue
    {
      |g_action_queue| == 2 &&
      |g_deferred_queue| == 0 &&
      var sx := set x:SendAction | x.msg.msg.is_msg_int() && x in g_action_queue;
      sx == {g_action_queue[0]} &&
      |int_msg_queue| == 1 &&
      (var msg := int_msg_queue[0].msg.msg;
        msg.is_msg_deployCall() &&
        msg.is_msg_int() &&
        msg.info.value == deploy_value &&
        msg.info.src == address_this &&
        msg.info.bounce == true &&
        msg.info.answer_id == None &&
        msg.info.answer_addr == None &&
        msg.body.val.ctor.TradingPair? &&
        msg.body.val.cm.onDeploy? &&
        msg.body.val.cm.deploy_value == deploy_min_value &&
        calc_address_from_stateinit(msg.body.val.init) == msg.info.dest)
    }

    // The Weakest Precondition for the deployTradingPair method
    twostate predicate deployTradingPair_pre()
      reads `st, `message_opt
    {
      // this is for msg_pubkey to ensure pubkey presence
      // it is not for call selector itself.
      msg_pubkey() == old(st.owner_)
    }

    // [[external, noaccept]]
    method deployTradingPair(
      tip3_root: addr_std_compact,
      deploy_min_value: uint128,
      deploy_value: uint128,
      min_trade_amount: uint128) returns (r: Status)
      // [[external]] attribute
      requires external_call_message()
      requires return_flag == TON_CPP_DEFAULT_MSG_FLAGS
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures deployTradingPair_pre() <==> r == Success
      ensures r == Success ==> deployTradingPair_comp(deploy_value, deploy_min_value)
    {
      :- require(msg_pubkey() == st.owner_,
        error_code_message_sender_is_not_my_owner);
      tvm_accept();
      var pair_data:DTradingPair := StateInit_TradingPair(st.flex_, tip3_root);
      var state_init, std_addr :=
        prepare_trading_pair_state_init_and_addr(pair_data, st.trading_pair_code_);
      var trade_pair := address.make_std(st.workchain_id_, std_addr);
      assume (calc_address_from_stateinit(state_init) == trade_pair);
      deploy_call(trade_pair, deploy_value, state_init,
        TradingPair, onDeploy(min_trade_amount, deploy_min_value),
        TON_CPP_DEFAULT_MSG_FLAGS, true, false);
      // return trade_pair.get()
      TON_CPP_return(returnDeployTradingPair(trade_pair));
      return Success;
    }

    twostate predicate deployXchgPair_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        msg_pubkey() == old(st.owner_) &&
        message_opt.val.body.val.cm.deployXchgPair?
    }

    twostate predicate deployXchgPair_comp()
      requires deployXchgPair_pre()
      reads `st, `action_queue, `message_opt
    {
      exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_deployCall() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.deploy_value &&
        m2.Action_SendMessage? &&
        m2.msg.msg.is_msg_event()
    }

    // [[external, noaccept]]
    method deployXchgPair(tip3_major_root: addr_std_compact,
      tip3_minor_root: addr_std_compact,
      deploy_min_value: uint128,
      deploy_value: uint128,
      min_trade_amount: uint128) returns (s:Status)
      // [[external]] attribute
      requires external_call_message()
      requires message_opt.val.body.val.cm.deployXchgPair?
      requires message_opt.val.body.val.cm.deploy_value == deploy_value
      requires return_flag == TON_CPP_DEFAULT_MSG_FLAGS
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures deployXchgPair_pre() <==> s == Success
      ensures s == Success ==> deployXchgPair_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);

      tvm_accept();

      var pair_data := StateInit_XchgPair(st.flex_, tip3_major_root, tip3_minor_root, 0);
      var state_init, std_addr := prepare_xchg_pair_state_init_and_addr(pair_data, st.xchg_pair_code_);
      var trade_pair := address.make_std(st.workchain_id_, std_addr);
      assume (calc_address_from_stateinit(state_init) == trade_pair);
      deploy_call(trade_pair, deploy_value, state_init,
        XchgPair, onDeploy(min_trade_amount, deploy_min_value),
        TON_CPP_DEFAULT_MSG_FLAGS, true, false);
      // return trade_pair.get()
      TON_CPP_return(returnDeployXchgPair(trade_pair));
      return Success;
    }

    twostate predicate deployPriceWithSell_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.deployPriceWithSell? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate deployPriceWithSell_comp()
      requires deployPriceWithSell_pre()
      reads `st, `message_opt, `action_queue, `deferred_queue
    {
      exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.tons_value &&
        m2.Action_SendMessage? &&
        m2.msg.msg.is_msg_event()
    }

    // [[external, noaccept]]
    method deployPriceWithSell(
      price:uint128,
      amount:uint128,
      lend_finish_time:uint32,
      min_amount:uint128,
      deals_limit:uint8,
      tons_value:uint128,
      price_code:cell,
      my_tip3_addr:addr_std_compact,
      receive_wallet:addr_std_compact,
      tip3cfg:Tip3Config
    ) returns (s:Status)
      requires external_call_message()
      requires message_opt.val.body.val.cm.deployPriceWithSell?
      requires message_opt.val.body.val.cm.tons_value == tons_value
      requires return_flag == TON_CPP_DEFAULT_MSG_FLAGS
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures deployPriceWithSell_pre() <==> s == Success
      ensures s == Success ==> deployPriceWithSell_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_.has_val(), error_code_missed_flex_wallet_code);
      tvm_accept();
      var state_init, addr, std_addr := preparePrice(price, min_amount,
        deals_limit, st.flex_wallet_code_.val, tip3cfg, price_code);
      var price_addr := addr;
      var deploy_init_cl:cell := build_make_cell(state_init);
      var sell_args := SellArgs(amount, receive_wallet);
      var payload := build_make_cell(sell_args);
      var my_tip3 := my_tip3_addr;
      method_call(my_tip3, tons_value,
        lendOwnership(tvm_myaddr(), 0, std_addr, amount, lend_finish_time,
        deploy_init_cl, payload)); // DEFAULT_MSG_FLAGS is put by default,
        // IHR disabled = flase makes no sense, since it is not implemented
        // in the Rust node.

      TON_CPP_return(returnDeployPriceWithSell(price_addr));
      return Success;
    }

    twostate predicate deployPriceWithBuy_pre()
      reads `message_opt, `st
    {
      external_call_message() &&
      msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate deployPriceWithBuy_comp(
      deploy_value:Grams,
      amount: Grams,
      tip3_addr: address,
      order_finish_time: uint32
    )
    reads `action_queue, `deferred_queue
    {
      exists m1: SendAction, m2: SendAction ::
        action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.is_int_msgfl() && // internal message
        m1.msg.flags == TON_CPP_DEFAULT_MSG_FLAGS &&
        m1.msg.msg.is_msg_deployCall() &&
        m1.msg.msg.info.value == deploy_value &&
        m1.msg.msg.info.bounce == true &&
        m1.msg.msg.info.answer_id == None &&
        m1.msg.msg.info.answer_addr == None &&
        m1.msg.msg.info.dest ==
          calc_address_from_stateinit(m1.msg.msg.body.val.init) &&
        m1.msg.msg.info.src == address_this &&
        m1.msg.msg.body.val.init.StateInit_Price? &&
        m1.msg.msg.body.val.ctor.Price? &&
        m1.msg.msg.body.val.cm.buyTip3? &&
        m1.msg.msg.body.val.cm.amount == amount &&
        m1.msg.msg.body.val.cm.my_tip3_addr == tip3_addr &&
        m1.msg.msg.body.val.cm.order_finish_time == order_finish_time &&
        m2.msg.is_event_msgfl() &&
        unchanged (`deferred_queue)
    }

    twostate predicate deployPriceWithBuy_act(deploy_value:Grams)
      reads `g_action_queue, `g_deferred_queue, `int_msg_queue
    {
      |g_action_queue| == 2 &&
      |g_deferred_queue| == 0 &&
       var sx := set x:SendAction | x.msg.msg.is_msg_int() && x in g_action_queue;
       sx == {g_action_queue[0]} &&
       |int_msg_queue| == 1 &&
       (var msg := int_msg_queue[0].msg.msg;
         msg.is_msg_deployCall() &&
          msg.is_msg_int() &&
          msg.info.value == deploy_value &&
          msg.info.src == address_this &&
          msg.info.bounce == true &&
          msg.info.answer_id == None &&
          msg.info.answer_addr == None &&
          msg.body.val.ctor.Price? &&
          msg.body.val.cm.buyTip3? &&
         calc_address_from_stateinit(msg.body.val.init) == msg.info.dest)
    }

    // [[external, noaccept]]
    method deployPriceWithBuy(
      price:uint128,
      amount:uint128,
      order_finish_time:uint32,
      min_amount:uint128,
      deals_limit:uint8,
      deploy_value:uint128,
      price_code:cell,
      my_tip3_addr:address,
      tip3cfg: Tip3Config
    )
      returns (r:Status)
      requires return_flag == TON_CPP_DEFAULT_MSG_FLAGS
      // external attribute
      requires external_call_message()
      requires msg().body.val.cm.deployPriceWithBuy?
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures deployPriceWithBuy_pre() <==> r == Success
      ensures r == Success ==> deployPriceWithBuy_comp( deploy_value, amount, my_tip3_addr, order_finish_time )
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_.has_val(), error_code_missed_flex_wallet_code);
      tvm_accept();
      var state_init, addr, std_addr :=
        preparePrice(price, min_amount, deals_limit,
        st.flex_wallet_code_.val, tip3cfg, price_code);
      var price_addr := addr;
      assert (action_queue == old(action_queue));
      assume (price_addr == calc_address_from_stateinit(state_init));
      deploy_call(price_addr, deploy_value, state_init,
        Price, buyTip3(amount, my_tip3_addr, order_finish_time));
      assert (exists m :: action_queue == old(action_queue) + [m]);
      TON_CPP_return(returnDeployPriceWithBuy(price_addr));
      assert (exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2]);
      assert (forall m1:SendAction, m2:SendAction ::  [m1] + [m2] == [m1, m2]);
      assert (exists m1:SendAction, m2:SendAction ::
        action_queue == old(action_queue) + [m1, m2] &&
        m2.msg.is_event_msgfl());
      return Success;
    }

    twostate predicate cancelSellOrder_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.cancelSellOrder? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate cancelSellOrder_comp()
      requires cancelSellOrder_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.value
    }

    // [[external, noaccept]]
    method cancelSellOrder(
      price:uint128,
      min_amount:uint128,
      deals_limit:uint8,
      value:uint128,
      price_code:cell,
      tip3cfg: Tip3Config
    )
    returns (s:Status)
      requires external_call_message()
      requires message_opt.val.body.val.cm.cancelSellOrder?
      requires message_opt.val.body.val.cm.value == value
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures cancelSellOrder_pre() <==> s == Success
      ensures s == Success ==> cancelSellOrder_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_.has_val(), error_code_missed_flex_wallet_code);
      tvm_accept();

      var state_init, addr, std_addr := preparePrice(price, min_amount,
        deals_limit, st.flex_wallet_code_.val, tip3cfg, price_code);
      var price_addr := addr;
      method_call(price_addr, value, cancelSell);
      return Success;
    }

    twostate predicate cancelBuyOrder_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.cancelBuyOrder? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate cancelBuyOrder_comp()
      requires cancelBuyOrder_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.value
    }

    // [[external, noaccept]]
    method cancelBuyOrder(
      price:uint128,
      min_amount:uint128,
      deals_limit:uint8,
      value:uint128,
      price_code:cell,
      tip3cfg: Tip3Config
    )
      returns (s:Status)
      requires external_call_message()
      requires message_opt.val.body.val.cm.cancelBuyOrder?
      requires message_opt.val.body.val.cm.value == value
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures cancelBuyOrder_pre() <==> s == Success
      ensures s == Success ==> cancelBuyOrder_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_.has_val(), error_code_missed_flex_wallet_code);
      tvm_accept();

      var state_init, addr, std_addr := preparePrice(price, min_amount,
        deals_limit, st.flex_wallet_code_.val, tip3cfg, price_code);
      var price_addr := addr;
      method_call(price_addr, value, cancelBuy);
      return Success;
    }

    twostate predicate cancelXchgOrder_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.cancelXchgOrder? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate cancelXchgOrder_comp()
      requires cancelXchgOrder_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.value
        //m1.msg.msg.body.val.cm ==
          //if message_opt.val.body.val.cm.sell then cancelSell() else cancelBuy()
    }

    // [[external, noaccept]]
    method cancelXchgOrder(
      sell: bool,
      price_num: uint128,
      price_denum: uint128,
      min_amount: uint128,
      deals_limit: uint8,
      value: uint128,
      xchg_price_code: cell,
      major_tip3cfg: Tip3Config,
      minor_tip3cfg: Tip3Config
    )
      returns (s: Status)
      requires external_call_message()
      requires message_opt.val.body.val.cm.cancelXchgOrder?
      requires message_opt.val.body.val.cm.value == value
      requires message_opt.val.body.val.cm.sell == sell
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures cancelXchgOrder_pre() <==> s == Success
      ensures s == Success ==> cancelXchgOrder_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_ != None, error_code_missed_flex_wallet_code);
      tvm_accept();

      var state_init, addr, std_addr :=
        preparePriceXchg(price_num, price_denum, min_amount, deals_limit,
        major_tip3cfg, minor_tip3cfg, xchg_price_code);

      var price_addr := addr;
      if (sell) {
        method_call(price_addr, value, cancelSell());
      }
      else {
        method_call(price_addr, value, cancelBuy());
      }
      return Success;
    }

    twostate predicate transfer_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.transfer_FlexClient? &&
        msg_pubkey() == old(st.owner_)
    }

    twostate predicate transfer_comp()
      requires transfer_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.body == None &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.value
        //m1.msg.msg.body.val.cm ==
          //if message_opt.val.body.val.cm.sell then cancelSell() else cancelBuy()
    }

    method transfer(dest: addr_std_compact, value: uint128, bounce: bool)
      returns (s:Status)
      requires external_call_message()
      requires message_opt.val.body.val.cm.transfer_FlexClient?
      requires message_opt.val.body.val.cm.value == value
      requires message_opt.val.body.val.cm.bounce == bounce
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures transfer_pre() <==> s == Success
      ensures s == Success ==> transfer_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      tvm_accept();
      tvm_transfer(dest, value, bounce);
      return Success;
    }

    twostate predicate deployPriceXchg_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.deployPriceXchg? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate deployPriceXchg_comp()
      requires deployPriceXchg_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.tons_value &&
        m2.Action_SendMessage? &&
        m2.msg.msg.is_msg_event()
    }

    // [[external, noaccept]]
    method deployPriceXchg(
      sell: bool,
      price_num: uint128,
      price_denum: uint128,
      amount: uint128,
      lend_amount: uint128,
      lend_finish_time: uint32,
      min_amount: uint128,
      deals_limit: uint8,
      tons_value: uint128,
      xchg_price_code: cell,
      my_tip3_addr: addr_std_compact,
      receive_wallet: addr_std_compact,
      major_tip3cfg: Tip3Config,
      minor_tip3cfg: Tip3Config
    )
    returns (s: Status)
    requires external_call_message()
    requires message_opt.val.body.val.cm.deployPriceXchg?
    requires message_opt.val.body.val.cm.tons_value == tons_value
    modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
    ensures deployPriceXchg_pre() <==> s == Success
    ensures s == Success ==> deployPriceXchg_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_ != None, error_code_missed_flex_wallet_code);
      tvm_accept();

      var state_init, addr, std_addr :=
        preparePriceXchg(price_num, price_denum, min_amount, deals_limit,
        major_tip3cfg, minor_tip3cfg, xchg_price_code);

      var price_addr := addr;
      var deploy_init_cl := build_make_cell(state_init);
      var payload_args := PayloadArgs(sell, amount, receive_wallet, tvm_myaddr());
      var payload := build_make_cell(payload_args);

      var my_tip3 := my_tip3_addr;
      method_call(my_tip3, tons_value, lendOwnership(tvm_myaddr(), 0, std_addr,
        lend_amount, lend_finish_time, deploy_init_cl, payload));

      TON_CPP_return(returnDeployPriceXchg(price_addr));
      return Success;
    }

    /* deployWrapperWithWallet() is skipped, because it is out of scope. */


    twostate predicate deployEmptyFlexWallet_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.deployEmptyFlexWallet? &&
        msg_pubkey() == old(st.owner_) &&
        old(st.flex_wallet_code_).has_val()
    }

    twostate predicate deployEmptyFlexWallet_comp()
      requires deployEmptyFlexWallet_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1, m2 :: action_queue == old(action_queue) + [m1] + [m2] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_deploy() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.tons_to_wallet &&
        m2.Action_SendMessage? &&
        m2.msg.msg.is_msg_event()
    }

    // [[external, noaccept]]
    method deployEmptyFlexWallet(
      pubkey: uint256,
      tons_to_wallet: uint128,
      tip3cfg: Tip3Config
    )
    returns (s: Status)
    requires external_call_message()
    requires message_opt.val.body.val.cm.deployEmptyFlexWallet?
    requires message_opt.val.body.val.cm.tons_to_wallet == tons_to_wallet
    modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
    ensures deployEmptyFlexWallet_pre() <==> s == Success
    ensures s == Success ==> deployEmptyFlexWallet_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      :- require(st.flex_wallet_code_ != None, error_code_missed_flex_wallet_code);
      tvm_accept();

      var init, hash_addr := prepare_internal_wallet_state_init_and_addr(
        tip3cfg.name, tip3cfg.symbol, tip3cfg.decimals,
        tip3cfg.root_public_key, pubkey, tip3cfg.root_address,
        Value(tvm_myaddr()), st.flex_wallet_code_.val, st.workchain_id_
      );
      var new_wallet := address.make_std(st.workchain_id_, hash_addr);
      assume (new_wallet == calc_address_from_stateinit(init));
      deploy_noop(new_wallet, tons_to_wallet, init, TONTokenWallet);

      TON_CPP_return(returnDeployEmptyFlexWallet(new_wallet));
      return Success;
    }

    twostate predicate burnWallet_pre()
      reads `st, `message_opt
    {
      external_call_message() &&
        message_opt.val.body.val.cm.burnWallet? &&
        msg_pubkey() == old(st.owner_)
    }

    twostate predicate burnWallet_comp()
      requires burnWallet_pre()
      reads `st, `message_opt, `action_queue
    {
      exists m1 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_SendMessage? &&
        m1.msg.msg.is_msg_int() &&
        m1.msg.msg.is_msg_call() &&
        m1.msg.msg.info.value == message_opt.val.body.val.cm.tons_value
    }

    method burnWallet(
      tons_value: uint128,
      out_pubkey: uint256,
      out_internal_owner: addr_std_compact,
      my_tip3_addr: addr_std_compact
    )
    returns (s:Status)
    requires external_call_message()
    requires message_opt.val.body.val.cm.burnWallet?
    requires message_opt.val.body.val.cm.tons_value == tons_value
    modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
    ensures burnWallet_pre() <==> s == Success
    ensures s == Success ==> burnWallet_comp()
    {
      :- require(msg_pubkey() == st.owner_, error_code_message_sender_is_not_my_owner);
      tvm_accept();
      var my_tip3 := my_tip3_addr;
      method_call(my_tip3, tons_value, burn(out_pubkey, out_internal_owner));
      return Success;
    }

    /* const private */
    method preparePrice(price:uint128, min_amount:uint128, deals_limit:uint8,
      tip3_code:cell, tip3cfg:Tip3Config, price_code:cell)
      returns (init:StateInit, addr1:address, id:uint256)
      ensures unchanged (`action_queue, `deferred_queue)
      ensures init.StateInit_Price?
    {
      var price_data := DPrice(
        price_ := price,
        sells_amount_ := 0,
        buys_amount_ := 0,
        flex_ := st.flex_,
        min_amount_ := min_amount,
        deals_limit_ := deals_limit,
        notify_addr_ := st.notify_addr_,
        workchain_id_ := st.workchain_id_,
        tons_cfg_ := st.tons_cfg_,
        tip3_code := tip3_code,
        tip3cfg_ := tip3cfg,
        sells_ := [],
        buys_ := [],
        next_id_ := 1
      );
      var state_init, std_addr := StateInit_Price, *;
//        prepare_price_state_init_and_addr(price_data, price_code);
      var addr := address.make_std(st.workchain_id_, std_addr);
      return state_init, addr1, std_addr;
    }

    /* const private */
    method preparePriceXchg(
      price_num:uint128,
      price_denum:uint128,
      min_amount:uint128,
      deals_limit:uint8,
      major_tip3cfg:Tip3Config,
      minor_tip3cfg: Tip3Config,
      price_code:cell
    )
    returns (init:StateInit, addr1:address, id:uint256)
    requires st.flex_wallet_code_.has_val()
    ensures unchanged (`action_queue, `deferred_queue)
    ensures init.StateInit_PriceXchg?
    {
      var price_data := DPriceXchg(
        price_ := RationalPrice(price_num, price_denum),
        sells_amount_ := 0,
        buys_amount_ := 0,
        flex_ := st.flex_,
        min_amount_ := min_amount,
        deals_limit_ := deals_limit,
        notify_addr_ := st.notify_addr_,
        workchain_id_ := st.workchain_id_,
        tons_cfg_ := st.tons_cfg_,
        tip3_code_ := st.flex_wallet_code_.val,
        major_tip3cfg_ := major_tip3cfg,
        minor_tip3cfg_ := minor_tip3cfg,
        sells_ := [],
        buys_ := [],
        next_id_ := 1
      );
      var state_init, std_addr :=
        prepare_price_xchg_state_init_and_addr(price_data, price_code);
      var addr := address.make_std(st.workchain_id_, std_addr);
      return state_init, addr, std_addr;
    }

    method prepare_price_xchg_state_init_and_addr(price_data:DPriceXchg, price_code:cell)
      returns (init:StateInit, id:uint256)
      ensures init.StateInit_PriceXchg?
    {
      var price_data_cl:cell :=
        prepare_persistent_data(/* hdr */ None, price_data);
      var price_init:StateInit := StateInit_PriceXchg(/* price_code_cl */);
      var price_init_cl:cell := build_make_cell(price_init);
      return price_init, tvm_hash(price_init_cl);
    }

    method prepare_price_state_init_and_addr(price_data: DPrice, price_code:cell)
      returns (init:StateInit, id:uint256)
    {
      var price_data_cl:cell :=
        prepare_persistent_data(/* hdr */ None, price_data);
      var price_init:StateInit := StateInit_Price(/* price_code_cl */);
      var price_init_cl:cell := build_make_cell(price_init);
      return price_init, tvm_hash(price_init_cl);
    }

    method prepare_trading_pair_state_init_and_addr(pair_data: T.StateInit, pair_code: cell)
      returns (stateInit:T.StateInit, addr_id:uint256)
      requires pair_data.StateInit_TradingPair?
      ensures stateInit == pair_data
      //ensures addr_id == calc_address_from_stateinit(stateInit)
    {
      // prepare_persistent_data
      // TON-Compiler/llvm/projects/ton-compiler/cpp-sdk/tvm/smart_switcher.hpp:265
      // pair_data carries the static data for the contract to be deployed
      var pair_data_cl := prepare_persistent_data(None, pair_data);
      var pair_init := pair_data; //StateInit(0, none(), pair_code, pair_data_cl, 0);
      var pair_init_cl := build_make_cell(pair_init);
      addr_id := tvm_hash(pair_init_cl);
      return pair_init, addr_id;
    }

    /* private */
    method prepare_xchg_pair_state_init_and_addr(pair_data: T.StateInit, pair_code: cell)
      returns (stateInit:T.StateInit, addr_id:uint256)
      requires pair_data.StateInit_XchgPair?
      ensures stateInit == pair_data
      //ensures addr_id == calc_address_from_stateinit(stateInit)
    {
      // prepare_persistent_data
      // TON-Compiler/llvm/projects/ton-compiler/cpp-sdk/tvm/smart_switcher.hpp:265
      // pair_data carries the static data for the contract to be deployed
      var pair_data_cl := prepare_persistent_data(None, pair_data);
      var pair_init := pair_data;
      var pair_init_cl := build_make_cell(pair_init);
      addr_id := tvm_hash(pair_init_cl);
      return pair_init, addr_id;
    }

    method execute_fallback...
      ensures r == Success
      ensures unchanged(`action_queue) // no ordinary actions produced
      ensures unchanged(`deferred_queue) // no deferred actions produced
    {
      return Success;
    }

    // A post condition that holds after the successful SmC constructor
    // call. Not to be confused with constructor() of the TONContract
    // which is the "system" constructor that is called before the applied
    // constructor of the SmC object.
    predicate constructor_post()
    {
      msg().body.val.ctor.FlexClient? && msg().body.val.ctor.pubkey != 0 ==>
      st.owner_ == msg().body.val.ctor.pubkey &&
      st.trading_pair_code_ == msg().body.val.ctor.trading_pair_code &&
      st.xchg_pair_code_ == msg().body.val.ctor.xchg_pair_code &&
      action_queue == []
    }

    method execute_constructor() returns (r:Status)
      ensures msg().body.val.ctor.FlexClient? && msg().body.val.ctor.pubkey != 0 ==>
      r == Success
    {
      var ctor := msg().body.val.ctor;
      if (ctor.FlexClient?) {
        var FlexClient(pubkey: uint256, trading_pair_code: cell, xchg_pair_code: cell) := ctor;
        :- require(pubkey != 0, error_code_zero_owner_pubkey);
        st.owner_ := pubkey;
        st.trading_pair_code_ := trading_pair_code;
        st.xchg_pair_code_ := xchg_pair_code;
        st.workchain_id_ := address_this.workchain_id;
        st.flex_ := address.make_std(0, 0);
        st.notify_addr_ := address.make_std(0, 0);
        return Success;
      }
      return Failure(UnknownFunctionId);
    }

    method execute_external_method() returns (r:Status)
      ensures msg().body.val.cm.deployTradingPair? &&
      deployTradingPair_pre() ==>
      r == Success && // TODO: remove params
      deployTradingPair_comp(msg().body.val.cm.deploy_value,
      msg().body.val.cm.deploy_min_value)

      ensures msg().body.val.cm.deployTradingPair? && !deployTradingPair_pre() ==>
      r != Success

      ensures r == Success && msg().body.val.cm.deployTradingPair? ==>
      deployTradingPair_comp(
        msg().body.val.cm.deploy_value,
        msg().body.val.cm.deploy_min_value)

      ensures msg().body.val.cm.deployPriceWithBuy? &&
      deployPriceWithBuy_pre() ==>
      r == Success &&
      deployPriceWithBuy_comp(
        msg().body.val.cm.deploy_value,
        msg().body.val.cm.amount,
        msg().body.val.cm.my_tip3_addr,
        msg().body.val.cm.order_finish_time)

      ensures msg().body.val.cm.setFlexWalletCode? &&
      setFlexWalletCode_pre() ==>
      r == Success &&
      setFlexWalletCode_comp(msg().body.val.cm.flex_wallet_code)

      ensures msg().body.val.cm.setFlexWalletCode? && !setFlexWalletCode_pre() ==>
      r != Success

      ensures msg().body.val.cm.deployPriceWithBuy? &&
       !deployPriceWithBuy_pre() ==>
       r != Success

      ensures r == Success && msg().body.val.cm.deployPriceWithBuy? ==>
      deployPriceWithBuy_comp( // TODO: remove params
        msg().body.val.cm.deploy_value,
        msg().body.val.cm.amount,
        msg().body.val.cm.my_tip3_addr,
        msg().body.val.cm.order_finish_time)

      ensures msg().body.val.cm.setFlexCfg? &&
      setFlexCfg_pre() ==> r == Success && setFlexCfg_comp()

      ensures msg().body.val.cm.setExtWalletCode? &&
      setExtWalletCode_pre() ==>
      r == Success && setExtWalletCode_comp()

      ensures msg().body.val.cm.setFlexWrapperCode? &&
      setFlexWrapperCode_pre() ==>
      r == Success && setFlexWrapperCode_comp()

      ensures msg().body.val.cm.deployXchgPair? &&
      deployXchgPair_pre() ==>
      r == Success && deployXchgPair_comp()

      ensures msg().body.val.cm.deployPriceWithSell? &&
      deployPriceWithSell_pre() ==>
      r == Success && deployPriceWithSell_comp()

      ensures msg().body.val.cm.cancelSellOrder? &&
      cancelSellOrder_pre() ==>
      r == Success && cancelSellOrder_comp()

      ensures msg().body.val.cm.cancelBuyOrder? &&
      cancelBuyOrder_pre() ==>
      r == Success && cancelBuyOrder_comp()

      ensures msg().body.val.cm.cancelXchgOrder? &&
      cancelXchgOrder_pre() ==>
      r == Success && cancelXchgOrder_comp()

      ensures msg().body.val.cm.transfer_FlexClient? &&
      transfer_pre() ==>
      r == Success && transfer_comp()

      ensures msg().body.val.cm.deployPriceXchg? &&
      deployPriceXchg_pre() ==>
      r == Success && deployPriceXchg_comp()

      ensures msg().body.val.cm.deployEmptyFlexWallet? &&
      deployEmptyFlexWallet_pre() ==>
      r == Success && deployEmptyFlexWallet_comp()

      ensures msg().body.val.cm.burnWallet? &&
      burnWallet_pre() ==>
      r == Success && burnWallet_comp()
    {
      var m := msg().body.val.cm;
      match m {
        case setFlexWrapperCode(wr_code) =>
          :- setFlexWrapperCode(wr_code);
        case setExtWalletCode(ext_wallet_code) =>
          :- setExtWalletCode(ext_wallet_code);
        case setFlexCfg(tons_cfg, flex, notify_addr) =>
          :- setFlexCfg(tons_cfg, flex, notify_addr);
        case setFlexWalletCode(c) =>
          :- setFlexWalletCode(c);
        case deployPriceWithBuy(p, a, o, m1, d, dv, pc, mt, t) =>
          :- deployPriceWithBuy(p, a, o, m1, d, dv, pc, mt, t);
        case deployTradingPair(tip3_root, deploy_min_value, deploy_value, min_trade_amount) =>
          :- deployTradingPair(tip3_root, deploy_min_value, deploy_value, min_trade_amount);
        case deployXchgPair(maj, min, min_val, dep_val, min_trade) =>
          :- deployXchgPair(maj, min, min_val, dep_val, min_trade);
        case deployPriceWithSell(price, amount, lend_finish_time, min_amount,
          deals_limit, tons_value, price_code, my_tip3_addr, receive_wallet,
          tip3cfg) =>
          :- deployPriceWithSell(price, amount, lend_finish_time, min_amount,
            deals_limit, tons_value, price_code, my_tip3_addr, receive_wallet,
            tip3cfg);
        case cancelSellOrder(price, min_amount, deals_limit, value, price_code,
          tip3cfg) =>
          :- cancelSellOrder(price, min_amount, deals_limit, value, price_code,
             tip3cfg);
        case cancelBuyOrder(price, min_amount, deals_limit, value, price_code,
          tip3cfg) =>
          :- cancelBuyOrder(price, min_amount, deals_limit, value, price_code,
             tip3cfg);
        case cancelXchgOrder(sell, price_num, price_denum, min_amount, deals_limit, value, xchg_price_code, major_tip3, minor_tip3) =>
          :- cancelXchgOrder(sell, price_num, price_denum, min_amount, deals_limit, value, xchg_price_code, major_tip3, minor_tip3);
        case transfer_FlexClient(dest, val, bounce) =>
          :- transfer(dest, val, bounce);
        case deployPriceXchg(sell, num, denum, amount, lend_am, lend_fin,
          min_am, deals_lim, tons_val, xchg_pc, my_tip3, recv_wal,
          maj_tip3, min_tip3) =>
          :- deployPriceXchg(sell, num, denum, amount, lend_am, lend_fin,
          min_am, deals_lim, tons_val, xchg_pc, my_tip3, recv_wal,
          maj_tip3, min_tip3);
        case deployEmptyFlexWallet(pk, tons_to_wal, tip3cfg) =>
          :- deployEmptyFlexWallet(pk, tons_to_wal, tip3cfg);
        case burnWallet(tons_val, out_pk, out_int_owner, my_tip3) =>
          :- burnWallet(tons_val, out_pk, out_int_owner, my_tip3);
        case _ => // this is a foreign method
          return Failure(UnknownFunctionId);
      }
      return Success;
    }

    method{:fuel addL,3} tvm_compute_phase ...
      ensures deploy_message() &&
      msg().body.val.ctor.FlexClient? &&
      msg().body.val.ctor.pubkey != 0 &&
      !constructed ==>
      r == Success &&
      st.owner_ == msg().body.val.ctor.pubkey &&
      st.trading_pair_code_ == msg().body.val.ctor.trading_pair_code &&
      st.xchg_pair_code_ == msg().body.val.ctor.xchg_pair_code &&
      tvm_action_phase1_pre(action_queue, balance) &&
      tvm_action_phase2_pre(deferred_queue)

      ensures external_call_message() &&
      msg().body.val.cm.deployTradingPair? &&
      deployTradingPair_pre() &&
      (var v := msg().body.val.cm.deploy_value;
       old(balance) >= addL([v, msg_send_fee, msg_send_fee])) &&
      old(constructed) ==>
      r == Success &&
      deployTradingPair_comp(
        msg().body.val.cm.deploy_value,
        msg().body.val.cm.deploy_min_value) &&
      |action_queue| == 2 &&
      // It was tricky to prove that the old(balance) is enough to
      // cover action_queue expenses. The trick was to manually show
      // that the balance is enough to cover each individual element
      // of the action queue.
      // The second insight is that of using {:fuel} attribute for
      // the addL function, to manually tune the unfolding depth.
      var tv0 := total_action_fee_value([action_queue[0]], old(balance));
      tv0.has_val() &&
      var tv1 := old(balance) - tv0.val;
      total_action_fee_value([action_queue[1]], tv1).has_val() &&
      tvm_action_phase1_pre(action_queue, old(balance)) &&
      tvm_action_phase2_pre(deferred_queue)

      ensures external_call_message() &&
      msg().body.val.cm.deployTradingPair? &&
      !deployTradingPair_pre() ==> r != Success

      ensures external_call_message() &&
      msg().body.val.cm.deployTradingPair? &&
      r == Success ==> // TODO: remove params
      deployTradingPair_comp(msg().body.val.cm.deploy_value,
      msg().body.val.cm.deploy_min_value)

      ensures message_opt.val.is_msg_return() ==>
      r == Success &&
      action_queue == [] &&
      deferred_queue == []

      ensures external_call_message() &&
      msg().body.val.cm.deployPriceWithBuy? &&
//      var deploy_value := msg().body.val.cm.deploy_value;
//      var amount := msg().body.val.cm.amount;
//      var my_tip3_addr := msg().body.val.cm.my_tip3_addr;
//      var order_finish_time := msg().body.val.cm.order_finish_time;
      old(balance) >= addL([msg().body.val.cm.deploy_value,
        msg_send_fee, msg_send_fee]) &&
      old(constructed) &&
      deployPriceWithBuy_pre() ==>
      r == Success &&
      deployPriceWithBuy_comp(msg().body.val.cm.deploy_value,
      msg().body.val.cm.amount,
      msg().body.val.cm.my_tip3_addr,
      msg().body.val.cm.order_finish_time) &&
      |action_queue| == 2 &&
      action_queue[0].msg.msg.is_msg_deployCall() &&
      action_queue[0].msg.msg.info.value == msg().body.val.cm.deploy_value &&
      var tv0 := total_action_fee_value([action_queue[0]], old(balance));
      tv0.has_val() &&
      tv0.val == add(msg().body.val.cm.deploy_value, msg_send_fee) &&
      var tv1 := old(balance) - tv0.val;
      total_action_fee_value([action_queue[1]], tv1).has_val() &&
      tvm_action_phase1_pre(action_queue, old(balance)) &&
      tvm_action_phase2_pre(deferred_queue)

      ensures external_call_message() &&
      msg().body.val.cm.setFlexWalletCode? &&
      constructed &&
      setFlexWalletCode_pre() ==>
      r == Success && setFlexWalletCode_comp(msg().body.val.cm.flex_wallet_code) &&
      tvm_action_phase1_pre(action_queue, old(balance)) &&
      tvm_action_phase2_pre(deferred_queue)

      ensures external_call_message() &&
      msg().body.val.cm.setFlexCfg? &&
      constructed &&
      setFlexCfg_pre() ==>
      r == Success && setFlexCfg_comp()

      ensures external_call_message() &&
      msg().body.val.cm.setExtWalletCode? &&
      constructed &&
      setExtWalletCode_pre() ==>
      r == Success && setExtWalletCode_comp()

      ensures external_call_message() &&
      msg().body.val.cm.setFlexWrapperCode? &&
      constructed &&
      setFlexWrapperCode_pre() ==>
      r == Success && setFlexWrapperCode_comp()

      ensures external_call_message() &&
      msg().body.val.cm.deployXchgPair? &&
      constructed &&
      deployXchgPair_pre() ==>
      r == Success && deployXchgPair_comp()

      ensures external_call_message() &&
      msg().body.val.cm.deployPriceWithSell? &&
      constructed &&
      deployPriceWithSell_pre() ==>
      r == Success && deployPriceWithSell_comp()

      ensures external_call_message() &&
      msg().body.val.cm.cancelSellOrder? &&
      constructed &&
      cancelSellOrder_pre() ==>
      r == Success && cancelSellOrder_comp()

      ensures external_call_message() &&
      msg().body.val.cm.cancelBuyOrder? &&
      constructed &&
      cancelBuyOrder_pre() ==>
      r == Success && cancelBuyOrder_comp()

      ensures external_call_message() &&
      msg().body.val.cm.cancelXchgOrder? &&
      constructed &&
      cancelXchgOrder_pre() ==>
      r == Success && cancelXchgOrder_comp()

      ensures external_call_message() &&
      msg().body.val.cm.transfer_FlexClient? &&
      constructed &&
      transfer_pre() ==>
      r == Success && transfer_comp()

      ensures external_call_message() &&
      msg().body.val.cm.deployPriceXchg? &&
      constructed &&
      deployPriceXchg_pre() ==>
      r == Success && deployPriceXchg_comp()

      ensures external_call_message() &&
      msg().body.val.cm.deployEmptyFlexWallet? &&
      constructed &&
      deployEmptyFlexWallet_pre() ==>
      r == Success && deployEmptyFlexWallet_comp()

      ensures external_call_message() &&
      msg().body.val.cm.burnWallet? &&
      constructed &&
      burnWallet_pre() ==>
      r == Success && burnWallet_comp()

    method msg_dispatcher ...
      ensures old(status) == T.Uninit &&
      msg().is_msg_deploy() &&
      msg().body.val.deploy? &&
      msg().body.val.ctor.FlexClient? &&
      msg().body.val.ctor.pubkey != 0 &&
      !old(constructed) ==>
      r == Success &&
      st.owner_ == msg().body.val.ctor.pubkey &&
      st.trading_pair_code_ == msg().body.val.ctor.trading_pair_code &&
      st.xchg_pair_code_ == msg().body.val.ctor.xchg_pair_code &&
      status == T.Active &&
      constructed

      ensures old(status) == T.Active &&
      external_call_message() &&
      msg().body.val.cm.deployTradingPair? &&
      deployTradingPair_pre() &&
      old(balance) >=
        addL([storage_fee, msg().body.val.cm.deploy_value,
              msg_send_fee, msg_send_fee]) &&
      old(constructed) ==>
      r == Success &&
      deployTradingPair_act(msg().body.val.cm.deploy_value,
      msg().body.val.cm.deploy_min_value)

      ensures old(status) == T.Active &&
      external_call_message() &&
      msg().body.val.cm.deployTradingPair? &&
      r == Success ==>
      deployTradingPair_act(msg().body.val.cm.deploy_value,
      msg().body.val.cm.deploy_min_value)

      ensures old(status) == T.Active &&
      old(balance) >= storage_fee &&
      msg().is_msg_return() ==>
      r == Success &&
      g_action_queue == [] &&
      g_deferred_queue == [] &&
      balance == add(sub(old(balance), storage_fee),
          msg().info.value)

      // ⚠ ⚠ ⚠
      // WARNING: Respect the order of the predicates.
      // Otherwise, expect surprises.
      // ⚠ ⚠ ⚠
      ensures old(status) == T.Active &&
      old(constructed) &&
      external_call_message() &&
      msg().body.val.cm.deployPriceWithBuy? &&
      old(balance) >=
        addL([storage_fee, msg().body.val.cm.deploy_value,
        msg_send_fee, msg_send_fee]) &&
      deployPriceWithBuy_pre() ==>
      r == Success &&
      deployPriceWithBuy_act(msg().body.val.cm.deploy_value)

      ensures old(status) == T.Active &&
      old(constructed) &&
      old(balance) >= storage_fee &&
      external_call_message() &&
      msg().body.val.cm.setFlexWalletCode? &&
      setFlexWalletCode_pre() ==>
      r == Success &&
      setFlexWalletCode_act(msg().body.val.cm.flex_wallet_code)


    /* st is copied into tmp_st */
    method backup_state()
    {
      tmp_st.flex_ := st.flex_;
      tmp_st.owner_ := st.owner_;
      tmp_st.trading_pair_code_ := st.trading_pair_code_;
      tmp_st.xchg_pair_code_ := st.xchg_pair_code_;
      tmp_st.workchain_id_ := st.workchain_id_;
      tmp_st.notify_addr_ := st.notify_addr_;
      tmp_st.tons_cfg_ := st.tons_cfg_;
      tmp_st.ext_wallet_code_ := st.ext_wallet_code_;
      tmp_st.flex_wallet_code_ := st.flex_wallet_code_;
      tmp_st.flex_wrapper_code_ := st.flex_wrapper_code_;
    }

    /* tmp_st is copied back into st */
    method rollback_state()
    {
      st.flex_ := tmp_st.flex_;
      st.owner_ := tmp_st.owner_;
      st.trading_pair_code_ := tmp_st.trading_pair_code_;
      st.xchg_pair_code_ := tmp_st.xchg_pair_code_;
      st.workchain_id_ := tmp_st.workchain_id_;
      st.notify_addr_ := tmp_st.notify_addr_;
      st.tons_cfg_ := tmp_st.tons_cfg_;
      st.ext_wallet_code_ := tmp_st.ext_wallet_code_;
      st.flex_wallet_code_ := tmp_st.flex_wallet_code_;
      st.flex_wrapper_code_ := tmp_st.flex_wrapper_code_;
    }
  }
}
