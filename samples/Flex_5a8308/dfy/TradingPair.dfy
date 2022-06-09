include "../../../src/TONContract.dfy"

include "FlexTypes.dfy"

module TradingPairModule refines TONModule
{
  import opened T = FlexTypes

  class ContractStateVariables ...
  {
    var flex_addr_: address;
    var tip3_root_: address;
    var min_amount_: uint128;

    constructor()
    {
      min_amount_ := 0;
      flex_addr_ := address.Default();
      tip3_root_ := address.Default();
    }

    predicate initial_values()
    {
      min_amount_ == 0 &&
        flex_addr_ == address.Default() &&
        tip3_root_ == address.Default()
    }
  }

  class TONContract ...
  {
    const error_code_not_enough_tons:uint := 101;
    const error_code_double_deploy:uint := 102;
    const error_code_zero_min_amount:uint := 103;

    // /TON-Compiler/llvm/projects/ton-compiler/cpp-sdk/tvm/schema/basics.hpp:491:
    predicate constructor_post ...
    {
      st.initial_values()
    }
    
    method execute_constructor() returns (r:Status)
      ensures action_queue == []
      ensures deferred_queue == []
      ensures msg().body.val.ctor.TradingPair? <==> r == Success
      ensures unchanged (st)
    {
      if (msg().body.val.ctor.TradingPair?) {
        return Success;
      }
      return Failure(UnknownFunctionId);
    }

    method execute_ctor_method() returns (r:Status)
      ensures msg().body.val.cm.onDeploy? &&
      onDeploy_pre(
        old(st.min_amount_),
        msg().body.val.cm.min_amount,
        msg().body.val.cm.deploy_value) ==>
        r == Success && onDeploy_comp(msg().body.val.cm.deploy_value)
    {
      r := Failure(UnknownFunctionId);
      // the match should be exhaustive.
      var m := msg().body.val.cm;
      match m {
        case onDeploy(min_amount, deploy_value) =>
          :- onDeploy(min_amount, deploy_value);
        case _ =>
          return Failure(UnknownFunctionId);
      }
      return Success;
    }

    twostate predicate onDeploy_pre(st_min_amount_:uint128, min_amount: uint128, deploy_value:uint128)
      reads `message_opt
    {
      internal_message() &&
        TON_CPP_int_value_get() > deploy_value as Grams &&
        st_min_amount_ == 0 &&
        min_amount > 0
    }

    twostate predicate onDeploy_comp(deploy_value:uint128)
      reads `action_queue, `return_flag, `message_opt,
      `deferred_queue, `return_value, `return_address
    {
      exists m1,m2 :: action_queue == old(action_queue) + [m1] &&
        m1.Action_RawReserve? &&
        m1.value == deploy_value as Grams &&
        m1.flags == rawreserve_at_most &&
        deferred_queue == old(deferred_queue) + [m2] &&
        m2.Action_SendMessage? &&
        m2.msg.is_int_msgfl() &&
        m2.msg.flags == SENDMSG_ALL_BALANCE &&
        m2.msg.msg.is_msg_return() &&
        m2.msg.msg.info.src == address_this &&
        m2.msg.msg.info.dest == return_address &&
        m2.msg.msg.info.value == return_value &&
        unchanged (`return_address)
    }

    twostate predicate onDeploy_act(deploy_value:uint128)
      reads `int_msg_queue, `message_opt, `g_action_balance, `g_action_queue
    {
      |g_action_queue| == 1 &&
        g_action_queue[0].Action_RawReserve? &&
        var total := total_action_fee_value(g_action_queue, g_action_balance);
        total.has_val() &&
        total.val == action_fee_value(g_action_queue[0], g_action_balance) &&
        action_fee_value(g_action_queue[0], g_action_balance) ==
        min(deploy_value as Grams, g_action_balance) &&
        message_opt.has_val() &&
        message_opt.val.is_msg_int() &&
        |int_msg_queue| == 1 &&
        var a := int_msg_queue[0];
        a.msg.msg.is_msg_return() &&
        a.msg.msg.info.dest == msg().info.src &&
        a.msg.msg.info.src == address_this &&
        a.msg.msg.info.value == g_action_balance - total.val
    }

    // bool_t onDeploy(uint128 min_amount, uint128 deploy_value)
    method onDeploy(min_amount: uint128, deploy_value: uint128) returns (r: Status)
      requires message_opt.has_val()
      requires deployCall_message()
      modifies st, `action_queue, `return_flag, `deferred_queue, `act_counter,
      `act_last
      ensures onDeploy_pre(old(st.min_amount_), min_amount, deploy_value) ==>
        r == Success && onDeploy_comp(deploy_value)
      ensures !onDeploy_pre(old(st.min_amount_), min_amount, deploy_value) ==> r != Success
    {
      :- require(TON_CPP_int_value_get() > deploy_value as Grams,
        error_code_not_enough_tons);
      :- require(st.min_amount_ == 0, error_code_double_deploy);
      :- require(min_amount > 0, error_code_zero_min_amount);
      st.min_amount_ := min_amount;
      tvm_rawreserve(deploy_value, rawreserve_at_most);
      TON_CPP_set_int_return_flag(SEND_ALL_GAS);
      TON_CPP_return(returnOnDeploy(true));
      return Success;
    }

    method tvm_compute_phase ...
      ensures internal_message() &&
      deployCall_message() &&
      msg().info.answer_addr == None &&
      msg().info.answer_id == None &&
      msg().body.val.ctor.TradingPair? &&
      msg().body.val.cm.onDeploy? && // TODO: remove args
      onDeploy_pre(old(st.min_amount_),
        msg().body.val.cm.min_amount,
        msg().body.val.cm.deploy_value) &&
      !old(constructed) ==>
      r == Success &&
      onDeploy_comp(msg().body.val.cm.deploy_value) &&
      tvm_action_phase1_pre(action_queue, old(balance)) &&
      tvm_action_phase2_pre(deferred_queue) &&
      unchanged (`return_address)

    method msg_dispatcher...
      ensures
      old(status) == T.Uninit &&
      deployCall_message() &&
      internal_message() &&
      msg().info.answer_addr == None &&
      msg().info.answer_id == None &&
      msg().body.val.ctor.TradingPair? &&
      msg().body.val.cm.onDeploy? &&
      onDeploy_pre(old(st.min_amount_), msg().body.val.cm.min_amount, msg().body.val.cm.deploy_value) &&
      !old(constructed) ==>
      r == Success && onDeploy_act(msg().body.val.cm.deploy_value)

    method backup_state()
    {
      tmp_st.flex_addr_ := st.flex_addr_;
      tmp_st.tip3_root_ := st.tip3_root_;
      tmp_st.min_amount_ := st.min_amount_;
    }

    method rollback_state()
    {
      st.flex_addr_ := tmp_st.flex_addr_;
      st.tip3_root_ := tmp_st.tip3_root_;
      st.min_amount_ := tmp_st.min_amount_;
    }
  }
}
