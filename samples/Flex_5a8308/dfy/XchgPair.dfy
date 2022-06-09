include "../../../src/TONContract.dfy"

include "FlexTypes.dfy"

module XchgPairModule refines TONModule
{
  import opened T = FlexTypes

  datatype DXchgPair = DXchgPair(
    flex_addr_: address,
    tip3_major_root_: address,
    tip3_minor_root_: address,
    min_amount_: uint128
  )

  class ContractStateVariables ...
  {
    var d:DXchgPair;

    constructor()
    {
      d := DXchgPair(address.Default(), address.Default(), address.Default(), 0);
    }

    predicate initial_values()
    {
      d.min_amount_ == 0 &&
        d.flex_addr_ == address.Default() &&
        d.tip3_major_root_ == address.Default() &&
        d.tip3_minor_root_ == address.Default()
    }
  }

  class TONContract ...
  {
    const error_code_not_enough_tons:uint := 101;
    const error_code_double_deploy:uint := 102;
    const error_code_zero_min_amount:uint := 103;

    predicate constructor_post ...
    {
      st.initial_values()
    }

    method execute_constructor() returns (r:Status)
      ensures action_queue == []
      ensures deferred_queue == []
      ensures msg().body.val.ctor.XchgPair? <==> r == Success
      ensures unchanged (st)
    {
      if (msg().body.val.ctor.XchgPair?) {
        return Success;
      }
      return Failure(UnknownFunctionId);
    }

    method execute_ctor_method() returns (r:Status)
      ensures onDeploy_pre() <==> r == Success
      ensures r == Success ==> onDeploy_comp(msg().body.val.cm.deploy_value)
    {
      r := Failure(UnknownFunctionId);
      // the match should be exhaustive.
      var m := msg().body.val.cm;

      match m {
        case onDeploy(min_amount, deploy_value) =>
          if (internal_message()) {
            :- onDeploy(min_amount, deploy_value);
          }
          else {
            assert(!onDeploy_pre());
            return Failure(UnknownFunctionId);
          }
        case _ =>
          assert(!onDeploy_pre());
          return Failure(UnknownFunctionId);
      }
      return Success;
    }


    twostate predicate onDeploy_pre()
      reads `message_opt
    {
      internal_message() &&
        deployCall_message() &&
        msg().body.val.cm.onDeploy? &&
        TON_CPP_int_value_get() > msg().body.val.cm.deploy_value as Grams &&
        old(st.d.min_amount_) == 0 &&
        msg().body.val.cm.min_amount > 0
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
      requires internal_message()
      requires deployCall_message()
      requires msg().body.val.cm.onDeploy?
      requires msg().body.val.cm.deploy_value == deploy_value
      requires msg().body.val.cm.min_amount == min_amount
      modifies st`d, `action_queue, `return_flag, `deferred_queue, `act_counter,
      `act_last
      ensures onDeploy_pre() <==> r == Success
      ensures r == Success ==> onDeploy_comp(deploy_value)
    {
      :- require(TON_CPP_int_value_get() > deploy_value as Grams,
        error_code_not_enough_tons);
      :- require(st.d.min_amount_ == 0, error_code_double_deploy);
      :- require(min_amount > 0, error_code_zero_min_amount);

      assert (onDeploy_pre());
      st.d := st.d.(min_amount_ := min_amount);
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
      msg().body.val.ctor.XchgPair? &&
      onDeploy_pre() &&
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
      msg().body.val.ctor.XchgPair? &&
      onDeploy_pre() &&
      msg().info.answer_addr == None &&
      msg().info.answer_id == None &&
      !old(constructed) ==>
      r == Success && onDeploy_act(msg().body.val.cm.deploy_value)

    method backup_state()
    {
      tmp_st.d := st.d;
    }

    method rollback_state()
    {
      st.d := tmp_st.d;
    }
  }
}
