include "BaseTypes.dfy"
include "TONTypes.dfy"
include "ErrorCodes.dfy"

abstract module TONModule
{
  import opened BaseTypes
  import opened T:TONTypes
  import opened ErrorCodes

  class ContractStateVariables
  {
    /* In the constructor, you have to initialize your state
       variables according to the rules defined for the used
       SmC programming language.
     */
    constructor()
      ensures initial_values()

    /* In this predicate you put assumptions about your variables
       after the constructor gets executed. This is used when you
       need to assert something about state variables right after
       the contract was constructed using 'new'.
     */
    predicate initial_values()
      reads this
  }

  /*******************************************************************
    Implements  most  of  the TVM-related  primitives  used  in
    verification effort.
   ******************************************************************/
  class TONContract //extends B.AccountTrait
  {
    const state_init: T.StateInit; // state_init from constructor message
    const address_this: address; // address of the contract.

    var act_counter: nat; // Monotonically increasing counter of generated actions.
    var act_last: option<Action>; // Latest generated action

    // Needed to establish global uniqueness among them.

    var constructed: bool; // after this is set to true, constructor messages are not allowed.
    // Initialized in a constructor as a hash of state init
    var tvm_pubkey_: uint256;  // pubkey of the contract
    // Initialized in a constructor
    var status: T.AccountStatus;
    // Initialized in a constructor
    var balance: Grams;  // current balance of the account.
    var due_payment: Grams;
    var exit_code: uint; // exit status. > 0 for exception

    var st: ContractStateVariables;  /* contract state variables */
    var tmp_st: ContractStateVariables; /* temporary storage for rollbacks */
    var message_opt: option<T.Message>; // current executing message
    var gas_remaining: int; /* g_r : may become negative */
    var action_queue: seq<Action>; // action list, including outbound msgs
    var deferred_queue: seq<SendAllBalanceAction>; // SENDMSG_ALL_BALANCE send message actions
    // TODO: change for msg queue, actions are redundant here.
    var int_msg_queue: seq<SendAction>; // internal messages to be delivered
    var bounced_msg_opt: option<BouncedMessage>;

    var unix_blocktime: uint64; // current unix time of the block
    // on each msg_dispatcher call, the following invariant must hold:
    // old_unix_blocktime <= unix_blocktime

    /* return operator params. */
    var return_value: Grams; /* the value attached to the return message */
    var return_flag: MsgFlags; /* return message get sent with this flag */
    var return_address: address; // where to send the answer
    var return_func_id_opt: option<T.ContractCallbackMethod>; // what function should be invoked with the answer message

    predicate return_op_default_values()
      reads `return_value, `return_flag, `return_address, `return_func_id_opt, `message_opt
    {
      return_value == 0 &&
        return_flag == TON_CPP_DEFAULT_MSG_FLAGS &&
        return_address == (
          if message_opt.has_val() then
            if message_opt.val.is_msg_int() then
              if message_opt.val.info.answer_addr.has_val() then
                message_opt.val.info.answer_addr.val
              else
                message_opt.val.info.src
            else
              address.Default()
          else
            address.Default()
        ) &&
        return_func_id_opt == (
            if message_opt.has_val() then
              if message_opt.val.is_msg_int() then
                message_opt.val.info.answer_id
              else
                None
            else
              None
        )
    }

    predicate action_id_monotonic(action_queue:seq<Action>, act_counter:nat)
    {
      true
      //a :: a in action_queue ==> a.id <= act_counter
    }

    predicate action_id_strict(action_queue:seq<Action>)
    {
      true
      //forall i:nat, j:nat :: |action_queue| > max(i,j) && i != j ==>
      //  action_queue[i].id != action_queue[j].id
    }

    predicate unique_actions(action_queue:seq<Action>, act_counter:nat)
    {
      action_id_monotonic(action_queue, act_counter) &&
        action_id_strict(action_queue)
    }

    /* A copy of the action queue taken before the Action phase */
    ghost var g_action_queue: seq<T.Action>;
    /* Balance before the Action phase */
    ghost var g_action_balance: Grams;
    /* A copy of the deferred queue taken before the Action phase */
    ghost var g_deferred_queue: seq<T.SendAllBalanceAction>;

    predicate Valid()
      reads `st, `tmp_st
    {
      st != tmp_st
    }

    constructor(st_init: T.StateInit, addr: address, bal: Grams)
      requires addr == T.calc_address_from_stateinit(st_init)
      //modifies blk
      ensures address_this == T.calc_address_from_stateinit(state_init)
      ensures balance == bal && status == T.Uninit &&
      state_init == st_init
      ensures action_queue == [] && int_msg_queue == [] && exit_code == success
      ensures g_action_queue == []
      ensures g_deferred_queue == []
      ensures constructed == false && deferred_queue == []
      ensures st.initial_values()
      ensures bounced_msg_opt == None
      ensures act_counter == 0
      ensures act_last == None
      ensures Valid() && fresh({st, tmp_st})
      ensures unique_actions(action_queue, act_counter)
      ensures return_op_default_values()
    {
      state_init := st_init; // const
      address_this := addr;  // const
      balance := bal;
      status := T.Uninit;
      action_queue := [];
      g_action_queue := [];
      g_deferred_queue := [];
      int_msg_queue := [];
      deferred_queue := [];
      exit_code := success;
      message_opt := None;
      bounced_msg_opt := None;
      unix_blocktime := *; // havoc; we do not know its value
      constructed := false; // constructor was not called yet.
      act_counter := 0;
      act_last := None;

      return_flag := TON_CPP_DEFAULT_MSG_FLAGS;
      return_value := 0;
      return_func_id_opt := None;
      return_address := address.Default(); // 0

      st := new ContractStateVariables();
      tmp_st := new ContractStateVariables();
      new; // mutating calls in constructor are allowed only
      // after 'new' operator.

      // TODO: maybe add reference to itself into the external blockchain
      // observer.
      //var tc:TONContract := this;
      //blk.add_account(address_this, tc);
    }

    /* st is copied into tmp_st */
    method backup_state()
      requires Valid()
      requires !constructed ==> st.initial_values()
      modifies tmp_st
      ensures Valid()
      ensures unchanged (this)
      ensures !constructed ==> tmp_st.initial_values()

    /* tmp_st is copied back into st */
    method rollback_state()
      requires Valid()
      requires !constructed ==> tmp_st.initial_values()
      modifies st
      ensures Valid()
      ensures unchanged (this)
      ensures !constructed ==> st.initial_values()

    /* Handful wrappers for message type testing. */
    predicate method external_message()
      reads `message_opt
    {
      message_opt.has_val() &&
        message_opt.val.is_msg_ext()
    }

    predicate method internal_message()
      reads `message_opt
    {
      message_opt.has_val() &&
        message_opt.val.is_msg_int()
    }

    predicate method call_message()
      reads `message_opt
    {
      message_opt.has_val() &&
        message_opt.val.is_msg_call()
    }

    predicate method deploy_message()
      reads `message_opt
    {
      message_opt.has_val() &&
        message_opt.val.is_msg_deploy()
    }

    predicate method deployCall_message()
      reads `message_opt
    {
      message_opt.has_val() &&
        message_opt.val.is_msg_deployCall()
    }

    predicate method external_call_message()
      reads `message_opt
    {
      external_message() && call_message()
    }

    /* shortcut for message_opt.val */
    function method msg(): Message
      reads `message_opt
      requires message_opt.has_val()
    {
      message_opt.val
    }

    function method tvm_myaddr(): address
    {
      address_this
    }

    function method tvm_balance(): Grams
      reads `balance
    {
      balance
    }

    // see ./tvm/default_support_functions.hpp for original semantics
    method int_value() returns (r:Status, g:Grams)
      requires message_opt.has_val()
      ensures internal_message() ==> r == Success && g == msg().info.value
      ensures !internal_message() ==> r.Failure?
    {
      if (internal_message()) {
        return Success, msg().info.value;
      }
      else {
        return Failure(InternalMessageExpected), 0;
      }
    }

    // see ./tvm/default_support_functions.hpp for original semantics
    method int_sender() returns (r:Status, a:address)
      requires message_opt.has_val()
      ensures internal_message() ==> r == Success && a == msg().info.src
      ensures !internal_message() ==> r.Failure?
    {
      if (internal_message()) {
        return Success, msg().info.src;
      }
      else {
        return Failure(InternalMessageExpected), address.Default();
      }
    }

    method int_sender_and_value() returns (r:Status, a:address, v:Grams)
      requires message_opt.has_val()
      ensures internal_message() ==> r == Success && a == msg().info.src && v == msg().info.value
      ensures !internal_message() ==> r.Failure?
    {
      a :- int_sender();
      v :- int_value();
      return Success, a, v;
    }

    method set_return_func_id(ret_func: option<ContractCallbackMethod>)
      modifies `return_func_id_opt
      ensures return_func_id_opt == ret_func
    {
      return_func_id_opt := ret_func;
    }

    method set_int_return_address(ret_addr: address)
      modifies `return_address
      ensures return_address == ret_addr
    {
      return_address := ret_addr;
    }

    method set_int_return_flag(fl: MsgFlags)
      modifies `return_flag
      ensures return_flag == fl
    {
      return_flag := fl;
    }

    method set_int_return_value(val: Grams)
      modifies `return_value
      ensures return_value == val
    {
      return_value := val;
    }

    function method tvm_now(): uint64
      reads `unix_blocktime
    {
      unix_blocktime
    }

    // returns the pubkey of the contract
    // (that was passed using state init on deployement)
    function method tvm_pubkey(): uint256
      reads `tvm_pubkey_
    {
      tvm_pubkey_
    }

    // Returns the signing key of the external message
    // for internal messages, this equals 0
    function method msg_pubkey(): uint256
      reads `message_opt
    {
      if (message_opt.None?) then
        0
      else
        if (internal_message()) then
          0
        else
          if (external_message()) then
            message_opt.val.info.pubkey
          else
            0
    }

    method tvm_accept()
      ensures unchanged (`deferred_queue)
    {
    }

    method inc_act_counter()
      modifies `act_counter
      ensures act_counter == old(act_counter) + 1
    {
      act_counter := act_counter + 1;
    }

    // modeling tvm_transfer function from
    // TON-Compiler/../cpp-sdk/tvm/contract.hpp
    method tvm_transfer(dest:address, nanograms:Grams, bounce:bool,
      flags:MsgFlags := TON_CPP_DEFAULT_MSG_FLAGS)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures flags & SENDMSG_ALL_BALANCE == 0 ==>
      exists m :: action_queue == old(action_queue) + [m] &&
      m.Action_SendMessage? &&
      m.msg.msg.OrdinaryMessage? &&
      m.msg.msg.info.dest == dest &&
      m.msg.msg.info.value == nanograms &&
      m.msg.msg.body == None &&
      unchanged (`deferred_queue)
      ensures flags & SENDMSG_ALL_BALANCE != 0 ==>
      exists m :: deferred_queue == old(deferred_queue) + [m] &&
      unchanged (`action_queue)

    {
      var msgHdr := IntMsgHdr(bounce, address_this, dest, nanograms,
        return_func_id_opt, Value(return_address));
      var msg := OrdinaryMessage(msgHdr, None);
      tvm_sendmsg(msg, flags);
    }

    method suicide(suicide_addr: address)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures unchanged (`action_queue)
      ensures |deferred_queue| == |old(deferred_queue)| + 1
    {
      var suicide_flags :=
        SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY |
        IGNORE_ACTION_ERRORS | SENDER_WANTS_TO_PAY_FEES_SEPARATELY;
      // Keep in mind that SEND_ALL_GAS is an alias for SENDMSG_ALL_BALANCE,
      // so the suicide message will be put into the deferred_queue, not
      // the action_queue
      tvm_transfer(suicide_addr, 0, false, suicide_flags);
    }

    // If the message does not have SENDMSG_ALL_BALANCE flag, put it in the
    // ordinary action_queue. Otherwise, put it in the deferred action queue.
    // Unfortunately, the latter messages have to be treated in a very special
    // way, this is why we have to store them separately.
    method tvm_sendmsg(msg:T.Message, flags:MsgFlags)
      requires !msg.is_msg_bounced()
      requires !msg.is_msg_ext()
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures
       var act := T.Action_SendMessage(old(act_counter) + 1, T.MessageWithFlags(msg, flags));
       (if !(act.msg.is_int_msgfl() && act.msg.has_msg_flag(SENDMSG_ALL_BALANCE) ) then
         action_queue == old(action_queue) + [act] && unchanged(`deferred_queue)
       else
         deferred_queue == old(deferred_queue) + [act] && unchanged(`action_queue)
       ) &&
      act.Action_SendMessage? &&
      act.msg.msg == msg &&
      act.msg.flags == flags &&
      act.id == act_counter &&
      !act.msg.msg.is_msg_bounced() &&
      !act.msg.msg.is_msg_ext() &&
      act_last == Value(act)
      ensures unique_actions(action_queue, act_counter)
    {
      inc_act_counter();
      var act := T.Action_SendMessage(act_counter, T.MessageWithFlags(msg, flags));
      if (act.msg.is_int_msgfl() && act.msg.has_msg_flag(SENDMSG_ALL_BALANCE)) {
        deferred_queue := deferred_queue + [act];
      }
      else {
        action_queue := action_queue + [act];
      }
      act_last := Value(act);
    }

    method tvm_rawreserve(value: Grams, flags: T.RawReserveFlags)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `act_counter
      ensures unique_actions(action_queue, act_counter)
      ensures |action_queue| == |old(action_queue)| + 1
      ensures exists m:T.Action :: action_queue == old(action_queue) + [m] &&
      m.Action_RawReserve? &&
      m.value == value &&
      m.flags == flags
    {
      inc_act_counter();
      var act := T.Action_RawReserve(act_counter, value, flags);
      action_queue := action_queue + [act];
    }

    method tvm_set_pubkey(pubkey: uint256)
      modifies `tvm_pubkey_
      ensures tvm_pubkey() == pubkey
    {
      tvm_pubkey_ := pubkey;
    }


    // The ordinary call into another smart-contract.
    // A wrapper around low-level tvm_sendmsg.
    method method_call(dest: address, amount: Grams, meth: ContractMethod,
      flags: MsgFlags := TON_CPP_DEFAULT_MSG_FLAGS,
      bounce: bool := true,
      ihr_disabled: bool := true,
      answer_id_opt:option<ContractCallbackMethod> := None,
      answer_addr_opt:option<address> := None)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures flags & SENDMSG_ALL_BALANCE == 0 ==>
      exists m :: action_queue == old(action_queue) + [m] &&
      m.Action_SendMessage? &&
      m.msg.msg.OrdinaryMessage? &&
      m.msg.msg.body.has_val() &&
      m.msg.msg.body.val.call? &&
      m.msg.msg.body.val.cm == meth &&
      m.msg.msg.info.dest == dest &&
      m.msg.msg.info.value == amount &&
      act_last == Value(m) &&
      unchanged (`deferred_queue)
      ensures flags & SENDMSG_ALL_BALANCE != 0 ==>
      exists m :: deferred_queue == old(deferred_queue) + [m] &&
      unchanged (`action_queue)
    {
      var msg_header := IntMsgHdr(bounce, address_this, dest, amount,
         answer_id_opt, answer_addr_opt);
      var msg_body := call(meth);
      var out_msg := OrdinaryMessage(msg_header, Value(msg_body));
      tvm_sendmsg(out_msg, flags);
    }

    // added for greater compatibility with TON C++
    method deploy_noop(dest: address, amount: Grams, init: StateInit,
      ctor: ConstructorMethod)
      requires dest == T.calc_address_from_stateinit(init)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures
       var msg_header := T.IntMsgHdr(true, address_this, dest, amount,
         None, None);
       var msg_body := T.deploy(init, ctor);
       var out_msg := T.OrdinaryMessage(msg_header, Value(msg_body));
       var act := T.Action_SendMessage(old(act_counter) + 1, T.MessageWithFlags(out_msg, TON_CPP_DEFAULT_MSG_FLAGS));
       (if !act.msg.has_msg_flag(SENDMSG_ALL_BALANCE) then
         action_queue == old(action_queue) + [act] && unchanged(`deferred_queue)
       else
         deferred_queue == old(deferred_queue) + [act] && unchanged(`action_queue)
       ) &&
      act.Action_SendMessage? &&
      act.msg.is_int_msgfl() &&
      act.msg.msg.info.value == amount &&
      act.msg.msg.info.src == address_this &&
      act.msg.msg.info.dest == dest &&
      act.msg.msg.info.bounce == true &&
      act.msg.flags == TON_CPP_DEFAULT_MSG_FLAGS &&
      act.msg.msg.body.has_val() &&
      act.msg.msg.body.val.deploy? &&
      act.msg.msg.body.val.ctor == ctor &&
      act.msg.msg.body.val.init == init
    {
      deploy(dest, amount, init, ctor);
    }

    method deploy(dest: address, amount: Grams, init: T.StateInit,
      ctor: T.ConstructorMethod,
      flags: MsgFlags := TON_CPP_DEFAULT_MSG_FLAGS,
      bounce: bool := true,
      ihr_disabled: bool := true,
      answer_id_opt:option<ContractCallbackMethod> := None,
      answer_addr_opt:option<address> := None)
      requires dest == T.calc_address_from_stateinit(init)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures
       var msg_header := T.IntMsgHdr(bounce, address_this, dest, amount,
         answer_id_opt, answer_addr_opt);
       var msg_body := T.deploy(init, ctor);
       var out_msg := T.OrdinaryMessage(msg_header, Value(msg_body));
       var act := T.Action_SendMessage(old(act_counter) + 1, T.MessageWithFlags(out_msg, flags));
       (if !act.msg.has_msg_flag(SENDMSG_ALL_BALANCE) then
         action_queue == old(action_queue) + [act] && unchanged(`deferred_queue)
       else
         deferred_queue == old(deferred_queue) + [act] && unchanged(`action_queue)
       ) &&
      act.Action_SendMessage? &&
      act.msg.is_int_msgfl() &&
      act.msg.msg.info.value == amount &&
      act.msg.msg.info.src == address_this &&
      act.msg.msg.info.dest == dest &&
      act.msg.msg.info.bounce == bounce &&
      act.msg.flags == flags &&
      act.msg.msg.body.has_val() &&
      act.msg.msg.body.val.deploy? &&
      act.msg.msg.body.val.ctor == ctor &&
      act.msg.msg.body.val.init == init
    {
      var msg_header := IntMsgHdr(bounce, address_this, dest, amount,
        answer_id_opt, answer_addr_opt);
      var msg_body:MsgBody := MsgBody.deploy(init, ctor);
      var out_msg := OrdinaryMessage(msg_header, Value(msg_body));
      tvm_sendmsg(out_msg, flags);
    }

    // contract_handle.hpp:276
    // If the destination address has no code, and T.StateInit is initialized
    // with code  and data fields, and  its hash equals to  the destination
    // address,  then the  code part  of  T.StateInit is  took as  if it  was
    // deployed on the destination address, and the body gets executed.
    method deploy_call(dest: address, amount: Grams, init: T.StateInit,
      ctor: T.ConstructorMethod, meth: T.ContractMethod,
      flags: MsgFlags := TON_CPP_DEFAULT_MSG_FLAGS,
      bounce: bool := true,
      ihr_disabled: bool := true,
      answer_id_opt:option<ContractCallbackMethod> := None,
      answer_addr_opt:option<address> := None)
      requires dest == T.calc_address_from_stateinit(init)
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures unique_actions(action_queue, act_counter)
      ensures
       var msg_header := T.IntMsgHdr(bounce, address_this, dest, amount,
         answer_id_opt, answer_addr_opt);
       var msg_body := T.deployWithCall(init, ctor, meth);
       var out_msg := T.OrdinaryMessage(msg_header, Value(msg_body));
       var act := T.Action_SendMessage(old(act_counter) + 1, T.MessageWithFlags(out_msg, flags));
       (if !act.msg.has_msg_flag(SENDMSG_ALL_BALANCE) then
         action_queue == old(action_queue) + [act] && unchanged(`deferred_queue)
       else
         deferred_queue == old(deferred_queue) + [act] && unchanged(`action_queue)
       ) &&
      act.Action_SendMessage? &&
      act.msg.is_int_msgfl() &&
      act.msg.msg.info.value == amount &&
      act.msg.msg.info.src == address_this &&
      act.msg.msg.info.dest == dest &&
      act.msg.msg.info.bounce == bounce &&
      act.msg.flags == flags &&
      act.msg.msg.body.has_val() &&
      act.msg.msg.body.val.deployWithCall? &&
      act.msg.msg.body.val.ctor == ctor &&
      act.msg.msg.body.val.cm == meth &&
      act.msg.msg.body.val.init == init
    {
      var msg_header := IntMsgHdr(bounce, address_this, dest, amount,
        answer_id_opt, answer_addr_opt);
      var msg_body := deployWithCall(init, ctor, meth);
      var out_msg := OrdinaryMessage(msg_header, Value(msg_body));
      tvm_sendmsg(out_msg, flags);
    }

    // Semantics of the TON return operator is as follows:
    //  - if the method is invoked by an external message, then
    //    event with ret_val body is generated.
    //  - if the method is invoked by a bounced internal message,
    //    then nothing happens.
    //  - if the method is invoked by a non-bounced internal message,
    //    then the message with ret_val is generated, where the destination
    //    address is set to the address of the caller, and the message value
    //    is set to 0, and the bounce flag is set to TRUE. Some of these
    //    may be changed using special functions, like set_int_return_flag,
    //    set_int_return_value, set_int_return_answer_id, etc.
    method TON_CPP_return(ret_val:T.ContractMethodReturnValue)
      requires {:error "message_opt.has_val() must hold"} message_opt.has_val()
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      ensures internal_message() ==>
      var IntMsgHdr(_, src, dest, _, _, _) := msg().info;
      // TODO: dest here has to be changed to return_address
      var ret_addr := return_address;
      var ret_value := return_value;
      var msgHdr := T.IntMsgHdr(true, address_this, ret_addr, ret_value);
      var out_msg := T.OrdinaryMessage(msgHdr, Value(T.returnCall(return_func_id_opt, ret_val)));
      var act := T.Action_SendMessage(old(act_counter) + 1, T.MessageWithFlags(out_msg, return_flag));
      (if !act.msg.has_msg_flag(SENDMSG_ALL_BALANCE) then
         action_queue == old(action_queue) + [act] && unchanged(`deferred_queue)
       else
         deferred_queue == old(deferred_queue) + [act] && unchanged(`action_queue)
      ) &&
      act.Action_SendMessage? &&
      act.msg.is_int_msgfl() &&
      act.msg.flags == return_flag &&
      act.msg.msg.body.has_val() &&
      act.msg.msg.body.val.returnCall? &&
      act.msg.msg.info.value == return_value &&
      act.msg.msg.info.dest == ret_addr &&
      act.msg.msg.info.src == address_this &&
      act.msg.msg.info.bounce == true && // !!
      act.msg.msg.body.val.ccm == return_func_id_opt
      ensures !internal_message() ==>
      exists m :: action_queue == old(action_queue) + [m] &&
      m.Action_SendMessage? &&
      m.msg.is_event_msgfl() &&
      m.msg.flags == SENDMSG_ORDINARY &&
      unchanged (`deferred_queue)
      ensures unique_actions(action_queue, act_counter)
    {
      // if the calling method is invoked by an internal message,
      // then the RETURN operator sends answer message.
      if (internal_message()) {
        var IntMsgHdr(_, src, dest, _, _, _) := msg().info;
        // return message is created with bounce=true by default.
        // see: smart_switcher.hpp:175 (send_internal_answer)
        // value = 0 is set by default. However, it could be changed
        // see: default_support_functions.hpp:61 (set_int_return_value)
        var ret_addr := return_address;
        var ret_value := return_value;
        var msgHdr := T.IntMsgHdr(true, address_this, ret_addr, ret_value);
        var callback := return_func_id_opt;
        tvm_sendmsg(
          T.OrdinaryMessage(msgHdr, Value(T.returnCall(callback, ret_val))),
          return_flag
          );
      }
      else {
        // if the calling method is invoked by an external message,
        // then we just put an event into the log ("outbound external msg")
        // smart_switcher.hpp:95 (send_external_answer)
        tvm_sendmsg(
        T.EventMessage(address_this, T.returnCall(None, ret_val)),
        SENDMSG_ORDINARY
        );
      }
    }

    // operator requre(cond, error)
    method require(cond:bool, error_code:uint) returns (r: Status)
      ensures cond ==> r == Success
      ensures !cond ==> r == Failure(error_code)
    {
      if (!cond) {
        return Failure(error_code);
      }
      return Success;
    }

    // TON-Compiler/llvm/projects/ton-compiler/cpp-sdk/tvm/default_support_functions.hpp:23
    function method TON_CPP_int_value_get() : Grams
      requires message_opt.has_val()
      reads `message_opt
    {
      if (internal_message()) then
        message_opt.val.info.value
      else
        0
    }

    method TON_CPP_set_int_return_flag(flag: MsgFlags)
      modifies `return_flag
      ensures return_flag == flag
    {
      return_flag := flag;
    }

    // calculates the fee that has to be paid for processing msg
    // by the node
    function method msgfl_fee_value(msg: T.MessageWithFlags): Grams
      requires msg.is_int_msgfl() || msg.is_event_msgfl()
    {
      // TODO: check the logic
      if (msg.msg.is_msg_int()) then
        add(
        (if !msg.has_msg_flag(IGNORE_ACTION_ERRORS) then
           msg.msg.info.value
         else
           0
         ), msg_send_fee)
      else ( /* (msg.msg.is_msg_event()) */
        assert (msg.msg.is_msg_event());
        if !msg.has_msg_flag(IGNORE_ACTION_ERRORS) then
          msg_send_fee
        else
          0
      )
    }

    /* Evaluate the minimum amount of Grams needed to successfully send */
    /* the given message according to the flags */
    function method action_fee_value(act: T.Action, balance: Grams): Grams
    {
      match act {
        case Action_SendMessage(_, msg) =>
          msgfl_fee_value(msg)
        case Action_RawReserve(_, value, flags) =>
          rawreserve_fee_value(value, flags, balance)
      }
    }

    /* The second balance argument stands for balance remaining. */
    /* It is needed to calculate reserve actions. */
    function method total_action_fee_value(action_queue: seq<T.Action>, balance: Grams): option<Grams>
      decreases |action_queue|
      ensures var v := total_action_fee_value(action_queue, balance);
      v.has_val() ==> v.val <= balance
    {
      if |action_queue| > 0 then
        var fee := action_fee_value(action_queue[0], balance);
        if (fee <= balance) then (
          var sub_total := total_action_fee_value(action_queue[1..],
          balance - fee);
          match sub_total {
            case Value(m) =>
              Value(add(fee, m))
            case None =>
              None
          }
        )
        else None
      else
        Value(0)
    }

    /* recursive unfolding of the total_action_fee_value */
    lemma total_action_fee_value_step(a:Action, l:seq<Action>, b:Grams)
      requires
      var v := total_action_fee_value([a] + l, b); v.has_val()
      ensures
      var v := total_action_fee_value([a] + l, b);
      var v1 := action_fee_value(a, b);
      v.val == v1 + total_action_fee_value(l, b - v1).val
    {
      /* auto. */
    }

    lemma total_action_fee_value_sublist(l1:seq<Action>, l:seq<Action>, b:Grams)
      requires l1 <= l
      requires var v := total_action_fee_value(l, b); v.has_val()
      ensures
      //var v := total_action_fee_value(l, b);
      var v1 := total_action_fee_value(l1, b);
      v1.has_val()
    {
      if (l1 == []) {
        /* auto. */
      } else {
        var a := l1[0];
        var l' := l[1..];
        var l1' := l1[1..];
        var av := action_fee_value(a, b);
        total_action_fee_value_sublist(l1', l', b - av);
      }
    }

    /* Lemma: the total fee value of action list concatenation equals
       the sum of each list's fee value.
     */
    lemma total_action_fee_value_additivity(l1:seq<Action>, l2:seq<Action>,
      b:Grams)
      ensures
      if (var v := total_action_fee_value(l1 + l2, b); v.has_val()) then
        var v := total_action_fee_value(l1 + l2, b);
        var v1 := total_action_fee_value(l1, b);
        v1.has_val() &&
          var v2 := total_action_fee_value(l2, b - v1.val);
          v2.has_val() &&
            v.val == v1.val + v2.val
      else true
    {
      var v := total_action_fee_value(l1 + l2, b);
      if (v.has_val()) {
        if (l1 == []) {
          assert (l1 + l2 == l2);
          assert (total_action_fee_value(l1 + l2, b) == total_action_fee_value(l2, b));
          /* auto */
        } else {
          var a := l1[0];
          var l1' := l1[1..];
          var av := action_fee_value(a, b);
          // pre: total_action_fee_value(l1' + l2, b - av).has_val()
          // this is implied by total_action_fee_value_step(a, l1' + l2, b)
          assert ([a] + (l1' + l2) == l1 + l2);
          var lf := l1' + l2;
          assert (
            var va := total_action_fee_value([a] + lf, b);
            va.has_val());
          total_action_fee_value_step(a, lf, b);
          total_action_fee_value_additivity(l1', l2, b - av);
        }
      }
      else {
        /* true */
      }
    }

    /********************************
       Storage Phase processor.
     ********************************/
    // Charge the account for data storage
    method tvm_storage_phase()
      requires Valid()
      modifies `balance, `status, `due_payment
      ensures old(status) != T.Active ==> status == old(status)
      ensures old(status) == T.Active && old(balance) >= storage_fee ==>
      balance == old(balance) - storage_fee && status == T.Active
      ensures old(status) == T.Active && old(balance) < storage_fee ==>
        balance == 0 && status == T.Frozen && due_payment == storage_fee - old(balance)
      ensures Valid()
    {
      if (status == T.Active) {
        if (balance >= storage_fee) {
          balance := balance - storage_fee;
        }
        else {
          status := T.Frozen;
          due_payment := storage_fee - balance;
          balance := 0;
        }
      }
    }

    // *****************************************************
    // See TVM manual, page 12, section 1.4
    // *****************************************************

    /********************************
       Credit Phase processor.
     ********************************/
    // The contract gets credited with the message value
    method tvm_credit_phase(msg: T.Message)
      requires Valid()
      modifies `balance
      ensures msg.is_msg_int() ==>
      balance == add(old(balance), msg.info.value)
      ensures !msg.is_msg_int() ==> balance == old(balance)
      ensures Valid()
    {
      if (msg.is_msg_int()) {
        balance := add(balance, msg.info.value);
      }
    }

    function method rawreserve_fee_value(
      res_value:Grams, flags:T.RawReserveFlags, balance: Grams): Grams
    {
      match flags {
        case rawreserve_at_most =>
          min(balance, res_value)
        case rawreserve_exact =>
          res_value
      }
    }

    // Returns new account status and compute step skip flag.
    function method compute_new_status(msg: T.Message): (bool, T.AccountStatus)
      reads `status, `balance
    {
      match status
        case Active =>
          (false, T.Active)
        case Uninit =>
          if (msg.is_msg_deploy() || msg.is_msg_deployCall()) then
            (false, T.Active)
          else
            (true, T.Uninit)
        case Frozen =>
          if (balance > 0) then
            (false, T.Active)
          else
            (true, T.Frozen)
    }

    predicate constructor_post()
      requires deploy_message() || deployCall_message()
      reads this, st

    method execute_constructor() returns (r:Status)
      requires Valid()
      requires return_op_default_values()
      requires st.initial_values()
      requires deploy_message() || deployCall_message()
      requires action_queue == [] && deferred_queue == []
      requires !constructed
      modifies st, `action_queue, `deferred_queue, `act_last
      ensures {:error "constructor is not allowed to emit messages with SENDMSG_ALL_BALANCE flag set"} deferred_queue == []
      ensures Valid()
      ensures return_op_default_values()
      ensures constructor_post()
      ensures unchanged (`constructed)

    /* Method   is invoked in a context of executing deploy_call,
       i.e. after the constructor has been executed. */
    method execute_ctor_method() returns (r: Status)
      requires Valid()
      requires !constructed
      requires deployCall_message()
      requires constructor_post()
      requires return_op_default_values()
      requires {:error "constructor is not allowed to emit messages with SENDMSG_ALL_BALANCE flag set"} deferred_queue == []
      modifies st, `action_queue, `deferred_queue, `return_value, `return_flag, `act_counter, `act_last
      ensures Valid()

    /* External method call. */
    method execute_external_method() returns (r:Status)
      requires Valid()
      requires action_queue == [] && deferred_queue == []
      requires external_message() && call_message()
      requires return_op_default_values()
      modifies st, `action_queue, `deferred_queue, `return_flag, `act_counter, `act_last
      ensures Valid()

    /* Internal method call. */
    method execute_internal_method() returns (r:Status)
      requires Valid()
      requires action_queue == [] && deferred_queue == []
      requires internal_message() && call_message()
      requires return_op_default_values()
      modifies st, `action_queue, `deferred_queue, `return_flag, `act_counter, `act_last
      ensures Valid()

    /********************************
       Compute Phase processor.
     ********************************/
    /* In this  dispatch procedure, we need to  guarantee that message
       gets processed according to its structure, and it is impossible
       to process internal deploy message  as if it is external deploy
       message, for example.  */
    /* By the convention, action_queue and ctor_actions are cleaned out
       by the msg_handler method. */
    method tvm_compute_phase() returns (r:Status)
      requires Valid()
      requires !constructed ==> st.initial_values()
      requires message_opt.has_val()
      requires !message_opt.val.is_msg_event()
      requires action_queue == [] && deferred_queue == []
      requires return_op_default_values()
      // requires !message_opt.val.is_msg_return() // TODO: add processing
      modifies st, `action_queue, `return_flag, `deferred_queue,
      `return_address, `return_func_id_opt, `act_counter, `return_value,
      `act_last
      ensures r != Success ==> action_queue == [] && deferred_queue == []
      ensures unchanged (`constructed)
      ensures Valid()
    {
      var in_msg := message_opt.val;
      var is_bounced := in_msg.is_msg_bounced();
      var is_deploy_msg := in_msg.is_msg_deploy();
      var is_deployCall_msg := in_msg.is_msg_deployCall();
      var is_call_msg := in_msg.is_msg_call();
      var is_return_msg := in_msg.is_msg_return();

      /* Message types are orthogonal */
      assert (is_bounced ==> !is_deploy_msg && !is_deployCall_msg && !is_call_msg && !is_return_msg);
      assert (is_deploy_msg ==> !is_deployCall_msg && !is_bounced && !is_call_msg && !is_return_msg);
      assert (is_call_msg ==> !is_deployCall_msg && !is_bounced && !is_deploy_msg && !is_return_msg);
      assert (is_return_msg ==> !is_deployCall_msg && !is_bounced && !is_deploy_msg && !is_call_msg);
      assert (is_deployCall_msg ==> !is_deploy_msg && !is_bounced && !is_call_msg && !is_return_msg);
      // There are also unfreeze messages, but we do not
      // consider it here for now.

      /* Here goes computing phase in several flavours */
      if (is_deploy_msg) {
        if (constructed) {
          return Failure(ComputePhaseFailed);
        }
        var deploy(init, ctor) := msg().body.val;
        r := execute_constructor();
      }
      else if (is_deployCall_msg) {
        if (constructed) {
          return Failure(ComputePhaseFailed);
        }
        // The deployCall is just a call in case the SmC is
        // already deployed,
        var deployWithCall(init, ctor, call) := msg().body.val;
        r := execute_constructor();
        // TODO: Should we reset the return operator parameters here?
        if (r == Success) {
          // TODO: This is an AD-HOC way of resetting the params, if
          // any changes were done in constructor. It should be rewritten.
          // assume (return_op_default_values());
          r := execute_ctor_method();
        }
      }
      else if (is_call_msg) {
        if ( !constructed ) {
          return Failure(ComputePhaseFailed);
        }
        // there has to be a fallback handler also
        assert (action_queue == []);
        // TODO : refactor the input argument, we need to use
        // only message_opt in our internal methods. It should
        // simply reasoning.
        if (in_msg.is_msg_int()) {
          r := execute_internal_method();
        }
        else {
          assert (in_msg.is_msg_ext());
          r := execute_external_method();
        }
      }
      else if (is_bounced) {
        assert (is_bounced);
        if ( !constructed ) {
          return Failure(ComputePhaseFailed);
        }
        r := execute_bounced_msg(in_msg);
      }
      else {
        r := execute_fallback(in_msg);
      }

      if (r != Success) {
        action_queue := [];
        deferred_queue := [];
      }
      return r;
    }

    predicate tvm_action_phase1_pre(action_queue:seq<Action>, balance:Grams)
    {
      var v := total_action_fee_value(action_queue, balance);
      v.has_val() &&
        balance >= v.val
    }

    predicate tvm_action_phase2_pre(deferred_queue:seq<Action>)
    {
      |deferred_queue| <= 1
    }

    /********************************
       Action phase processor.
     ********************************/
    // In case of a success SmC balance gets updated.
    // In case of an error, SmC balance stays unchanged.
    // IFF there is a sufficient balance and |old(deferred_queue)| <= 1,
    // then the phase will succeed and the following holds:
    //  * If the old(deferred_queue) is empty, then the int_msg_queue
    //    will contain all SendMsg_Actions of old(action_queue)
    //  * if the |old(deferred_queue)| == 1, then the int_msg_queue
    //    will contain all SendMsg_Actions of old(action_queue)
    //    plus the SendMsg_Action carrying
    //    balance - total_action_fee_value(old(action_queue))

    // Here, old(X) refers to the value of X at the point of
    // the method invocation.
    method tvm_action_phase() returns (r: Status)
      requires Valid()
      requires int_msg_queue == []
      requires g_action_balance == balance
      requires g_deferred_queue == deferred_queue
      requires g_action_queue == action_queue
      requires unique_actions(action_queue, act_counter)
      modifies `action_queue, `int_msg_queue, `balance, `deferred_queue
      ensures unchanged (`g_action_queue, `g_action_balance, `g_deferred_queue)
      ensures tvm_action_phase1_pre(old(action_queue), old(balance)) &&
      tvm_action_phase2_pre(old(deferred_queue)) ==>
      r == Success &&
      var send_set :=
         set x:SendAction | x.msg.msg.is_msg_int() && x in g_action_queue;
      (forall a :: a in send_set ==> a in int_msg_queue) &&
      |int_msg_queue| == |send_set| + |g_deferred_queue| //&&
      ensures r == Success && |g_deferred_queue| == 1 ==>
      tvm_action_phase1_pre(old(action_queue), old(balance)) &&
      var send_msg_count :=
        |set x:SendAction | x.msg.msg.is_msg_int() && x in g_action_queue|;
      |int_msg_queue| == send_msg_count + 1  &&
      var d := old(deferred_queue)[0];
      var a := int_msg_queue[|int_msg_queue| - 1];
      a.msg.msg.is_msg_int() &&
        // old(balance) here refers to the balance at the time of the
        // action phase invocation
      a.msg.msg.info.value == old(balance) - total_action_fee_value(old(action_queue), old(balance)).val &&
      a.msg.msg.body == d.msg.msg.body &&
      a.msg.msg.info.src == d.msg.msg.info.src &&
      a.msg.msg.info.dest == d.msg.msg.info.dest
      ensures |int_msg_queue| <= |g_action_queue| + |g_deferred_queue|
      ensures r == Success ==>
      var send_msg_count :=
        |set x:SendAction | x.msg.msg.is_msg_int() && x in g_action_queue|;
        |int_msg_queue| == send_msg_count + |g_deferred_queue|
      ensures Valid()
      ensures action_queue == [] && deferred_queue == []
      ensures old(action_queue) == [] && old(deferred_queue) == [] ==>
      unchanged(`balance)
      ensures !tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
      r == Failure(ActionPhaseFailed) &&
      balance == old(balance) &&
      action_queue == [] &&
      int_msg_queue == []
      ensures unique_actions(action_queue, act_counter)
    {
      r := tvm_action_phase1(); // process ordinary actions
      assert (tvm_action_phase1_pre(old(action_queue), old(balance)) <==>
        r == Success);
      if (r == Success && |deferred_queue| != 0) {
        assert (balance == old(balance) -
          total_action_fee_value(old(action_queue), old(balance)).val);
        assert (tvm_action_phase1_pre(old(action_queue), old(balance)) <==>
          r == Success);
        r := tvm_action_phase2(); // process deferred actions
      }
      // queues are either fully processed or have to be reset,
      // so, anyway, they have to be empty at the end.
      action_queue := [];
      deferred_queue := [];
      if (r != Success) {
        int_msg_queue := [];
      }
      return r;
    }

    method tvm_action_phase1() returns (r: Status)
      requires Valid()
      requires unique_actions(action_queue, act_counter)
      requires int_msg_queue == []
      requires g_action_balance == balance // old(balance)
      modifies `action_queue, `int_msg_queue, `balance
      ensures unique_actions(action_queue, act_counter)
      ensures tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
      r == Success &&
      /* ACT1-BALANCE */
      (var total :=
         total_action_fee_value(old(action_queue), old(balance)).val;
         balance == g_action_balance - total ) &&
      /* ACT1-SENDSET */
      (var send_set :=
        set x:SendAction | x.msg.msg.is_msg_int() && x in old(action_queue);
        (forall x :: x in send_set <==> x in int_msg_queue) &&
        |int_msg_queue| == |send_set|)
//      ensures tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
//      (var send_set :=
//        set x:SendAction | x.msg.msg.is_msg_int() && x in old(action_queue);
//        |int_msg_queue| == |send_set|)
      ensures Valid()
      ensures |int_msg_queue| <= |old(action_queue)|
      ensures action_queue == []
      ensures !tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
      r == Failure(ActionPhaseFailed) &&
      balance == old(balance)
    {
      ghost var processed_part:seq<Action> := []; // processed part of the action queue
      ghost var processed_part_old:seq<Action> := [];
      ghost var act_others:seq<Action> := [];
      ghost var total_fee_pre, total_fee_post := 0, 0; // total fee accumulated in a cycle
      ghost var last_act:option<Action> := None;

      var old_balance := balance; // roll back on error
      var exit_code:uint := success;
      var balance_rem:Grams := balance; // balance remaining
      r := Success;

      while (action_queue != [])
        decreases |action_queue|
        invariant forall a :: a in int_msg_queue ==> a in processed_part
        invariant forall a :: a in processed_part ==> a in old(action_queue)
        invariant processed_part + action_queue == old(action_queue)
        invariant processed_part <= old(action_queue)
        invariant |int_msg_queue| <= |old(action_queue)|
        invariant |int_msg_queue| + |act_others| == |processed_part|
        invariant forall x :: (x in processed_part && x !in int_msg_queue) ==>
         |int_msg_queue| < |processed_part|

        invariant tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
        tvm_action_phase1_pre(action_queue, balance)

        invariant !tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
        !tvm_action_phase1_pre(action_queue, balance)

        /* ACT1-BALANCE */
        invariant |processed_part| > 0 ==>
         var act := processed_part[|processed_part| - 1];
         var fee := action_fee_value(act, balance_rem);
         balance_rem >= fee ==>
          balance == balance_rem - fee &&
          total_fee_post == add(total_fee_pre, fee)

        /* ACT1-BALANCE */
        invariant |processed_part| > 0 ==>
        var act := processed_part[|processed_part| - 1];
        processed_part == processed_part_old + [act]

        /* ACT1-BALANCE */
        invariant tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
        var v := total_action_fee_value(processed_part, old(balance));
        v.has_val()

        /* ACT1-BALANCE */
        invariant tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
        var fee_val := total_action_fee_value(processed_part, old(balance));
        total_fee_post == add(total_fee_pre, fee_val.val)

        /* ACT1-BALANCE */
        invariant old(balance) == add(balance, total_fee_post)

        /* ACT1-SENDSET */
        invariant var send_set :=
        set x:SendAction | x.msg.msg.is_msg_int() && x in processed_part;
        (forall a :: a in send_set <==> a in int_msg_queue)

        invariant var send_set :=
        set x:SendAction | x.msg.msg.is_msg_int() && x in processed_part;
        |int_msg_queue| == |send_set|
      {
        total_fee_pre := total_fee_post;
        processed_part_old := processed_part;
        balance_rem := balance;
        var act := action_queue[0];

        var act_fee := action_fee_value(act, balance);
        var res :=
          if (balance >= act_fee) then
            (success, balance - act_fee)
          else
            (error_action_phase_failed, balance);
        exit_code := res.0;
        if (exit_code != success) {
          assert (balance_rem < act_fee);
          action_queue := [];
          int_msg_queue := [];
          balance := old_balance;
          r := Failure(ActionPhaseFailed);
          return r;
        }
        balance := res.1;
        total_fee_post := add(total_fee_pre, act_fee);
        assert (balance_rem >= act_fee ==> balance == balance_rem - act_fee);
        if (act.Action_SendMessage? && act.msg.is_int_msgfl()) {
          int_msg_queue := int_msg_queue + [act];
        }
        else {
          act_others := act_others + [act];
        }
        processed_part := processed_part + [act];
        assert (act in processed_part && act.Action_SendMessage? && act.msg.msg.is_msg_int() ==> act in int_msg_queue);

        action_queue := action_queue[1..];
        assert (processed_part + action_queue == old(action_queue));

        // Check that premise holds, otherwise this call is useless.
        total_action_fee_value_additivity(processed_part, action_queue, old(balance));
        assert (balance == old(balance) - total_fee_post);
        assert (processed_part == processed_part_old + [act]);

        assume (tvm_action_phase1_pre(old(action_queue), old(balance)) ==>
        var fee_val := total_action_fee_value(processed_part, old(balance));
        total_fee_post == add(total_fee_pre, fee_val.val));

        assume (var send_set :=
          set x:SendAction | x.msg.msg.is_msg_int() && x in processed_part;
          |int_msg_queue| == |send_set|);
      } /* END WHILE */

      /* ACT1-BALANCE */
      assert (processed_part == old(action_queue));
      assert (total_action_fee_value(processed_part, old(balance)) ==
        total_action_fee_value(old(action_queue), old(balance)));
      assume (total_fee_post ==
        total_action_fee_value(processed_part, old(balance)).val);
      assert (balance == old(balance) - total_fee_post);

      return Success;
    }

    method tvm_action_phase2() returns (r:Status)
      requires var total :=
        total_action_fee_value(g_action_queue, g_action_balance);
        total.has_val() &&
        balance == g_action_balance - total.val
      modifies `deferred_queue, `int_msg_queue, `balance
      ensures deferred_queue == []
      ensures |old(deferred_queue)| > 1 ==>
        r != Success &&
        unchanged (`int_msg_queue, `balance)
      ensures |old(deferred_queue)| == 1 ==>
        var act := old(deferred_queue)[0];
        var hdr := act.msg.msg.info.(value := old(balance));
        var msg := act.msg.msg.(info := hdr);
        var act2 := act.(msg := act.msg.(msg := msg));
        int_msg_queue == old(int_msg_queue) + [act2] &&
        balance == 0 &&
        r == Success
      ensures |old(deferred_queue)| == 0 ==>
        r == Success &&
        unchanged (`deferred_queue, `balance, `int_msg_queue)
    {
      r := Success;
      if (|deferred_queue| > 1) {
        /* Currently, we do not allow more than 1 SENDMSG_ALL_BALANCE
           message to be sent. */
        r := Failure(ActionPhaseFailed);
      }
      else if (|deferred_queue| == 1) {
        var act := deferred_queue[0];
        assert (act.msg.has_msg_flag(SENDMSG_ALL_BALANCE));
        // this balance refers to the balance of the SmC
        // after all fees for other non-deferred actions
        // were conducted.
        var hdr := act.msg.msg.info.(value := balance);
        var msg := act.msg.msg.(info := hdr);
        var act2 := act.(msg := act.msg.(msg := msg));
        balance := 0;
        int_msg_queue := int_msg_queue + [act2];
      }
      deferred_queue := [];
      return r;
    }

    /********************************
       Bounce phase processor.
     ********************************/
    // The previous phases may have failed. Generate the reply
    // message to the calling site.
    method tvm_bounce_phase(msg: T.Message) //returns (r:Status)
      requires Valid()
      modifies `bounced_msg_opt, `balance, `act_counter
      ensures !msg.is_msg_bounce() ==>
        bounced_msg_opt == None && unchanged(`balance)
      ensures  msg.is_msg_bounce() ==> bounced_msg_opt.has_val() &&
        var bmsg_val := sub(msg.info.value, storage_fee);
        var bmsg_info := msg.info.(src := address_this,
          dest := msg.info.src, bounce := false, value := bmsg_val);
      bounced_msg_opt.val == BouncedMessage(bmsg_info, msg.body) &&
        bounced_msg_opt.val.hdr.value == sub(msg.info.value, storage_fee) &&
        balance == sub(add(old(balance), storage_fee), bmsg_info.value);
      ensures Valid()
    {
      if (msg.is_msg_bounce()) {
        var bmsg_val := sub(msg.info.value, storage_fee);
        var bmsg_hdr := msg.info.(src := address_this,
          dest := msg.info.src, bounce := false, value := bmsg_val);
        bounced_msg_opt := Value(BouncedMessage(bmsg_hdr, msg.body));
        balance := sub(add(balance, storage_fee), bmsg_hdr.value);
      } else {
        bounced_msg_opt := None;
      }
    }

    function method check_gas(): uint
      reads `gas_remaining
      ensures gas_remaining >= 0 ==> check_gas() == success
    {
      if gas_remaining < 0 then
        error_out_of_gas
      else
        success
    }

    /* Decrease the remaining gas value by the amount of gas consumed by
       the given function. For simplicity, we assume that all functions
       consume the same amount of gas equal to the gas_max_limit */
    method charge_gas(/*function*/) // TODO: make charges more granular
      modifies `gas_remaining
      ensures gas_remaining == old(gas_remaining) - gas_max_limit as int
    {
      gas_remaining := gas_remaining - gas_max_limit as int;
    }

    method execute_fallback(msg: T.Message) returns (r:Status)
      requires Valid()
      modifies st, `action_queue, `deferred_queue, `act_counter, `act_last
      ensures Valid()
    {
      /* It is a default behavior for TON C++ commit f5c4ff7c1 */
      return Failure(ComputePhaseFailed);
    }

    // In TON C++, current default behavior for on_bounce is to
    // throw exception.
    // https://github.com/tonlabs/TON-Compiler/blob/f5c4ff7c19677dc9b5b7a2a68
    // 6f8ae191c262dfd/llvm/projects/ton-compiler/cpp-sdk/tvm/smart_switcher.
    // hpp#L650
    method execute_bounced_msg(msg: T.Message) returns (r:Status)
      requires Valid()
      requires msg.is_msg_bounced()
      modifies st, `action_queue
      ensures Valid()
    {
      /* It is a default behavior for TON C++ commit f5c4ff7c1 */
      return Failure(BouncePhaseFailed);
    }

      /* This method is refined only to add post-conditions */

    /********************************
       Message executor.
     ********************************/
    method msg_dispatcher(in_msg: T.Message) returns (r: Status)
      requires Valid()
      requires !constructed ==> st.initial_values()
      requires !in_msg.is_msg_event()  // TODO: reject events, they can't be processed
      requires in_msg.is_msg_call() || in_msg.is_msg_deploy() ==>
      in_msg.info.dest == address_this
      requires in_msg.is_msg_bounced() ==> in_msg.hdr.dest == address_this
      requires action_queue == [] && deferred_queue == []
      requires unique_actions(action_queue, act_counter)
      modifies st, tmp_st, `action_queue, `message_opt, `status, `balance,
      `due_payment, `int_msg_queue, `return_flag, `constructed,
      `deferred_queue, `g_action_queue, `g_action_balance,
      `g_deferred_queue, `bounced_msg_opt, `return_address, `unix_blocktime,
      `return_func_id_opt, `act_counter,`return_value, `act_last
      ensures message_opt.has_val() && message_opt.val == in_msg
      ensures action_queue == [] && deferred_queue == []
      ensures r != Success ==> int_msg_queue == []
      ensures r != Success && !message_opt.val.is_msg_bounce() ==> bounced_msg_opt == None
      ensures r != Success && r != Failure(ComputePhaseSkipped) && message_opt.val.is_msg_bounce() ==>
      bounced_msg_opt.has_val() &&
      bounced_msg_opt.val.hdr.value == sub(message_opt.val.info.value, storage_fee) &&
      bounced_msg_opt.val.hdr.dest == message_opt.val.info.src
      ensures r == Success ==> bounced_msg_opt == None
      ensures unix_blocktime >= old(unix_blocktime)
      ensures unique_actions(action_queue, act_counter)
      ensures !constructed ==> st.initial_values()
      ensures Valid()
    {
      int_msg_queue := [];
      bounced_msg_opt := None;
      message_opt := Value(in_msg);

      // Default values for the return operator.  Those values may be changed
      // by calling set_int_return_* family of functions from the SmC code.
      set_int_return_flag(TON_CPP_DEFAULT_MSG_FLAGS);
      set_int_return_value(0);
      set_return_func_id(
        if msg().is_msg_int() && msg().info.answer_id.has_val() then
          msg().info.answer_id
        else
          None
      );
      set_int_return_address(
        if msg().is_msg_int() then
          if msg().info.answer_addr.has_val() then
            msg().info.answer_addr.val
          else
            msg().info.src
        else
          address.Default()
      );
      assert (return_op_default_values());
      var is_bounce := in_msg.is_msg_bounce();
      var is_call_msg_int := in_msg.is_msg_call() && in_msg.is_msg_int();
      var credit_first := !is_bounce && is_call_msg_int;

      /**
      if (is_ord_msg_ext) {
        if (balance < in_fwd_fee as int) {
          return Failure(InsufficientFunds);
        } else {
          balance := balance - in_fwd_fee as int;
        }
      } **/

      if (credit_first) {
        tvm_credit_phase(in_msg);
      }

      tvm_storage_phase();

      if (!credit_first) {
        tvm_credit_phase(in_msg);
      }
      // In the Rust node, this logic is hidden inside the
      // compute_phase function. We put it here instead to
      // make it more explicit.
      var (skip, new_status) := compute_new_status(in_msg);
      status := new_status;

      if (!skip) {
        backup_state();
        assert (!constructed ==> st.initial_values());
        assert (status == T.Active);
        assert (message_opt.val == in_msg);
        r := tvm_compute_phase();

        // the time parameter is not used anywhere below,
        // so increase it here, to establish monotonicity
        // of the tvm_now() values.
        unix_blocktime := *;
        assume (unix_blocktime >= old(unix_blocktime));

        // TODO: charge_gas();
        /* Before proceeding into the action phase, we check the gas. */
        // assume (gas_remaining > 0);
        // exit_code := check_gas();

        if (r == Success) { // Computing phase succeeded?

          // We need those to build proper reasoning in the
          // client implementation modules: original action_queue
          // and deferred_queue, as well as balance changes
          // after the action phase gets executed, but we need
          // to refer to their original values.

          g_action_queue := action_queue;
          g_action_balance := balance;
          g_deferred_queue := deferred_queue;

          r := tvm_action_phase();
          if (r != Success) {
            tvm_bounce_phase(in_msg);
            int_msg_queue := [];
            rollback_state();
            return Failure(ActionPhaseFailed);
          }
          // it doesn't matter if this was a deploy message or not,
          // 'constructed' must be true at this point anyway.
          constructed := true;
          return Success; // both Computing and Action phases succeeded.
        }
        else { // Computing phase failed.
          tvm_bounce_phase(in_msg);
          int_msg_queue := [];
          rollback_state();
          // The bounce phase is a side-effect of some failure.
          return Failure(MessageBounced);
        }
        return Failure(ComputePhaseFailed);
      }
      return Failure(ComputePhaseSkipped);
    }
  }
}
