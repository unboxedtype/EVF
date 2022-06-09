include "BaseTypes.dfy"

abstract module TONTypes
{
  import opened BaseTypes
  // This is the Rust node flag names.
  // For flags description, check the SENDRAWMSG TVM instruction.
  const SENDMSG_ORDINARY:MsgFlags := 0;
  const SENDMSG_PAY_FEE_SEPARATELY: MsgFlags := 1;
  const SENDMSG_IGNORE_ERROR:MsgFlags := 2;
  const SENDMSG_DELETE_IF_EMPTY:MsgFlags := 32;
  const SENDMSG_REMAINING_MSG_BALANCE:MsgFlags := 64;
  const SENDMSG_ALL_BALANCE:MsgFlags := 128;

  // -------------------------------------------------------------
  // TON C++ message flags aliases
  // -------------------------------------------------------------
  // IGNORE_ACTION_ERRORS
  // Do not consider insufficient balance as an error
  // SEND_ALL_GAS
  // used for  messages that  are to  carry all  the remaining
  // balance of the current smart contract (instead of the value originally
  // indicated in the message)
  // SENDER_WANTS_TO_PAY_FEE_SEPARATELY
  // Message send fee must be deducted from the balance of the sender
  // not from the msg value
  const IGNORE_ACTION_ERRORS := SENDMSG_IGNORE_ERROR;
  const SEND_ALL_GAS := SENDMSG_ALL_BALANCE;
  const DELETE_ME_IF_I_AM_EMPTY := SENDMSG_DELETE_IF_EMPTY;
  const SENDER_WANTS_TO_PAY_FEES_SEPARATELY := SENDMSG_PAY_FEE_SEPARATELY;

  // Default flags for TON C++
  const TON_CPP_DEFAULT_MSG_FLAGS:MsgFlags := SENDMSG_ORDINARY;

  // Constants names and values were taken from the
  // ton-labs-block/src/out_actions.rs for greater
  // compatibility.

  const ONE_TON:Grams := 1000000000;

  /* System error codes */
  const error_out_of_gas:uint := 100;
  const error_action_phase:uint := 101;
  const error_already_deployed:uint := 102;
  const error_deploy_failed:uint := 103;
  const error_compute_phase_failed:uint := 104;
  const error_action_phase_failed:uint := 105;
  const error_no_funds_to_import_msg:uint := 106;
  const success:uint := 0;

  const in_fwd_fee: Grams;
  const gas_max_limit:Grams; /* g_m according to TVM manual */
  const gas_credit_value:Grams; /* how much gas TVM credits the contract before ACCEPT */
  const msg_send_fee:Grams; /* coins needed to send a single biggest possible message */
  const storage_fee: Grams; /* = max_storage_fee * mean_duration */

  function method deploy_cost(st: StateInit): Grams
  function method msg_fee_value(msg: Message): Grams

  function method calc_address_from_stateinit<T(!new)>(st: T): address

  lemma {:axiom} calc_address_from_stateinit_bijection<T(!new)>()
    ensures forall st1:T, st2:T ::
    st1 != st2 <==>
     calc_address_from_stateinit(st1) != calc_address_from_stateinit(st2)


  // All methods that could be called using internal or external
  // messages. Constructor method does not belong here.
  type ContractMethod
  /* Have to be refined in the implementation module. */

  // Constructor method is declared in this type.
  type ConstructorMethod
  /* Have to be refined in the implementation module. */

  // All methods that are to be called by a response
  // message sent using the RETURN operator.
  type ContractCallbackMethod
  /* May be refined in the implementation module. */

  // Type denoting return value together with function identifier
  // that a return message originates from.
  type ContractMethodReturnValue
  /* May be refined in the implementation module. */
  {
    function method serialize():nat
    static function method deserialize(inp:nat):ContractMethodReturnValue
  }

  // All "external outbound" messages are declared here, including
  // external return messages and ordinary events. All those entities
  // we call contract events.
  // type ContractEvent

  // The idea of introducing the foreign types proved itself
  // untenable. From the perspective of an external observer (user)
  // all messages are foreign.

  datatype MsgBody =
    | call(cm:ContractMethod)
    | deploy(init:StateInit, ctor:ConstructorMethod)
    | deployWithCall(init:StateInit, ctor:ConstructorMethod, cm:ContractMethod)
    | returnCall(ccm:option<ContractCallbackMethod>,
    rv:ContractMethodReturnValue)

  type StateInit
  /* Have to be specified in the implementation module. */

  // message.hpp, line:65, int_msg_info_t et al.
  datatype MsgHeader =
    // Internal messages
    IntMsgHdr(bounce: bool, src: address, dest:address, value: Grams,
    answer_id:option<ContractCallbackMethod> := None,
    answer_addr:option<address> := None) |
    // external message, received from the outer world
    ExtMsgHdr(dest: address, pubkey: uint256)

  type IntMsgHdr = x:MsgHeader | x.IntMsgHdr? witness *

  // We injected StateInit into the message body block due
  // to convenience reasons
  // The current message dichotomy is as follows:
  //  - Messages can be Ordinary, Bounced or Event.
  //  - Ordinary message is either deploy message or call message or return
  //       messages. Ordinay messages can be internal or external.
  //  - Bounced message is an envelop over the Ordinary internal message
  //  - Event message is just a record.
  datatype Message =
    | OrdinaryMessage(info: MsgHeader, body: option<MsgBody>)
    | BouncedMessage(hdr: IntMsgHdr, body: option<MsgBody>)
    | EventMessage(src: address, ev: MsgBody)
  {
    predicate method is_msg_int()
    { this.OrdinaryMessage? && this.info.IntMsgHdr? }

    predicate method is_msg_ext()
    { this.OrdinaryMessage? && this.info.ExtMsgHdr? }

    predicate method is_msg_event()
    { this.EventMessage? }

    predicate method is_msg_bounce()
    { is_msg_int() && this.info.bounce }

    predicate method is_msg_bounced()
    { this.BouncedMessage? }

    predicate method is_msg_deploy()
    {
      (is_msg_int() || is_msg_ext()) &&
        this.body.has_val() &&
        this.body.val.deploy?
    }

    predicate method is_msg_deployCall()
    {
      (is_msg_int() || is_msg_ext()) &&
        this.body.has_val() &&
        this.body.val.deployWithCall?
    }

    predicate method is_msg_return()
    { is_msg_int() && this.body.has_val() && this.body.val.returnCall? }

    predicate method is_msg_call()
    {
      (is_msg_int() || is_msg_ext()) && this.body.has_val() && this.body.val.call?
    }
  }

  type BouncedMessage = x:Message | x.is_msg_bounced() witness *

  datatype MessageWithFlags =
    MessageWithFlags(msg: Message, flags: MsgFlags)
  {
    predicate method has_msg_flag(n: MsgFlags)
    { flags & n != 0 }
    predicate method is_msg_extfl()
    { this.msg.is_msg_ext() }
    predicate method is_int_msgfl()
    { this.msg.is_msg_int() }
    predicate method is_event_msgfl()
    { this.msg.is_msg_event() }
  }

  // a subset containing only internal messages and event messages,
  // i.e. all those that could be sent from contract using the
  // tvm_send primitive.
  type MessageWithFlagsIE = x:MessageWithFlags | x.is_int_msgfl() || x.is_event_msgfl() witness *

  datatype RawReserveFlags =
    rawreserve_exact |      // 0x0
    // rawreserve_all_except | // 0x1, 0x3
    rawreserve_at_most     // up_to 0x2    /tvm/message_flags.hpp:23

  const rawreserve_flag_upto:RawReserveFlags := rawreserve_at_most();

  datatype Action =
    Action_SendMessage(id: nat, msg: MessageWithFlagsIE) |
    Action_RawReserve(id: nat, value: Grams, flags: RawReserveFlags)

  type SendAction = x:Action | x.Action_SendMessage? witness *
  type SendAllBalanceAction = x:SendAction | x.msg.is_int_msgfl() && x.msg.has_msg_flag(SENDMSG_ALL_BALANCE) witness *

  datatype AccountStatus =
    Uninit |
    Active |
    Frozen

  datatype Account =
    Account(balance: int, status: AccountStatus, state_init: option<StateInit>)

  function method tvm_hash(c: cell): uint256

  lemma perfect_hash_hypothesis()
    ensures forall c1,c2 ::
    tvm_hash(c1) == tvm_hash(c2) <==> c1 == c2

  // hdr here refers to message header structure defined in:
  //./cpp-sdk/tvm/persistent_data_header.hpp
  // We do not use headers machinery here explicitely, so we
  // put None there, but leave the argument for greater
  // similarity with the original Flex code.
  function method prepare_persistent_data<T(!new)>(hdr: option<cell>, base: T): cell

  lemma prepare_persistent_data_bijection<T(!new)>()
    ensures forall hdr1,hdr2,base1:T,base2:T ::
    prepare_persistent_data(hdr1,base1) ==
    prepare_persistent_data(hdr2,base2) <==>
    hdr1 == hdr2 && base1 == base2

  function method build_make_cell<T(!new)>(s: T): cell

  lemma build_make_cell_bijection<T(!new)>()
    ensures forall s1:T, s2:T ::
    build_make_cell(s1) == build_make_cell(s2) <==> s1 == s2

}
