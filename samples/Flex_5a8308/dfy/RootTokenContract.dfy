include "../../../src/TONContract.dfy"
include "../../../src/MapToSeq.dfy"

include "FlexTypes.dfy"
include "TONTokenWallet.dfy"

module RootTokenContractModule refines TONModule
{
  import opened T = FlexTypes
  import TONTokenWalletModule

  class ContractStateVariables ...
  {
    var name_:string;
    var symbol_:string;
    var decimals_:uint8;
    var root_public_key_:uint256;
    var total_supply_: uint128;
    var total_granted_: uint128;
    var wallet_code_: optcell;
    var owner_address_: option<address>;
    var start_balance_: Grams;
  }

  class TONContract ...
  {
    const wallet_hash:unsigned := 0x7725a0815bada71953072fc17409af23b26e521e768e686a50d8658dd9dfe11f;

    const error_code_message_sender_is_not_my_owner:unsigned := 100;
    const error_code_not_enough_balance:unsigned := 101;
    const error_code_wrong_bounced_header:unsigned := 102;
    const error_code_wrong_bounced_args:unsigned := 103;
    const error_code_internal_owner_enabled:unsigned := 104;
    const error_code_internal_owner_disabled:unsigned := 105;
    const error_code_define_pubkey_or_internal_owner:unsigned := 106;
    const error_code_wrong_wallet_code_hash:unsigned := 107;
    const error_code_cant_override_wallet_code:unsigned := 108;
    const error_code_too_big_decimals:unsigned := 109;

    // https://github.com/tonlabs/flex/issues/29
    const error_code_wallet_code_not_initialized:unsigned := 110;

    predicate constructor_post ...
    {
      true
    }

    // [[internal, external, dyn_chain_parse]]
    method execute_constructor() returns (r:Status)
    {
      var ctor := msg().body.val.ctor;
      if (ctor.RootTokenContract?) {
        var RootTokenContract(name, sym, decimals, root_public_key, root_owner, total_supply) := ctor;
        :- require(root_public_key != 0 || root_owner.id != 0 , error_code_define_pubkey_or_internal_owner);
        :- require(decimals < 4, error_code_too_big_decimals);

        st.name_ := name;
        st.symbol_ := sym;
        st.decimals_ := decimals;
        st.root_public_key_ := root_public_key;
        st.total_supply_ := total_supply;
        st.total_granted_ := 0;
        st.owner_address_ := optional_owner(root_owner);
        st.start_balance_ := tvm_balance();
        return Success;
      }
      return Failure(UnknownFunctionId);
    }

    // [[internal, external, noaccept, dyn_chain_parse, answer_id]]
    method setWalletCode(wallet_code: cell) returns (s: Status)
      requires internal_message()
      modifies st`wallet_code_
      modifies `action_queue, `deferred_queue, `act_last, `act_counter
      modifies `return_flag
    {
      :- check_owner();
      tvm_accept();
      :- require(!st.wallet_code_.has_val(), error_code_cant_override_wallet_code);
      :- require(builtin_tvm_hashcu(wallet_code) == wallet_hash,
        error_code_wrong_wallet_code_hash);
      st.wallet_code_ := Value(wallet_code);

      if (Internal()) {
        var value_gr :- int_value();
        assume (tvm_balance() > value_gr);
        tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
        set_int_return_flag(SEND_ALL_GAS);
      }
      TON_CPP_return(returnSetWalletCode(true));
      return Success;
    }

    // [[internal, external, noaccept, dyn_chain_parse, answer_id]]
    method deployWallet(pubkey: uint256, internal_owner: address,
      tokens: uint128, grams: uint128)
      returns (s:Status)
      requires message_opt.has_val()
      modifies `action_queue, `act_last, `act_counter, `deferred_queue
    {
      :- check_owner();
      tvm_accept();
      :- require(add(st.total_granted_, tokens) <= st.total_supply_,
        error_code_not_enough_balance);
      :- require(pubkey != 0 || internal_owner.id != 0,
        error_code_define_pubkey_or_internal_owner);
      // see issue: https://github.com/tonlabs/flex/issues/29
      :- require(st.wallet_code_.has_val(),
        error_code_wallet_code_not_initialized);

      var answer_addr: address;

      if (Internal()) {
        var value_gr :- int_value();
        assume (tvm_balance() > value_gr);
        tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
        answer_addr :- int_sender();
      }
      else {
        answer_addr := tvm_myaddr();
      }

      var wallet_init, dest := calc_wallet_init(pubkey, internal_owner);
      var dest_handle := dest; // ITONTokenWalletPtr
      var answer_id_opt := return_func_id_opt;
      var answer_addr_opt := Value(return_address);

      assume (dest_handle == calc_address_from_stateinit(wallet_init));

      deploy_call(dest_handle, grams, wallet_init,
        TONTokenWallet(), accept(tokens, answer_addr, grams),
        TON_CPP_DEFAULT_MSG_FLAGS, true, true,
        answer_id_opt, answer_addr_opt);
    }

    // [[internal, noaccept, dyn_chain_parse, answer_id]]
    method deployEmptyWallet(pubkey:uint256, internal_owner:address, grams:uint128)
      returns (s:Status)
      requires internal_message()
      modifies `action_queue, `deferred_queue, `act_last, `act_counter
      modifies `return_flag
    {
      :- require(pubkey != 0 || internal_owner.id != 0,
        error_code_define_pubkey_or_internal_owner);

      // see issue: https://github.com/tonlabs/flex/issues/29
      :- require(st.wallet_code_.has_val(),
        error_code_wallet_code_not_initialized);

      var value_gr :- int_value();
      // coins are on the balance already
      assume (tvm_balance() >= value_gr);
      tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
      var wallet_init, dest := calc_wallet_init(pubkey, internal_owner);
      var dest_handle := dest; // ITONTokenWalletPtr

      assume (dest_handle == calc_address_from_stateinit(wallet_init));
      deploy_noop(dest_handle, grams, wallet_init, TONTokenWallet());

      set_int_return_flag(SEND_ALL_GAS);

      TON_CPP_return(returnDeployEmptyWallet(dest));

      return Success;
    }


    // [[internal, external, noaccept, dyn_chain_parse, answer_id]]
    method grant(dest:address, tokens:uint128, grams:uint128)
      returns (s:Status)
      modifies st`total_granted_
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
    {
      :- check_owner();
      :- require(add(st.total_granted_, tokens) <= st.total_supply_,
        error_code_not_enough_balance);

      tvm_accept();

      var grams1 := grams;
      var answer_addr: address;
      var msg_flags := SENDMSG_ORDINARY; // = 0

      if (Internal()) {
        var value_gr :- int_value();
        assume (tvm_balance() >= value_gr);
        tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
        msg_flags := SEND_ALL_GAS;
        grams1 := 0;
        answer_addr :- int_sender();
      }
      else {
        answer_addr := tvm_myaddr();
      }

      var dest_handle := dest; // ITONTokenWalletPtr
      method_call(dest_handle, grams1, accept(tokens, answer_addr, 0),
        msg_flags);

      st.total_granted_ := add(st.total_granted_, tokens);

      return Success;
    }

    // [[internal, external, noaccept, dyn_chain_parse, answer_id]]
    method mint(tokens:uint128) returns (s:Status)
      requires message_opt.has_val()
      modifies st`total_supply_
      modifies `action_queue, `deferred_queue, `act_last , `act_counter
      modifies `return_flag
    {
      :- check_owner();

      tvm_accept();

      if (Internal()) {
        var value_gr :- int_value();
        assume (tvm_balance() >= value_gr);
        tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
      }

      st.total_supply_ := add(st.total_supply_, tokens);

      set_int_return_flag(SEND_ALL_GAS);
      TON_CPP_return(returnMint(true));

      return Success;
    }

    // [[internal, noaccept, answer_id]]

    method requestTotalGranted()
      returns (s:Status)
      requires internal_message()
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
      modifies `return_flag
    {
      var value_gr :- int_value();
      assume (tvm_balance() >= value_gr);
      tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
      set_int_return_flag(SEND_ALL_GAS);
      TON_CPP_return(returnRequestTotalGranted(st.total_granted_));
      return Success;
    }

    method calc_wallet_init(pubkey:uint256, owner_addr:address)
      returns (state_init:StateInit, addr:address)
      // see issue: https://github.com/tonlabs/flex/issues/29
      requires st.wallet_code_.has_val()
    {
      var wallet_data :=
        TONTokenWalletModule.prepare_wallet_data(
        st.name_, st.symbol_, st.decimals_,
        st.root_public_key_, pubkey, tvm_myaddr(),
        optional_owner(owner_addr),
        st.wallet_code_.val, workchain_id());
      var wallet_init, dest_addr := TONTokenWalletModule.prepare_wallet_state_init_and_addr(wallet_data);
      var dest := address.make_std(workchain_id(), dest_addr);
      return wallet_init, dest;
    }

    function method workchain_id():int8
    {
      tvm_myaddr().workchain_id
    }

    predicate method is_internal_owner()
      reads `st, st`owner_address_
    {
      st.owner_address_.has_val()
    }

    method check_internal_owner()
      returns (s: Status)
      requires message_opt.has_val()
    {
      :- require(is_internal_owner(),
        error_code_internal_owner_disabled);
      var sender :- int_sender();
      :- require(st.owner_address_.val == sender,
        error_code_message_sender_is_not_my_owner);
    }

    method check_external_owner()
      returns (s:Status)
    {
      :- require( !is_internal_owner(),
        error_code_internal_owner_enabled);
      :- require( msg_pubkey() == st.root_public_key_,
        error_code_message_sender_is_not_my_owner);
    }

    method check_owner()
      returns (s:Status)
    {
      if (Internal()) {
        :- check_internal_owner();
      }
      else {
        :- check_external_owner();
      }
    }

    predicate method Internal()
      reads `message_opt
    {
      message_opt.has_val() && message_opt.val.is_msg_int()
    }

    function method optional_owner(owner: address): option<address>
    {
      if (owner.id != 0) then Value(owner) else None
    }

  }
}
