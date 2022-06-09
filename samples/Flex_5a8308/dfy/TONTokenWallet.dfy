include "../../../src/TONContract.dfy"
include "../../../src/MapToSeq.dfy"

include "FlexTypes.dfy"

// The TONTokenWallet.cpp is compiled with the following macro set:
// -DTIP3_ENABLE_LEND_OWNERSHIP -DTIP3_ENABLE_BURN

module TONTokenWalletModule refines TONModule
{
  import opened T = FlexTypes
  import opened MapToSequenceModule
  import opened TONTokenWalletCommon

  class ContractStateVariables ...
  {
    var name_:string;
    var symbol_:string;
    var decimals_:uint8;
    var balance_:uint128;
    var root_public_key_:uint256;
    var wallet_public_key_:uint256;
    var root_address_:address;
    var owner_address_:option<address>;
    var lend_ownership_: lend_ownership_map;
    var code_:cell;
    var workchain_id_:int8;
  }

  method prepare_internal_wallet_state_init_and_addr(name:string, symbol:string,
    decimals:uint8, root_public_key:uint256, wallet_public_key:uint256,
    root_address:address, owner_address:option<address>, code: cell,
    workchain_id:int8)
    returns (state_init:StateInit, addr:uint256)
  {
    var wallet_data := DTONTokenWallet(name, symbol, decimals, 0,
      root_public_key, wallet_public_key, root_address, owner_address,
      map[], code, workchain_id);
    var wallet_data_cl := prepare_persistent_data(None, wallet_data);
    var wallet_init := StateInit_TONTokenWallet(wallet_data);
    var wallet_init_cl := build_make_cell(wallet_init);
    return wallet_init, tvm_hash(wallet_init_cl);
  }


  method prepare_wallet_state_init_and_addr(wallet_data:DTONTokenWallet)
    returns (st:StateInit, addr_id:uint256)
  {
    var wallet_data_cl:cell := prepare_persistent_data(None, wallet_data);
    var wallet_init := StateInit_TONTokenWallet(wallet_data);
    var wallet_init_cl := build_make_cell(wallet_init);
    addr_id := tvm_hash(wallet_init_cl);
    return wallet_init, addr_id;
  }

  function method prepare_wallet_data(name:string, symbol:string,
    decimals:uint8, root_public_key:uint256, wallet_public_key:uint256,
    root_address:address, owner_address:option<address>, code:cell,
    workchain_id:int8) : DTONTokenWallet
  {
    DTONTokenWallet(name, symbol, decimals, 0, root_public_key,
      wallet_public_key, root_address, owner_address, map[],
      code, workchain_id)
  }


  class TONContract ...
  {
    const min_transfer_costs:unsigned := 150000000;

    // error_codes
    const error_code_message_sender_is_not_my_owner:uint := 100;
    const error_code_not_enough_balance:uint := 101;
    const error_code_message_sender_is_not_root:uint := 102;
    const error_code_message_sender_is_not_good_wallet:uint := 103;
    //...
    const error_code_only_original_owner_allowed:uint := 113;
    const error_code_internal_owner_enabled:uint := 110;
    const error_code_internal_owner_disabled:uint := 111;
    const error_code_wallet_in_lend_ownership:uint := 114;
    const error_code_finish_time_must_be_greater_than_now:uint := 115;
    const error_code_not_enough_tons_to_process:uint := 116;
    const error_code_allowance_is_set:uint := 117;
    const error_code_transfer_to_zero_address:uint := 118;

    // [[internal, noaccept]]
    method transfer(answer_addr: addr_std_compact, to: addr_std_compact, tokens: uint128,
      grams: uint128, return_ownership: bool) returns (s:Status)
      requires internal_message()
      modifies st`lend_ownership_
      modifies `action_queue, `act_counter, `deferred_queue, `act_last
      modifies st`balance_, st`lend_ownership_
    {
      :- transfer_impl(answer_addr, to, tokens, grams, return_ownership, false, 0);
      return Success;
    }

    // requestBalance() comes from the latest master commit.
    // It is absent in the branch that we took for FV.

    // [[internal, noaccept, answer_id]]
    method requestBalance()
      requires internal_message()
      modifies `action_queue, `act_last, `act_counter, `deferred_queue
      modifies `return_flag
    {
      var r0, gr_val := int_value();
      assert (r0 == Success);

      assume (tvm_balance() >= gr_val);
      // message value is always put on the SmC balance, so this is a
      // reasonable assumption.
      tvm_rawreserve(tvm_balance() - gr_val, rawreserve_flag_upto);
      set_int_return_flag(SEND_ALL_GAS);
      TON_CPP_return(returnRequestBalance(st.balance_));
    }

    // [[internal, noaccept, answer_id]]
    method accept(tokens:uint128, answer_addr: address, keep_grams:uint128)
      returns (s:Status)
      requires internal_message()
      modifies st`balance_, `return_address, `return_value, `return_flag
      modifies `action_queue, `act_last, `act_counter, `deferred_queue
    {
      var r0, sender, value_gr := int_sender_and_value();
      assert (r0 == Success);
      :- require(st.root_address_ == sender, error_code_message_sender_is_not_root);
      tvm_accept();

      st.balance_ := add(st.balance_, tokens);
      // message value is always put on the SmC balance, so this is a
      // reasonable assumption.
      assume (tvm_balance() >= value_gr);
      tvm_rawreserve(add(tvm_balance(), keep_grams) - value_gr, rawreserve_flag_upto);
      set_int_return_address(answer_addr); // alias for set_int_sender
      set_int_return_value(0);
      set_int_return_flag(SEND_ALL_GAS | IGNORE_ACTION_ERRORS);

      TON_CPP_return(returnAccept(true));
      return Success;
    }

    // [[internal, noaccept, answer_id]]
    method internalTransfer(tokens:uint128, answer_addr:addr_std_compact,
      sender_pubkey:uint256, sender_owner: addr_std_compact,
      notify_receiver:bool, payload: cell)
      returns (s: Status)
      requires internal_message()
      modifies st`balance_
      modifies `action_queue, `deferred_queue, `act_last, `act_counter
    {
      var expected_address := expected_sender_address(sender_pubkey, sender_owner);
      var sender, value_gr :- int_sender_and_value();

      :- require(sender.id == expected_address,
        error_code_message_sender_is_not_good_wallet);

      // dont be afraid, just add them.
      st.balance_ := add(st.balance_, tokens);

      // int_value() is already on the balance
      assume (tvm_balance() > value_gr);
      tvm_rawreserve(tvm_balance() - value_gr, rawreserve_flag_upto);
      if (notify_receiver && st.owner_address_.has_val()) {
        var answer_id := return_func_id_opt;
        method_call(st.owner_address_.val, 0,
          onTip3Transfer(answer_addr, st.balance_, tokens, sender_pubkey, sender_owner, payload),
          SEND_ALL_GAS, true, true, answer_id, Value(answer_addr));
      }
      else {
        if (answer_addr != tvm_myaddr()) {
          tvm_transfer(answer_addr, 0, false, SEND_ALL_GAS);
        }
      }
    }


    // [[internal, noaccept, answer_id]]
    method burn(out_pubkey:uint256, out_internal_owner:address)
      returns (s:Status)
      requires internal_message()
      modifies st`lend_ownership_
      modifies `action_queue, `deferred_queue, `act_last, `act_counter
    {
      var _ :- check_owner(true, false);
      tvm_accept();
      var root_ptr := st.root_address_;
      var flags := SEND_ALL_GAS | SENDER_WANTS_TO_PAY_FEES_SEPARATELY |
        DELETE_ME_IF_I_AM_EMPTY | IGNORE_ACTION_ERRORS;
      var sender :- int_sender();
      var call := ContractMethod.IWrapper_burn(sender, st.wallet_public_key_,
        get_owner_addr(), out_pubkey, out_internal_owner, getBalance());
      method_call(root_ptr, 0, call, flags);
    }

    function method getBalance(): uint128
      reads `st, st`balance_
    {
      st.balance_
    }

    method expected_sender_address(sender_pk: uint256, sender_owner: address)
      returns (r:uint256)
    {
      var _, addr := calc_wallet_init_hash(sender_pk, sender_owner);
      return addr; // .second
    }

    function method optional_owner(owner: address): option<address>
    {
      if (owner.id != 0) then Value(owner) else None
    }

    method calc_wallet_init_hash(pubkey: uint256, internal_owner:address)
      returns (state_init:StateInit, addr:uint256)
    {
      var wallet_data := prepare_wallet_data(st.name_, st.symbol_,
        st.decimals_, st.root_public_key_, pubkey, st.root_address_,
        optional_owner(internal_owner), st.code_, st.workchain_id_);
      state_init, addr := prepare_wallet_state_init_and_addr(wallet_data);
      return state_init, addr;
    }

    method check_transfer_requires(tokens:uint128, grams:uint128)
      returns (s: Status, v: uint128)
      requires internal_message()
      modifies st`lend_ownership_
    {
      var active_balance :- check_owner(false, false);
      :- require(tokens <= active_balance, error_code_not_enough_balance);

      if (Internal()) {
        var v1:Grams :- int_value();
        :- require(v >= min_transfer_costs as Grams,
          error_code_not_enough_tons_to_process);
      }
      else {
        :- require(grams >= min_transfer_costs as Grams &&
             tvm_balance() > grams,
            error_code_not_enough_tons_to_process);
      }
      return Success, active_balance;
    }

    method update_spent_balance(tokens: uint128, return_ownership: bool)
      returns (s: Status)
      requires message_opt.has_val()
      modifies st`balance_, st`lend_ownership_
    {
      assume (st.balance_ > tokens);
      st.balance_ := st.balance_ - tokens;

      // TIP3_ENABLE_LEND_OWNERSHIP macro is defined for the FlexToken

      if (|st.lend_ownership_| == 0) {
        return Success;
      }
      var sender :- int_sender();
      if (return_ownership) {
        // lend_ownership_.erase(sender);
        // no throw operation
        st.lend_ownership_ := st.lend_ownership_ - {sender};
      }
      else {
        if (sender !in st.lend_ownership_.Keys) {
          var iterator_overflow := 64;
          return Failure(iterator_overflow);
        }
        var v:lend_record := st.lend_ownership_[sender];
        assume (v.lend_balance >= tokens);
        v := v.(lend_balance := v.lend_balance - tokens);
        if (v.lend_balance == 0) {
          // lend_ownership_.erase(sender);
          // no throw operation
          st.lend_ownership_ := st.lend_ownership_ - {sender};
        }
        else {
          // see https://github.com/tonlabs/flex/issues/28
          st.lend_ownership_ := st.lend_ownership_[sender := v];
        }
      }
    }

    method transfer_impl(answer_addr: addr_std_compact,
      to: addr_std_compact, tokens: uint128,
      grams: uint128, return_ownership: bool,
      send_notify: bool, payload: cell)
      returns (s: Status)
      requires internal_message()
      modifies st`lend_ownership_
      modifies `action_queue, `act_counter, `deferred_queue, `act_last
      modifies st`balance_, st`lend_ownership_
    {
      var active_balance :- check_transfer_requires(tokens, grams);
      :- require(to.id != 0, error_code_transfer_to_zero_address);
      tvm_accept();

      var answer_addr_fxd :- fixup_answer_addr(answer_addr);

      var grams1, msg_flags := prepare_transfer_message_flags(grams);
      // grams := grams1;
      var dest_wallet := to; // ITONTokenWalletPtr
      var call :=
        // we need fully qualified name because we have a method
        // with the same name in the class.
        ContractMethod.internalTransfer(tokens, answer_addr_fxd,
        st.wallet_public_key_, get_owner_addr(), send_notify, payload);
      method_call(dest_wallet, grams1, call, msg_flags);
      :- update_spent_balance(tokens, return_ownership);
      return Success;
    }

    predicate method Internal()
      reads `message_opt
    {
      message_opt.has_val() && message_opt.val.is_msg_int()
    }

    function method get_owner_addr(): address
      reads `st, st`owner_address_
    {
      if st.owner_address_.has_val() then
        st.owner_address_.val
      else
        address.Default()
    }

    function method is_internal_owner(): bool
      reads `st, st`owner_address_
    {
      st.owner_address_.has_val()
    }

    predicate method addr_order(a:address, b:address)
    { a.to_nat() <= b.to_nat() }

    method filter_lend_ownerhip_map() returns (rv1:lend_ownership_map, lend_balance1:uint128)
      modifies st`lend_ownership_
    {
      if (|st.lend_ownership_| == 0) {
        return map[], 0;
      }
      var now_v := tvm_now();
      var rv:lend_ownership_map := map[]; //default TON C++ map constructor
      var lend_balance:uint128 := 0; // default TON C++ uint128_t constructor
      var los := MapToSequence(st.lend_ownership_, addr_order);
      // Move all unexpired records into rv map.
      // Accumulate all balances of all unexpired records in the lend_balance.
      for i := 0 to |los|-1 {
        var v := los[i]; // tuple, (key,value)
        assume (now_v as nat < MAX_UINT32_NAT);
        if (now_v as uint32 < v.1.lend_finish_time) {
          rv := rv[v.0 := v.1]; // rv.insert(v);
          lend_balance := add(lend_balance, v.1.lend_balance);
        }
      }
      st.lend_ownership_ := rv;
      return rv, lend_balance;
    }

    method check_external_owner() returns (r:Status, b:uint128)
      modifies st`lend_ownership_
    {
      :- require(!is_internal_owner(),
        error_code_internal_owner_enabled);
      :- require(msg_pubkey() == st.wallet_public_key_,
        error_code_message_sender_is_not_my_owner);
      tvm_accept();
      var filtered_map, actual_lend_balance := filter_lend_ownerhip_map();
      :- require(|filtered_map| == 0, error_code_wallet_in_lend_ownership);
      return Success, st.balance_;
    }

    method check_owner(original_owner_only:bool, allowed_in_lend_state:bool)
      returns (r:Status, b:uint128)
      requires internal_message()
      modifies st`lend_ownership_
    {
      if (Internal()) {
        b :- check_internal_owner(original_owner_only,
          allowed_in_lend_state);
      } else {
        b :- check_external_owner();
      }
      return Success, b;
    }

    method fixup_answer_addr(answer_addr:addr_std_compact) returns (r:Status, a:address)
      ensures r== Success
    {
      a := answer_addr;
      if (answer_addr == address.Default()) {
        if (Internal()) {
          a :- int_sender();
        }
        else {
          a := tvm_myaddr();
        }
      }
      return Success, a;
    }

    // original_owner_only - methods only allowed to call by original owner (no lend)
    // allowed_for_original_owner_in_lend_state - methods allowed to call by original owner in lend state
    method check_internal_owner(original_owner_only:bool, allowed_for_original_owner_in_lend_state:bool)
      returns (r:Status,b:uint128)
      /* CIO.PRE.1 */
      requires internal_message()
      modifies st`lend_ownership_
    {
      var filtered_map, actual_lend_balance := filter_lend_ownerhip_map();
      if (actual_lend_balance > 0) {
        if (allowed_for_original_owner_in_lend_state) {
          :- require(is_internal_owner(), error_code_internal_owner_disabled);
          var _, sender := int_sender(); // always succeeds here due to CIO.PRE.1
          if (st.owner_address_ == Value(sender)) {
            // The hypothesis here is that the total lending amount (for all lends)
            // is less that the actual balance.
            assume (st.balance_ >= actual_lend_balance);
            return Success, st.balance_ - actual_lend_balance;
          }
        }
        :- require(!original_owner_only, error_code_only_original_owner_allowed);
        var src :- int_sender();
        var has_elem := src in filtered_map;
        // require(!!elem, error_code::message_sender_is_not_my_owner);
        :- require(has_elem, error_code_message_sender_is_not_my_owner);
        var elem := filtered_map[src]; // filtered_map.lookup(int_sender())
        return Success, min(st.balance_, elem.lend_balance);
      }
      else {
        :- require(is_internal_owner(), error_code_internal_owner_disabled);
        var sender: address;
        sender :- int_sender();
        assert (is_internal_owner());
        :- require(st.owner_address_ == Value(sender),
          error_code_message_sender_is_not_my_owner);
        return Success, st.balance_;
      }
    }

    /* Grams is passed by reference, so it must be updated after
     the call. */
    method prepare_transfer_message_flags(/* REF */ grams:Grams)
      returns (g:Grams, msg_flags:MsgFlags)
      requires internal_message()
      modifies `action_queue, `act_counter
    {
      msg_flags := IGNORE_ACTION_ERRORS;
      if Internal() {
        var _, val := int_value();
        //!OVERFLOW CHECK
        assume (tvm_balance() >= val);
        tvm_rawreserve(tvm_balance() - val, rawreserve_flag_upto);
        msg_flags := SEND_ALL_GAS;
        g := 0;
      }
      return g, msg_flags;
    }

    // [[internal, noaccept, answer_id]]
    method lendOwnership(
      answer_addr:addr_std_compact,
      grams:uint128,
      std_dest:uint256,
      lend_balance:uint128,
      lend_finish_time:uint32, // is it enough?
      deploy_init_cl:option<StateInit>, // originally, StateInit is serialized into cell here.
      payload:cell) returns (r:Status)
      requires internal_message()
      modifies st`lend_ownership_
      modifies `action_queue, `deferred_queue, `act_counter, `act_last
    {
      var allowed_balance :- check_owner(true, true);
      :- require(lend_balance > 0 && lend_balance <= allowed_balance,
        error_code_not_enough_balance);
      assume (tvm_now() as nat < MAX_UINT32_NAT);
      :- require(lend_finish_time > tvm_now() as uint32,
        error_code_finish_time_must_be_greater_than_now);
      tvm_accept();
      var answer_addr_fxd :- fixup_answer_addr(answer_addr);
      var dest := address.make_std(st.workchain_id_, std_dest);
      st.lend_ownership_ := st.lend_ownership_[dest := lend_record(lend_balance, lend_finish_time)]; // small_dict.set_at(K,V)
      var deploy_init := deploy_init_cl; // parse<StateInit>(deploy_init_cl.ctos())
      var grams1, msg_flags := prepare_transfer_message_flags(grams); // REF grams
      if (deploy_init.has_val()) {
        var owner_addr := get_owner_addr();
        var call := onTip3LendOwnership(answer_addr_fxd, lend_balance,
          lend_finish_time, st.wallet_public_key_, owner_addr, payload);
        assume (dest == calc_address_from_stateinit(deploy_init.val));
        deploy_call(dest, grams1, deploy_init.val, Price, call,
          msg_flags, true, false /*ihr*/, return_func_id_opt,
          Value(answer_addr_fxd));
      }
      else {
        var owner_addr := get_owner_addr();
        var call := onTip3LendOwnership(answer_addr_fxd, lend_balance,
          lend_finish_time, st.wallet_public_key_, owner_addr, payload);
        method_call(dest, grams, call, msg_flags, true, false /*ihr*/,
          return_func_id_opt, Value(answer_addr_fxd));
      }
    }


    // [[internal, noaccept, answer_id]]
    method returnOwnership() returns (s: Status)
      requires internal_message()
      modifies st`lend_ownership_
    {
      var _ :- check_owner(false, false);

      // lend_ownership_.erase(int_sender());
      var sender :- int_sender();
      st.lend_ownership_ := st.lend_ownership_ - {sender};

      return Success;
    }
  }
}
