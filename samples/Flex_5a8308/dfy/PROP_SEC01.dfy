/***
**SEC01.**
If a user sends  request to create a Trading Pair  P attaching M coins
to  their request,  and specifying  the correct  TIP3-compatible Token
address, then  the trading pair  P will  be added into  the securities
list and  the user  will be  provided the  identifier of  this trading
pair. The following inequality must hold:

               M >= DeployValue

where DeployValue  is a  special parameter that  is provided  into the
Trading Pair depending on the life time chosen for this trading pair.

------------------------
Formalisation:

1) The FlexClient smart-contract has been successfully deployed.
2) After the FlexClient::deployTradingPair(tip3Root,minValue) successful call,
 the following holds:
 - one external outbound message {trade_pair, TPAddr} is generated (event)
 - one internal outbound  message {create,  TPAddr, TPBody}  is
   generated,
    where:
  - TPAddr is the address of a trade pair
  - TPBody is the TVC body of the TradePair contract
  - the constructor call of TradingPair will succeed at the time of a call

3) The newly generated outobund message is successfuly processed by
   the node.

4) The newly created TradingPair SmC returns change by sending the
   return message attaching ~ (M - DeployValue) coins to it.
   After delivery, the return message is successfuly processed by
   a FlexClient SmC, and its balance is indeed increased.
 ***/

include "FlexClient.dfy"
include "TradingPair.dfy"

import opened FlexClientModule
import opened TradingPairModule
import opened BaseTypes
import opened ErrorCodes
import opened FlexTypes

method SEC01_property()
{
  /* Create blockchain and an account with some coins */
  var fc_init := StateInit_FlexClient();
  var fc_addr := calc_address_from_stateinit(fc_init);

  /*******************************************************/
  // 1. Deploy the FlexClient SmC using external deploy msg
  /*******************************************************/
  var owner_pk := *; //
  assume (owner_pk != 0);
  var tp_code := *;
  var ep_code := *; // any exchg pair code
  var hdr := ExtMsgHdr(fc_addr, owner_pk);
  var ctor := FlexClient(owner_pk, tp_code, ep_code);
  var body := deploy(fc_init, ctor);
  var deployFCMsg := OrdinaryMessage(hdr, Value(body));
  var fc :=
    new FlexClientModule.TONContract(fc_init, fc_addr, msg_fee_value(deployFCMsg) );
  var r := fc.msg_dispatcher(deployFCMsg);
  assert (r == Success);
  assert (fc.st.owner_ == owner_pk);
  assert (fc.address_this == fc_addr);


  /*******************************************************/
  // 2. Call deployTradingPair method in the FlexClient
  /*******************************************************/
  var pk1 := owner_pk; //
  var tp_addr := *;
  var deploy_min_value := *; // the minimum amount of coins that the TP is going
  // to accept for successful construction
  var deploy_value := *; // amount of coins attached to new TP message
  assume (deploy_value > deploy_min_value);
  var min_trade_amount := *;
  var deployTPBody :=
    call(deployTradingPair(tp_addr, deploy_min_value, deploy_value, min_trade_amount));
  var deployTradingPairMsg :=
    OrdinaryMessage(ExtMsgHdr(fc_addr, pk1), Value(deployTPBody));
  var dm := deployTradingPairMsg;
  assume {:fuel addL,5} // unfolding depth
    (fc.balance >=
     addL([storage_fee, deploy_value, msg_send_fee, msg_send_fee]));
  r := fc.msg_dispatcher(dm);
  assert (r == Success);
  assert (fc.address_this == fc_addr);

  /*******************************************************/
  // 3. Process the deploy TradingPair message that was generated
  // by the FlexCLient
  /*******************************************************/
  var td_msg := fc.int_msg_queue[0].msg.msg;
  var td_init := td_msg.body.val.init;
  var td_addr := td_msg.info.dest;
  assert (td_msg.info.src == fc_addr);
  var td_bal:uint128 := *;
  var td :=
    new TradingPairModule.TONContract(td_init, td_addr, td_bal);
  // // assume (dest != fc_addr);
  // // assume (blk.get_status(td_msg.info.dest) == Uninit);
  var Action_SendMessage(_, MessageWithFlags(msg2,_)) := fc.int_msg_queue[0];
  // Processing constructor message will succeed
  assume (td_msg.body.val.cm.min_amount > 0);
  r := td.msg_dispatcher(td_msg);
  assert (r == Success);
  assert (|td.int_msg_queue| == 1);

  /*******************************************************/
  // 4. TradingPair returns change by sending the answer.
  // Process this message and check that change has been
  // returned indeed.
  /*******************************************************/
  var ret_msg := td.int_msg_queue[0].msg.msg;
  assert (ret_msg.is_msg_return());
  assert (ret_msg.info.dest == fc_addr);
  var reserve_value :=
    min(td_msg.body.val.cm.deploy_value, td.g_action_balance);
  assert (ret_msg.info.value == td.g_action_balance - reserve_value);
  assume (fc.balance >= storage_fee);
  assume (fc.status == Active);
  var old_fc_balance := fc.balance;
  r := fc.msg_dispatcher(ret_msg);
  assert (r == Success);
  /* Check that the balance is increased indeed. */
  var expected := sub(add(old_fc_balance, ret_msg.info.value), storage_fee);
  assert (fc.balance == expected);
}
