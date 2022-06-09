/***
**SEC02.**
If an error happens during the trading pair creation, the user is
provided with the error code and the remaining coins initially sent
with the request.

------------------------

Formalisation:

Looking more closely, the failure way happen at least in two places:
on the FlexClient side - during the deployTradingPair call, and on
the TradingPair side, during the deployment with onDeploy call.
So we have to consider both scenarios and distinguish their outcomes.

Scenario 1
----------
1) The FlexClient smart-contract has been successfully deployed.
2) After the FlexClient::deployTradingPair(tip3Root,minValue) failed call,
 the following holds:
 - no messages is generated in this case.

Scenario 2
----------
1) The FlexClient smart-contract has been successfully deployed.
2) FlexClient::deployTradingPair(tip3Root,minValue) call succeed.
3) During the deployWithCall message processing, some error happens,
 and, after that, the following holds:
 - Bounce message is generated carrying the original message value minus
   storage_fee.
 ***/

include "FlexClient.dfy"
include "TradingPair.dfy"

import opened FlexClientModule
import opened TradingPairModule
import opened BaseTypes
import opened ErrorCodes
import opened FlexTypes

method SEC02_scenario1()
{
  /* Create blockchain and an account with some coins */
  var fc_init := StateInit_FlexClient();
  var fc_addr := calc_address_from_stateinit(fc_init);

  /* Send external deploy message with FlexClient SmC */
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

  /* Send external deployTradingPair message into the FlexClient SmC */
  var pk1 := *; // owner_pk; //
  var tp_addr := *;
  var deploy_min_value := *; // the minimum amount of coins that the TP is going
  // to accept for successful construction
  var deploy_value := *; // amount of coins attached to new TP message
  var min_trade_amount := *;
  var deployTPBody :=
    call(deployTradingPair(tp_addr, deploy_min_value, deploy_value, min_trade_amount));
  var deployTradingPairMsg :=
    OrdinaryMessage(ExtMsgHdr(fc_addr, pk1), Value(deployTPBody));
  var dm := deployTradingPairMsg;
  assert (fc.status == Active);
  r := fc.msg_dispatcher(dm);
  assume (r != Success);
  assert (fc.int_msg_queue == []);
  assert (fc.bounced_msg_opt == None);
}

method SEC02_scenario2()
{
  /* Create blockchain and an account with some coins */
  var fc_init := StateInit_FlexClient();
  var fc_addr := calc_address_from_stateinit(fc_init);

  /* Send external deploy message with FlexClient SmC */
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

  /* Send external deployTradingPair message into the FlexClient SmC */
  var pk1 := owner_pk; //
  var tp_addr := *;
  var deploy_min_value := *; // the minimum amount of coins that the TP is going
  // to accept for successful construction
  var deploy_value := *; // amount of coins attached to new TP message
  var min_trade_amount := *;
  var deployTPBody :=
    call(deployTradingPair(tp_addr, deploy_min_value, deploy_value, min_trade_amount));
  var deployTradingPairMsg :=
    OrdinaryMessage(ExtMsgHdr(fc_addr, pk1), Value(deployTPBody));
  var dm := deployTradingPairMsg;
  assert (fc.status == Active);
  r := fc.msg_dispatcher(dm);
  assume (r == Success);

  /* Process the outbound internal message to create a Trading Pair contract */
  /* message from FlexClient into TradingPair (non-existent, maybe) */
  var td_msg := fc.int_msg_queue[0].msg.msg;
  var td_init := td_msg.body.val.init;
  var td_addr := td_msg.info.dest;
  assert (td_msg.info.src == fc_addr);
  assert (td_msg.info.bounce);
  var td_bal:uint128 := *;
  var td :=
    new TradingPairModule.TONContract(td_init, td_addr, td_bal);
  var Action_SendMessage(_, MessageWithFlags(msg2,_)) := fc.int_msg_queue[0];
  r := td.msg_dispatcher(td_msg);
  assume (r != Success && r != Failure(ComputePhaseSkipped));
  assert (td.bounced_msg_opt.has_val());// here comes the bounce message
  var bmsg := td.bounced_msg_opt.val;
  assert (bmsg.hdr.value == sub(td_msg.info.value, storage_fee));
}
