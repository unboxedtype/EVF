// **ORD01**. If  a user sends an  order to buy  (or sell) n tokens  with the
// price p  and a lifetime T  , supplying all necessary  parameters, then
// such an order will either be processed immediately or will be placed in
// the  queue after  partial processing  or will  be placed  in the  queue
// without processing.

//------------------------
//Formalisation:

// Two cases - for buy and for sell - has to be verified separately.

// CASE 1. BUY ORDER

// - The FlexClient smart-contract has been successfully deployed.
//
// - The FlexClient::setFlexWalletCode(..) has been successfully called.
//
// - The FlexClient::deployPriceWithBuy(...) has been successfully called.
//   As a result, one outbound internal message is generated, we call it
//   m1.
//
// - After the message m1 is processed by uninit Price SmC, the
//   smart-contract is sucessfully deployed and the user BUY order
//   is either get matched immediately or stay in the queue.

include "FlexClient.dfy"
include "Price.dfy"

import opened FlexClientModule
import opened PriceModule
import opened BaseTypes
import opened ErrorCodes
import opened FlexTypes

method ORD01_property()
{
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
  // 2. Call setFlexWalletCode API to put the code for
  //    Flex Wallet, otherwise the deployPriceWithBuy
  //    wiil fail.
  /*******************************************************/
  var flex_code := *;
  body := call(setFlexWalletCode(flex_code));
  hdr := ExtMsgHdr(fc_addr, owner_pk);
  assume (fc.balance >= storage_fee);
  r := fc.msg_dispatcher(OrdinaryMessage(hdr, Value(body)));
  assert (r == Success);
  assert (fc.st.flex_wallet_code_.has_val());

  var price, amount, order_finish_time, min_amount, deals_limit,
    deploy_value, price_code, my_tip3_addr, tip3cfg := *, *, *, *, *, *, *, *, *;

  /*******************************************************/
  // 3. Call deployPriceWithBuy with some arbitrary (any)
  //    parameters.
  /*******************************************************/
  body := call(deployPriceWithBuy(price, amount, order_finish_time,
    min_amount, deals_limit, deploy_value, price_code, my_tip3_addr, tip3cfg));
  hdr := ExtMsgHdr(fc_addr, owner_pk);
  var buyMsg := OrdinaryMessage(hdr, Value(body));
  assume (fc.balance >= addL([storage_fee, deploy_value, msg_send_fee, msg_send_fee]));
  assume (fc.constructed);
  assume (fc.status == Active);
  assert (owner_pk == fc.st.owner_);
  r := fc.msg_dispatcher(buyMsg);
  assert (r == Success);
  assert (fc.int_msg_queue[0].msg.msg.is_msg_deployCall());

  /*******************************************************/
  // 4. Process the Price outbound deployCall message.
  /*******************************************************/
  var pr_msg := fc.int_msg_queue[0].msg.msg;
  var pr_init := pr_msg.body.val.init;
  var pr_addr := pr_msg.info.dest;
  assert (pr_msg.info.src == fc_addr);
  var pr_bal:uint128 := 0;
  var pr :=
    new PriceModule.TONContract(pr_init, pr_addr, pr_bal);
  r := pr.msg_dispatcher(pr_msg);

  // This will  not verify, because  right now,  there are some  errors in
  // Price smart-contract, that are still not fixed, so we did'nt derived
  // the weakest precondition for it.
  
  assert {:error "this will not verify and for the good reason."}
    (r == Success);
  // assert (ord in pr.queue);
}
