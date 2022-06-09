/***
**SEC03.**
 For every token  that is traded, there  must be only one  item in the
 security list.

------------------------
Formalisation:
 Each   traded   token   must   be  represented   as   a   TradingPair
 smart-contract.   We have  to show  that  it is  impossible that  two
 distinct active TradingPair smart contracts  point to the same traded
 token.

 - If two  TradingPair smart-contracts point  to the same  token, then
   they must be the same (their Code+StateInits are the same)
 ***/

include "FlexClient.dfy"
include "TradingPair.dfy"

import opened FlexClientModule
import opened TradingPairModule
import opened BaseTypes
import opened FlexTypes

method SEC03_property()
{
  var td1_init := *;
  var td1_addr := *;
  var td1_bal:uint128 := *;
  // the assumption below is a precondition for any SmC constructor
  assume (td1_addr == calc_address_from_stateinit(td1_init));
  var td1 :=
    new TradingPairModule.TONContract(td1_init, td1_addr, td1_bal);

  var td2_init := *;
  var td2_addr := *;
  var td2_bal:uint128 := *;
  // the assumption below is a precondition for any SmC constructor
  assume (td2_addr == calc_address_from_stateinit(td2_init));
  var td2 :=
    new TradingPairModule.TONContract(td2_init, td2_addr, td2_bal);

  /* Due to bijectivity of the calc_address_from_stateinit() function,
   we are able to conclude the needed statement. */
  calc_address_from_stateinit_bijection<StateInit>();
  assert (td1_addr == td2_addr <==> td1_init == td2_init);
  assert (td1_addr != td2_addr <==> td1_init != td2_init);
}
