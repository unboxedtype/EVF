/***
**SEC04.**
 The securities list can change over time: trading pairs may come
 and go, depending on their lifetime.

------------------------
Formalisation:
 If the balance of an  SmC becomes insufficient to cover storage_phase
 expenses, then  it becomes frozen -  it is no longer  operable. After
 some more  time, it is  deleted from  the blockchain. After  that, in
 case of a need, the same Trading Pair SmC could be redeployed.

 We do not model the freeze of an account and its deletion, so we reduce
 this property to the fact that equal state inits will give you the
 same SmC addresses.

 It is a special case of the PROP_SEC03.
 ***/

include "FlexClient.dfy"
include "TradingPair.dfy"

import opened FlexClientModule
import opened TradingPairModule
import opened BaseTypes
import opened FlexTypes

method SEC04_property()
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
  assert (td1_init == td2_init ==> td1_addr == td2_addr);
}
