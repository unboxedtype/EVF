include "../../../src/TONTypes.dfy"

include "PriceCommon.dfy"
include "TONTokenWalletCommon.dfy"

module FlexTypes refines TONTypes
{
  import opened PriceCommon
  import opened TONTokenWalletCommon
  import opened Flex

  datatype ConstructorMethod =
    | FlexClient(
        pubkey: uint256,
        trading_pair_code: cell,
        xchg_pair_code: cell
      )

    | TradingPair()

    | XchgPair()

    | Price()

    | PriceXchg()

    | TONTokenWallet()

    | RootTokenContract(
        name:string,
        symbol:string,
        decimals:uint8,
        root_pubkey:uint256,
        root_owner: address,
        total_supply:uint128
      )

  datatype ContractMethod =
    // ----------------------------------------------------------
    // IFlexClient interface methods
    // ----------------------------------------------------------
    | deployTradingPair(
        tip3_root: addr_std_compact,
        deploy_min_value: uint128,
        deploy_value: uint128,
        min_trade_amount: uint128
      )

    | deployXchgPair(
        tip3_major_root: addr_std_compact,
        tip3_minor_root: addr_std_compact,
        deploy_min_value: uint128,
        deploy_value: uint128,
        min_trade_amount: uint128
      )

    | deployPriceWithSell(
        price:uint128,
        amount:uint128,
        lend_finish_time:uint32,
        min_amount:uint128,
        deals_limit:uint8,
        tons_value:uint128,
        price_code:cell,
        my_tip3_addr:addr_std_compact,
        receive_wallet:addr_std_compact,
        tip3cfg:Tip3Config
      )

    | deployPriceWithBuy(
        price:uint128,
        amount:uint128,
        order_finish_time: uint32,
        min_amount: uint128,
        deals_limit: uint8,
        deploy_value: uint128,
        price_code: cell,
        my_tip3_addr: address,
        tip3cfg: Tip3Config
      )

    | cancelSellOrder(
        price:uint128,
        min_amount:uint128,
        deals_limit:uint8,
        value:uint128,
        price_code:cell,
        tip3cfg: Tip3Config
      )

    | cancelBuyOrder(
        price:uint128,
        min_amount:uint128,
        deals_limit:uint8,
        value:uint128,
        price_code:cell,
        tip3cfg: Tip3Config
      )

    | cancelXchgOrder(
        sell: bool,
        price_num: uint128,
        price_denum: uint128,
        min_amount: uint128,
        deals_limit: uint8,
        value: uint128,
        xchg_price_code: cell,
        major_tip3cfg: Tip3Config,
        minor_tip3cfg: Tip3Config
      )

    | transfer_FlexClient(dest: addr_std_compact, value: uint128, bounce: bool)

    | deployPriceXchg(
        sell: bool,
        price_num: uint128,
        price_denum: uint128,
        amount: uint128,
        lend_amount: uint128,
        lend_finish_time: uint32,
        min_amount: uint128,
        deals_limit: uint8,
        tons_value: uint128,
        xchg_price_code: cell,
        my_tip3_addr: addr_std_compact,
        receive_wallet: addr_std_compact,
        major_tip3cfg: Tip3Config,
        minor_tip3cfg: Tip3Config
      )

    | deployEmptyFlexWallet(
        pubkey: uint256,
        tons_to_wallet: uint128,
        tip3cfg: Tip3Config
      )

    | burnWallet(
        tons_value: uint128,
        out_pubkey: uint256,
        out_internal_owner: addr_std_compact,
        my_tip3_addr: addr_std_compact
      )

    | setFlexWalletCode(flex_wallet_code: cell)

    | setFlexCfg(tons_cfg: TonsConfig, flex:addr_std_compact, notify_addr:addr_std_compact)

    | setExtWalletCode(ext_wallet_code: cell)

    | setFlexWrapperCode(flex_wrapper_code: cell)
    // ----------------------------------------------------------
    // ITradingPair interface methods
    // ----------------------------------------------------------
    | onDeploy(min_amount: uint128, deploy_value: uint128)

    // ----------------------------------------------------------
    // IPrice interface methods
    // ----------------------------------------------------------
    | buyTip3(
        amount:uint128,
        my_tip3_addr:addr_std_compact,
        order_finish_time:uint32
      )

    | onTip3LendOwnership(
        answer_addr:address,
        balance:uint128,
        lend_finish_time:uint32,
        pubkey:uint256,
        internal_owner:address,
        payload:cell
      )

    | processQueue()

    | cancelSell()

    | cancelBuy()

    // ----------------------------------------------------------
    // IFlexNotify interface methods
    // ----------------------------------------------------------
    | onOrderAdded(
        sell:bool,
        tip3root:address,
        price:uint128,
        amount:uint128,
        sum_amount:uint128
      )

    | onOrderCanceled(
        sell:bool,
        tip3root:address,
        price:uint128,
        amount:uint128,
        sum_amount:uint128
      )

    | onDealCompleted(
        tip3root: address,
        price:uint128,
        amount:uint128
      )

    | onOrderFinished(ret:OrderRet, sell:bool)

    | onXchgDealCompleted(
        tip3root_sell: address,
        tip3root_buy: address,
        price_num:uint128,
        price_denum:uint128,
        amount:uint128
      )

    | onXchgOrderAdded(
        sell:bool,
        tip3_major_root: address,
        tip3_minor_root: address,
        price_num: uint128,
        price_denum:uint128,
        amount:uint128,
        sum_amount:uint128
      )

    | onXchgOrderCanceled(
        sell:bool,
        tip3_major_root: address,
        tip3_minor_root: address,
        price_num: uint128,
        price_denum:uint128,
        amount:uint128,
        sum_amount:uint128
      )


    // ----------------------------------------------------------
    // ITONTokenWallet interface methods
    // ----------------------------------------------------------
    | transfer_TONTokenWallet(
        answer_addr:address,
        to:address,
        tokens:uint128,
        grams:uint128,
        return_ownership: bool
      )

    | returnOwnership()

    | lendOwnership(
        answer_addr: addr_std_compact,
        grams: uint128,
        std_dest: uint256,
        lend_balance:uint128,
        lend_finish_time: uint32,
        deploy_init_cl: cell,
        payload: cell
      )

    | burn(out_pubkey: uint256, out_internal_owner: addr_std_compact)

    | internalTransfer(
        tokens: uint128,
        answer_addr: addr_std_compact,
        sender_pubkey: uint256,
        sender_owner: addr_std_compact,
        notify_receiver: bool,
        payload:cell
      )

    | onTip3Transfer(
        answer_addr: addr_std_compact,
        balance: uint128,
        new_tokens: uint128,
        sender_pubkey: uint256,
        sender_owner: addr_std_compact,
        payload: cell
      )

    | accept(tokens:uint128, answer_addr: address, grams: uint128)

    // ----------------------------------------------------------
    // IWrapper interface methods
    // ----------------------------------------------------------
    | IWrapper_burn(
        answer_addr: address,
        sender_pubkey: uint256,
        sender_owner: address,
        out_pubkey: uint256,
        out_internal_owner: address,
        tokens: uint128
      )


  datatype ContractCallbackMethod =
    | Fallback(msg:nat, msg_body:nat)

  datatype StateInit =
    | StateInit_FlexClient()
    | StateInit_TradingPair(
       flex_addr_: addr_std_compact,
       tip3_root_: addr_std_compact,
       min_amount:uint128 := 0
      )
    | StateInit_XchgPair(
       flex_addr_: addr_std_compact,
       tip3_major_root_: addr_std_compact,
       tip3_minor_root_: addr_std_compact,
       min_amount:uint128
      )
    | StateInit_Price()
    | StateInit_PriceXchg()
    | StateInit_TONTokenWallet(d:DTONTokenWallet)

  type DTradingPair = x:StateInit | x.StateInit_TradingPair? witness *

  datatype ContractMethodReturnValue =
    | returnDeployEmptyFlexWallet(wt_addr: addr_std_compact)
    | returnDeployPriceXchg(pr_addr: addr_std_compact)
    | returnDeployXchgPair(xp_addr: addr_std_compact)
    | returnDeployTradingPair(tp_addr: addr_std_compact)
    | returnDeployPriceWithBuy(pr_addr: addr_std_compact)
    | returnDeployPriceWithSell(pr_addr: addr_std_compact)
    | returnOnDeploy(bool)
    | returnBuyTip3(or:OrderRet)
    | returnOnTip3LendOwnership(or:OrderRet)
    // ITONTokenWallet
    | returnAccept(bool)
    | returnRequestBalance(balance:uint128)
    // RootTokenContract
    | returnSetWalletCode(bool)
    | returnDeployEmptyWallet(address)
    | returnMint(bool)
    | returnRequestTotalGranted(uint128)
}
