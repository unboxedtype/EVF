#include "FlexClient.hpp"
#include "TradingPair.hpp"
#include "XchgPair.hpp"
#include "Wrapper.hpp"

#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class FlexClient final : public smart_interface<IFlexClient>, public DFlexClient {
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner = 100;
    static constexpr unsigned missed_ext_wallet_code         = 101;
    static constexpr unsigned missed_flex_wallet_code        = 102;
    static constexpr unsigned missed_flex_wrapper_code       = 103;
    static constexpr unsigned zero_owner_pubkey              = 104;
  };

  __always_inline
  void constructor(uint256 pubkey, cell trading_pair_code, cell xchg_pair_code) {
    require(pubkey != 0, error_code::zero_owner_pubkey);
    owner_ = pubkey;
    trading_pair_code_ = trading_pair_code;
    xchg_pair_code_ = xchg_pair_code;
    workchain_id_ = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
    flex_ = address::make_std(int8(0), uint256(0));
    notify_addr_ = address::make_std(int8(0), uint256(0));
  }

  __always_inline
  void setFlexCfg(TonsConfig tons_cfg, addr_std_compact flex, addr_std_compact notify_addr) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    tons_cfg_ = tons_cfg;
    flex_ = flex;
    notify_addr_ = notify_addr;
  }
  
  // === additional configuration necessary for deploy wrapper === //
  __always_inline
  void setExtWalletCode(cell ext_wallet_code) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    ext_wallet_code_ = ext_wallet_code;
  }

  __always_inline
  void setFlexWalletCode(cell flex_wallet_code) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    flex_wallet_code_ = flex_wallet_code;
  }

  __always_inline
  void setFlexWrapperCode(cell flex_wrapper_code) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    flex_wrapper_code_ = flex_wrapper_code;
  }
  // === ===================================================== === //

  __always_inline
  address deployTradingPair(
    addr_std_compact tip3_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DTradingPair pair_data {
      .flex_addr_ = flex_,
      .tip3_root_ = tip3_root
    };

    auto [state_init, std_addr] = prepare_trading_pair_state_init_and_addr(pair_data, trading_pair_code_);
    auto trade_pair = ITradingPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy(min_trade_amount, deploy_min_value);

    return trade_pair.get();
  }

  __always_inline
  address deployXchgPair(
    addr_std_compact tip3_major_root,
    addr_std_compact tip3_minor_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DXchgPair pair_data {
      .flex_addr_ = flex_,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root
    };

    auto [state_init, std_addr] = prepare_xchg_pair_state_init_and_addr(pair_data, xchg_pair_code_);
    auto trade_pair = IXchgPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy(min_trade_amount, deploy_min_value);

    return trade_pair.get();
  }

  __always_inline
  address deployPriceWithSell(
    uint128 price,
    uint128 amount,
    uint32  lend_finish_time,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 tons_value,
    cell    price_code,
    addr_std_compact my_tip3_addr,
    addr_std_compact receive_wallet,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePrice(price, min_amount, deals_limit, flex_wallet_code_.get(), tip3cfg, price_code);
    auto price_addr = IPricePtr(addr);
    cell deploy_init_cl = build(state_init).endc();
    SellArgs sell_args = {
      .amount = amount,
      .receive_wallet = receive_wallet
    };
    cell payload = build(sell_args).endc();

    ITONTokenWalletPtr my_tip3(my_tip3_addr);
    my_tip3(Grams(tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(address{tvm_myaddr()}, uint128(0), std_addr, amount,
                    lend_finish_time, deploy_init_cl, payload);

    return price_addr.get();
  }

  __always_inline
  address deployPriceWithBuy(
    uint128 price,
    uint128 amount,
    uint32 order_finish_time,
    uint128 min_amount,
    uint8 deals_limit,
    uint128 deploy_value,
    cell price_code,
    addr_std_compact my_tip3_addr,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePrice(price, min_amount, deals_limit, flex_wallet_code_.get(), tip3cfg, price_code);
    IPricePtr price_addr(addr);
    price_addr.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).
      buyTip3(amount, my_tip3_addr, order_finish_time);
    return price_addr.get();
  }

  __always_inline
  void cancelSellOrder(
    uint128 price,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 value,
    cell    price_code,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePrice(price, min_amount, deals_limit, flex_wallet_code_.get(), tip3cfg, price_code);
    IPricePtr price_addr(addr);
    price_addr(Grams(value.get()), DEFAULT_MSG_FLAGS, false).cancelSell();
  }

  __always_inline
  void cancelBuyOrder(
    uint128 price,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 value,
    cell    price_code,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePrice(price, min_amount, deals_limit, flex_wallet_code_.get(), tip3cfg, price_code);
    IPricePtr price_addr(addr);
    price_addr(Grams(value.get()), DEFAULT_MSG_FLAGS, false).cancelBuy();
  }

  __always_inline
  void cancelXchgOrder(
    bool_t  sell,
    uint128 price_num,
    uint128 price_denum,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 value,
    cell    xchg_price_code,
    Tip3Config major_tip3cfg,
    Tip3Config minor_tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePriceXchg(price_num, price_denum, min_amount, deals_limit,
                       major_tip3cfg, minor_tip3cfg, xchg_price_code);
    IPriceXchgPtr price_addr(addr);
    if (sell)
      price_addr(Grams(value.get()), DEFAULT_MSG_FLAGS, false).cancelSell();
    else
      price_addr(Grams(value.get()), DEFAULT_MSG_FLAGS, false).cancelBuy();
  }

  __always_inline
  void transfer(addr_std_compact dest, uint128 value, bool_t bounce) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    tvm_transfer(dest, value.get(), bounce.get());
  }

  __always_inline
  address deployPriceXchg(
    bool_t  sell,
    uint128 price_num,
    uint128 price_denum,
    uint128 amount,
    uint128 lend_amount,
    uint32  lend_finish_time,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 tons_value,
    cell    xchg_price_code,
    addr_std_compact my_tip3_addr,
    addr_std_compact receive_wallet,
    Tip3Config major_tip3cfg,
    Tip3Config minor_tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePriceXchg(price_num, price_denum, min_amount, deals_limit,
                       major_tip3cfg, minor_tip3cfg, xchg_price_code);
    auto price_addr = IPriceXchgPtr(addr);
    cell deploy_init_cl = build(state_init).endc();
    PayloadArgs payload_args = {
      .sell = sell,
      .amount = amount,
      .receive_tip3_wallet = receive_wallet,
      .client_addr = address{tvm_myaddr()}
    };
    cell payload = build(payload_args).endc();

    ITONTokenWalletPtr my_tip3(my_tip3_addr);
    my_tip3(Grams(tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(address{tvm_myaddr()}, uint128(0), std_addr, lend_amount,
                    lend_finish_time, deploy_init_cl, payload);
    return price_addr.get();
  }

  __always_inline
  address deployWrapperWithWallet(
    uint256 wrapper_pubkey,
    uint128 wrapper_deploy_value,
    uint128 wrapper_keep_balance,
    uint128 ext_wallet_balance,
    uint128 set_internal_wallet_value,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(ext_wallet_code_, error_code::missed_ext_wallet_code);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    require(flex_wrapper_code_, error_code::missed_flex_wrapper_code);
    tvm_accept();

    DWrapper wrapper_data {
      .name_ = tip3cfg.name,
      .symbol_ = tip3cfg.symbol,
      .decimals_ = tip3cfg.decimals,
      .workchain_id_ = workchain_id_,
      .root_public_key_ = wrapper_pubkey,
      .total_granted_ = {},
      .internal_wallet_code_ = {},
      .owner_address_ = address{tvm_myaddr()},
      .start_balance_ = Grams(wrapper_keep_balance.get()),
      .external_wallet_ = {}
    };
    auto [wrapper_init, wrapper_hash_addr] = prepare_wrapper_state_init_and_addr(flex_wrapper_code_.get(), wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(workchain_id_, wrapper_hash_addr));

    // ============= Deploying external wallet for Flex wrapper ============ //
    auto [wallet_init, wallet_hash_addr] = prepare_external_wallet_state_init_and_addr(
      tip3cfg.name, tip3cfg.symbol, tip3cfg.decimals,
      tip3cfg.root_public_key, wrapper_pubkey, tip3cfg.root_address,
      wrapper_addr.get(), ext_wallet_code_.get(), workchain_id_);
    ITONTokenWalletPtr wallet_addr(address::make_std(workchain_id_, wallet_hash_addr));
    wallet_addr.deploy_noop(wallet_init, Grams(ext_wallet_balance.get()));

    // ================== Deploying Flex wrapper for Nuka ================== //
    wrapper_addr.deploy(wrapper_init, Grams(wrapper_deploy_value.get())).init(wallet_addr.get());

    wrapper_addr(Grams(set_internal_wallet_value.get())).setInternalWalletCode(flex_wallet_code_.get());

    return wrapper_addr.get();
  }

  __always_inline
  address deployEmptyFlexWallet(
    uint256 pubkey,
    uint128 tons_to_wallet,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [init, hash_addr] = prepare_internal_wallet_state_init_and_addr(
      tip3cfg.name, tip3cfg.symbol, tip3cfg.decimals, tip3cfg.root_public_key,
      pubkey, tip3cfg.root_address, address{tvm_myaddr()}, flex_wallet_code_.get(), workchain_id_
      );
    ITONTokenWalletPtr new_wallet(address::make_std(workchain_id_, hash_addr));
    new_wallet.deploy_noop(init, Grams(tons_to_wallet.get()));
    return new_wallet.get();
  }

  __always_inline
  void burnWallet(
    uint128 tons_value,
    uint256 out_pubkey,
    addr_std_compact out_internal_owner,
    addr_std_compact my_tip3_addr
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    ITONTokenWalletPtr my_tip3(my_tip3_addr);
    my_tip3(Grams(tons_value.get())).
      burn(out_pubkey, out_internal_owner);
  }

  __always_inline
  uint256 getOwner() {
    return owner_;
  }

  __always_inline
  address getFlex() {
    return flex_;
  }

  __always_inline
  bool_t hasExtWalletCode() {
    return bool_t{!!ext_wallet_code_};
  }

  __always_inline
  bool_t hasFlexWalletCode() {
    return bool_t{!!flex_wallet_code_};
  }

  __always_inline
  bool_t hasFlexWrapperCode() {
    return bool_t{!!flex_wrapper_code_};
  }

  __always_inline
  cell getPayloadForDeployInternalWallet(
    uint256 owner_pubkey,
    addr_std_compact owner_addr,
    uint128 tons
  ) {
    return build(FlexDeployWalletArgs{owner_pubkey, owner_addr, tons}).endc();
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IFlexClient, replay_protection_t)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }

private:
  __always_inline
  std::tuple<StateInit, address, uint256> preparePrice(
      uint128 price, uint128 min_amount, uint8 deals_limit, cell tip3_code, Tip3Config tip3cfg, cell price_code) const {
    DPrice price_data {
      .price_ = price,
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = IFlexNotifyPtr(notify_addr_),
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = tip3_code,
      .tip3cfg_ = tip3cfg,
      .sells_ = {},
      .buys_ = {}
    };
    auto [state_init, std_addr] = prepare_price_state_init_and_addr(price_data, price_code);
    auto addr = address::make_std(workchain_id_, std_addr);
    return { state_init, addr, std_addr };
  }
  __always_inline
  std::tuple<StateInit, address, uint256> preparePriceXchg(
      uint128 price_num, uint128 price_denum, uint128 min_amount, uint8 deals_limit,
      Tip3Config major_tip3cfg, Tip3Config minor_tip3cfg, cell price_code) const {

    DPriceXchg price_data {
      .price_ = { price_num, price_denum },
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = IFlexNotifyPtr(notify_addr_),
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = flex_wallet_code_.get(),
      .major_tip3cfg_ = major_tip3cfg,
      .minor_tip3cfg_ = minor_tip3cfg,
      .sells_ = {},
      .buys_ = {}
    };
    auto [state_init, std_addr] = prepare_price_xchg_state_init_and_addr(price_data, price_code);
    auto addr = address::make_std(workchain_id_, std_addr);
    return { state_init, addr, std_addr };
  }
};

DEFINE_JSON_ABI(IFlexClient, DFlexClient, EFlexClient);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(FlexClient, IFlexClient, DFlexClient, TIMESTAMP_DELAY)

