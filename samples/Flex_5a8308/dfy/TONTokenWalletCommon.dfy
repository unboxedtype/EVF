/* The module is introduced to break a cycle in the types definition. */

include "../../../src/BaseTypes.dfy"

module TONTokenWalletCommon
{
	import opened BaseTypes
		
	datatype lend_record =
		| lend_record(lend_balance:uint128, lend_finish_time:uint32)

	type addr_std_fixed = address
	type lend_ownership_map = map<addr_std_fixed, lend_record>

	datatype DTONTokenWallet = DTONTokenWallet(
		name_:string,
		symbol_:string,
		decimals_:uint8,
		balance_:uint128,
		root_public_key_:uint256,
		wallet_public_key_:uint256,
		root_address_:address,
		owner_address_:option<address>,
		lend_ownership_: lend_ownership_map,
		code_: cell,
		// allowance_ is absent, becase TIP3_ENABLE_ALLOWANCE
		// define is not set
		workchain_id_:int8
	)
	type DTONTokenWalletInternal = DTONTokenWallet	
}
