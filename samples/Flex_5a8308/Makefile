## Flex Sample Makefile

## Dafny flags to run verification with.
## For details, see 'dafny /help'
FLAGS=/vcsLoad:0.5 /timeLimit:240 /compile:0 /warnShadowing /separateModuleOutput /mimicVerificationOf:3.3
.PHONY:

all: flex properties

flex: ./dfy/FlexClient.dfy \
	./dfy/TradingPair.dfy \
	./dfy/XchgPair.dfy \
	./dfy/Price.dfy \
	./dfy/PriceXchg.dfy \
	./dfy/RootTokenContract.dfy \
	./dfy/TONTokenWallet.dfy
	dafny $(FLAGS) $?

properties: ./dfy/PROP_SEC01.dfy \
            ./dfy/PROP_SEC02.dfy \
            ./dfy/PROP_SEC03.dfy \
            ./dfy/PROP_SEC04.dfy
	dafny $(FLAGS) $?