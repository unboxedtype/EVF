## ================================================================
## Everscale build makefile
## ================================================================

## Dafny flags to run verification with.
## For details, see 'dafny /help'
FLAGS=/vcsLoad:0.5 /timeLimit:240 /compile:0 /warnShadowing /separateModuleOutput /mimicVerificationOf:3.3
.PHONY:

all: sys

sys: ./src/BaseTypes.dfy \
     ./src/TONTypes.dfy \
     ./src/TONContract.dfy \
     ./src/Queue.dfy \
     ./src/MapToSeq.dfy
	dafny $(FLAGS) $?