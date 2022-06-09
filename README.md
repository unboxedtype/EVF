Everscale Verification Framework
========

![EVF logo goes here](https://i.ibb.co/qxrL0mD/logo.png)

*"Write spec, receive proofs for free!"* -- EVF moto


**Everscale Verification Framework** (EVF for short)  is both a
methodology and a tool for  building   formally  verified  Everscale smart-contracts.

EVF is provided a set of libraries written in [Dafny](https://github.com/dafny-lang/dafny), 
verification-aware programming language.
The libraries contain primitives necessery to precisly model the behavior
of Everscale smart-contracts programmed in [TON C++](https://github.com/tonlabs/TON-Compiler) 
or [TON Solidity languages](https://github.com/tonlabs/TON-Solidity-Compiler).


The most basic workflow is as follows:
1. User codes their smart-contract into [Dafny](https://github.com/dafny-lang/dafny) program
equipped with EVF primitives. We call this artifact *the Model*.
2. User put annotations to the model. Annotations specify
how the contract should behave. 
3. Dafny checks if the annotated behavior correspond to the real behavior of the Model, showing all found errors.
4. User fixes found errors in the Model and/or annotations and goes to step 3.
5. After the EVF/Dafny model is verified, User introduces neccessary changes in the 
original smart-contract program code, using the verified Model as a gold standard.

EVF Goals
---
The **EVF** framework strives to give the following advantages to the
user:
1. The EVF code stay syntactically close to the original TON C++/TON Solidity program text.
2. Hide most of message handling protocol complexities from the
engineer, leaving visible only those parts that are needed to put annotations.
3. Hide Compute and Action phase complexities.
4. Give an engineer a way to specify the outcome of different Smart Contract execution phases.
5. Give the engineer all the Everscale execution environment related primitives and types.


How to use
---

Please review our [report]() on using EVF to perform a partial formal verification of a 
blockchain trading system called Flex. All artifacts are available inside _samples_ directory.
Please keep in mind that the report was written when Everscale was called FreeTON, hence
the framework was called TVF, i.e. TON Verification framework. Besides those syntactic changes,
everything else seems actual.

License
---
**EVF** is licensed under the MIT license. (See LICENSE.txt in the root directory for details.) 

Sponsoring
---
Thanks goes to our sponsors [EverX Labs](https://everx.dev/) and [Broxus](https://broxus.com/) for making this work possible. 
