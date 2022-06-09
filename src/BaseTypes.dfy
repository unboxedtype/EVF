module BaseTypes
{
  const MAX_UINT256_NAT:nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF // 2**256 - 1
  const MAX_UINT128_NAT:nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  const MAX_UINT64_NAT:nat := 0xFFFFFFFFFFFFFFFF
  const MAX_UINT32_NAT:nat := 0xFFFFFFFF
  const MAX_UINT8_NAT:nat := 0xFF

  newtype uint256 = x:int | 0 <= x <= MAX_UINT256_NAT
  newtype uint128 = x:int | 0 <= x <= MAX_UINT128_NAT
  newtype uint64 = x:int | 0 <= x <= MAX_UINT64_NAT
  newtype uint32 = x:int | 0 <= x <= MAX_UINT32_NAT
  newtype uint8 = x: int | 0 <= x <= MAX_UINT8_NAT

  type unsigned = uint256

  const MAX_UINT256:uint256 := MAX_UINT256_NAT as uint256;
  const MAX_UINT128:uint128 := MAX_UINT128_NAT as uint128;
  const MAX_UINT64:uint64 := MAX_UINT64_NAT as uint64;
  const MAX_UINT32:uint32 := MAX_UINT32_NAT as uint32;
  const MAX_UINT8:uint8 := MAX_UINT8_NAT as uint8;


  /* Reminder: TON int type has an extra bit for the sign */
  newtype int8 = x: int | -255 <= x <= 255

  type uint = uint256

  datatype option<T> =
    None |
    Value(val:T)
  {
    predicate method has_val() { this.Value? }
    predicate method none() { this.None? }
  }

  datatype Status =
    | Success
    | Failure(error: unsigned)
  {
    predicate method IsFailure() { this.Failure? }
    function method PropagateFailure(): Status
      requires IsFailure()
    {
      Failure(this.error)
    }
  }

  type Grams = uint128

  // Use this function when you need to add message value with
  // some fee value, that we know for sure will not overflow the
  // Grams type.
  function method add(a:Grams, b:Grams): Grams
  {
    assume (a as nat + b as nat <= MAX_UINT128_NAT);
    a + b
  }

  function method addL(l:seq<Grams>): Grams
  {
    if l == [] then 0 else add(l[0], addL(l[1..]))
  }

  lemma add_addL(a:Grams, b:Grams)
    ensures add(a,b) == addL([a,b])
  {
    assert (addL([a,b]) == add(a, addL([b])));
    assert (add(a, addL([b])) == add(a, b));
  }

  lemma addL_step()
    ensures forall a, l :: addL([a] + l) == add(a, addL(l))
  {
    /* auto. */
  }

  lemma addL_subset(l1:seq<Grams>, l:seq<Grams>)
    requires l1 <= l
    ensures addL(l1) <= addL(l)
  { // proof by induction on l1
    if (l1 == []) {
      assert (addL([]) <= addL(l));
    } else {
      addL_subset(l1[1..], l[1..]);
    }
  }

  // Safe subtract operation
  function method sub(a:Grams, b:Grams): Grams
  {
    if (a >= b) then a - b else 0
  }

  type MsgFlags = bv8
  type cell = nat
  type optcell = option<cell>

  /* 'Classic' definition of TON address looks as follows:
  datatype address =
    AddressInt(workchain_id: int8, id: uint256) |
    AddressExt(id: uint256) |
    AddressNone()

  We strongly believe that this type  is redundant: it is nearly never
  the  case that  you need  AddressNone()  (just use  option type)  or
  AddressExt (you never send external messages, do you?)
  */

  function method abs(n: int8): nat
  {
    if n < 0 then ((-n) as nat) else (n as nat)
  }

  function method min(a:Grams, b:Grams): Grams
  {
    if a < b then a else b
  }

  function method max(a:nat, b:nat): nat
  {
    if a >= b then a else b
  }

  datatype address = AddressInt(workchain_id: int8, id: uint256)
  {
    static function method Default(): address { AddressInt(0, 0) }

    function method to_nat(): nat
    {
      if this.workchain_id < 0 then
        (abs(this.workchain_id) as nat) + (id as nat)*1000000
      else
        (this.workchain_id as nat)*1000 + (id as nat)*1000000
    }
    static function method make_std(workchain_id: int8, id: uint256) : address
    {
      AddressInt(workchain_id, id)
    }
  }

  // Original definitions to be found here:
  // TON-Compiler/llvm/projects/ton-compiler/cpp-sdk/tvm/schema/message.hpp

  // Semantically, both types are identical. The difference is only on the
  // encoding/decoding level: one is represented in a more compact way than
  // the other.
  type addr_std_compact = address
  type addr_std_fixed = address

  function method address_make_std(workchain_id: int8, id: uint256) : address
  {
    AddressInt(workchain_id, id)
  }

  function method SeqToSet<T>(s: seq<T>): set<T>
  {
    if s == [] then {} else {s[0]} + SeqToSet(s[1..])
  }

  // A stub function to mimic the C++ parse(cell),
  // for greater similarity with the original FLeX codebase.
  method parse<T>(payload:T) returns (r:T)
    ensures r==payload
  {
    return payload;
  }

  class Ref<T>  {
    var st:T;
    constructor(st1:T)
      ensures st == st1
    {
      st := st1;
    }
  }

  function method builtin_tvm_muldirv(a:uint128, b:uint128, c:uint128) : unsigned
    requires c != 0
  {
    assume (a as nat * b as nat / c as nat < MAX_UINT128_NAT);
    // assert (forall x :: x < MAX_UINT128_NAT ==> x < MAX_UINT256_NAT);
    // Warning: !!TODO!!
    // In Dafny 3.4.0, this expression still not verifies.
    // We introduce the lemma above, it helps to resolve the problem,
    // but maybe it is a soundness issue.
    (a as nat * b as nat / c as nat) as unsigned
  }

  function method builtin_tvm_hashcu(c:cell): unsigned
}
