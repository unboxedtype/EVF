/* 
  Generic MapToSequence implementation.
  -------------------------------------
  The following code is extracted from the article:
  Rustan Leino - "Dafny Power User: Iterating over a Collection", KRML 275, 2020
*/

module MapToSequenceModule
{
  function method MapToSequence<A(!new),B>(m: map<A,B>, R: (A, A) -> bool): seq<(A,B)>
    requires IsTotalOrder(R)
  {
    var keys := SetToSequence(m.Keys, (a,a') => R(a, a'));
    seq(|keys|, i requires 0 <= i < |keys| => (keys[i], m[keys[i]]))
  }

  predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
    // connexity
    && (forall a, b :: R(a, b) || R(b, a))
    // antisymmetry
    && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
    // transitivity
    && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
  }

  function method SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
    requires IsTotalOrder(R)
    ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
  {
    if s == {} then [] else
      ThereIsAMinimum(s, R);
      var x :| x in s && forall y :: y in s ==> R(x, y);
      [x] + SetToSequence(s - {x}, R)
  }

  lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
    requires s != {} && IsTotalOrder(R)
    ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
  {
    var x :| x in s;
    if s == {x} {
      assert forall y :: y in s ==> x == y;
    } else {
      var s' := s - {x};
      assert s == s' + {x};
      ThereIsAMinimum(s', R);
      var z :| z in s' && forall y :: y in s' ==> R(z, y);
      if
      case R(z, x) =>
        forall y | y in s
        ensures R(z, y)
      {
        assert x == y || y in s';     
      }
      case R(x, z) =>
        forall y | y in s
        ensures R(x, y)
      {
        assert y in s' ==> R(z, y);      
      } 
    } 
  }
}
