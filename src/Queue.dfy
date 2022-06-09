/* Queue that models the queue behavior of TON C++
	 defined in /cpp-sdk/tvm/queue.hpp file */

include "BaseTypes.dfy"

module Queue
{
	import opened BaseTypes

	const iterator_overflow:uint := 64;

	type queue<T> = seq<T>

	function method len<T>(q:queue): nat
	{
		|q|
	}

	predicate method empty<T>(q:queue)
	{
		len(q) == 0
	}

	// Inserts a new element at the end of the queue, after its
	// current last element.
	function method push<T>(q:queue, e:T): queue
	{
		q + [e]
	}

	method pop<T>(q:queue) returns (r:Status, q1:queue)
		ensures !empty(q) ==> r == Success && len(q1) < len(q) && q[1..] == q1
		ensures r == Success ==> len(q1) < len(q)
	{
		if (empty(q)) {
			return Failure(iterator_overflow), [];
		}
		else {
			return Success, q[1..];
		}
	}

	method front<T(!new,0)>(q:queue) returns (r:Status, val:T)
	{
		if (empty(q)) {
			return Failure(iterator_overflow), *;
		}
		return Success, q[0];
	}

	method change_front<T(!new,0)>(q:queue<T>, e:T)
		returns (r:Status, q1:queue<T>)
		ensures len(q) > 0 ==> r == Success && q1 == [e] + q[1..]
		ensures len(q) == 0 ==> r.Failure?
	{
		var len := len(q);
		if (len == 0) {
			return Failure(iterator_overflow), [];
		}
		q1 := [e] + q[1..];
		return Success, q1;
	}

	method back_with_idx<T(!new,0)>(q:queue<T>)
		returns (r:Status, idx_elem:(nat, T))
		ensures len(q) != 0 ==> r == Success && idx_elem == (len(q), q[len(q) - 1]);
		ensures len(q) == 0 ==> r.Failure?
	{
		if (len(q) == 0) {
			var v := *;
			return Failure(iterator_overflow), (0, v);
		}
		else {
			var e := q[len(q) - 1];
			return Success, (len(q), e);
		}
	}

	method front_with_idx_opt<T>(q:queue) returns (r:option<(unsigned, T)>)
		ensures !empty(q) ==> r == Value((0, q[0]))
	{
		if (!empty(q)) {
			return Value((0, q[0]));
		}
		return None;
	}

	// erase element at position i.
	method erase(q:queue, i:nat) returns (r:bool, q1:queue)
		ensures len(q) <= i ==> r == false && q1 == q
		ensures len(q) > i ==> r == true &&
		|q1| < |q| &&
		q1 == (if (i >= 1) then q[0..(i-1)] else []) + q[(i+1)..]
	{
		if (i >= len(q)) {
			return false, q;
		}
		var left := if (i >= 1) then q[0..(i-1)] else [];
		var right := q[(i+1)..];
		return true, left + right;
	}
}
