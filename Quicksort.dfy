method Main()
{
	var a: array<int> := new int[4];
	a[0], a[1], a[2], a[3] := 50, 20, 30, 10;
	Sort(a);
	assert Sorted(a);
	print a[..];
}

predicate Sorted(a: array<int>)
	requires a != null
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSeq(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method Sort(a: array<int>)
	requires a != null
	ensures Sorted(a)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	if a.Length > 1
	{
		Quicksort(a, 0, a.Length-1);
	}
	else
	{
		assert Sorted(a);
	}
}

predicate QuicksortAdditionalPostconditions(q: seq<int>, lo: nat, hi: nat, q0: seq<int>)
requires 0 <= lo <= hi < |q| == |q0| && |q|>1 && |q0|>1
{
	(forall k :: 0 <= k < lo ==> q[k] == q0[k]) && (forall m :: hi < m < |q| == |q0| ==> q[m] == q0[m])
	&&( multiset(q[lo..hi+1]) == multiset(q0[lo..hi+1]))
}

method Quicksort(a: array<int>, lo: nat, hi: nat)
	requires a != null && a.Length > 1 && lo <= hi < a.Length
	ensures SortedSeq(a[lo..hi+1])
	ensures multiset(a[..]) == multiset(old(a[..]))
    ensures QuicksortAdditionalPostconditions(a[..], lo, hi, old(a[..]))
	modifies a
	decreases hi-lo
{
		var p:nat;
		assert a != null && a.Length > 1 && lo <= hi < a.Length;
		p := partition(a, lo, hi);
		assert forall i :: lo <= i < p <= hi ==> a[i] <= a[p]; 
		assert forall i :: lo <= p < i <= hi ==> a[p ] <= a[i];
		assert forall i :: 0 <= i < lo ==> a[i] == old(a[i]);
		assert forall i :: hi < i < a.Length ==> a[i] == old(a[i]);
		assert multiset(a[..]) == multiset(old(a[..]));
		assert multiset(a[lo..hi+1]) == multiset(old(a[lo..hi+1]));
		assert lo <= p <= hi;


		ghost var left := a[lo..p];
		ghost var right := a[p+1..hi+1];
		assert left+[a[p]]+right == a[lo..hi+1];
		assert multiset(left+[a[p]]+right) == multiset(old(a[lo..hi+1]));
		
		if p > lo
		{
			assert p>lo;	
			assert multiset(right) == multiset (a[p+1..hi+1]);
			assert multiset(a[lo..hi+1]) == multiset(old(a[lo..hi+1]));
			Lemma1(left, multiset(left[..]), a[lo..p], multiset(a[lo..p]), a[p]);
			Quicksort(a,lo, p - 1);
			assert multiset(a[..]) == multiset(old(a[..]));
			assert right == a[p+1..hi+1];
		}
		if p < hi
		{	
			assert p<hi;
			ghost var l_t := a[lo..p];
			Lemma2(right, multiset(right[..]),a[p+1..hi+1],multiset(a[p+1..hi+1]),a[p]);
			Quicksort(a, p + 1, hi);  
			assert multiset(a[..]) == multiset(old(a[..]));
			assert l_t == a[lo..p];
		}
		ghost var a_lo:=a[lo..p];
		ghost var a_p:=a[p+1..hi+1];
		ghost var a_val :=a[p];
		ghost var a_lo_h:=a[lo..hi+1];
		
		assert multiset(old(a[lo..hi+1]))==multiset(left+[a_val]+right);
		assert multiset([a_val]) == multiset (a[p..p+1]);
		assert a_lo+a[p..p+1]+a_p == a[lo..hi+1];
		assert multiset (a_lo +a[p..p+1]+a_p)==multiset(a[lo..hi+1]);
	
		Lemma3(a_lo,multiset(a_lo),a_p,multiset(a_p),a_val);
		assert forall k :: 0 <= k < |a_lo| ==> a_lo[k] <= a_val;
		assert a_lo+[a_val]+a_p == a_lo_h;
		assert SortedSeq(a_lo_h);
}
lemma Lemma1(left:seq<int>, a_l_m:multiset<int>, a_l_p:seq<int>, a_l_p_m:multiset<int>, p:int)
	requires a_l_m == a_l_p_m
	requires forall k :: k in a_l_m ==> k <= p
	requires forall k :: k in left <==> k in a_l_m
	ensures forall k :: k in a_l_p_m ==> k <= p
{	
}

lemma Lemma2(right:seq<int>, a_l_m:multiset<int>, a_l_p:seq<int>, a_l_p_m:multiset<int>, p:int)
	requires a_l_m == a_l_p_m
	requires forall k :: k in a_l_m ==> p <= k
	requires forall k :: k in right <==> k in a_l_m
	ensures forall k :: k in a_l_p_m ==> p <= k
{	
}

lemma Lemma3(a_lo:seq<int>, a_lo_m:multiset<int>, a_p:seq<int>, a_p_m:multiset<int>, p:int)
	requires forall k :: k in a_lo <==> k in a_lo_m
	requires forall k :: k in a_p_m ==> p <= k
	requires forall k :: k in a_p <==> k in a_p_m
	requires forall k :: k in a_lo_m ==> k <= p;
	ensures forall k :: 0 <= k < |a_p| ==> p <= a_p[k]
	ensures forall k :: 0 <= k < |a_lo| ==> a_lo[k] <= p;
{
	assert forall k:: 0 <= k < |a_lo| ==> a_lo[k] in a_lo_m;
	assert forall k :: k in a_lo_m ==> k <= p ==>forall k:: 0 <= k < |a_lo| ==> a_lo[k] <= p;
	assert forall k:: 0 <= k < |a_p| ==> a_p[k] in a_p_m;
	assert forall k :: k in a_p_m ==> p <= k ==> forall k:: 0 <= k < |a_p| ==> p <= a_p[k];
}



predicate part_inv_partition1(a:array<int>,lo:nat,hi:nat,p_val:int,i:int,j:int)
requires a!=null
requires 0 <= lo <=hi <a.Length
requires  0 <= i <a.Length &&    0 <= j <a.Length
reads a
	{
	forall b :: lo <= b <= i <= hi ==> a[b] <= p_val &&
	forall c :: lo-1 <= i < c < j <= hi ==> a[c] >= p_val 
	}
method partition(a:array<int>, lo: nat, hi: nat) returns (pivot: nat)
	requires a != null && a.Length > 1 && lo <= hi < a.Length
	ensures forall i :: lo <= i < pivot <= hi ==> a[i] <= a[pivot]; 
	ensures forall i :: lo <= pivot < i <= hi ==> a[pivot ] <= a[i];
	ensures forall i :: 0 <= i < lo ==> a[i] == old(a[i]);
	ensures forall i :: hi < i < a.Length ==> a[i] == old(a[i]);
	ensures multiset(a[..]) == multiset(old(a[..]))
	ensures multiset(a[lo..hi+1]) == multiset(old(a[lo..hi+1]))
	ensures lo <= pivot <= hi
	modifies a
{
	var p_val,i,j:=a[hi],lo-1,lo;

	while j<=hi-1 
	invariant forall b :: lo <= b <= i <= hi ==> a[b] <= p_val
	invariant forall c :: lo-1 <= i < c < j <= hi ==> a[c] >= p_val 
	invariant forall d :: 0 <= d< lo ==> a[d] == old(a[d])
	invariant forall e :: hi < e < a.Length ==> a[e] == old(a[e])
	invariant multiset(a[..]) == multiset(old(a[..]));
	invariant multiset(a[lo..hi+1]) == multiset(old(a[lo..hi+1]))
	invariant lo-1 <= i < j <= hi
	invariant p_val == a[hi];
	decreases hi - j
	{
		if a[j]<p_val
		{
			a[j],a[i+1]:=a[i+1],a[j];
			i:=i+1;
		}
		j:=j+1;
	}
	a[hi],a[i+1]:=a[i+1],a[hi];
	pivot:= i+1;
}
