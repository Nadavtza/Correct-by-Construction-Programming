method Main() {
	var q := [2,3,4];
	var productSets := FindProductSets(q, 12);
	assert {1,2} in productSets by {
		calc {
			SubProduct(q, {1,2});
		== { LemmaSubProductsOrderIndifference(q, {1,2}, 1); }
			q[1]*q[2];
		==
			3*4;
		==
			12;
		}
	}
}



function SubProduct(q: seq<int>, indexSet: set<nat>): int
	requires InRange(q, indexSet)
{
	if |indexSet| == 0 then 1 else var i :| i in indexSet; q[i] * SubProduct(q, indexSet-{i})
}

predicate InRange<T>(q: seq<T>, indexSet: set<nat>)
{
	forall i :: i in indexSet ==> 0 <= i < |q|
}

function AllIndexSubsets<T>(q: seq<T>): (res: set<set<nat>>)
	ensures forall s :: s in res ==> InRange(q, s)
{
	AllSubsets(set i | P(i) && 0 <= i < |q|)
}

predicate P<T>(x: T) { true } // this is helpful only for avoiding a "no triggers found" warning by Dafny

function AllSubsets<T>(s: set<T>): set<set<T>>
{
	set subset: set<T> | P(subset) && subset <= s
}

method FindProductSets(q: seq<int>, num: int) returns (result: set<set<int>>)
	ensures forall indexSet :: indexSet in result <==> indexSet in AllIndexSubsets(q) && SubProduct(q, indexSet) == num
	{
	var sub_sets:set<set<int>> :=GenerateAllIndexSubsets(q);
	assert sub_sets == AllIndexSubsets(q) ;
	var removed_sets: set<set<int>>  :={};
	result := {};
	var sub_sets_orginal : set<set<int>>:=sub_sets;
	assert sub_sets_orginal - sub_sets==result + removed_sets;
	assert  inv1FindProduct(q, result, num) && inv2FindProduct(q, removed_sets, num) 
					&& inv3FindProduct(result, removed_sets,sub_sets,sub_sets_orginal,num,q) ;
	while  sub_sets != {} 
		invariant  inv1FindProduct(q, result, num) &&  inv2FindProduct(q, removed_sets, num) 
					&&  inv3FindProduct(result, removed_sets,sub_sets,sub_sets_orginal,num,q) 		
		decreases sub_sets	
	{
		assert  sub_sets != {} ;
		var indexSet :| indexSet in sub_sets;
		assert indexSet in sub_sets;	
		
			
		assert InRange(q, indexSet);
		var sub_product:int  := ComputeSubProduct(q,indexSet);
		assert  sub_product == SubProduct(q, indexSet);
		
		if sub_product == num
		{
			assert sub_product == num;
			result := result +{indexSet}; 
			assert indexSet in result;
				
		}
		else 
		{
			assert sub_product != num;
			removed_sets := removed_sets +{indexSet}; 
			assert indexSet in removed_sets;
		}
		assert sub_sets >  sub_sets - { indexSet };
		sub_sets := sub_sets - { indexSet };
		assert inv1FindProduct(q, result, num) &&  inv2FindProduct(q, removed_sets, num) && inv3FindProduct(result, removed_sets,sub_sets,sub_sets_orginal,num,q) ;
	}
	assert inv3FindProduct(result, removed_sets,sub_sets,sub_sets_orginal,num,q);
	assert inv1FindProduct(q, result, num) &&  inv2FindProduct(q, removed_sets, num) ;
	assert sub_sets=={};
	assert removed_sets + result==AllIndexSubsets(q);
	assert forall indexSet :: indexSet in result <==> indexSet in AllIndexSubsets(q) && SubProduct(q, indexSet) == num ;
	}

predicate inv1FindProduct(q: seq<int>, result: set<set<int>>, num:int)
{
	forall indexSet :: indexSet in result ==> (indexSet in  AllIndexSubsets(q)) && SubProduct(q, indexSet) == num
}
predicate inv2FindProduct(q: seq<int>, removed_sets: set<set<int>>, num:int)
{
	forall indexSet :: indexSet in removed_sets ==> (indexSet in  AllIndexSubsets(q)) && !(SubProduct(q, indexSet) == num)
}

predicate inv3FindProduct(result: set<set<int>>, removed_sets: set<set<int>>,sub_sets: set<set<int>>,sub_sets_orginal: set<set<int>>,num:int,q: seq<int>)	 
{
	sub_sets_orginal - sub_sets==result + removed_sets
}

method GenerateAllIndexSubsets<T>(q: seq<T>) returns (res: set<set<nat>>)
	ensures res == AllIndexSubsets(q)  
{
		res:= {{}};
		var i:nat := 0;
		assert i==0;
		LemmaZeroElements(q[..i]);
		assert res == AllIndexSubsets(q[..i]);
		assert i<=|q|;

		while i!=|q|
		invariant i <= |q| && invGenerate(q,res,i) 
		decreases |q|-i
		{			
			assert i <|q|;
			assert  invGenerate(q,res,i);
			res := addIndexToSets(q,res,i);
			assert 	res == AllIndexSubsets(q[..i+1]);			
			i:= i+1;
			assert invGenerate(q,res,i);
		}	
		assert res == AllIndexSubsets(q[..i]);
		assert i==|q|;	
		assert res == AllIndexSubsets(q);
} 

predicate invGenerate<T>(q: seq<T>, res: set<set<nat>>, i:nat)
	requires i<=|q|
{
	res == AllIndexSubsets(q[..i])
}


method addIndexToSets<T>(q: seq<T>,old_res: set<set<nat>>, i:nat ) returns (loop_res: set<set<nat>>)
				requires i<|q|
				requires old_res == AllIndexSubsets(q[..i])
				ensures  loop_res== AllIndexSubsets(q[..i+1])
{	
				var temp_old_res: set<set<nat>> := old_res;
				ghost var removed_sets: set<set<nat>> := old_res-temp_old_res;
				loop_res :=  {};	
				assert forall s1:: s1 in loop_res ==> s1 in AllIndexSubsets(q[..i+1]);
				assert old_res == AllIndexSubsets(q[..i]);
				assert loop_res == set x | x in removed_sets;

				while ( temp_old_res != {} )
					invariant  inv1addIndex(q, loop_res, i) &&inv2addIndex(q, loop_res,removed_sets,  old_res,  temp_old_res, i)			
					decreases temp_old_res			
				{
					
					assert inv1addIndex(q, loop_res, i);
					assert inv2addIndex(q, loop_res,removed_sets,  old_res,  temp_old_res, i);

					var y :| y in temp_old_res;
					assert y in temp_old_res;	
					assert temp_old_res >  temp_old_res - { y };
					temp_old_res, removed_sets := temp_old_res - { y } , removed_sets + {y};
					assert y in removed_sets;	
					y:= y+ {i};
					assert InRange(q[..i+1], y);	
					assert  y in AllIndexSubsets(q[..i+1]);			
					loop_res := loop_res +{y}; 
					assert y in loop_res;
	

					assert inv1addIndex(q, loop_res, i);
					assert inv2addIndex(q, loop_res,removed_sets,  old_res,  temp_old_res, i);
				}
				assert removed_sets == old_res;
				assert  temp_old_res == {};
				assert inv1addIndex(q, loop_res, i);
				assert inv2addIndex(q, loop_res,removed_sets,  old_res,  temp_old_res, i);				
				assert old_res == AllIndexSubsets(q[..i]);

				LemmaAddSubsets(q,old_res,loop_res,i);	
				loop_res:= old_res +loop_res;	
				assert loop_res== AllIndexSubsets(q[..i+1])	;
	
}


predicate inv1addIndex<T>(q: seq<T>, loop_res: set<set<nat>>, i:nat)
	requires i<|q|
{
	forall s1:: s1 in loop_res ==> s1 in AllIndexSubsets(q[..i+1])
}

predicate inv2addIndex<T>(q: seq<T>, loop_res: set<set<nat>>, removed_sets: set<set<nat>>,  old_res: set<set<nat>>,  temp_old_res: set<set<nat>>, i:nat)
		requires i<|q|
{
	(loop_res == set x | x in removed_sets :: x+ {i}) &&( removed_sets==old_res-temp_old_res)
}

lemma  {:verify false}LemmaAddSubsets <T>(q: seq<T>, res: set<set<nat>>,add_to_res: set<set<nat>>,i:nat) // //with words
	requires i<|q|
	requires res== AllIndexSubsets(q[..i])
	requires forall s1:: s1 in add_to_res ==> s1 in AllIndexSubsets(q[..i+1])
	requires add_to_res ==set x | x in res:: x+ {i}   	
	ensures res+add_to_res== AllIndexSubsets(q[..i+1])
{
//  AllIndexSubsets(q[..i+1]) is all the sets that we can create til i-1, and all the sets we can create with them if we add them i
//meaning AllIndexSubsets(q[..i+1])=AllIndexSubsets(q[..i]) + set x | x in AllIndexSubsets(q[..i]):: x+ {i} 
//(adding all the subsets we can create from AllIndexSubsets(q[..i] by adding them i)
// since we know forall s1:: s1 in add_to_res ==> s1 in AllIndexSubsets(q[..i+1]) we know they are in AllIndexSubsets(q[..i+1]), 
//probably can get this from add_to_res ==set x | x in res:: x+ {i} and res== AllIndexSubsets(q[..i]) and i<|q|  , but easier to see this way.
}

lemma {:verify false} LemmaZeroElements <T>(q: seq<T>)  
	requires |q|==0
	ensures {{}} == AllIndexSubsets(q)
{
// if |q|==0 , there is no i such that set i | P(i) && 0 <= i < |q| 
//not possible to create any set but the empty set {}.
}

method ComputeSubProduct(q: seq<int>, indexSet: set<nat>) returns (prod: int)
	requires InRange(q, indexSet) 
	ensures prod == SubProduct(q, indexSet) 
	{
		assert	InRange(q, indexSet); 
		if |indexSet| == 0 
		{
			assert |indexSet| == 0 ;
			prod:=1;
			assert prod == SubProduct(q, indexSet);
		}
		else
		{
			assert |indexSet| != 0 ;
			var e :| e in indexSet;
			assert e in indexSet;
			var s1 := indexSet-{e};
			assert s1 < indexSet; 
			LemmaSubProductsOrderIndifference(q, indexSet,e);
			prod:= ComputeSubProduct(q, indexSet-{e});
			assert prod == SubProduct(q, indexSet-{e});
			prod:=q[e] * prod;
			 assert prod == SubProduct(q, indexSet);
		}
	}

lemma {:verify false} LemmaSubProductsOrderIndifference(q: seq<int>, indexSet: set<nat>, i: nat)
	requires i in indexSet
	requires InRange(q, indexSet)
	ensures q[i] * SubProduct(q, indexSet-{i}) == SubProduct(q, indexSet)
{}
