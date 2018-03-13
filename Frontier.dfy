datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)

class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() //alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate method EOF() reads this { alpha == [] }

}

//Output the elements at the leaves/tips of a given binary tree, iteratively, using a sequence of subtrees as a stack.

method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var io: IO<int>;
	io := new IO<int>;
	FrontierIter(tree, io);
	print io.omega;

	io.Rewrite();
	tree := Node(tree, Tip(2));
	FrontierIter(tree, io);
	print io.omega;
}

function Frontier<T>(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function FrontierForest<T>(stack: seq<BT<T>>): seq<T>
{
	if stack == [] then [] else Frontier(stack[0]) + FrontierForest(stack[1..])
}

function TreeSize<T>(nt: BT<T>): nat
{
	match nt {
		case Tip(n) => 1
		case Node(nt1,nt2) => 1+TreeSize(nt1)+TreeSize(nt2)
	}
}

function SizeForest<T>(stack: seq<BT<T>>): nat
{
	if stack == [] then 0 else TreeSize(stack[0]) + SizeForest(stack[1..])
}



method FrontierIter<T>(tree: BT<T>, io: IO<T>)
	requires io != null
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)

{
	assert io != null;
	var stack: seq<BT<T>>;
	stack := [tree];
	var temp_omega: seq<T>:=[];
	assert temp_omega==[];

	while stack != []
		invariant Frontier(tree) ==  temp_omega + FrontierForest(stack)
		decreases SizeForest(stack);
	{
		assert stack != [];
		assert Frontier(tree) ==  temp_omega + FrontierForest(stack);

		ghost var V0 := SizeForest(stack);
		var temp;
		// pop
		temp, stack := stack[0], stack[1..];
		match temp {
		case Tip(n) =>
				temp_omega:= temp_omega+[n] ;
		case Node(nt1, nt2) =>
			// push
			stack := [nt1, nt2] + stack;
		}
		assert SizeForest(stack) < V0;
		assert Frontier(tree) ==  temp_omega + FrontierForest(stack);
	}

	assert stack == [];
	assert Frontier(tree) ==   temp_omega + FrontierForest(stack);
	assert FrontierForest(stack)==[];
	assert temp_omega==Frontier(tree);
	io.omega := io.omega + temp_omega;
	assert io.omega == old(io.omega) + temp_omega;	
	assert io.omega == old(io.omega) + Frontier(tree);	
	
}