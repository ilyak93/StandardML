(* Ilya Kotlov 321851784 s3218517@campus.technion.ac.il *)

(*Targil 1*)

datatype ('a, 'b) heterolist = Nil | Cons of 'a * ('b,'a) heterolist; 

fun head(Cons(x,_)) = x;

fun tail(Cons(_,xf)) = xf;

fun build4 (x,one,y,two) = Cons(x,Cons(one, Cons(y,Cons(two,Nil))));

fun hetero_list_2_first_list Nil = nil |
	hetero_list_2_first_list (Cons(x, xf)) = (x::hetero_list_2_first_list (tail xf)); 

fun hetero_list_2_second_list Nil = nil |
	hetero_list_2_second_list (Cons(x, xf)) = ((head xf)::hetero_list_2_second_list (tail xf)); 

fun unzip Nil = (nil,nil) |
	unzip hlist = (hetero_list_2_first_list hlist, hetero_list_2_second_list hlist);

fun zip (nil, nil) = Nil |
	zip ((x::xs),(y::ys)) = if length(ys) > length(xs) orelse length(ys) < length(xs)-1 then raise Empty 
							else Cons(x, Cons(y, zip (xs,ys)));

(*Targil 2*)

(*a seq*)

datatype 'a seq = Nil | Cons of 'a * (unit-> 'a seq);

exception EmptySeq;

fun head(Cons(x,_)) = x | head Nil = raise EmptySeq;

fun tail(Cons(_,xf)) = xf() | tail Nil = raise EmptySeq;


(*bseq*)

datatype direction = Back | Forward;
datatype 'a bseq =   bNil | bCons of 'a * (direction -> 'a bseq);

fun bHead(bCons(x,_)) = x | bHead bNil = raise EmptySeq;

fun bForward(bCons(_,xf)) = xf(Forward) | bForward bNil = raise EmptySeq;

fun bBack(bCons(_,xf)) = xf(Back) | bBack bNil = raise EmptySeq;


(*function 1*)
fun intbseq k = bCons(k,fn dir => if dir = Forward then intbseq(k+1) else intbseq(k-1) );

(*function 2*)

fun bmap f bNil = bNil | 
	bmap f (bCons(x,xf)) = bCons( f(x), fn dir => bmap f (xf(dir)) );

(*function 3*)

fun bfilter pred dir bNil = bNil | 
	bfilter pred dir (bCons(x,xf)) = if pred x then bCons(x, fn dir => bfilter pred dir (xf(dir)))
								 	 else bfilter pred dir (xf(dir));

(*function 4*)

fun binterleaving_aux _ bNil yq = yq | 
	binterleaving_aux _ xq bNil = xq | 
	binterleaving_aux firstb (bCons(x,xf)) (bCons(y,yf)) = bCons(x, fn dir => 
														if dir = Forward 
														then binterleaving_aux true (bCons(y,yf)) (xf(dir))
														else if firstb 
															 then binterleaving_aux false (yf(dir)) (xf(dir))
															 else binterleaving_aux false (bCons(y,yf)) (xf(dir)));

fun binterleaving bseq1 bseq2 = binterleaving_aux true bseq1 bseq2;

(*function 5*)

fun bappend bNil yq = yq | 
	bappend xq bNil = xq | 
	bappend (bCons(x,xf)) yq = bCons(x,fn dir => bappend (xf(dir)) yq);

fun seq2bseq Nil (Cons(y,yf)) = intbseq y |
	seq2bseq (Cons(x,xf)) Nil  = intbseq x |
	seq2bseq (Cons(x,xf)) (Cons(y,yf)) = bappend (intbseq y) (intbseq x);

(*function 6*)
fun bfilter i m dir bNil = bNil |
	bfilter i m dir (bCons(x,xf)) = if (i mod m = 0) then (bCons(x, fn dir => bfilter (i+1) m dir (xf(dir)) ))
	else bfilter (i+1) m dir (xf(dir));

fun bSeqJump bNil m = bNil |
	bSeqJump _ 0 = bNil |
	bSeqJump bseq_c m = bfilter 0 m Forward bseq_c;