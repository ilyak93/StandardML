
datatype ('a, 'b) heterolist = HNil
  | HCons of 'a * ('b, 'a) heterolist;

(* Example:
  build4 ("x",1,"y",2) = ["x",1,"y",2];
  (not syntactically correct, since heterolist cannot be written with []) *)
fun build4 (x,one,y,two) = HCons(x, HCons(one, HCons(y, HCons(two, HNil))));

(* Example:
    unzip ["x", 1, "y", 2] = (["x", "y"], [1,2]);
    (not syntactically correct, since heterolist cannot be written with []) *)
local
  fun unzip_a HNil acc = acc
  | unzip_a (HCons(a, bas)) (acc_a, acc_b) = unzip_b bas (acc_a @ [a], acc_b)
  and unzip_b HNil acc = acc
  | unzip_b (HCons(b, abs)) (acc_a, acc_b) = unzip_a abs (acc_a, acc_b @ [b])
in
  fun unzip hlist = unzip_a hlist ([], [])
end;

(* Example:
    zip (["x", "y"], [1,2]) = ["x", 1, "y", 2];
    (not syntactically correct, since heterolist cannot be written with []) *)
local
  fun zip_a ([], []) = HNil
  | zip_a ([], _) = raise Empty
  | zip_a (a::ass, bs) = HCons(a, zip_b(ass, bs))
  and zip_b ([], []) = HNil
  | zip_b (_, []) = raise Empty
  | zip_b (ass, b::bs) = HCons(b, zip_a(ass, bs))
in
  fun zip two_hlists = zip_a two_hlists
end;


(* One direction sequences *)
exception EmptySeq;
datatype 'a seq = Nil | Cons of 'a * (unit-> 'a seq);
fun head(Cons(x,_)) = x | head Nil = raise EmptySeq;
fun tail(Cons(_,xf)) = xf() | tail Nil = raise EmptySeq;

(* Bidirectional sequences *)
datatype direction = Back | Forward;
datatype 'a bseq =   bNil | bCons of 'a * (direction -> 'a bseq);
fun bHead(bCons(x,_)) = x | bHead bNil = raise EmptySeq;
fun bForward(bCons(_,xf)) = xf(Forward) | bForward bNil = raise EmptySeq;
fun bBack(bCons(_,xf)) = xf(Back) | bBack bNil = raise EmptySeq;

(* Creates Bidirectional sequence of consequtive integers with n as starting pivot *)
fun intbseq n = bCons(n, fn dir =>
  (case dir of Forward => intbseq (n+1) | Back => intbseq (n-1)));

fun bmap _ bNil = bNil
| bmap f (bCons(x, xf)) = bCons(f x, fn dir => bmap f (xf dir));

fun bfilter _ _ bNil = bNil
| bfilter pred dir (bCons(x, xf)) = if pred x then
    bCons(x, fn dir => bfilter pred dir (xf dir))
    else bfilter pred dir (xf dir);

fun seq2bseq _ Nil = bNil |
    seq2bseq Nil (Cons(fw, fwf)) = bCons(fw, fn dir =>
        case dir of Forward => seq2bseq (Cons(fw, fn () => Nil)) (fwf()) | 
                    Back => bNil) | 
    seq2bseq (Cons(bw, bwf)) (Cons(fw, fwf)) = bCons(fw, fn dir =>
        case dir of Forward => seq2bseq (Cons(fw, fn () => Cons(bw, bwf))) (fwf()) | 
                    Back => seq2bseq (bwf()) (Cons(bw, fn () => Cons(fw, fwf))));

local
  exception NonPositiveJump;
  fun jmp bNil _ _ = raise Empty
    | jmp biseq 0 _ = biseq
    | jmp (bCons(x, xf)) n dir = jmp (xf dir) (n-1) dir;
in
  fun bSeqJump bNil _ = raise Empty
  | bSeqJump (bCons(x, xf)) jump = if jump <= 0 then raise NonPositiveJump else
          bCons(x, fn dir => bSeqJump (jmp (bCons(x, xf)) jump dir) jump)
end;
