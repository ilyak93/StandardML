(* Lev Pechersky 333815546 levpechersky@campus.technion.ac.il Kfir Taizi 208044610 kfirtaizi@campus.technion.ac.il *)

datatype color = BLACK | RED;
datatype 'a RBTree = Nil |  Br of (int * 'a * color) * 'a RBTree * 'a RBTree;
datatype Balance = RR | LR | LL | RL;
exception NotFound;


local (* of module *)
	val cmp = Int.compare;

	fun max (a, b) = if a>b then a else b;

	fun height Nil = 0
	| height (Br(_, l, r)) = 1 + max(height l, height r) 
in

fun black_height Nil = 0
| black_height (Br((_,_,BLACK), l, r)) = 1 + max(black_height l, black_height r)
| black_height (Br((_,_,RED), l, r)) = max(black_height l, black_height r);

local
	local
		fun keys_inorder Nil = []
		| keys_inorder (Br((k,_,_), l, r)) = (keys_inorder l) @ [k] @ (keys_inorder r)

		fun increasing_seq [] = true
		| increasing_seq [x] = true
		| increasing_seq (x1::x2::xs) = x2>x1 andalso increasing_seq(x2::xs);
	in
		fun is_BST tree = increasing_seq (keys_inorder tree)
	end;

	fun is_balanced Nil = true
	| is_balanced (Br(_, l, r)) = is_balanced l andalso is_balanced r andalso
			abs(height l - height r)<2

	fun root_is_black Nil = false
	| root_is_black (Br((_,_,c), _, _)) = c=BLACK;

	fun all_leaves_black Nil = true
	| all_leaves_black (Br((_,_,RED), Nil, Nil)) = false
	| all_leaves_black (Br((_,_,_), l, r)) = all_leaves_black l andalso all_leaves_black r;

	fun red's_children_black Nil = true
	| red's_children_black (Br((_,_,RED), l, r)) = root_is_black r andalso root_is_black l
			andalso red's_children_black l andalso red's_children_black r
	| red's_children_black (Br((_,_,BLACK), l, r)) = red's_children_black l andalso red's_children_black r;

	fun black_height_equal Nil = true
	| black_height_equal (Br(_, l, r)) = black_height l = black_height r;

	local
		fun leaves_depths (Nil, _) = []
		| leaves_depths (Br(_, Nil, Nil), cur_depth) = [cur_depth]
		| leaves_depths (Br((_,_,BLACK), l, r), cur_depth) = leaves_depths(l, cur_depth+1) @ leaves_depths(r, cur_depth+1)
		| leaves_depths (Br((_,_,RED), l, r), cur_depth) = leaves_depths(l, cur_depth) @ leaves_depths(r, cur_depth)
	in
		fun leaves_black_depth_equal Nil = true
		| leaves_black_depth_equal tree = let
				val all_depths = leaves_depths(tree, 0)
			in
				foldl (fn (x, acc) => acc andalso x=(hd all_depths)) true all_depths
			end
	end;
in
	fun is_rbtree Nil = true
	| is_rbtree tree = foldl (fn(f, acc) => f tree andalso acc) true
			[is_BST, is_balanced, root_is_black, all_leaves_black, red's_children_black,
			 leaves_black_depth_equal]
end;

fun size Nil = 0
| size (Br(_, l, r)) = 1 + size l + size r;

(* Counts all black nodes *)
fun blacks Nil = 0
| blacks (Br((_,_,BLACK), l, r)) = 1 + blacks l + blacks r
| blacks (Br((_,_,RED), l, r)) = blacks l + blacks r;

(* Postorder of values *)
fun postorder Nil = []
| postorder (Br((_,v,_),l,r)) = (postorder l) @ (postorder r) @ [v];

fun get (Nil, _) = raise NotFound
| get (Br((k,v,c),l,r), key) = case cmp(key, k) of
		EQUAL => (v,c) | GREATER => get (r, key) | LESS => get (l, key)

local (* of insert *)
	exception BadRoll;
	fun BF Nil = 0 | BF (Br(_, l, r)) = height l - height r;

	fun necessary_roll Nil = NONE
	| necessary_roll (Br(node, l, r)) =  case BF (Br(node, l, r)) of
			 2 => if BF l >= 0 then SOME LL else SOME LR
		| ~2 => if BF r <= 0 then SOME RR else SOME RL
		| _ => NONE; (* Assuming tree was balanced before *)

	(* webcourse.cs.technion.ac.il/234218/Winter2016-2017/ho/WCFiles/Recitation%205%20-%20AVL.pdf Slide 9*)
	fun roll(tree, NONE) = tree
	| roll(Br(b, Br(a, ll, lr), r), SOME LL) = Br(a, ll, Br(b, lr, r))
	| roll(Br(c, Br(b, ll, Br(a, lrl, lrr)), r), SOME LR) = Br(a, Br(b, ll, lrl), Br(c, lrr, r))
	| roll(Br(a, l, Br(b, rl, rr)), SOME RR) = Br(b, Br(a, l, rl), rr)
	| roll(Br(c, l, Br(b, Br(a, rll, rlr), rr)), SOME RL) = Br(a, Br(c, l, rll), Br(b, rlr, rr))
	| roll _ = raise BadRoll; (* Cannot occur in valid balanced tree *)
in
	fun insert (Nil, node) = Br(node, Nil, Nil)
	| insert (Br((k,v,c),l,r), (key,value,color)) = case cmp(key, k) of
			EQUAL   => Br((k,value,c),l,r)
		| GREATER => let val tree = Br((k,v,c), l,  insert(r, (key, value, color))) in
				roll(tree, necessary_roll tree) end
		| LESS    => let val tree = Br((k,v,c), insert(l, (key, value, color)),  r) in
				roll(tree, necessary_roll tree) end
end; (* of insert *)

(*
Serialization:
We build a list, containing full BFS traversal of tree as it were full
binary tree. Then we encode each non-Nil node in following format:
Tag, key, value (exact format is described below).
Each sequence of Nil nodes is compressed to pair of tag and number of
consequtive Nil nodes.
Tag is a single char representing a bit array (exact format is described below).
Every other value may be encoded in 1-4 characters. Tag contains information
about encoded values' sizes.

Serialization format (per characters):
[0]           tag
[1...length]  (length depends on tag) for regular nodes: node key and value
															 for Nil nodes: number of consequtive Nil nodes
[length+1]    next tag
[length+2...] next node (if any)

Tag (per bits):
[0-1] 0: empty (in this case it's 1st and last char in stream,
				 and all other data is irrelevant)
			1: BLACK
			2: RED
			3: Nil
[2-3]: ((number of bytes)-1) for key / for number of consequtive Nil nodes
[4-5]: ((number of bytes)-1) for value, e.g 01(binary) means that value
			 takes 2 bytes
[6]: key sign (1 is negative)
[7]: value sign (1 is negative)
*)
local (* of encode, decode *)
	(* Exception type for all serialization errors *)
	exception LSerialError;
	datatype tag = EMPTY | NIL_TAG | NODE_TAG;

	fun substr(s, from, to) = if from>to then ""
			else str(String.sub(s,from)) ^ substr(s, from+1, to);

	(* Returns list of length n, filled with value init *)
	fun fill_list(_, 0) = []
	| fill_list(init, n) = init :: fill_list(init, n-1);

	(* Checks how many bytes needed to store x, with no respect to sign.
		 For example, bytes_needed 255 = 1, bytes_needed 12345 = 2
		 Returns value in range 1..4 *)
	fun bytes_needed x = if (abs x)<256 then 1 else 1 + bytes_needed (x div 256);

	fun tag_type c = case (ord c) mod 4 of
			0 => EMPTY
		| 3 => NIL_TAG
		| _ => NODE_TAG;

	(* Convert number of bytes to tag format. Number of bytes must be in range 1..4,
		 since we work with int *)
	fun bytes2tag n = if n>0 andalso n<=4 then n-1 else raise LSerialError;

	(* Gets a node tag - single char containing all node metadata, and
		 returns it in readable format. *)
	fun unpack_tag c = let
		val tag = ord c
		val color = case tag mod 4 of 1 => BLACK | 2 => RED | _ => raise LSerialError
		val k_bytes = ((tag div 4) mod 4) + 1
		val v_bytes = ((tag div 16) mod 4) + 1
		val k_sign = if ((tag div 64) mod 2)=0 then 1 else ~1
		val v_sign = if ((tag div 128) mod 2)=0 then 1 else ~1
	in
		(color, k_bytes, v_bytes, k_sign, v_sign)
	end;

	fun pack_tag (color, k_bytes, v_bytes, k_sign, v_sign) = let
		val t_color = case color of BLACK => 1 | RED => 2
		val t_k_bytes = bytes2tag k_bytes
		val t_v_bytes = bytes2tag v_bytes
		val t_k_sign = if k_sign<0 then 1 else 0
		val t_v_sign = if v_sign<0 then 1 else 0
	in
		chr(t_color + 4*t_k_bytes + 16*t_v_bytes + 64*t_k_sign + 128*t_v_sign)
	end;

	(* Gets a Nil tag - single char containing all node metadata
		 Returns number of bytes where number of consequtive Nil nodes stored *)
	fun unpack_nil_tag c = (((ord c) div 16) mod 4) + 1;

	(* As explained before, 3 is code of Nil node *)
	fun pack_nil_tag len_bytes = chr(3 + (bytes2tag len_bytes)*4);

	(* Works with positive values only, sign information lost when zipping *)
	local
		fun zip 0 _ s = s
		| zip bytes x s = zip (bytes-1) (x div 256) (str(chr(x mod 256))^s);
	in
		fun zip_int bytes x = zip bytes (abs x) "";
	end

	(* Works with positive values only *)
	local
		fun unzip index s acc = if index>=String.size(s) then acc else
			unzip (index+1) s (acc*256 + ord(String.sub(s, index)));
	in
		fun unzip_int bytes s = if bytes<>String.size(s) then
			raise LSerialError else unzip 0 s 0;
	end

	(* Given tree, returns list representation of full binary tree.
		 List elements are trees. 1st element is root.
		 Missing nodes (if tree isn't full) are replaced with Nil trees. *)
	local (* of complete_bfs *)
		fun deeper_level [] = []
		| deeper_level (Nil::trees) = [Nil, Nil] @ deeper_level trees
		| deeper_level ((Br(node,l,r))::trees) = [l, r] @ deeper_level trees

		fun c_bfs_aux trees acc = let
			val next = deeper_level trees
		in
			if List.all (fn x => x=Nil) next then acc else (c_bfs_aux next (acc @ next))
		end
	in
		fun complete_bfs tree = c_bfs_aux [tree] [tree]
	end;

	fun tree2node Nil = NONE
	| tree2node (Br(node,_,_)) = SOME node;

	(* Returns encoded string, representing single node *)
	fun pack_node (k,v,c) = let
		val k_bytes = bytes_needed k
		val v_bytes = bytes_needed v
		val tag = pack_tag (c, k_bytes, v_bytes, k, v)
	in
		(str tag) ^ (zip_int k_bytes k) ^ (zip_int v_bytes v)
	end;

	fun unpack_node stream = let
		val (c, k_bytes, v_bytes, k_sign, v_sign) = unpack_tag (String.sub(stream, 0))
		val k = unzip_int k_bytes (substr(stream, 1, k_bytes))
		val v = unzip_int v_bytes (substr(stream, k_bytes+1, k_bytes + v_bytes))
	in
		(k*k_sign, v*v_sign, c)
	end;

	fun unpack_nils stream = let
		val bytes = unpack_nil_tag (String.sub(stream, 0))
		val nils_count = unzip_int bytes (substr(stream, 1, bytes))
	in
		fill_list(NONE, nils_count)
	end;
in
	local (* of encode *)
		(* Last Nil nodes are dropped *)
		fun pack_nodes ([], acc, _) = acc
		| pack_nodes (NONE::nodes, acc, nil_count) = pack_nodes(nodes, acc, nil_count+1)
		| pack_nodes (SOME(node)::nodes, acc, 0) = pack_nodes(nodes, acc@[pack_node node], 0)
		| pack_nodes (SOME(node)::nodes, acc, nil_count) = let
			val bytes = bytes_needed nil_count
			val consequtive_nils = str(pack_nil_tag bytes) ^ (zip_int bytes nil_count)
		in
			pack_nodes(nodes, acc@[consequtive_nils]@[pack_node node], 0)
		end
	in
		fun encode Nil = str(chr 0)
		| encode tree = foldl op^ "" (pack_nodes(map tree2node (complete_bfs tree), [], 0))
	end;

	local (* of decode *)
		fun unpack_string("", acc) = acc
		| unpack_string(stream, acc) = let
			val tag = String.sub(stream, 0)
		in
			case tag_type tag of
				NODE_TAG => let
					val (_, k_bytes, v_bytes, _, _) = unpack_tag tag
					val stream_tail = substr(stream, 1+k_bytes+v_bytes, String.size(stream)-1)
				in
					unpack_string(stream_tail , SOME(unpack_node stream)::acc)
				end
			| NIL_TAG => let
					val bytes = unpack_nil_tag tag
					val stream_tail = substr(stream, 1+bytes, String.size(stream)-1)
				in
					unpack_string (stream_tail, (unpack_nils stream) @ acc)
				end
			| EMPTY => [NONE]
		end;

		(* Returns list of lists of SOME nodes or NONE, where lists of lists are
			 levels of the decoded tree from bottom to root. If there are missing
			 nodes at bottom level, necessary number of NONE will be added to that level.
			 I.e. each list is of length of power of 2 *)
		fun break_to_levels([], _, acc) = acc
		| break_to_levels(list, level_width, acc) = let
			val missing_nodes = level_width - length list
			val current_level = if missing_nodes < 0 then List.take(list, level_width)
				else list @ fill_list(NONE, missing_nodes)
			val rest = if missing_nodes < 0 then List.drop(list, level_width) else []
		in
			break_to_levels (rest, 2*level_width, current_level::acc)
		end;

		(* Builds Rb tree from bottom to top, given a list of nodes by levels of depth *)
		local (* of build_tree *)
			fun build_level([], []) = []
			| build_level([], NONE::top) =  Nil::build_level([], top)
			| build_level([], (SOME node)::top) = (Br(node,Nil,Nil))::build_level([], top)
			| build_level(_::_::bottom, NONE::top) = Nil::build_level(bottom, top)
			| build_level(l::r::bottom, (SOME node)::top) = (Br(node,l,r))::build_level(bottom, top)
			| build_level _ = raise LSerialError;
		in
			fun build_tree ([], acc) = acc
			| build_tree (level::levels, acc) = build_tree(levels, build_level(acc, level))
		end (* of build_tree *)
	in
		(* "\^@" = \0 char represents an empty tree *)
		fun decode "\^@" = Nil
		| decode stream = let
			val tree_levels = break_to_levels(unpack_string(stream, []), 1, [])
		in
			hd (build_tree(tree_levels, []))
		end
	end (* of decode *)
end; (* of encode, decode *)

end; (* of module *)