(*Ilya Kotlov 321851784 s3218517@campus.technion.ac.il*)


(*First*)
fun count_apps_aux lst_elem [] = 0 | 
	count_apps_aux lst_elem (x::xs) = 
		if x = lst_elem 
		then 1 + count_apps_aux lst_elem xs 
		else count_apps_aux lst_elem xs;

fun count_apps [] = [] |
 count_apps (x::xs) = (count_apps_aux x (x::xs))::(count_apps xs);

fun max_t ((e1,e2), (e3,e4)) = 
	if e2 > e4 
	then (e1,e2) 
	else (e3,e4);

fun max_e (e1,e2) = e1;

fun append_elm_count ([], []) = [] | 
	append_elm_count ((x::xs),(y::ys)) = (x,y)::append_elm_count(xs,ys);

fun toup_extract (a,b) = a;

fun common (x::xs) = toup_extract (foldl max_t (x, 0) (append_elm_count((x::xs) , count_apps (x::xs))));

(*Second*)
fun getLast (x::xs) = if (length xs = 0) then x else getLast xs;

fun getSeqAux [] _ = [] | 
	getSeqAux cur_list [y] = cur_list@[] |  
	getSeqAux (x::xs) (y::ys) = 
		if getLast (x::xs) + 1 = hd ys 
		then getSeqAux ((x::xs) @ [hd ys]) ys  
		else (x::xs); 

fun getSeq [] = [] | 
	getSeq (x::xs) = getSeqAux [x] (x::xs);

fun drop (0,xs) = xs | 
	drop (i, _::xs) = drop (i - 1, xs);

fun getSeqs [] = [[]] | 
	getSeqs lst = (getSeq lst)::(getSeqs (drop ((length(getSeq lst)), lst)));

fun maxSeqByLen (max_lst, lst) = 
	if length(max_lst) < length(lst) 
	then lst 
	else max_lst; 

fun getMaxSeq [] = [] | 
	getMaxSeq intlst = foldl maxSeqByLen (getSeq intlst) (getSeqs intlst);
	

(*Third*)
fun count_apps_aux lst_elem [] = 0 | 
	count_apps_aux lst_elem (x::xs) = 
		if x = lst_elem 
		then 1 + count_apps_aux lst_elem xs 
		else count_apps_aux lst_elem xs;

fun filter pred [] = [] | 
	filter pred (x::xs) =
		if pred x 
		then (x:: filter pred xs)
		else filter pred xs;

fun count_apps [] = [] |
 	count_apps (x::xs) = (count_apps_aux x (x::xs))::(count_apps (filter (fn y => y <> x) xs));

fun append_elm_count ([], []) = [] | 
	append_elm_count ((x::xs),(y::ys)) = (x,y)::append_elm_count( (filter (fn y => y <> x) xs) ,ys);

val l = [3,3,2,7,5,7,5];

fun thin (x::xs) = append_elm_count((x::xs) , count_apps (x::xs));



(*function 1*)
fun are_nighbours ((1,_,_,_),(_,_,1,_)) = true |
	are_nighbours ((_,1,_,_),(_,_,_,1)) = true |
	are_nighbours ((_,_,1,_),(1,_,_,_)) = true |
	are_nighbours ((_,_,_,1),(_,1,_,_)) = true |
	are_nighbours _ = false;		



(*function 2 aux func*)
fun getElem (0,(x::xs)) = x |
	getElem (j,(x::xs)) = getElem(j-1,xs);
fun getRow (0,x::xs) = x | 
	getRow (i,x::xs) = getRow (i-1, xs); 
fun getCellByIndex ((i,j),lst) : int*int*int*int = getElem(j,(getRow(i,lst)));

(*function 2*)
fun is_valid_maze maze = 
	let
		val len = length(maze)-1
		val wid = length(hd maze)-1
		val (x,y,z,w) = getCellByIndex ((0,0), maze)
		fun isLegalCell i j =
			let
				val curCelll = getCellByIndex ((i,j), maze)
				fun isRightLegal() = 
					let
						val rightCell = getCellByIndex ((i,j+1), maze)
					in
						(#3(curCelll),#1(rightCell)) = (1,1) orelse (#3(curCelll),#1(rightCell)) = (0,0)
					end 
				fun isBottomLegal() = let
						val rightCell = getCellByIndex ((i+1,j), maze)
					in
						(#4(curCelll),#2(rightCell)) = (1,1) orelse (#4(curCelll),#2(rightCell)) = (0,0)
					end 
			in
				if (i,j) = (len,wid) then true 
				else 
					if j = wid then isBottomLegal()
					else 
						if i = len then isRightLegal()
						else isRightLegal() andalso isBottomLegal()
			end

		fun isWholeMazeLegal i j = 
			if (i,j) = (len,wid) then true
			else 
				if j = wid then (isLegalCell i j) andalso (isWholeMazeLegal (i+1) 0)
				else (isLegalCell i j) andalso isWholeMazeLegal i (j+1)

	in
		if (len,wid) = (0,0) then x+y+z+w > 0 
		else  isWholeMazeLegal 0 0
	end;

(*functions 3+4 Aux funcs*)

fun isExitable dirCameFrom ((xCurr,yCurr),(xStart, yStart)) maze =  
	let
		val len = length(maze)-1
		val wid = length(hd maze)-1
	 	val curCelll = getCellByIndex ((xCurr,yCurr), maze)
		fun shortPathStartPoint() = 
	 		if (xCurr,yCurr) = (0,0) andalso (dirCameFrom = 2 orelse dirCameFrom = 3) then false
	 		else if (xCurr,yCurr) = (0,0) andalso (dirCameFrom = 1 andalso #1(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (0,0) andalso (dirCameFrom = 0 andalso #2(curCelll) = 1) then true
			else if (xCurr,yCurr) = (0,wid) andalso (dirCameFrom = 0 orelse dirCameFrom = 3) then false 
	 		else if (xCurr,yCurr) = (0,wid) andalso (dirCameFrom = 1 andalso #3(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (0,wid) andalso (dirCameFrom = 2 andalso #2(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (len,0) andalso (dirCameFrom = 1 orelse dirCameFrom = 2) then false 
	 		else if (xCurr,yCurr) = (len,0) andalso (dirCameFrom = 0 andalso #4(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (len,0) andalso (dirCameFrom = 3 andalso #1(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (len,wid) andalso (dirCameFrom = 0 orelse dirCameFrom = 1) then false 
	 		else if (xCurr,yCurr) = (len,wid) andalso (dirCameFrom = 2 andalso #4(curCelll) = 1) then true
	 		else if (xCurr,yCurr) = (len,wid) andalso (dirCameFrom = 3 andalso #3(curCelll) = 1) then true
	 		else if xCurr = 0 then false
			else if yCurr = 0 then false
			else if xCurr = List.length(maze)-1 then false
			else if yCurr = List.length(List.hd(maze))-1 then false
	 		else true
	 in
	 		if (xCurr,yCurr) = (xStart, yStart) then if shortPathStartPoint() then true else false
			else if xCurr = 0 andalso ((#2(curCelll)) = 1 andalso dirCameFrom <> 0 ) then true
			else if yCurr = 0 andalso ((#1(curCelll)) = 1  andalso dirCameFrom <> 1 ) then true
			else if xCurr = List.length(maze)-1 andalso ((#4(curCelll)) = 1 andalso dirCameFrom <> 3) then true
			else if yCurr = List.length(List.hd(maze))-1 andalso ((#3(curCelll)) = 1 andalso dirCameFrom <> 2) then true
			else false
	 end 

fun returnWallState 0 (curCel: int*int*int*int) : int = #1(curCel) |
	returnWallState 1 curCel = #2(curCel) |
	returnWallState 2 curCel = #3(curCel) |
	returnWallState 3 curCel = #4(curCel) 

fun goLeft dir = (dir-1)mod 4

fun goRight dir = (dir+1)mod 4

fun findPath f (strtDir,(xStr,yStr)) (dirCameFrom,(xCurr, yCurr)) currRoute maze = 
	let
		fun mirror dir = (dir+2)mod 4
		val currCell = getCellByIndex ((xCurr, yCurr), maze)
		fun dirPossible dir origDir = 
			let
				val right1 = f dir
				val right2 = f right1
				val right3 = f right2
			in
					if (returnWallState right1 currCell) = 1 then if origDir=right1 then ~1 else right1
					else if (returnWallState right2 currCell) = 1 then if origDir=right2 then ~1 else right2
					else if (returnWallState right3 currCell) = 1 then if origDir=right3 then ~1 else right3
					else ~1
			end
		fun getNextPos (0,(xCurr,yCurr)) = (xCurr,yCurr-1) |
			getNextPos (1,(xCurr,yCurr)) = (xCurr-1,yCurr) |
			getNextPos (2,(xCurr,yCurr)) = (xCurr,yCurr+1) |
			getNextPos (3,(xCurr,yCurr)) = (xCurr+1,yCurr)
	in
		if returnWallState dirCameFrom currCell <> 1 then [] else 
		if isExitable dirCameFrom ((xCurr,yCurr),(xStr,yStr)) maze then ((dirCameFrom,(xCurr, yCurr))::currRoute) 
		else (* go the rightest you can *) 
				if dirPossible dirCameFrom (dirCameFrom) = ~1 then []
				else let
						val nxtCameFrom1 = (mirror(dirPossible dirCameFrom (dirCameFrom) ))
						val nxtPos1 = getNextPos((dirPossible dirCameFrom (dirCameFrom),(xCurr, yCurr)))
						val nxt1 = findPath f (strtDir,(xStr,yStr)) (nxtCameFrom1, nxtPos1) ((dirCameFrom,(xCurr, yCurr))::currRoute) maze
						in
							if nxt1<>[] andalso ((List.exists(fn x => x=(nxtCameFrom1,nxtPos1))(nxt1))=true) then nxt1 
							else if dirPossible nxtCameFrom1 dirCameFrom = ~1 then []
							else let
									val nxtCameFrom2 = (mirror(dirPossible nxtCameFrom1 dirCameFrom))
									val nxtPos2 = getNextPos(((dirPossible nxtCameFrom1 dirCameFrom),(xCurr, yCurr)))
									val nxt2 = findPath f (strtDir,(xStr,yStr)) (nxtCameFrom2, nxtPos2) ((dirCameFrom,(xCurr, yCurr))::currRoute) maze
										in
											if nxt2<>[] andalso ((List.exists(fn x => x=(nxtCameFrom2,nxtPos2))(nxt2))=true) then nxt2 
											else if dirPossible nxtCameFrom2 dirCameFrom = ~1 then []
											else  let
													val nxtCameFrom3 = (mirror(dirPossible nxtCameFrom2 dirCameFrom))
													val nxtPos3 = getNextPos(((dirPossible nxtCameFrom2 dirCameFrom),(xCurr, yCurr)))
													val nxt3 = findPath f (strtDir,(xStr,yStr)) (nxtCameFrom3, nxtPos3) ((dirCameFrom,(xCurr, yCurr))::currRoute) maze
														in
															if nxt3<>[] andalso (((List.exists(fn x => x=(nxtCameFrom3,nxtPos3))) (nxt3))=true) then nxt3 else []
														end
													end
										end
	end

fun allStartPoints maze = 
		let
			fun getHorizonCords (curColl,maze) =
			let
				val currUpperCell = getCellByIndex ((0, curColl), maze)
				val currBottomCell = getCellByIndex ((length(maze) - 1, curColl), maze)

			in
				if curColl >= ((length(hd maze) - 1)) then 
					if(returnWallState 1 currUpperCell = 1) andalso 
						(returnWallState 3 currUpperCell = 1) then 
					   (1,(0,curColl))::(3,(length(maze)-1,curColl))::[]
				else if (returnWallState 1 currUpperCell = 1) then
													 (1,(0,curColl))::[]
				else if (returnWallState 3 currBottomCell = 1) then 
					(3,(length(maze)-1,curColl))::[]
				else []
			else	 
			if (returnWallState 1 currUpperCell = 1) andalso (returnWallState 3 currUpperCell = 1) then 
				(1,(0,curColl))::(3,(length(maze)-1,curColl))::getHorizonCords (curColl+1,maze)
			else if (returnWallState 1 currUpperCell = 1) then (1,(0,curColl))::getHorizonCords (curColl+1,maze)
			else if (returnWallState 3 currUpperCell = 1) then (3,(length(maze)-1,curColl))::getHorizonCords (curColl+1,maze)
			else getHorizonCords (curColl+1, maze)
		end

		fun getVerticalCords (curRow,maze) =
			let
				val currLeftCell = getCellByIndex ((curRow, 0), maze)
				val currRightCell = getCellByIndex ((curRow, length(hd maze)-1), maze)
			in
			if curRow >= ((length(maze) - 1)) then 
				if (returnWallState 0 currLeftCell = 1) andalso (returnWallState 2 currRightCell = 1) then 
			  		(0,(curRow,0))::(2,(curRow, length(hd maze) - 1))::[]
			  	else if (returnWallState 0 currLeftCell = 1) then (0,(curRow,0))::[]
			 	else if (returnWallState 2 currRightCell = 1) then (2,(curRow, length(hd maze)-1))::[]
			  	else [] 
			  else
			  if (returnWallState 0 currLeftCell = 1) andalso (returnWallState 2 currRightCell = 1) then 
			  		(0,(curRow,0))::(2,(curRow, length(hd maze) - 1))::getVerticalCords (curRow+1,maze)
			  else if (returnWallState 0 currLeftCell = 1) then (0,(curRow,0))::getVerticalCords (curRow+1,maze)
			  else if (returnWallState 2 currRightCell = 1) then (2,(curRow, length(hd maze)-1))::getVerticalCords (curRow+1,maze)
			  else getVerticalCords (curRow+1, maze)
			end

			val len = length(maze)-1
			val wid = length(hd maze)-1
	in
		(*List.filter (fn (x,(y,z)) => (x,(y,z)) <> (1,(len,wid)))
		(List.filter (fn (x,(y,z)) => (x,(y,z)) <> (1,(0,len)) )
		(List.filter (fn (x,(y,z)) => (x,(y,z)) <> (1,(0,wid)) )
		(List.filter (fn (x,(y,z)) => (x,(y,z)) <> (1,(0,0)) )*)(getHorizonCords (0,maze))@getVerticalCords(0,maze)(*))))*)
	end

	fun allRightPathes maze = 
		let
			fun allRightPathesAux [] maze = [[]] |
				allRightPathesAux [x] maze = [(findPath goRight x x [] maze)] | 
				allRightPathesAux (x::xs) maze = (((findPath goRight x x [] maze)::(allRightPathesAux xs maze)));
			val pathes = (allRightPathesAux (allStartPoints(maze)) maze);
		in
			List.filter (fn x => if x = [] then false else true) pathes
		end;

(*function3*)

(*len = 2 wid = 1 len = 1 wid = 2*)

fun exit_maze [[]] = true |
  	exit_maze maze = 
	let
		val len = length maze;
		val wid = length (hd maze)
		val (x,y,z,w) =  getCellByIndex ((0,0), maze)
	in
		if (len,wid) = (1,1) then if (x+y+z+w > 1) then true else false 
		else allRightPathes maze <> []
	end;


(*function4*)


(*to do: different 1 length pathes*)
fun differentPathesExist maze = 
	let
		fun allLeftPathes maze = 
			let
				fun allLeftPathesAux [] maze = [[]] |
					allLeftPathesAux [x] maze = [(findPath goLeft x x [] maze)] | 
					allLeftPathesAux (x::xs) maze = (((findPath goLeft x x [] maze)::(allLeftPathesAux xs maze)));
				val pathes = (allLeftPathesAux (allStartPoints(maze)) maze);
			in
				List.filter (fn x => if x = [] then false else true) pathes
			end;
	
	in
		let
			fun single pathes = map (fn (path) => map (fn (x:int,(y:int,z:int)) => (y,z)) path) pathes
			val right_pathes = single (allRightPathes maze)
			val left_pathes = single(allLeftPathes maze)
			fun isRightPathInLeftPath _ [] = true |
				isRightPathInLeftPath (x::xs) [y] = (xs = [] andalso x = y) |
 				isRightPathInLeftPath left_path (y::ys) = (List.exists (fn z => z = y) left_path) andalso  isRightPathInLeftPath left_path ys;
			
			fun isRightPathesInLeftPathes all_left_pathes [y] = (List.exists (fn z => ( (length(z) = 1) andalso isRightPathInLeftPath z y orelse isRightPathInLeftPath y z)) all_left_pathes) = false |
 				isRightPathesInLeftPathes all_left_pathes (y::ys) = ((List.exists (fn z => (isRightPathInLeftPath z y orelse isRightPathInLeftPath y z)) all_left_pathes) = false) andalso  isRightPathesInLeftPathes all_left_pathes ys;
		in
			isRightPathesInLeftPathes right_pathes left_pathes = false
		end
	end;

fun one_path_maze [[]] = true |
	one_path_maze maze =
	let
		val len = length maze;
		val wid = length (hd maze)
		val (x,y,z,w) =  getCellByIndex ((0,0), maze)
	in
		if (len,wid) = (1,1) then x+y+z+w = 2 
		else exit_maze maze andalso differentPathesExist maze = false
	end;





