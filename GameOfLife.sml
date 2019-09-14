(* Ilya Kotlov s3218517@campus.technion.ac.il 
   Michael Shohat michaelsho@campus.yechnion.ac.il *)

type matrix = bool list list;   

local 
    fun is_matrix_legal [] = false |
        is_matrix_legal [[]] = false |
        is_matrix_legal ((x::xs):matrix) = 
            let 
                val colls = List.length(x)
            in 
               List.all (fn y => List.length(y) = colls) xs
            end
in            
            
fun row_size []  = 0 |
    row_size [[]] = 0 |
    row_size (mat:matrix) = if is_matrix_legal(mat) then List.length(mat) else ~1; 
    
fun col_size [] = 0 |
    col_size [[]] = 0 |
    col_size ((x::xs):matrix) = if is_matrix_legal(x::xs) then List.length(x) else ~1; 
 

local 
    fun mat_get_row_col (mat:matrix) (row,col) = hd(List.drop(List.take(hd(List.drop(List.take(mat,row+1),row)),col+1),col))
    fun mat_get_row (mat:matrix) row = hd(List.drop(List.take(mat,row+1),row))
in  
    fun is_alive [] _ = false |
        is_alive [[]] _ = false|
        is_alive mat (row,col) = if is_matrix_legal(mat) = false orelse 
                                    (row >= row_size(mat)) orelse (row < 0) orelse 
                                    (col >= col_size(mat)) orelse (col < 0) then false
                                 else mat_get_row_col mat (row,col)

    local
        fun bool_to_int true = 1 |
            bool_to_int false = 0;
    in
        fun live_neighbours [] _ = ~1 |
            live_neighbours [[]] _ = ~1 |
            live_neighbours mat (row,col) = if is_matrix_legal(mat) = false orelse 
                                               (row >= row_size(mat)) orelse (row < 0) orelse 
                                               (col >= col_size(mat)) orelse (col < 0) then ~1
                                            else bool_to_int(is_alive mat (row-1,col-1)) + 
                                                 bool_to_int(is_alive mat (row,col-1)) + 
                                                 bool_to_int(is_alive mat (row+1,col-1)) + 
                                                 bool_to_int(is_alive mat (row+1,col)) +
                                                 bool_to_int(is_alive mat (row+1,col+1)) + 
                                                 bool_to_int(is_alive mat (row,col+1)) +
                                                 bool_to_int(is_alive mat (row-1,col+1)) + 
                                                 bool_to_int(is_alive mat (row-1,col))
    end

    local
        fun row_make (mat:matrix) row = 
            let
                val last_index = List.length((mat_get_row (mat) row))-1
                fun row_make_aux row 0 =
                let
                    val cur_cell = mat_get_row_col (mat) (row, 0)
                    val neighbours = live_neighbours (mat) (row,0)
                in
                    if (cur_cell = true) andalso ((neighbours <= 1) orelse (neighbours > 3))
                        then [false]
                    else 
                        if (cur_cell = false) andalso (neighbours = 3) 
                            then [true]
                        else [cur_cell]
                end 
                    |
                    row_make_aux row col_itr =
                let
                    val cur_cell = mat_get_row_col (mat) (row, col_itr)
                    val neighbours = live_neighbours (mat) (row,col_itr)
                in
                    if (cur_cell = true) andalso ((neighbours <= 1) orelse (neighbours > 3)) 
                        then ((row_make_aux row (col_itr-1))@[false])
                    else 
                        if (cur_cell = false) andalso (neighbours = 3) 
                            then ((row_make_aux row (col_itr-1))@[true])
                        else ((row_make_aux row (col_itr-1))@[cur_cell])
                end
            in
                    row_make_aux row last_index
            end
        fun next_state_aux [] _ = [[]] |
            next_state_aux [[]] _ = [[]] |
            next_state_aux (mat:matrix) 0 = [row_make mat 0] |
            next_state_aux mat row_ind = (next_state_aux mat (row_ind-1))@([row_make mat row_ind])
    in    
       fun next_state [] = [[]] |
           next_state [[]] = [[]] |
           next_state mat = if (is_matrix_legal(mat) = false) then [] else next_state_aux mat (List.length(mat)-1)
    end
end

fun start_game (mat:matrix) k = if (is_matrix_legal(mat) = false) then [] else
    let
        fun start_game_aux [] _ = [[]] |
        start_game_aux [[]] _ = [[]] |
        start_game_aux (mat:matrix) 0 =  mat |
        start_game_aux mat k = start_game_aux(next_state(mat)) (k-1); 
    in 
        start_game_aux mat k
    end
end;    