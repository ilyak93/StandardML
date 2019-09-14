(* Ilya Kotlov s3218517@campus.technion.ac.il 
   Michael Shohat michaelsho@campus.yechnion.ac.il *)

fun curry f x y = f(x,y);

fun uncurry f(x,y) = f x y;

local
    fun splitUtf8String "" = ("", "") | 
        splitUtf8String s =
            let val (x::xs) = map (fn wc => UTF8.encode wc) (UTF8.explode s)
        in
            (x, List.foldl (op ^) "" xs)
        end 

    fun char_to_gematric_value c = case c of
        "א" => 1
        | "ב" => 2
        | "ג" => 3
        | "ד" => 4
        | "ה" => 5 
        | "ו" => 6
        | "ז" => 7
        | "ח" => 8
        | "ט" => 9
        | "י" => 10
        | "כ" => 20
        | "ך" => 20
        | "ל" => 30
        | "מ" => 40
        | "ם" => 40
        | "נ" => 50
        | "ן" => 50
        | "ס" => 60
        | "ע" => 70
        | "פ" => 80
        | "ף" => 80
        | "צ" => 90
        | "ץ" => 90
        | "ק" => 100
        | "ר" => 200
        | "ש" => 300
        | "ת" => 400
        | _ => 0;
 
    
    fun gematria_aux "" _ = 0 |
        gematria_aux s ~1 = 0 |
        gematria_aux s sz = 
        let 
            val (x,y) = splitUtf8String s
        in
            char_to_gematric_value(x) + gematria_aux y (sz-1)
        end
in
fun gematria "" = 0 |
    gematria s = 
    let
        val (x,y) = splitUtf8String s
    in
            gematria_aux s (size(y)) 
    end
end;

fun apply_on_nth_char f n s = if n < 0 orelse n >= size(s) then f(#"!") else f(String.sub(s,n));
	
local     
    fun c_bl_aux(s,i,num_of_opened_closures,num_of_oc_closures) = if i=size(s) then num_of_oc_closures 
															 else if String.sub(s,i)= #"(" 
															 then c_bl_aux(s,i+1, num_of_opened_closures+1,num_of_oc_closures) 
																  else if (String.sub(s,i)= #")" andalso num_of_opened_closures>0) 
																	   then c_bl_aux(s,i+1,num_of_opened_closures-1,num_of_oc_closures+1) 
																	   else c_bl_aux(s,i+1,num_of_opened_closures, num_of_oc_closures)
in	
    fun count_balanced(s) = c_bl_aux(s,0,0,0)*2
end;
