(* Ilya Kotlov s3218517@campus.technion.ac.il 
   Michael Shohat michaelsho@campus.yechnion.ac.il *)
 
local
    fun findIndexOfReminder [] _ = ~1 |
        findIndexOfReminder ((cur_rem,_)::ts) reminder = 
            if cur_rem = reminder then 0
            else 1+(findIndexOfReminder ts reminder)
   
    fun devider_aux n m lst = if List.exists (fn (rem,_) => rem = n mod m) lst
                            then [(findIndexOfReminder lst (n mod m),~1)]@lst
                          else
                            if n mod m = 0 
                                then [(~1,~1)]@lst
                            else 
                                devider_aux ((n*10) mod m) m (lst@[((n mod m),(n*10 div m))])
                                
    fun split ((~1,_)::xs) = (List.take(xs,0), List.drop(xs,0)) |
        split ((index,_)::xs) = (List.take(xs,index), List.drop(xs,index))
           
                                
    fun devider n m = 
        let 
            val res = devider_aux n m []
            val (rem, _) = hd(List.take(res,1))
            fun intsToString [] = "" |
                intsToString r = foldl (fn ((_,qout),init) => init^Int.toString(qout)) "" r
            
        in
            if rem = ~1 
                then "0."^(intsToString (#2(split(res))))
            else
                "0."^(intsToString (#1(split(res))))^"("^(intsToString (#2(split(res))))^")"  
        end 
 
in 
    fun fraction2RepeatingDecimal _ 0 = "" |
        fraction2RepeatingDecimal 0 _ = "0.0" |
        fraction2RepeatingDecimal n m = devider n m;
    
end;  

datatype HuffmanTree =      
         Node of (string * int) * HuffmanTree * HuffmanTree   | 
         Symbol of char * int;
         
fun computeHistogram "" = [] |
    computeHistogram s = 
        let 
            fun stringToList "" _ = [] |
                stringToList s i = if (i = (String.size(s)-1)) then [String.sub(s,i)]
                                   else  (String.sub(s,i)::(stringToList s (i+1)))
        
            fun count (char_list:char list) chr = foldl (fn (x, c) => if x = chr then c+1 else c ) 0 char_list
            fun computeHistogramAux [] _ = [] |
                computeHistogramAux (chr::chrs) i = ((chr, (count (chr::chrs) chr))::(computeHistogramAux(List.filter (fn x => x <> chr) (chr::chrs)) 0))
        in
            computeHistogramAux (stringToList s 0) 0 
        end;
local   
    fun charHistToHoffmanTreeAuxHist [] = [] |
        charHistToHoffmanTreeAuxHist ((chr,count)::tx) = ((Symbol(chr,count))::(charHistToHoffmanTreeAuxHist tx))

    fun hoffmanTreeAuxGet (Symbol(c,i)) = (str(c),i) | 
        hoffmanTreeAuxGet (Node((c,i),d,e)) = (c,i)
        
    fun hoffmanTreeAuxCmp ta1 ta2 =  if #2(hoffmanTreeAuxGet ta1) = #2(hoffmanTreeAuxGet ta2) 
                                        then #1(hoffmanTreeAuxGet ta1) < #1(hoffmanTreeAuxGet ta2)
                                     else #2(hoffmanTreeAuxGet ta1) < #2(hoffmanTreeAuxGet ta2) 
    
    fun findMinimalPair [] = (Symbol(#"a",~1),Symbol(#"a",~1)) |
        findMinimalPair lst = 
            let
                fun findMin (t::[]) = t |
                    findMin (t1::t2::tx1) = if hoffmanTreeAuxCmp t1 t2 
                                                then findMin (t1::tx1)
                                            else findMin(t2::tx1)
                fun findSecondMin chr_list =
                    let 
                        val first_min = findMin chr_list
                        val lst_without_first = List.filter (fn (cur_vx) => cur_vx <> first_min) chr_list
                    in
                        findMin lst_without_first
                    end
            in 
                ((findMin lst),(findSecondMin lst))
            end
            
            fun buildHuffmanTreeAux [x] = [x] |
                buildHuffmanTreeAux lst = 
                    let 
                        val (first_min,second_min) = findMinimalPair lst
                        val lst_without_pair = List.filter (fn y => y <> second_min) (List.filter (fn x => x <> first_min) lst) 
                    in
                        buildHuffmanTreeAux ((Node((((#1(hoffmanTreeAuxGet first_min))^(#1(hoffmanTreeAuxGet second_min))),((#2(hoffmanTreeAuxGet first_min))+(#2(hoffmanTreeAuxGet second_min)))),first_min,second_min))::lst_without_pair)
                    end
            
in
    fun buildHuffmanTree lst = hd (buildHuffmanTreeAux (charHistToHoffmanTreeAuxHist(lst)))
    
end;   
                      
fun encodeMessage tree "" = "" |
    encodeMessage tree input = 
        let
            fun inorderComputeCodes (Symbol(chr,_)) (s:string) = [(chr, s)] |
                inorderComputeCodes (Node(t,lft,rht)) s = (inorderComputeCodes lft (s^"0")) 
                                                          @ (inorderComputeCodes rht (s^"1"));
            val code_list = inorderComputeCodes tree ""
            fun charToCode c lst = #2(hd(List.filter (fn (chr,code) => c = chr) lst))
            fun encodeMessageAux tree input ~1 = "" |
                encodeMessageAux tree input i  = (encodeMessageAux tree input (i-1))^(charToCode (String.sub(input,i)) code_list);
        in
            encodeMessageAux tree input (size(input)-1)
        end;
           
fun decodeMessage tree "" = "" |
    decodeMessage tree input = 
        let
            fun inorderComputeCodes (Symbol(chr,_)) (s:string) = [(chr, s)] |
                inorderComputeCodes (Node(t,lft,rht)) s = (inorderComputeCodes lft (s^"0")) 
                                                          @ (inorderComputeCodes rht (s^"1"));
            val code_list = inorderComputeCodes tree ""
            fun codeToChar cod = str(#1(hd(List.filter (fn (chr,code) => code = cod) code_list)))
            fun findCode i init max len =  
                if i >= (size(input)-1) 
                    then (max,len)
                else 
                    let
                        val cod = List.filter (fn (chr,code) => code = init^(str((String.sub(input,i+1))))) code_list
                    in
                        if cod <> [] 
                            then findCode (i+1) (init^(str((String.sub(input,i+1))))) (init^(str((String.sub(input,i+1))))) (i+2)
                        else
                            findCode (i+1) (init^(str((String.sub(input,i+1))))) max len
                    end;
            fun decodeMessageAux cur_index = 
                if cur_index >= (size(input)) 
                    then ""
                else
                    let
                        val (max,index) = findCode cur_index (str(String.sub(input,cur_index))) (str(String.sub(input,cur_index))) (cur_index+1) 
                    in 
                        (codeToChar(max))^(decodeMessageAux index)
                    end
        in
            decodeMessageAux 0
        end;
    
    fun encodeHuffmanTree tree = 
        let 
            fun inorderGetHisto (Symbol(chr,count)) = [(chr, count)] |
                inorderGetHisto (Node(t,lft,rht)) = (inorderGetHisto lft)@(inorderGetHisto rht)
            val hst = inorderGetHisto tree
            fun intToString n =
                let
                    fun intToStringAux 0 = "" |
                        intToStringAux n = (intToStringAux(floor(real(n)/10.0)))^(str(chr(ord(#"0") + n mod 10)))
                    val num = intToStringAux n
                in
                    str(chr(ord(#"0") + size(num)))^num
                end
            fun encodeAux [] = "" |
                encodeAux ((chr,count)::tx) = (str(chr))^(intToString count)^(encodeAux tx)
        in
            encodeAux hst
        end;
    
    fun decodeHuffmanTree code = 
        let 
            fun getSubstring str s 0 = "" |
                getSubstring str s len = (getSubstring str s (len-1))^(String.str((String.sub(str,s+len-1))))
            
            fun decodeAux i chr_count_list = 
                if i>=size(code) 
                    then chr_count_list
                else
                    let 
                        fun stringToInt str i = 
                        if i >= size(str) 
                            then 0 
                            else ((ord(String.sub(str, (i))))-ord(#"0"))*(pow 10 (size(str)-i-1))+(stringToInt str (i+1))
                        val sz = (ord(String.sub(code, (i+1))))-ord(#"0")
                        val count = stringToInt (getSubstring code (i+2) sz) 0
                    in
                        decodeAux (i+2+sz) (chr_count_list@[((String.sub(code,i)),count)])
                    end
        in
            buildHuffmanTree(decodeAux 0 [])
        end;
        
        