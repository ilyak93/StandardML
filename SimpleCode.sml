

fun isPalindromeAux (s,left,right) = if (left >= right) then true 
								   else String.sub(s,left) = String.sub(s,right) 
								   andalso isPalindromeAux (s,(left+1),(right-1));

fun isPalindrome s = if s = "" then true 
					 else isPalindromeAux (s,0,(size(s)-1));

fun	countLetterAux (s,c,i) = if (i<0) then 0 
							 else 
							 	if String.sub(s,i) = c then 1 + (countLetterAux (s,c,(i-1)))
							 	else countLetterAux (s,c,(i-1));

fun countLetter (s,c) = if (s = "") then 0 
					  	else countLetterAux (s,c,(size(s)-1));

fun nonRepeatedLetterAux (s,i) = if countLetter(s,(String.sub(s,i))) = 1 then (String.sub(s,i))
								 else nonRepeatedLetterAux (s,i+1);  

fun nonRepeatedLetter s = if size(s) = 1 then (String.sub(s,0))
						  else nonRepeatedLetterAux (s,0);

fun neg y = ~y;

fun int2stringAux z = if z < 10 then str(chr(ord #"0"+z)) else int2stringAux(floor(real(z)/10.0))^str(chr(ord #"0" + z mod 10));

fun int2string x = if x < 0 then "-"^int2stringAux(neg(x)) else int2stringAux(x);

fun ilsAux (f,s,ind) = if ind = 0 then f(String.sub(s,ind)) else f(String.sub(s,ind)) andalso ilsAux(f,s,ind-1);

fun isLegalString (f,s) = if s = "" then true else ilsAux(f,s,size(s)-1);

fun rvrsAux (s,ind) = if ind = 0 then str(String.sub(s,ind)) else str(String.sub(s,ind))^rvrsAux(s,ind-1);

fun reverseString s = if s = "" then "" else rvrsAux(s,size(s)-1);
