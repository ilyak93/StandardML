(* Ilya Kotlov 321851784 s3218517@campus.technion.ac.il *)

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