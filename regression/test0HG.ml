open MiniKanren
open Tester.M
open ImplicitPrinters
open Tester

(*convert string to list of chars*)
let toChars s =
  let rec helper i l =
    if i < 0 then l else helper (i - 1) (s.[i] :: l) in
  helper (String.length s - 1) [] 

let hackStr s = of_list_hack (toChars s)
let lstr s = !(hackStr s)
let lbool (b:bool) = of_list [b]

(*convert list of strings to list of (llist of chars)*)
let rec toHackList = function
	| [] -> []
	| x :: xs -> ((hackStr x) :: (toHackList xs))

(*build representation of set of strings*)
let strSet xs = of_list (toHackList xs)  

(*check if x contains in l*)
let rec containo x l ans =
 conde [
   (l === !Nil) &&& (ans === !false);
   fresh (y l')
      (l === y % l')
      (conde [
        (x === y) &&& (ans === !true);
        (x =/= y) &&& (containo x l' ans)
      ])
 ]

(*concat l and s without repetition*)
let rec uniono l s ls =
 conde [
   (l === !Nil) &&& (s === ls);
   fresh (x l' ans ls')
      (l === x % l')
      (containo x s ans)
      (conde [
         (ans === !true) &&& (uniono l' s ls);
         (ans === !false) &&& (x % ls' === ls) &&& (uniono l' s ls')
      ])
 ]

(*concat l and s with repetition*)
let rec appendo l s ls =
 conde [
   (l === !Nil) &&& (s === ls);
   fresh (x l' ls')
      (l === x % l')
      (ls === x % ls')
      (appendo l' s ls')
 ]

(*add x in the beginning of all elemnts of l*)
let rec prependo x l xl =
 conde [
   (l === !Nil) &&& (xl === !Nil);
   fresh (y l' xl' xy)
      (l === y % l')
      (appendo x y xy)
      (xl === xy % xl')
      (prependo x l' xl')
 ]

(*concat all elemnets of l with all elements of s*)
let rec concato l s ls =
 conde [
   (l === !Nil) &&& (ls === !Nil);
   fresh (x l' xs ls')
      (l === x % l')
      (prependo x s xs)
      (appendo xs ls' ls)
      (concato l' s ls')
 ]


(*
	Hypergrammar_1({a^n b^n c^n}):
	S -> f(a, b, c)
	f(X1, X2, X3) -> f(a*X1, b*X2, c*X3) + X1*X2*X3
	f(X1, X2, X3) -> empty_set,
	where:
		* --- concatination under sets of strings
		+ --- union under sets of strings
*)
let rec h1_f x1 x2 x3 rh =
 conde [
 	(rh === !Nil);
	fresh (x1' x2' x3' rh' x1x2 x1x2x3)
		(concato (strSet ["a"]) x1 x1')
   		(concato (strSet ["b"]) x2 x2')
   		(concato (strSet ["c"]) x3 x3')
   		(h1_f x1' x2' x3' rh')
   		(concato x1 x2 x1x2)
   		(concato x1x2 x3 x1x2x3)
   		(uniono rh' x1x2x3 rh)
 ]
 
let h1_s rh = h1_f (strSet ["a"])
              (strSet ["b"])
              (strSet ["c"])
              rh

(*
	Hypergrammar_2({aa, ba, ab, bb}):
	S -> f(g)
	f(X) -> X*X
	g -> {a, b}
*)

let h2_f x rh =
	concato x x rh

let h2_g rh =
	(rh === (strSet ["a"; "b"]))

let h2_s rh =
	fresh (rh_g)
		(h2_g rh_g)
		(h2_f rh_g rh)

(*
	Hypergrammar_3( {a, b}* ):
	S -> f(eps) (*eps is empty_string*)
	f(X) -> f(a*X) + X
	f(X) -> f(b*X) + X
	f(X) -> empty_set
*)

let rec h3_f x rh =
 conde [
	(rh === !Nil);
   	fresh (ax rh')
   		(concato (strSet ["a"]) x ax)
   		(h3_f ax rh')
   		(uniono rh' x rh);
   	fresh (bx rh')
   		(concato (strSet ["b"]) x bx)
   		(h3_f bx rh')
   		(uniono rh' x rh)
 ]

let h3_s rh = h3_f (strSet [""]) rh

(*
	Hypergrammar_4( a*b* ):
	S -> A(eps)*B(eps)
	A(X) -> A(a*X) + X
	A(X) -> empty_set
	B(X) -> B(b*X) + X
	B(X) -> empty_set
*)

let rec h4_A x rh =
 conde [
	(rh === !Nil);
   	fresh (ax rh')
   		(concato (strSet ["a"]) x ax)
   		(h4_A ax rh')
   		(uniono rh' x rh)
 ]

let rec h4_B x rh =
 conde [
	(rh === !Nil);
   	fresh (bx rh')
   		(concato (strSet ["b"]) x bx)
   		(h4_B bx rh')
   		(uniono rh' x rh)
 ]

let h4_s rh =
	fresh (rh_a rh_b)
		(h4_A (strSet [""]) rh_a)
		(h4_B (strSet [""]) rh_b)
		(concato rh_a rh_b rh)

(*check if str is correct string in language of hypergrammar with start_rule*)
let hypergrammar start_rule str correct =
	fresh (set_of_strings)
		(start_rule set_of_strings)
		(conde [
			(containo str set_of_strings !true) &&& (correct === (of_list [true]));
			(containo str set_of_strings !false) &&& (correct === (of_list [false]));
		])

let _ =
(*
  (*containo tests*)
  run1 ~n:1  (REPR (fun q -> containo q (lstr "a") !true ) );
  run1 ~n:(-1)  (REPR (fun q -> containo q (lstr "a") !false ) );

  (*uniono tests*)
  run1 ~n:1  (REPR (fun q -> uniono (strSet ["a"]) (strSet ["a"]) q ) );
  run1 ~n:2  (REPR (fun q -> uniono q (strSet ["a"]) (strSet ["b";"c";"a"]) ) );
  run1 ~n:1  (REPR (fun q -> uniono (strSet ["a"]) q (strSet ["b";"c";"a"]) ) );

  (*appendo tests*)
  run1 ~n:(-1)  (REPR (fun q -> appendo !Nil (strSet ["a"]) q ) );
  run1 ~n:(-1)  (REPR (fun q -> appendo q (strSet ["a"]) (strSet ["b";"c";"a"]) ) );
  run1 ~n:(-1)  (REPR (fun q -> appendo (strSet ["a"]) q (strSet ["a";"b";"c"]) ) );

  (*prependo tests*)
  run1 ~n:1  (REPR (fun q -> prependo (lstr "ab") 
  									   (strSet ["cd"; "ef"])
  									   q ) );
  run1 ~n:1  (REPR (fun q -> prependo (q) 
  									   (strSet ["cd"; "ef"])
  									   (strSet ["acd"; "aef"]) ) );
  									   
  (*concato tests*)
  run1 ~n:1  (REPR (fun q -> concato (strSet ["ab"; "cd"]) 
  									   (strSet ["ef"; "gh"])
  									   q ) );
  run1 ~n:1  (REPR (fun q -> concato (q) 
  									  (strSet ["ef"; "gh"])
  									  (strSet ["aef"; "agh"; "bef"; "bgh"]) ) );
*)
  (*Hypergrammar_1 tests*)
  run1 ~n:1  (REPR (fun q -> (hypergrammar h1_s (lstr "abc") q)
  							                    &&& (q === (lbool true)) ) );
  (*(*inf*)  
  run1 ~n:1  (REPR (fun q -> (hypergrammar h1_s (lstr "ab") q )
                                                &&& (q === (lbool true)) ) );
  *)
  
  (*Hypergrammar_2 tests*)
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s (lstr "ab") q)
  							                    &&& (q === (lbool true)) ) );  
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s (lstr "abc") q )
                                                &&& (q === (lbool true)) ) );
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s (q) (lbool true)) ) );
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s (q) (lbool false)) ) );
  
  (*Hypergrammar_3 tests*)
  run1 ~n:(1)  (REPR (fun q -> (hypergrammar h3_s (lstr "abaabb") q)
  							                    &&& (q === (lbool true)) ) );
  run1 ~n:(40)  (REPR (fun q -> (hypergrammar h3_s q (lbool false))) );  
  (*(*inf*)
  run1 ~n:(1)  (REPR (fun q -> (hypergrammar h3_s (lstr "abc") q )
                                                &&& (q === (lbool true)) ) );
  *)
  run1 ~n:(40)  (REPR (fun q -> (hypergrammar h3_s (q) (lbool true)) ) );

  (*Hypergrammar_4 tests*)
  run1 ~n:(1)  (REPR (fun q -> (hypergrammar h4_s (lstr "aaabb") q)
  							                    &&& (q === (lbool true)) ) );
  (*(*inf*)  
  run1 ~n:(1)  (REPR (fun q -> (hypergrammar h4_s (lstr "aababb") q )
                                                &&& (q === (lbool true)) ) );
  *)
  run1 ~n:(40)  (REPR (fun q -> (hypergrammar h4_s (q) (lbool true)) ) );


  ()
