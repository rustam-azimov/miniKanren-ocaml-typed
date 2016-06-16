open MiniKanren
open Tester.M
open ImplicitPrinters
open Tester 

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
   (concato (of_list [of_list_hack ['a']]) x1 x1')
   (concato (of_list [of_list_hack ['b']]) x2 x2')
   (concato (of_list [of_list_hack ['c']]) x3 x3')
   (h1_f x1' x2' x3' rh')
   (concato x1 x2 x1x2)
   (concato x1x2 x3 x1x2x3)
   (uniono rh' x1x2x3 rh)
 ]
 
let h1_s rh = h1_f (of_list [of_list_hack ['a']])
              (of_list [of_list_hack ['b']])
              (of_list [of_list_hack ['c']])
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
	(rh === (of_list [of_list_hack ['a']; of_list_hack ['b']]))

let h2_s rh =
	fresh (rh_g)
		(h2_g rh_g)
		(h2_f rh_g rh)

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
  run1 ~n:1  (REPR (fun q -> containo q (of_list [1]) !true ) );
  run1 ~n:10  (REPR (fun q -> containo q (of_list [1]) !false ) );

  (*uniono tests*)
  run1 ~n:1  (REPR (fun q -> uniono (of_list [1]) (of_list [1]) q ) );
  run1 ~n:2  (REPR (fun q -> uniono q (of_list [1]) (of_list [2;3;1]) ) );
  run1 ~n:1  (REPR (fun q -> uniono (of_list [1]) q (of_list [1;2;3]) ) );

  (*appendo tests*)
  run1 ~n:1  (REPR (fun q -> appendo !Nil (of_list [1]) q ) );
  run1 ~n:1  (REPR (fun q -> appendo q (of_list [1]) (of_list [2;3;1]) ) );
  run1 ~n:1  (REPR (fun q -> appendo (of_list [1]) q (of_list [1;2;3]) ) );

  (*prependo tests*)
  run1 ~n:1  (REPR (fun q -> prependo (of_list ['a'; 'b']) 
  									   (of_list [of_list_hack ['c';'d']; 
                                                 of_list_hack ['e';'f']] )
  									   q ) );
  run1 ~n:1  (REPR (fun q -> prependo (q) 
  									   (of_list [of_list_hack ['c';'d']; 
                                                 of_list_hack ['e';'f']])
  									   (of_list [of_list_hack ['a';'c';'d']; 
                                                 of_list_hack ['a';'e';'f']]) ) );
  									   
  (*concato tests*)
  run1 ~n:1  (REPR (fun q -> concato (of_list [of_list_hack ['a';'b']; 
                                                 of_list_hack ['c';'d']]) 
  									   (of_list [of_list_hack ['e';'f']; 
                                                 of_list_hack ['g';'h']] )
  									   q ) );
  run1 ~n:1  (REPR (fun q -> concato (q) 
  									  (of_list [of_list_hack ['e';'f']; 
                                                of_list_hack ['g';'h']] )
  									  (of_list [of_list_hack ['a';'e';'f']; 
                                                of_list_hack ['a';'g';'h'];
                                                of_list_hack ['b';'e';'f']; 
                                                of_list_hack ['b';'g';'h']] ) ) );

  (*Hypergrammar_1 tests*)
  run1 ~n:1  (REPR (fun q -> (hypergrammar h1_s !(of_list_hack ['a';'b';'c']) q)
  							                    &&& (q === (of_list [true])) ) );  
  run1 ~n:1  (REPR (fun q -> (hypergrammar h1_s !(of_list_hack ['a';'b']) q )
                                                &&& (q === (of_list [true])) ) );
  (*Hypergrammar_2 tests*)
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s !(of_list_hack ['a';'b']) q)
  							                    &&& (q === (of_list [true])) ) );  
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s !(of_list_hack ['a';'b';'c']) q )
                                                &&& (q === (of_list [true])) ) );
  run1 ~n:(-1)  (REPR (fun q -> (hypergrammar h2_s (q) (of_list [true])) ) );
*)

  ()
