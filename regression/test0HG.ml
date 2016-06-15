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

open ImplicitPrinters

let _ =
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
  ()
