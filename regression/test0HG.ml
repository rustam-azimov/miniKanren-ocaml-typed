open MiniKanren
open Tester.M
open ImplicitPrinters
open Tester 

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

let rec appendo l s ls =
 conde [
   (l === !Nil) &&& (s === ls);
   fresh (x l' ls')
      (l === x % l')
      (ls === x % ls')
      (appendo l' s ls')
 ]

(*let rec prependo (x : char llist) (l : (char llist) llist) (xl : (char llist) llist) =
 *conde [
 *  (l === !Nil) &&& (xl === !Nil);
 *  fresh (y l' xl')
 *     (l === y % l')
 *     (uniono (of_list [x ^ y]) xl' xl)
 *     (prependo x l' xl')
 *]
 *
 *let rec concato l s ls =
 *conde [
 *  (l === !Nil) &&& (ls === !Nil);
 *  fresh (x l' xs ls')
 *     (l === x % l')
 *     (prependo x s xs)
 *     (uniono xs ls' ls)
 *     (concato l' s ls')
 *]
 *)


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

  ()
