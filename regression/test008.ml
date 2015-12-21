open GT
open MiniKanren
open Tester.M

let just_a a = a === !5

let a_and_b a =
  q (
    fun b ->
      conj (a === !7)
           (disj (b === !6)
                 (b === !5)
           )
  )

let a_and_b' b =
  q (
    fun a ->
      conj (a === !7)
           (disj (b === !6)
                 (b === !5)
           )
  )

let rec fives x =
  disj (x === !5)
       (fun st -> Stream.from_fun (fun () -> fives x st))

let rec appendo a b ab =
  disj
    (conj (a === !Nil) (b === ab) )
    (two
      (fun h t ->
        (conj (a === h % t)
           (one (fun ab' ->
              conj (h % ab' === ab)
                   (appendo t b ab')
           ))
        )
      )
    )

let rec reverso a b =
  disj
    (conj (a === !Nil) (b === !Nil))
    (succ one
      (fun h t ->
          (conj (a === h % t)
                (one (fun a' ->
                   conj (appendo a' !< h b)
                        (reverso t a')
                ))
        )
      )
    )

let show_int      = GT.( show(logic) (show int) )
let show_int_list = GT.( show(logic) (show(llist) (show int)) )

open Tester

let _ =
  run show_int_list empty_reifier 1  q (fun q   st -> REPR (appendo q (of_list [3; 4]) (of_list [1; 2; 3; 4]) st), ["q", q]);
  run show_int_list empty_reifier 4 qr (fun q r st -> REPR (appendo q (of_list []) r                          st), ["q", q; "r", r]);
  run show_int_list empty_reifier 1  q (fun q   st -> REPR (reverso q (of_list [1; 2; 3; 4])                  st), ["q", q]);
  run show_int_list empty_reifier  1  q (fun q   st -> REPR (reverso (of_list []) (of_list [])                 st), ["q", q]);
  run show_int_list empty_reifier  1  q (fun q   st -> REPR (reverso (of_list [1; 2; 3; 4]) q                  st), ["q", q]);
  run show_int_list empty_reifier  1  q (fun q   st -> REPR (reverso q q                                       st), ["q", q]);
  run show_int_list empty_reifier  2  q (fun q   st -> REPR (reverso q q                                       st), ["q", q]);
  run show_int_list empty_reifier  3  q (fun q   st -> REPR (reverso q q                                       st), ["q", q]);
  run show_int_list empty_reifier 10  q (fun q   st -> REPR (reverso q q                                       st), ["q", q]);
  run show_int_list empty_reifier  2  q (fun q   st -> REPR (reverso q (of_list [1])                           st), ["q", q]);
  run show_int_list empty_reifier  1  q (fun q   st -> REPR (reverso (of_list [1]) q                           st), ["q", q]);
  run show_int      empty_reifier  1  q (fun q   st -> REPR (a_and_b q                                         st), ["q", q]);
  run show_int      empty_reifier  2  q (fun q   st -> REPR (a_and_b' q                                        st), ["q", q]);
  run show_int      empty_reifier 10  q (fun q   st -> REPR (fives q                                           st), ["q", q])
