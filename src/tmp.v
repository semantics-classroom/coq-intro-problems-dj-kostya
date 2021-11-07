Print bool.


Inductive nat' :=
| MyZero
| MyOne
.

Print nat.

Compute 0.
Print O.



Definition nat_eq_0 n : bool := 
    match n with
    | 0 => true
    | _ => false
    end.

Print nat_eq_0.

Compute nat_eq_0 0.

Fixpoint is_odd n := 
match n with
| 0 => false
| 1 => true
| S (S n) => is_odd n
end.    

Print is_odd.









Require Import List.
Import ListNotations.



Module Attempt1.

    Inductive tree {A} :=
    | Empty
    | Leaf (a : A)
    | Node  (a : A) 
            (l : tree)
            (r : tree)
    .


    Fixpoint tree2list {A} (t: @tree A) : list A :=
        match t with
        | Empty  => [ ]
        | Leaf a => [ a ]
        | Node a l r => (tree2list l)  ++ (tree2list r) ++ [a]
        end
        .



End Attempt1. 









