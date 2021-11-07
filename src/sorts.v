Require Import Sorting.Permutation.
Require Import List.
Require Import Lia.
Require Import Arith Arith.EqNat.
Import ListNotations.



(* Fixpoint is_sorted (l: list nat) :bool :=
    match l with
    | [] => true
    | a :: l' => 
        match l' with
        | b :: l'' =>  leb a b && is_sorted l'
        | [] => true
        end
    end. *)
   
Inductive is_smallest : nat -> list nat -> Prop :=
| smallest_unit : forall a, is_smallest a [a]
| smallest_head : forall a b tl 
                    (LE : a <= b)
                    (SST: is_smallest b tl),
                is_smallest a (a :: tl)    
| smallest_tail : forall a b tl 
                    (LE : a <= b)
                    (SST: is_smallest a tl),
                is_smallest a (b :: tl)
.

Inductive is_sorted : list nat -> Prop :=
| sorted_nil  : is_sorted []
| sorted_one  : forall a, is_sorted [a] 
| sorted_cons : forall a tl 
                    (SORTED : is_sorted tl) 
                    (SST    : is_smallest a (a :: tl)), 
                is_sorted (a :: tl)

.


Inductive is_inserted : nat -> list nat -> list nat -> Prop
    :=
| ins_head : forall n tl, is_inserted n tl (n :: tl)
| ins_tail : forall n m tl tl' (INS : is_inserted n tl tl'),
                is_inserted n (m :: tl) (m :: tl')
.

Lemma is_inserted_perm a tl tl' (INS : is_inserted a tl tl') :
Permutation (a :: tl) tl'.
Proof.
    generalize dependent a.
    generalize dependent tl'.
    induction tl.
    {   intros.
        inversion INS. 
        apply Permutation_refl.    }
    intros.
    inversion INS.
    { apply Permutation_refl. }
    apply IHtl in INS0.
    (* apply perm_trans with (l' := (a :: a0 :: tl)). *)
    eapply perm_trans.
    { apply perm_swap. }
    apply perm_skip.
    apply INS0.
Qed.

Lemma insert_sorted a l (SORT: is_sorted l) : 
{ l' | is_inserted a l l' & is_sorted l'}.
Proof. Admitted.
    (* induction l.
    {exists [a]; constructor. }
    assert ( is_sorted l) as AA.
    { inversion SORT. 
        {constructor. }
        assumption. }
    apply IHl in AA.
    clear IHl.
    destruct AA as [l' INS SORT'].
    
    destruct (le_gt_dec a a0) as [AA|AA].
    { exists (a :: a0 :: l). 
        { constructor. }
        constructor. 
        { auto. }
        eapply smallest_head.
        { apply AA. }
        inversion SORT.
        { constructor. }
        assumption. }
    exists (a0 :: l').
    { constructor. auto. }
    inversion SORT.
    { subst. 
    inversion INS. 
    subst. 
    constructor.
    { constructor. }
    eapply smallest_head.
    2: constructor.
    lia. }
    subst.
    clear SORT SORTED.
    constructor.
    { assumption. }
    clear SORT'.
    
    generalize dependent l'.
    generalize dependent a.

    induction l; intros.
    { inversion INS. subst.
     eapply smallest_head.
     2: constructor.
     lia. }

    assert (is_smallest a0 (a0 :: l)) as BB.
    { inversion SST; subst. }. Admitted. *)
    
        
    
    
    





Theorem  sort l: 
    { l' | Permutation l l' & is_sorted l'}
.
Proof.
    induction l.
    { exists [].
    {apply perm_nil. }
    apply sorted_nil.
    }
    inversion IHl.
    rename x into l'.
    rename H into PERM.
    rename H0 into SORT.
    apply (insert_sorted a l') in  SORT.
    destruct SORT as [l'' AA BB].
    exists l''.
    2: apply BB.
    apply is_inserted_perm in AA. 
    eapply perm_trans. 
    2: apply AA. 
    apply perm_skip. 
    apply PERM.  
Qed.
