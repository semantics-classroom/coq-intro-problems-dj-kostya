Require Import Sorting.Permutation.
Require Import Lia.
Require Import List.
Export ListNotations.
Require Import Arith Arith.EqNat.
Require Extraction.

Fixpoint is_sorted' (l : list nat) : bool :=
  match l with
  | []      => true
  | a :: l' => 
      match l' with
      | []       => true
      | b :: l'' => leb a b && is_sorted' l'
      end
  end.

Inductive is_smallest : nat -> list nat -> Prop :=
| smallest_unit : forall a, is_smallest a [a]
| smallest_head : forall a b tl
                         (LE  : a <= b)
                         (SST : is_smallest b tl),
    is_smallest a (a :: tl)
| smallest_tail : forall a b tl
                         (LT : a < b)
                         (SST : is_smallest a tl),
    is_smallest a (b :: tl)
.

Inductive is_sorted : list nat -> Prop :=
| sorted_nil   : is_sorted []
| sorted_one a : is_sorted [a]
| sorted_cons a tl
              (SORTED : is_sorted tl)
              (SST : is_smallest
                       a (a :: tl))
  :
    is_sorted (a :: tl)
.

Theorem sort l :
  { l' | Permutation l l' & is_sorted l' }.
Proof.
  induction l.
  { exists [].
    { apply perm_nil. }
    apply sorted_nil. }
  inversion IHl.
  rename x into l'.
  rename H into PERM.
  rename H0 into SORT.
Abort.

Inductive is_inserted : nat -> list nat -> list nat -> Prop
  :=
| ins_head : forall n tl, is_inserted n tl (n :: tl)
| ins_tail : forall n m tl tl'
                    (INS : is_inserted n tl tl'),
    is_inserted n (m :: tl) (m :: tl')
.

Lemma is_inserted_perm a tl tl' 
  (INS : is_inserted a tl tl') :
  Permutation (a :: tl) tl'.
Proof.
  generalize dependent a.
  generalize dependent tl'.
  induction tl.
  { intros.
    inversion INS.  
    apply Permutation_refl. }
    (* Search Permutation. *)
    (* apply perm_skip. *)
    (* apply perm_nil. *)
  intros.
  inversion INS.
  { apply Permutation_refl. }
  apply IHtl in INS0.
  (* apply perm_trans with (l' := (a :: a0 :: tl)). *)
  eapply perm_trans.
  { apply perm_swap. }
  apply perm_skip. apply INS0.
Qed.

Lemma insert_sorted a l (SORT : is_sorted l) :
  { l' | is_inserted a l l' & is_sorted l'}.
Proof.
  induction l.
  { exists [a]; constructor. }
  edestruct IHl as [l'].
  { clear -SORT. inversion SORT; subst.
    { constructor. }
    assumption. }
  destruct (le_gt_dec a a0).
  { exists (a::a0::l).
    { constructor. }
    apply sorted_cons; auto.
    eapply smallest_head; eauto.
    inversion SORT; subst.
    { constructor. }
    assumption. }

  exists (a0::l').
  { constructor. assumption. }
  
  clear -SORT i i0 g.
  induction i. 
  { constructor; auto.
    eapply smallest_head with (b:=n).
    { lia. }
    inversion i0; subst.
    { constructor. }
    assumption. }

  constructor; auto.
  apply smallest_head with (b:=m).
  2: { inversion i0; subst.
       { constructor. }
       assumption. }
  
  clear -SORT.
  inversion SORT; subst.
  inversion SST; subst.
  2: lia.
  inversion SST0; subst.
  { assumption. }
  { assumption. }
  lia.
Defined.

Theorem sort l :
  { l' | Permutation l l' & is_sorted l' }.
Proof.
  induction l.
  { exists [].
    { apply perm_nil. }
    apply sorted_nil. }
  inversion IHl.
  rename x into l'.
  rename H into PERM.
  rename H0 into SORT.
  apply (insert_sorted a l') in SORT.
  destruct SORT as [l'' AA BB].
  exists l''.
  2: { apply BB. }
  apply is_inserted_perm in AA.
  eapply perm_trans.
  2: apply AA.
  apply perm_skip.
  apply PERM.
Defined.

Print sort.

Extraction Language OCaml.





