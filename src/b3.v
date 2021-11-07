(* These exercises require inductive proofs. *)
(* Now that you have some experience with Coq, 
   you can use 'auto' tactic to avoid solving simple subgoals manually. *)

Require Import b1.
Require Import b2.
Require Import List.
Require Import Nat.
Require Import Lia.
Import ListNotations. 

Section NatDict'Proofs.
  Context {V: Type}.

  (* Prove that 'remove' operation actually removes a key. *)
  (* The list inside nat_dict_list consists of pairs.
     To extract components of such list's head, 
     either perform pattern matching in 'induction' tactics
     or directly 'destruct' the element of nat*V type. *)
  Lemma removed_not_contained (d: @nat_dict_list V) (n: nat):
    contains'' (remove'' d n) n = false.
  Proof. induction d. reflexivity. destruct a as [aF aS]. 
   destruct (Nat.eqb aF n) eqn: H. 
  {unfold remove''. rewrite H. apply IHd. }
  unfold remove''. rewrite H. unfold contains''. simpl. rewrite H. apply IHd.  Qed.  

  (* Define a mapping function similar to one defined for regular lists.
     It should replace values stored in dict but keep them under the same keys. *)
  Fixpoint map'' {W: Type} (f: V -> W) (d: @nat_dict_list V): @nat_dict_list W :=
    match d with
    | [] => []
    | (k, v) :: xs => (k, f v) :: map'' f xs
    end.
  

  (* Prove that a value stored in a mapped dict 
     requires a corresponding value stored in an original dict. *)
  Lemma dict_map_get {W: Type} (m: V -> W) (d: @nat_dict_list V):
    forall n w,
      (get'' (map'' m d) n = Some w) <->
      (exists v, get'' d n = Some v /\ m v = w).
  Proof. unfold iff. split.
  { induction d.  
    {simpl. intros. exfalso. inversion H.    }
    {
      destruct a as [aF aS].  
      destruct (Nat.eqb aF n) eqn: H. 
      {
        unfold get''.
        rewrite H. 
        unfold map''.
        rewrite H.
        intros.
        exists aS.
        split.
        {reflexivity. }
        inversion H0.
        reflexivity.
      }
      {
        unfold get''.
        rewrite H.
        unfold map''.
        rewrite H.
        apply IHd.
      }
    }
  } 
  {
    induction d.
    { simpl. intros.  inversion H. exfalso. inversion H0.  inversion H1. }
    {
      destruct a as [aF aS].  
      destruct (Nat.eqb aF n) eqn: H; unfold get''; rewrite H;
      unfold map'';
      rewrite H.
      {
        intros.
        inversion H0.
        inversion H1.
        inversion H2 in H3.
        rewrite <- H5 in H3.
        rewrite <- H5.
        inversion H3.
        reflexivity.
      }
      {
        apply IHd.
      }
    }
  } Qed.

  (* Implement a filtering function. 
     The result should contain only those keys whose values satisfy the predicate;
     in this case they remain unchanged. *)
  Fixpoint filter'' {U: Type} (f: U -> bool) (d: @nat_dict_list U): @nat_dict_list U :=
      match d with
      | [] => []
      | (k, v) :: xs => let tail := remove'' (filter'' f xs) k in
                        if f v
                        then
                          (k, v) :: tail
                        else
                          tail
      end.
  

(*...*)

  Lemma insert_others' (d: @nat_dict_list V):
  forall n v n', n <> n' -> get'' (insert'' d n v) n' = get'' d n'. 
  Proof.
     intros.
     simpl.
     rewrite <- PeanoNat.Nat.eqb_neq in H.
     rewrite H.
     induction d.
     {
       simpl.
       reflexivity.
     }
     {
       destruct a as [aF aS].
       destruct (eqb aF n) eqn: H1.
       {simpl.
       rewrite H1.
       rewrite PeanoNat.Nat.eqb_eq in H1.
       rewrite <- H1 in H.
       rewrite H.
       auto. }
       simpl.
       rewrite H1.
       {
        destruct (eqb aF n') eqn: H2.
        {
          simpl.
          rewrite H2.
          auto.
        }
        {
         simpl.
         rewrite H2.
         auto.  
        }
       }

       

     } Qed.





  Lemma contains_remove (d: @nat_dict_list V):
    forall a b : nat, (Nat.eqb a b = false) -> ((contains'' (remove'' d a) b = true )
      <-> (contains'' (d) b = true)).
  Proof. 
    intros.
    induction d.
    {
     simpl.
     reflexivity. 
    }
    {
      destruct a0 as [aF aS].
      destruct (Nat.eqb aF a) eqn:eqT.
      {
        simpl.
        rewrite eqT.
        apply PeanoNat.Nat.eqb_eq in eqT as eqCoq.

        (* Search Nat.eqb. *)

        (* Nat.eqb aF a = true -> Af = a *)
        (* apply Nat.eqb_implies_eq in eqT as eqCoq. *)
        rewrite <- eqCoq in H.
        unfold contains''.
        simpl.

        rewrite H.
        apply IHd.
      }
      {
        unfold remove''.
        rewrite eqT.
        unfold contains''.
        unfold get''.
        destruct (Nat.eqb aF b) eqn:eqTB.
        {reflexivity. }
        apply IHd.

      }
      

    } Qed.






  (* Prove that the result of filtering is actually filtered *)
  Lemma filter_elem (f: V -> bool) (d: @nat_dict_list V):
    forall n,
      (contains'' (filter'' f d) n = true) <->
      (exists v, get'' d n = Some v /\ f v = true).
  Proof. 
    induction d; simpl; unfold iff; split.
    1, 2: intros; exfalso; inversion H.
    {inversion H0. inversion H1. }  
    {
      destruct a as [aF aS]. 
      destruct (Nat.eqb aF n) eqn:eqT; destruct (f aS) eqn:fT.
      {
        eauto.
      }    
      intros H.
      (* remember eqT as eqNat. *)
      apply PeanoNat.Nat.eqb_eq in eqT as eqCoq.
      subst.
      rewrite removed_not_contained in H.
      exfalso.
      inversion H.
      {
        apply PeanoNat.Nat.eqb_neq in eqT as eqCoq.
        simpl.    
        
        inversion eqT.
        unfold contains''.
        simpl.
        rewrite eqT.
        intros LeftPart.
        apply contains_remove in LeftPart.
        2: auto.
        apply IHd in LeftPart.   
        auto.
      }
      intros LeftPart.
      apply contains_remove in LeftPart.
      2: auto.
      
      apply IHd in LeftPart.   
      auto.
    }
    {
      destruct a as [aF aS]. 
      destruct (Nat.eqb aF n) eqn:eqT; destruct (f aS) eqn:fT.
      {
        unfold contains''.
        unfold get''.
        rewrite eqT. 
        auto. 
      }
      {
        intros EX.
        exfalso.
        inversion EX.
        inversion H.
        inversion H0.
        subst.
        rewrite H1 in fT.
        inversion fT.
      }
      {
        intros.
        apply IHd in H.
        unfold contains''.
        unfold get''.
        rewrite eqT.        
        fold (get'' (remove'' (filter'' f d) aF) n).
        fold (contains'' (remove'' (filter'' f d) aF) n).
        apply contains_remove; auto.
      }
      {
        intros.
        apply IHd in H.
        unfold contains''.
        unfold get''.
        apply contains_remove; auto.
      }

    } 
    Qed.

  (* You (most probably) implemented list-based dictionary in a way
     that doesn't distinguish, say, [(1, 2), (3, 4)] and [(3, 4), (1, 2)] dicts. *)
  (* That is, the results of 'insert', 'contains' and other interface operations
     should be the same for them. *)
  (* Such lists are not-equal, though, 
     since the only list equal to [(1, 2), (3, 4)] is exactly [(1, 2), (3, 4)]. *)
  (* We can formalize the specific notion of equivalence for dictionaries 
     to prove their more complicated properties. *)
  (* Note that this equ ivalence only deals with dict interface 
     and not the particular implementation. *)
  Definition sim_dicts (d1 d2: @nat_dict_list V) :=
    forall n, get'' d1 n = get'' d2 n.

(*...*)

  Lemma get_remove_differrent:
    forall d: @nat_dict_list V,forall  k n: nat,  Nat.eqb k n = false -> get'' d n = get'' (remove'' d k) n.
  Proof.
    intros.
    induction d.
    {simpl. reflexivity. }
    destruct a as [PF PS].
    destruct (Nat.eqb PF n) eqn:EqN.
    {
      simpl.
      rewrite EqN.

     apply PeanoNat.Nat.eqb_eq  in EqN as EqK.
     rewrite <- EqK in H.
     rewrite PeanoNat.Nat.eqb_sym in H.
     
     rewrite H.
     simpl.
     rewrite EqN.
     reflexivity.
    }
    {
      unfold get''.
      unfold remove''.
      rewrite EqN.
      destruct (Nat.eqb PF k) eqn:EqK; try rewrite EqN; apply IHd.

    }
    
  Qed.
  
  


  Lemma sim_dicts_trans_eq: 
    forall d1 d2 k v, 
      sim_dicts d1  d2 
          -> sim_dicts ((k, v) :: d1) ((k, v) :: d2)
  .
  Proof.
    intros.
    unfold sim_dicts in *.
    intros.
    simpl.
    destruct (eqb k n) eqn: H1; auto. 

  Qed.
  


  Lemma sim_dicts_trans :
    forall d1 d2 d, sim_dicts d1 d -> sim_dicts d d2 -> sim_dicts d1 d2.

  Proof.
      unfold sim_dicts in *.
      intros.
      apply eq_trans with  (y := get'' d n); auto.
  Qed.

  Lemma sim_dicts_insertion: 
  forall d1 d2 k v, sim_dicts d1 d2 -> sim_dicts (insert'' d1 k v) (insert'' d2 k v)
  .
  Proof.
    intros.
    unfold sim_dicts.
    intros.
    destruct (Nat.eqb k n) eqn:Eq; auto.
    {
      simpl.
      rewrite Eq.
      auto.
    }
    {
      rewrite insert_others'.
      2: {apply PeanoNat.Nat.eqb_neq  in Eq. auto. }
      apply eq_sym.
      rewrite insert_others'.
      2: {apply PeanoNat.Nat.eqb_neq  in Eq. auto. }

      apply eq_sym.
      apply H.

    } Qed.


  Lemma remove_remove_with_same:
  forall (d: @nat_dict_list V) k, remove'' (remove'' d k) k = remove'' d k.
  Proof.
    intros.
    induction d.
    {
      simpl.
      reflexivity.
    }
    {
      destruct a as [aF aS].
      destruct (eqb aF k) eqn:EqK.
      {
        simpl.
        rewrite EqK.
        apply IHd.
      }
      simpl.
      rewrite EqK.
      simpl.
      rewrite EqK.
      rewrite IHd.
      reflexivity.

    } Qed.


  Lemma insert_remove_eq: 
  forall (d: @nat_dict_list V) k v, insert'' (remove'' d k) k v = insert'' d k v
  .
  Proof.
    intros.
    induction d.
    {
      simpl.
      reflexivity.
    }
    {
      destruct a as [aF aS].
      destruct (eqb aF k) eqn:EqK.
      {
        simpl.
        rewrite EqK.
        rewrite IHd.
        unfold insert''.
        simpl.
        rewrite EqK.
        reflexivity.
      }
      { 
        simpl.
        rewrite EqK.
        unfold insert''.
        simpl.
        rewrite EqK.
        rewrite remove_remove_with_same.
        reflexivity.
      }

    }
    
  Qed.
  


      
    

  (* Prove that an insertion makes a preceding removal pointless. 
     To ease the proof, you may want to prove separately that:
     - sim_dicts relation is transitive
     - an insertion of the same key-value pair preserves sim_dicts
     - a double insertion of the same key-value pair
       is similar (in terms of sim_dicts) to a single insertion
     - insertions of separate keys commute
       (that is, their results are related by sim_dicts).
     Also, it can be easier to operate on level of a higher level of 'insert's 
     instead of a lower level of list 'cons'es. 
     To replace 'cons' with 'insert', use 'fold' tactic. 
*)
  Lemma insert_remove_simpl (d: @nat_dict_list V) (n: nat) (v: V):
    sim_dicts (insert'' (remove'' d n) n v) (insert'' d n v).
  Proof.
    rewrite insert_remove_eq.
    unfold sim_dicts.
    reflexivity.
  Qed.

  
End NatDict'Proofs.   
