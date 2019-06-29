Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

From q3_2001 Require Export nat_list_sum.

Definition value_counts (l : list nat) :=
  map (count_occ Nat.eq_dec l) (nodup Nat.eq_dec l).

(* The proofs below are awful. I'd love to tidy them up if I can find the time. *)

Lemma value_counts_sum_in : forall (l : list nat) (x : nat),
  In x l -> nat_list_sum (value_counts (x::l)) = 1 + nat_list_sum (value_counts l).
Proof.
  intros l x Hx.
  pose (f := (fun x' => if Nat.eq_dec x x' then 1 + count_occ Nat.eq_dec l x' else count_occ Nat.eq_dec l x')).
  assert (Hf : forall x', f x' = count_occ Nat.eq_dec (x::l) x'). {
    intros x'. unfold f. simpl. destruct (Nat.eq_dec x x') as [Hxx' | Hxx']; reflexivity.
  }
  assert (Hfx : f x = 1 + count_occ Nat.eq_dec l x). {
    unfold f. destruct (Nat.eq_dec x x) as [Hxx | Hxx]; [reflexivity | contradiction].
  }
  assert (H : exists l', Permutation (nodup Nat.eq_dec l) (x::l')). {
    assert (Hx' : In x (nodup Nat.eq_dec l)). { apply nodup_In. assumption. }
    destruct (in_split x (nodup Nat.eq_dec l) Hx') as [l1 [l2 Hl1l2]].
    exists (l1++l2). rewrite -> Hl1l2. apply Permutation_sym. apply Permutation_middle.
  }
  destruct H as [l' Hl'].
  assert (H : ~In x l' /\ NoDup l'). {
    apply Permutation_NoDup in Hl'; [|apply NoDup_nodup].
    rewrite -> NoDup_cons_iff in Hl'. assumption.
  }
  destruct H as [Hxl' Hndl'].
  assert (Hf' : forall x', In x' l' -> f x' = count_occ Nat.eq_dec l x'). {
    intros x' H. assert (Hxx' : x <> x'). { intros contra. subst. contradiction. }
    unfold f. destruct (Nat.eq_dec x x') as [H' | H']; [contradiction | reflexivity].
  }
  assert (H_LHS : nat_list_sum (value_counts (x::l)) = 1 + (count_occ Nat.eq_dec l x) + nat_list_sum (map (count_occ Nat.eq_dec l) l')). {
    unfold value_counts.
    assert (HP : Permutation (nodup Nat.eq_dec (x::l)) (nodup Nat.eq_dec l)). {
      apply NoDup_Permutation; try (apply NoDup_nodup).
      intros x'. repeat (rewrite -> (nodup_In Nat.eq_dec)). split; intros H.
      - destruct H as [H' | H'].
        + subst. assumption.
        + assumption.
      - right. assumption.
    }
    pose (HP' := (Permutation_trans HP Hl')).
    apply Permutation_map with (f:=(count_occ Nat.eq_dec (x::l))) in HP'.
    apply nat_list_sum_permutation in HP'. rewrite -> HP'.
    rewrite <- (map_ext _ _ Hf). simpl. rewrite <- (map_ext_in _ _ l' Hf'). rewrite -> Hfx. omega.
  }
  assert (H_RHS : nat_list_sum (value_counts l) = (count_occ Nat.eq_dec l x) + nat_list_sum (map (count_occ Nat.eq_dec l) l')). {
    unfold value_counts.
    apply Permutation_map with (f:=(count_occ Nat.eq_dec l)) in Hl'. apply nat_list_sum_permutation in Hl'. rewrite -> Hl'. auto.
  }
  rewrite -> H_LHS. rewrite -> H_RHS. omega.
Qed.

Lemma value_counts_sum_not_in : forall (l : list nat) (x : nat),
  ~In x l -> nat_list_sum (value_counts (x::l)) = 1 + nat_list_sum (value_counts l).
Proof.
  intros l x Hx.
  assert (H : Permutation (nodup Nat.eq_dec (x::l)) (x::(nodup Nat.eq_dec l))). {
    apply NoDup_Permutation.
    - apply NoDup_nodup.
    - rewrite -> NoDup_cons_iff. rewrite -> nodup_In. split; [assumption | apply NoDup_nodup].
    - intros x'. rewrite -> nodup_In. simpl. rewrite -> nodup_In. firstorder.
  }
  assert (H' : Permutation (value_counts (x::l))
                           (map (count_occ Nat.eq_dec (x::l)) (x::(nodup Nat.eq_dec l)))). {
    apply Permutation_map. assumption.
  }
  assert (H'' : map (count_occ Nat.eq_dec (x::l)) (x::(nodup Nat.eq_dec l)) =
                1 :: (value_counts l)). {
    simpl.
    assert (Hxc : count_occ Nat.eq_dec l x = 0). { apply count_occ_not_In. assumption. } rewrite -> Hxc.
    assert (Hxr : (if Nat.eq_dec x x then 1 else 0) = 1). {
      destruct (Nat.eq_dec x x); [reflexivity | contradiction]. } rewrite -> Hxr.
    pose (f:=(fun x' : nat =>
      if Nat.eq_dec x x' then S (count_occ Nat.eq_dec l x') else count_occ Nat.eq_dec l x')).
    fold f.
    assert (Hlc : forall x', In x' (nodup Nat.eq_dec l) -> count_occ Nat.eq_dec l x' = f x'). {
      intros x' Hx'. rewrite nodup_In in Hx'. unfold f.
      assert (Hxx' : x <> x'). { intros contra. rewrite <- contra in Hx'. contradiction. }
      destruct (Nat.eq_dec x x'); [contradiction | reflexivity].
    }
    apply map_ext_in in Hlc. unfold value_counts. rewrite -> Hlc. reflexivity.
  }
  assert (Hf : Permutation (value_counts (x::l))
                            (1::(value_counts l))). {
    rewrite -> H'' in H'. assumption.
  }
  apply nat_list_sum_permutation in Hf. rewrite Hf. simpl. apply eq_S. reflexivity.
Qed.

Lemma count_occ_nodup : forall (l : list nat),
  length l = nat_list_sum (value_counts l).
Proof.
  induction l as [| x l IHl]; [auto|].
  destruct (in_dec Nat.eq_dec x l) as [Hx | Hx].
  - rewrite value_counts_sum_in; simpl; auto.
  - rewrite value_counts_sum_not_in; simpl; auto.
Qed.
