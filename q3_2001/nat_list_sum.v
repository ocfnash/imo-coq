Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition nat_list_sum (l : list nat) :=
  fold_right Nat.add 0 l.

Lemma nat_list_sum_app : forall (l l' : list nat),
  nat_list_sum (l++l') = (nat_list_sum l) + (nat_list_sum l').
Proof.
  induction l as [| x l IHl].
  - intros l'. reflexivity.
  - intros l'. rewrite <- app_comm_cons. simpl. rewrite (IHl l'). omega.
Qed.

Lemma nat_list_sum_bound : forall (l : list nat) (n : nat),
  (forall m, In m l -> m <= n) -> nat_list_sum l <= length l * n.
Proof.
  induction l as [| k l IHl].
  - intros. simpl. apply le_n.
  - simpl. intros. assert (Hk : k <= n). { apply H. left. reflexivity. }
    assert (Hl : nat_list_sum l <= length l * n). {
      apply IHl. intros. apply H. right. assumption. }
    omega.
Qed.

Lemma nat_list_sum_permutation : forall (l l' : list nat), Permutation l l' ->
  nat_list_sum l = nat_list_sum l'.
Proof.
  induction l as [| x l]; intros l' HP; simpl.
  - apply Permutation_nil in HP. subst. reflexivity.
  - assert (Hl' : exists l1' l2', l' = l1' ++ x::l2'). {
      assert (Hxl' : In x l'). { apply (Permutation_in x HP). left. reflexivity. }
      apply in_split. assumption.
    }
    destruct Hl' as [l1' [l2' Hl']].
    assert (H : Permutation l (l1' ++ l2')). {
      apply Permutation_cons_app_inv with (a:=x). rewrite -> Hl' in HP. assumption.
    }
    apply IHl in H. rewrite -> H. rewrite -> Hl'.
    repeat (rewrite -> nat_list_sum_app). simpl. omega.
Qed.
