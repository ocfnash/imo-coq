Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From q3_2001 Require Export misc.

(* TODO Retire in favour of largest_elt? *)
Definition nat_list_max (l : list nat) : nat :=
  fold_right max 0 l.

Lemma nat_list_max_spec_0 : forall m l,
  m <= nat_list_max (m::l).
Proof. intros. simpl. apply Nat.le_max_l. Qed.

Lemma nat_list_max_spec_1 : forall m l,
  nat_list_max l <= nat_list_max (m::l).
Proof. intros. simpl. fold nat_list_max. apply Nat.le_max_r. Qed.

Lemma nat_list_max_spec_2 : forall (l : list nat),
  l <> [] -> In (nat_list_max l) l.
Proof.
  intros l Hl. generalize dependent l. induction l as [| x l IHl]; try contradiction.
  destruct (Nat.max_spec_le x (nat_list_max l)) as [[Hmax Hmax'] | [Hmax Hmax']];
  intros H; simpl; rewrite Hmax'.
  + destruct (list_empty_dec l) as [Hl' | Hl'].
    * left. subst. simpl. simpl in Hmax. omega.
    * right. apply IHl in Hl'. apply Hl'.
  + left. reflexivity.
Qed.

Lemma nat_list_max_spec_3 : forall (l : list nat) (m : nat),
  In m l -> m <= nat_list_max l.
Proof.
  intros l m Hm. induction l as [| x l IHl]; try contradiction.
  destruct Hm as [H | H].
  - subst. apply nat_list_max_spec_0.
  - apply IHl in H. pose (H' := (nat_list_max_spec_1 x l)). omega.
Qed.

Lemma nat_list_max_spec_4 : forall (l : list nat),
  nat_list_max l = 0 <-> (forall x, In x l -> x = 0).
Proof.
  intros l.
  split.
  - intros H x Hx.
    apply nat_list_max_spec_3 in Hx. rewrite H in Hx. omega.
  - intros H. destruct (list_empty_dec l) as [Hl | Hl].
    + rewrite Hl. auto.
    + apply nat_list_max_spec_2 in Hl. apply H in Hl. assumption.
Qed.
