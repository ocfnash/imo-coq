Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From q3_2001 Require Export misc.
From q3_2001 Require Export largest_elt.

(* Similarly to nunique, we could work with any type with decidable equality
   at the cost of having to carry round a bunch of 'decA' terms. *)
Definition mode (l : list nat) : option nat :=
  largest_elt (nodup Nat.eq_dec l) (count_occ Nat.eq_dec l).

Lemma mode_spec_0 : forall (l : list nat),
  mode l = None <-> l = [].
Proof.
  intros l. split; intros H.
  - destruct (largest_elt (nodup Nat.eq_dec l) (count_occ Nat.eq_dec l)) eqn:mode_l.
    + (* largest_elt (nodup Nat.eq_dec l) (count_occ Nat.eq_dec l) = Some p : cannot actually happen *)
      unfold mode in H. rewrite mode_l in H. inversion H.
    + (* largest_elt (nodup Nat.eq_dec l) (count_occ Nat.eq_dec l) = None *)
      rewrite largest_elt_spec_2 in mode_l. apply nodup_empty_spec in mode_l. assumption.
  - subst. unfold mode. reflexivity.
Qed.

Lemma mode_spec_1 : forall (l : list nat),
  (exists x, mode l = Some x) <-> l <> [].
Proof. intros l. rewrite option_spec. split; apply contrapositive; rewrite mode_spec_0; trivial. Qed.

Lemma mode_spec_2 : forall (l : list nat) (x y : nat),
  mode l = Some x -> count_occ Nat.eq_dec l y <= count_occ Nat.eq_dec l x.
Proof.
  intros l x y Hl.
  destruct (in_dec Nat.eq_dec y l) as [Hy | Hy].
  - rewrite <- (nodup_In Nat.eq_dec) in Hy.
    apply largest_elt_spec_4 with (z:=y) in Hl; assumption.
  - rewrite (count_occ_not_In Nat.eq_dec) in Hy. rewrite -> Hy. apply Nat.le_0_l.
Qed.

Lemma mode_spec_3 : forall (l : list nat) (x : nat),
  mode l = Some x -> In x l.
Proof.
  intros l x Hl.
  apply largest_elt_spec_3 in Hl. rewrite <- (nodup_In Nat.eq_dec). assumption.
Qed.
