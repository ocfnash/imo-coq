Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

From q3_2001 Require Export misc.

(* As elsewhere, no difference to work over a general type with decidable
   equality except that we'd have to litter the codebase with lots of 
   'decA' terms so let's just stick with nat. *)
Definition nunique := compose (@length nat) (nodup Nat.eq_dec).

Lemma nunique_spec_0 : forall (l : list nat),
  nunique l = length (nodup Nat.eq_dec l).
Proof. auto. Qed.

Lemma nunique_spec_1 : forall (l : list nat),
  nunique l = 0 <-> l = [].
Proof. intros l. rewrite nunique_spec_0. rewrite length_zero_iff_nil. apply nodup_empty_spec. Qed.

Lemma nunique_spec_2 : forall (l : list nat),
  nunique l <> 0 <-> l <> [].
Proof. intros l. split; apply contrapositive; rewrite nunique_spec_1; trivial. Qed.

Lemma nunique_spec_3 : forall (l : list nat) (x : nat),
  In x l -> nunique (x::l) = nunique l.
Proof.
  intros l x Hx. unfold nunique. unfold compose.
  assert (H_incl : incl (nodup Nat.eq_dec (x::l)) (nodup Nat.eq_dec l)). {
    unfold incl. intros x' Hx'. rewrite -> nodup_In. rewrite -> nodup_In in Hx'.
    destruct Hx'; [subst |]; assumption.
  }
  assert (H_incl' : incl (nodup Nat.eq_dec l) (nodup Nat.eq_dec (x::l))). {
    unfold incl. intros x' Hx'. rewrite -> nodup_In. rewrite -> nodup_In in Hx'. right. assumption.
  }
  apply NoDup_incl_length in H_incl; try (apply NoDup_nodup).
  apply NoDup_incl_length in H_incl'; try (apply NoDup_nodup).
  omega.
Qed.

Lemma nunique_spec_4 : forall (l : list nat) (x : nat),
  ~In x l -> nunique (x::l) = 1 + nunique l.
Proof.
  intros l x Hx. unfold nunique. unfold compose.
  assert (H_incl : incl (nodup Nat.eq_dec (x::l)) (x::(nodup Nat.eq_dec l))). {
    unfold incl. intros x' Hx'. simpl. rewrite -> nodup_In. rewrite -> nodup_In in Hx'. simpl in Hx'. assumption.
  }
  assert (H_incl' : incl (x::(nodup Nat.eq_dec l)) (nodup Nat.eq_dec (x::l))). {
    unfold incl. intros x' Hx'. rewrite -> nodup_In. simpl in Hx'. rewrite -> nodup_In in Hx'. simpl. assumption.
  }
  apply NoDup_incl_length in H_incl; try (apply NoDup_nodup).
  apply NoDup_incl_length in H_incl'; try (rewrite NoDup_cons_iff).
  - assert (H : length (nodup Nat.eq_dec (x :: l)) = length (x :: nodup Nat.eq_dec l)). { omega. }
    rewrite -> H. reflexivity.
  - split.
    + rewrite -> nodup_In. assumption.
    + apply NoDup_nodup.
Qed.

Lemma nunique_spec_5 : forall (l : list nat),
  l = [] <-> nunique l = 0.
Proof.
  intros l.
  split; intros H.
  - subst. auto.
  - rewrite nunique_spec_0 in H. rewrite length_zero_iff_nil in H.
    rewrite nodup_empty_spec in H. assumption.
Qed.
