Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From q3_2001 Require Export stdlib_candidates.

(* Some of the below should really be axed. *)

(* There must be a tactic that does this but I couldn't find it. *)
Lemma equal_args : forall {A B : Type} (f : A -> B) (a a' : A),
  a = a' -> f a = f a'.
Proof. firstorder; subst; reflexivity. Qed.

Lemma option_spec : forall {X Y : Type} (f : X -> option Y) (x : X),
  (exists y : Y, f x = Some y) <-> f x <> None.
Proof.
  intros X Y f x. split; intros H.
  - unfold not. intros contra. rewrite contra in H. destruct H as [y Hy]. inversion Hy.
  - destruct (f x) eqn:Hx.
    + exists y. reflexivity.
    + exfalso. apply H. reflexivity.
Qed.

Lemma mult_is_O' : forall x y : nat,
  x <> 0 -> y <> 0 -> x * y <> 0.
Proof. intros x y Hx Hy contra. destruct (mult_is_O _ _ contra) as [Hx' | Hy']; contradiction. Qed.

Lemma list_empty_dec : forall {A : Type} (l : list A),
  {l = []} + {l <> []}.
Proof. destruct l; [left | right]; [reflexivity | discriminate]. Qed.

Lemma list_non_empty_iff_length_non_zero : forall {A : Type} (l : list A),
  l <> [] <-> length l <> 0.
Proof. intros A l. split; apply contrapositive; apply length_zero_iff_nil. Qed.

Open Scope bool_scope.

Definition orf {A : Type} (f g : A -> bool) (x : A) :=
  (f x) || (g x).

Definition negf {A : Type} (f : A -> bool) (x : A) :=
  negb (f x).

Lemma negf_spec_0 : forall (A : Type) (f : A -> bool) (x : A),
  f x = true <-> (negf f) x = false.
Proof.
 intros A f x. unfold negf.  unfold negb. split; intros Hfx.
 - rewrite -> Hfx. reflexivity.
 - destruct (f x); [reflexivity | inversion Hfx].
Qed.

Lemma negf_spec_1 : forall (A : Type) (f : A -> bool) (x : A),
  f x = false <-> (negf f) x = true.
Proof.
 intros A f x. destruct (f x) eqn:Hfx; unfold negf; unfold negb; rewrite -> Hfx.
  - simpl. firstorder.
  - split; reflexivity.
Qed.

Lemma divmod_spec_0 : forall x,
  Nat.divmod x 0 0 0 = (x, 0).
Proof.
  intros x.
  rewrite surjective_pairing at 1.
  pose (q := (fst (Nat.divmod x 0 0 0))).
  pose (u := (snd (Nat.divmod x 0 0 0))).
  pose (H := (Nat.divmod_spec x 0 0 0 (le_n 0))).
  assert (HD : (q, u) = Nat.divmod x 0 0 0). { symmetry. apply surjective_pairing. }
  rewrite <- HD in H. destruct H as [H H'].
  firstorder.
Qed.
