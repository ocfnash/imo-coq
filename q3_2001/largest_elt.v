Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From q3_2001 Require Export ceil.
From q3_2001 Require Export misc.
From q3_2001 Require Export nat_list_sum.

(* TODO Fold instead of Fixpoint ? *)
Fixpoint largest_elt {X : Type} (l : list X) (size : X -> nat) : option X :=
  match l with
  | [] => None
  | x::l' => match largest_elt l' size with
             | None => Some x
             | Some y => if size x <=? size y then Some y else Some x
             end
  end.

Lemma largest_elt_spec_1 : forall {X : Type} (l : list X) (size : X -> nat),
  (exists y, largest_elt l size = Some y) <-> l <> [].
Proof. (* TODO Prove largest_elt_2 directly and get this via option_spec *)
  destruct l; split; intros.
  - destruct H as [y Hy]. simpl in Hy. inversion Hy.
  - contradiction.
  - intros Hl. inversion Hl.
  - destruct (largest_elt l size) eqn:Hl; simpl; rewrite -> Hl.
    + destruct (size x <=? size x0).
      * exists x0. reflexivity.
      * exists x. reflexivity.
    + exists x. reflexivity.
Qed.

Lemma largest_elt_spec_2 : forall {X : Type} (l : list X) (size : X -> nat),
  largest_elt l size = None <-> l = [].
Proof.
  intros. destruct (list_empty_dec l) as [Hl|Hl]; subst.
  - simpl. split; reflexivity.
  - assert (Hl' : exists y : X, largest_elt l size = Some y). { apply largest_elt_spec_1. assumption. }
    destruct Hl' as [y Hy]. rewrite -> Hy. split; intros H.
    + inversion H.
    + contradiction.
Qed.

Lemma largest_elt_spec_3 : forall {X : Type} (l : list X) (size : X -> nat) (y : X),
  largest_elt l size = Some y -> In y l.
Proof.
  induction l as [| x l IHl]; intros.
  - inversion H.
  - destruct (largest_elt l size) eqn:Hl; simpl in H; rewrite -> Hl in H.
    + apply IHl in Hl. destruct (size x <=? size x0).
      * right. inversion H. subst. assumption.
      * left. inversion H. reflexivity.
    + inversion H. left. reflexivity.
Qed.

Lemma largest_elt_spec_4 : forall {X : Type} (l : list X) (size : X -> nat) (y z : X),
  largest_elt l size = Some y -> In z l -> size z <= size y.
Proof.
  induction l as [| x l IHl]; intros size y z H_largest H_in.
  - intros. inversion H_in.
  - destruct H_in; subst.
    + destruct (largest_elt l size) eqn:Hl. simpl in H_largest; rewrite -> Hl in H_largest.
      * destruct (Nat.leb_spec0 (size z) (size x)) as [Hx|Hx]; inversion H_largest; subst.
        -- assumption.
        -- apply le_n.
      * simpl in H_largest. rewrite -> Hl in H_largest. inversion H_largest. apply le_n.
    + destruct (largest_elt l size) eqn:Hl. simpl in H_largest; rewrite -> Hl in H_largest.
      destruct (Nat.leb_spec0 (size x) (size x0)) as [Hx|Hx]; inversion H_largest; subst.
      * apply IHl; assumption.
      * apply (le_trans (size z) (size x0) (size y)).
        -- apply IHl; assumption.
        -- omega.
      * apply largest_elt_spec_2 in Hl. subst. inversion H.
Qed.

Lemma largest_elt_spec_5 : forall {X : Type} (l : list X) (size : X -> nat) (y : X),
  largest_elt l size = Some y -> nat_list_sum (map size l) <= (length l) * (size y).
Proof.
  intros. assert (H_len : length (map size l) = length l). { apply map_length. } rewrite <- H_len.
  apply nat_list_sum_bound. intros m H_in. rewrite in_map_iff in H_in. destruct H_in as [x [Hx Hx_in]]. subst.
  apply (largest_elt_spec_4 l); assumption.
Qed.

Lemma largest_elt_spec_6 : forall {X : Type} (l : list X) (size : X -> nat) (x y z : X),
  largest_elt l size = Some y -> largest_elt (x::l) size = Some z -> size y <= size z.
Proof.
  intros X l size x y z Hy Hz. simpl in Hz. rewrite -> Hy in Hz.
  destruct (Nat.leb_spec0 (size x) (size y)) as [Hxy|Hxy]; inversion Hz; subst; omega.
Qed.

Lemma largest_elt_spec_7 : forall {X : Type} (l : list X) (size : X -> nat) (y : X),
  let N' := nat_list_sum (map size l) in
    largest_elt l size = Some y -> ceil N' (length l) <= size y.
Proof.
  destruct l as [| s l']; intros size y N' H.
  - simpl. apply Nat.le_0_l.
  - destruct (list_empty_dec l') as [Hl' | Hl']; subst.
    + unfold length. rewrite ceil_spec_2. unfold N'. simpl. simpl in H. rewrite Nat.add_0_r. inversion H. subst. apply le_n.
    + assert (Hlenl' : length l' <> 0). { rewrite length_zero_iff_nil. assumption. }
      rewrite <- (largest_elt_spec_1 l' size) in Hl'. destruct Hl' as [y' Hl'].
      rewrite ceil_spec_0.
      * assert (H1 : size s <= size y). {
          apply (largest_elt_spec_4 (s::l')).
          - assumption.
          - left. reflexivity. }
        assert (H2 : nat_list_sum (map size l') <= (length l') * (size y')). {
          apply largest_elt_spec_5. assumption. }
        assert (H3 : (length l') * (size y') <= (length l') * (size y)). {
          apply mult_le_compat_l.
          apply (largest_elt_spec_6 l' size s y' y); assumption. }
        unfold N'. simpl. omega.
      * simpl. intros contra. inversion contra.
Qed.
