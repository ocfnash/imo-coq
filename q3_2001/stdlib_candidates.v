Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(* Minor results that _might_ be worth adding to stdlib.
   I've been pretty liberal in what I've included here. I will
   make a more careful pass in the future and consider a PR with
   some subset of these results, and cleaner proofs etc. *)

Lemma contrapositive : forall P Q : Prop, (* Surely in standard library but cannot find. *)
  (P -> Q) -> (~Q -> ~P).
Proof. intros P Q H H' p. apply H'. apply H. assumption. Qed.

Lemma list_in_nil : forall {A : Type} (l : list A),
  (forall a, ~In a l) -> l = [].
Proof.
  destruct l as [| a' l].
  - intros H. reflexivity.
  - intros H. exfalso. specialize H with (a:=a'). apply H. apply in_eq.
Qed.

Lemma filter_ext : forall (A : Type) (f g : A -> bool), (forall a, f a = g a) -> forall l, filter f l = filter g l.
Proof.
  intros A f g Hfg. induction l as [| a l]; [reflexivity|].
  specialize Hfg with (a:=a).
  destruct (f a) eqn:Hfa; simpl; rewrite <- Hfg; rewrite -> Hfa; rewrite IHl; reflexivity.
Qed.

Lemma filter_app : forall {A : Type} (f : A -> bool) (l l' : list A),
  filter f (l ++ l') = (filter f l) ++ (filter f l').
Proof.
  intros A f. induction l as [| x l IHl]; simpl; [reflexivity|].
  intros l'. destruct (f x) eqn:Hfx; specialize (IHl l'); rewrite IHl; auto.
Qed.

Lemma concat_nil' : forall {A : Type} (l : list (list A)),
  concat l = [] <-> (forall (m : list A), In m l -> m = []).
Proof.
  intros A. induction l as [| m' l IHl].
  - simpl. split; intros; [contradiction | reflexivity].
  - split; intros Hl.
    + intros m Hm. simpl in Hl. destruct (app_eq_nil _ _ Hl) as [Hm' Hl'].
      simpl in Hm. destruct Hm as [Hm | Hm].
      * subst. reflexivity.
      * apply IHl in Hm; assumption.
    + assert (Hl' : forall m, In m l -> m = []). { intros m Hm. apply Hl. right. assumption. }
      assert (Hm' : m' = []). { apply Hl. left. reflexivity. }
      simpl. apply IHl in Hl'. rewrite -> Hl'. rewrite -> Hm'. auto.
Qed.

Lemma concat_In : forall {A : Type} (l : list (list A)) (a : A),
  In a (concat l) <-> exists v, In v l /\ In a v.
Proof.
  intros A l a. induction l as [| v l Hv]; split.
  - simpl. contradiction.
  - intros [v [Hv _]]. inversion Hv.
  - simpl. intros Ha. rewrite in_app_iff in Ha. destruct Ha as [H | H].
    + exists v. auto.
    + apply Hv in H. destruct H as [v' [Hlv' Hav']]. exists v'. auto.
  - intros [v' [Hlv' Hav']]. simpl. rewrite in_app_iff. destruct Hlv' as [H | H].
    + subst. left. assumption.
    + right. rewrite Hv. exists v'. auto.
Qed.

Lemma concat_filter_map : forall {A : Type} (l : list (list A)) (f : A -> bool),
  concat (map (filter f) l) = filter f (concat l).
Proof.
  intros A l f. induction l as [| v l IHl]; [auto|].
  simpl. rewrite IHl. rewrite filter_app. reflexivity.
Qed.
Lemma nodup_empty_spec : forall {A : Type} (l : list A) (decA : forall x y, {x=y} + {x<>y}),
  nodup decA l = [] <-> l = [].
Proof.
  intros A l decA. split; intros H.
  - assert (H' : forall a, ~In a l). {
      intros a contra. rewrite <- (nodup_In decA) in contra.
      rewrite -> H in contra. apply in_nil in contra. contradiction.
    }
    apply list_in_nil. assumption.
  - subst. reflexivity.
Qed.

Lemma filter_empty_spec : forall (A : Type) (f : A -> bool) (l : list A),
  filter f l = [] <-> (forall x, In x l -> f x = false).
Proof.
  intros A f l. split.
  - intros H x Hx. destruct (f x) eqn:Hx'.
    + exfalso. assert (H' : In x (filter f l)). { rewrite filter_In. split; assumption. }
      rewrite -> H in H'. apply in_nil in H'. contradiction.
    + reflexivity.
  - intros H. apply list_in_nil. intros a. intros contra. rewrite filter_In in contra.
    destruct contra as [Ha Hf]. apply H in Ha. rewrite -> Hf in Ha. inversion Ha.
Qed.

Lemma filter_non_empty_spec : forall (A : Type) (f : A -> bool) (l : list A),
  filter f l <> [] <-> (exists x, In x l /\ f x = true).
Proof.
  intros A f l.
  assert (H_dec : forall x, {f x = true} + {f x <> true}). {
    intros x. destruct (f x) eqn:Hx; firstorder.
  }
  assert (H_dec' : forall x, f x = false \/ f x <> false). {
    intros x. destruct (f x) eqn:Hx; firstorder.
  }
  assert (DM : (exists x : A, In x l /\ f x = true) <-> ~(forall x, In x l -> f x = false)). {
    rewrite <- Forall_forall.
    rewrite <- Exists_exists.
    rewrite <- Exists_Forall_neg; try assumption.
    repeat (rewrite -> Exists_exists).
    split; intros [x Hx]; exists x.
    - rewrite -> Bool.not_false_iff_true; assumption.
    - rewrite -> Bool.not_false_iff_true in Hx; assumption.
  }
  rewrite -> DM. split; apply contrapositive; rewrite filter_empty_spec; trivial.
Qed.

Lemma combine_nil : forall {A B : Type} (l : list A),
  combine l (@nil B) = @nil (A*B).
Proof.
  intros A B l.
  apply length_zero_iff_nil.
  rewrite combine_length. simpl. rewrite Nat.min_0_r.
  reflexivity.
Qed.

Lemma filter_map_commute : forall {A B : Type} (g : A -> B) (fA : A -> bool) (fB : B -> bool) (l : list A),
  (forall x, In x l -> fB (g x) = fA x) -> filter fB (map g l) = map g (filter fA l).
Proof.
  induction l as [| y l IHl]; intros Hcomm; [reflexivity|].
  simpl; destruct (fB (g y)) eqn:HfB; destruct (fA y) eqn:HfA; simpl.
  - assert (filter fB (map g l) = map g (filter fA l)). {
      apply IHl. intros x Hx. apply Hcomm. apply in_cons. assumption.
    } rewrite H. reflexivity.
  - assert (contra : fB (g y) = fA y). { apply Hcomm. apply in_eq. }
    rewrite HfB in contra. rewrite HfA in contra. discriminate.
  - assert (contra : fB (g y) = fA y). { apply Hcomm. apply in_eq. }
    rewrite HfB in contra. rewrite HfA in contra. discriminate.
  - apply IHl. intros x Hx. apply Hcomm. apply in_cons. assumption.
Qed.

Lemma combine_firstn_l : forall {A B : Type} (l : list A) (l' : list B),
  length l <= length l' -> combine l l' = combine l (firstn (length l) l').
Proof.
  intros A B.
  induction l as [| x l IHl]; intros l' H; [reflexivity|].
  destruct l' as [| x' l']; [reflexivity|].
  simpl in H. apply le_S_n in H. apply IHl in H.
  simpl. rewrite H. reflexivity.
Qed.

Lemma combine_firstn_r : forall {A B : Type} (l : list A) (l' : list B),
  length l' <= length l -> combine l l' = combine (firstn (length l') l) l'.
Proof.
  intros A B l l'. generalize dependent l.
  induction l' as [| x' l' IHl']; intros l H.
  - simpl. apply combine_nil.
  - destruct l as [| x l]; [reflexivity|].
    simpl in H. apply le_S_n in H. apply IHl' in H.
    simpl. rewrite H. reflexivity.
Qed.

Lemma combine_firstn : forall {A B : Type} (l : list A) (l' : list B) (n : nat),
  firstn n (combine l l') = combine (firstn n l) (firstn n l').
Proof.
  intros A B. induction l as [| x l IHl]; intros l' n.
  - simpl. repeat (rewrite firstn_nil). reflexivity.
  - destruct l' as [| x' l'].
    + simpl. repeat (rewrite firstn_nil). rewrite combine_nil. reflexivity.
    + simpl. destruct n as [| n]; [reflexivity|].
      repeat (rewrite firstn_cons). simpl.
      rewrite IHl. reflexivity.
Qed.

Lemma nth_error_nth : forall {A : Type} (l : list A) (n : nat) (a : A),
  nth_error l n = Some a -> nth n l a = a.
Proof.
  intros A l n a H.
  apply nth_error_split in H. destruct H as [l1 [l2 [H H']]].
  subst. rewrite app_nth2; [|auto].
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma nth_error_nth' : forall {A : Type} (l : list A) (n : nat) (a : A),
  n < length l -> nth_error l n = Some (nth n l a).
Proof.
  intros A l n a H.
  apply nth_split with (d:=a) in H. destruct H as [l1 [l2 [H H']]].
  subst. rewrite H. rewrite nth_error_app2; [|auto].
  rewrite app_nth2; [| auto]. repeat (rewrite Nat.sub_diag). reflexivity.
Qed.

Lemma permutation_filter : forall {A : Type} (f : A -> bool) (l l' : list A),
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f.
  induction l as [| x l IHl]; intros l' Hl'.
  - apply Permutation_nil in Hl'. subst. apply Permutation_refl.
  - assert (Hx : In x l'). { apply Permutation_in with (l:=(x::l)) (x:=x) in Hl'; [assumption | apply in_eq]. }
    apply in_split in Hx. destruct Hx as [l1 [l2 H]].
    assert (H' : Permutation l (l1++l2)). { rewrite H in Hl'. apply Permutation_cons_app_inv in Hl'. assumption. }
    apply IHl in H'.
    simpl. destruct (f x) eqn:Hfx.
    + assert (Hfl : Permutation (filter f l') (x::filter f (l1++l2))). {
        rewrite H. repeat (rewrite filter_app). simpl. rewrite Hfx.
        apply Permutation_sym. apply Permutation_middle.
      }
      apply perm_skip with (x:=x) in H'. apply Permutation_sym in Hfl.
      apply (Permutation_trans H' Hfl).
    + assert (Hfl : filter f l' = filter f (l1 ++ l2)). {
        rewrite H. rewrite filter_app. simpl. rewrite Hfx. rewrite filter_app. reflexivity.
      }
      rewrite Hfl. assumption.
Qed.

Lemma nodup_fixed_point : forall {A : Type} (decA : forall x y, {x=y} + {x<>y}) (l : list A),
  NoDup l -> nodup decA l = l.
Proof.
  intros A decA. induction l as [| x l IHl]; [auto|]. intros H.
  simpl. destruct (in_dec decA x l) as [Hx | Hx]; rewrite NoDup_cons_iff in H.
  - destruct H as [H' _]. contradiction.
  - destruct H as [_ H']. apply IHl in H'. rewrite -> H'. reflexivity.
Qed.
